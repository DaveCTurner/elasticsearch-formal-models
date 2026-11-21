theory Stateless_Recovery_Handoff
  imports Stateless_Changing_View_Liveness Stateless_Next_Publication
begin

section \<open>Keeping the Coordinator slot during a changing-view search\<close>

definition recovery_core_move where
  "recovery_core_move n x y \<longleftrightarrow> window_move x y \<and>
    incarnation (processes y n) = incarnation (processes x n) \<and>
    app_term (processes y n) = app_term (processes x n) \<and>
    issued (shared_state y) = issued (shared_state x)"

lemma lift_recovery_core_path:
  assumes "(recovery_core_move n ^^ k) (slot_exec st) x"
  shows "(next_slot_move n ^^ k) st (st\<lparr>slot_exec := x\<rparr>)"
  using assms
proof (induction k arbitrary: x)
  case 0
  then show ?case by simp
next
  case (Suc k)
  from Suc.prems obtain y where path: "(recovery_core_move n ^^ k) (slot_exec st) y"
    and step: "recovery_core_move n y x" by (rule relpowp_Suc_E)
  have "next_slot_move n (st\<lparr>slot_exec := y\<rparr>) (st\<lparr>slot_exec := x\<rparr>)"
    using step next_slot_core_move[where st="st\<lparr>slot_exec := y\<rparr>" and x=x and n=n]
    by (simp add: recovery_core_move_def)
  from relpowp_Suc_I[OF Suc.IH[OF path] this] show ?case .
qed

lemma service_slot_path:
  assumes path: "(next_slot_move n ^^ k) st st'"
    and service: "bounded_service {..<k} (\<lambda>i. {..<i}) select B horizon"
    and time: "k * B \<le> horizon"
  obtains run where "run 0 = st" "run (k * B) = st'"
    "\<And>j. next_slot_move n (run j) (run (Suc j))"
proof -
  from path obtain f where f: "f 0 = st" "f k = st'"
    "\<And>i. i < k \<Longrightarrow> next_slot_move n (f i) (f (Suc i))"
    unfolding relpowp_fun_conv by blast
  let ?run = "serviced_stateless_trace k select f"
  have "?run 0 = st" using f(1) by (simp add: serviced_stateless_trace_def)
  moreover have "?run (k * B) = st'"
    using serviced_stateless_trace_end[OF service time, of f] f(2) by simp
  moreover have "next_slot_move n (?run j) (?run (Suc j))" for j
    by (rule serviced_next_trace_projects[where k=k and sel=select and f=f, OF f(3)])
  ultimately show thesis by (rule that)
qed

text \<open>
  The search starts after election entry, while the first publication
  slot is still free. The header responses can differ in their provider
  views. The interlude before the base decision may include cleanup and
  storage effects, provided this process retains its incarnation, term,
  and empty slot and no publication is issued in the interlude. A
  separately serviced base decision either returns a readable protected
  image or uses the local or empty base. MasterService admission of the
  election-completion update and worker availability are part of the
  scheduled path. A replacement lease or a failed read can interrupt it.
\<close>

locale changing_view_slot_publication =
  fixes st :: stateless_slot_state and n :: node and i t :: nat
    and selected :: "nat \<Rightarrow> state_manifest option" and views replies
    and gap :: nat and y :: stateless_execution and warm base :: lineage
    and payload :: nat and F :: config and m :: state_manifest and files
  assumes reached: "stateless_slot_reachable n st"
    and free: "active_slot st = None" "slot_leading st"
    and pending: "searches (shared_state (slot_exec st)) t = Some (Probe i)"
    and views: "\<And>j. j \<in> requested_headers selected i \<Longrightarrow>
      serviced_header (shared_state (slot_exec st)) j (views j) (replies j) (selected j)"
    and interlude: "(recovery_core_move n ^^ gap)
      (exec_search (slot_exec st) t (stable_probe_result (header_choices selected) i)) y"
    and grant: "holds_grant (shared_state y) (endpoint y n) t"
    and fence: "reserved_term (shared_state y) = t"
    and process: "app_term (processes y n) = t" "app_accepted (processes y n) = position warm"
      "running_application (processes y n) = None"
    and warm: "warm \<in> insert [] (issued (shared_state y))" "term_of warm < t"
    and unopened: "latest_issued (shared_state y) t = None"
    and base: "serviced_base (shared_state y) t warm base"
    and image: "manifest_history m = stateless_update (endpoint y n) t payload F base" "files_match files m"
begin

abbreviation scans where "scans \<equiv> stable_probe_count (header_choices selected) i"
abbreviation reads where "reads \<equiv> scans + gap + 1"
abbreviation ready where "ready \<equiv> st\<lparr>slot_exec := y\<rparr>"
abbreviation h where "h \<equiv> stateless_update (endpoint y n) t payload F base"

lemma recovery_read_path: "(next_slot_move n ^^ reads) st ready"
proof -
  let ?scanned = "exec_search (slot_exec st) t (stable_probe_result (header_choices selected) i)"
  have scan: "(recovery_core_move n ^^ scans) (slot_exec st) ?scanned"
    by (rule changing_scan_path[OF pending views]) (auto simp: recovery_core_move_def window_move_def exec_search_def)
  have path: "(recovery_core_move n ^^ (scans + gap)) (slot_exec st) y"
    by (rule counted_path_append[OF scan interlude])
  have read: "next_slot_move n ready ready" by (simp add: next_slot_move_def)
  from relpowp_Suc_I[OF lift_recovery_core_path[OF path] read] show ?thesis by simp
qed

lemma recovery_publication_locale: "stateless_slot_publication n t h ready m files"
proof -
  let ?s = "shared_state y"
  have ready_reached: "stateless_slot_reachable n ready"
    by (rule next_slot_moves_reachable[OF reached recovery_read_path])
  have raced: "stateless_reachable ?s"
    using stateless_execution_projection[OF slot_state_projects(1)[OF ready_reached]] by simp
  then have ii: "issued_ok ?s" using stateless_invariants by (simp add: stateless_ok_def)
  have fresh: "h \<notin> issued ?s" using ii unopened by (auto simp: issued_ok_def new_tip_fields)
  have accept: "rank_term (app_accepted (processes y n)) \<noteq> t"
    using process(2) warm(2) by simp
  have issue: "stateless_exec_step y (y\<lparr>shared_state :=
    ?s\<lparr>issued := insert h (issued ?s), latest_issued := (latest_issued ?s)(t \<mapsto> h)\<rparr>\<rparr>)"
    by (rule stateless_exec_step.first_publish[where n=n and t=t and warm=warm and base=base and payload=payload and F=F])
      (use grant process warm unopened serviced_base_projects[OF base] in simp_all)
  show ?thesis
    by unfold_locales (use ready_reached free grant fence process fresh accept issue image
      in \<open>simp_all add: new_tip_fields\<close>)
qed

theorem changing_view_recovery_releases_slot:
  fixes issue :: "nat \<Rightarrow> nat option"
  assumes search_service: "bounded_service {..<reads} (\<lambda>i. {..<i}) lookups A search_horizon"
    and search_time: "reads * A \<le> search_horizon"
    and publication_service: "bounded_service {..<16} (\<lambda>i. {..<i}) issue B publication_horizon"
    and publication_time: "16 * B \<le> publication_horizon"
    and completion: "bounded_service (completion_jobs (position h)) (completion_dependencies (position h))
      callbacks C completion_horizon"
    and completion_time: "3 * C \<le> completion_horizon"
  obtains run where "run 0 = st" "\<And>j. next_slot_move n (run j) (run (Suc j))"
    "run (reads * A) = ready"
    "\<exists>p. active_slot (run (reads * A + 16 * B)) = Some p \<and> object_phase p = Local_Apply_Queued \<and>
      object_history p = h \<and> object_generation p = next_object_generation st \<and>
      object_incarnation p = incarnation (processes y n) \<and>
      matching_local_application n (slot_exec (run (reads * A + 16 * B))) p (position h)"
    "h \<in> notifications (shared_state (slot_exec (run (reads * A + (16 * B + 3 * C)))))"
    "installed (processes (slot_exec (run (reads * A + (16 * B + 3 * C)))) n) = Some (position h)"
    "stateless_next_ready n t h (run (reads * A + (16 * B + 3 * C)))"
    "incarnation (processes (slot_exec (run (reads * A + (16 * B + 3 * C)))) n) = incarnation (processes y n)"
proof -
  interpret publication: stateless_slot_publication n t h ready m files
    by (rule recovery_publication_locale)
  obtain r where r: "r 0 = st" "r (reads * A) = ready"
    "\<And>j. next_slot_move n (r j) (r (Suc j))"
    using service_slot_path[OF recovery_read_path search_service search_time] by blast
  obtain s where s: "s 0 = ready" "\<And>j. next_slot_move n (s j) (s (Suc j))"
    and outcome: "h \<in> notifications (shared_state (slot_exec (s (16 * B + 3 * C))))"
      "installed (processes (slot_exec (s (16 * B + 3 * C))) n) = Some (position h)"
      "stateless_next_ready n t h (s (16 * B + 3 * C))"
      "incarnation (processes (slot_exec (s (16 * B + 3 * C))) n) = incarnation (processes y n)"
    and app: "\<exists>p. active_slot (s (16 * B)) = Some p \<and> object_phase p = Local_Apply_Queued \<and>
      object_history p = h \<and> object_generation p = next_object_generation st \<and>
      object_incarnation p = incarnation (processes y n) \<and>
      matching_local_application n (slot_exec (s (16 * B))) p (position h)"
    by (rule publication.serviced_publication_releases_slot[
      OF publication_service publication_time completion completion_time]) simp
  let ?run = "\<lambda>j. if j < reads * A then r j else s (j - reads * A)"
  have link: "r (reads * A) = s 0" using r(2) s(1) by simp
  note path = concatenate_next_traces[where r=r and s=s and k="reads * A", OF r(3) s(2) link]
  have start: "?run 0 = st" using path(1) r(1) by simp
  have read: "?run (reads * A) = ready" using s(1) by simp
  have at_apply: "?run (reads * A + 16 * B) = s (16 * B)" by (rule path(3))
  have at_completion: "?run (reads * A + (16 * B + 3 * C)) = s (16 * B + 3 * C)" by (rule path(3))
  show thesis by (rule that[OF start path(2) read])
    (unfold at_apply at_completion, (rule app outcome)+)
qed

end

section \<open>Finishing the successful callback and admitting a successor\<close>

text \<open>
  Coordinator clears the publication under its mutex, calls
  updateMaxTermSeen(getCurrentTerm()), then checks abdication and
  schedules any reconfiguration under the same lock. A higher observed
  term leads to candidate mode whether the term bump succeeds or throws.
  The slot model projects its mode effect here. It models a local term
  change when joining a granted term, so the observed term remains an
  external lower bound for a renewed claim. The Boolean records the
  outcome of the remaining leadership work, including any abdication.
  The edge immediately after slot release is a logical cut within this
  callback. There is no intervening publication admission. Realizing
  the successor's scheduled admission also requires the prior
  publishListener response to reach MasterService after this callback.
  The bounds apply to the scheduled jobs in this witness. They require
  service of those Java actions when the witness is realized.
\<close>

definition after_deferred_publication_work where
  "after_deferred_publication_work n max_seen retain st =
    (if active_slot st = None \<and> slot_leading st \<and>
      (app_term (processes (slot_exec st) n) < max_seen \<or> \<not> retain)
     then st\<lparr>slot_leading := False\<rparr> else st)"

lemma deferred_publication_work_moves:
  "next_slot_move n st (after_deferred_publication_work n max_seen retain st)"
  unfolding after_deferred_publication_work_def next_slot_move_def
  by (auto intro: stateless_slot_step.step_down)

lemma deferred_publication_work_keeps_ready:
  assumes "stateless_next_ready n t h st" "max_seen \<le> t" "retain"
  shows "after_deferred_publication_work n max_seen retain st = st"
  using assms by (simp add: after_deferred_publication_work_def stateless_next_ready_def Let_def)

lemma deferred_publication_work_requires_election:
  assumes "active_slot st = None" "app_term (processes (slot_exec st) n) < max_seen \<or> \<not> retain"
  defines "done \<equiv> after_deferred_publication_work n max_seen retain st"
  shows "next_slot_move n st done" "active_slot done = None" "\<not> slot_leading done" "slot_exec done = slot_exec st"
proof -
  show "next_slot_move n st done" unfolding done_def by (rule deferred_publication_work_moves)
  show "active_slot done = None" "\<not> slot_leading done" "slot_exec done = slot_exec st"
    using assms(1-2) by (simp_all add: done_def after_deferred_publication_work_def)
qed

context changing_view_slot_publication
begin

theorem changing_view_recovery_then_next_publication:
  fixes payload' :: nat and F' :: config and m' :: state_manifest
    and prepare prepare' :: "nat \<Rightarrow> nat option"
  assumes search_service: "bounded_service {..<reads} (\<lambda>i. {..<i}) lookups A search_horizon"
    and search_time: "reads * A \<le> search_horizon"
    and issue: "bounded_service {..<16} (\<lambda>i. {..<i}) prepare B issue_horizon"
    and issue_time: "16 * B \<le> issue_horizon"
    and completion: "bounded_service (completion_jobs (position h)) (completion_dependencies (position h))
      callbacks C completion_horizon"
    and completion_time: "3 * C \<le> completion_horizon"
    and maximum: "max_seen \<le> t" and retain: "retain"
    and next_history: "h' = stateless_update (endpoint y n) t payload' F' h"
    and next_manifest: "manifest_history m' = h'" "files_match files' m'"
    and next_issue: "bounded_service {..<16} (\<lambda>i. {..<i}) prepare' B' issue_horizon'"
    and next_time: "16 * B' \<le> issue_horizon'"
    and next_completion: "bounded_service (completion_jobs (position h')) (completion_dependencies (position h'))
      callbacks' C' completion_horizon'"
    and next_completion_time: "3 * C' \<le> completion_horizon'"
  defines "local_apply \<equiv> reads * A + 16 * B"
    and "cleared \<equiv> reads * A + (16 * B + 3 * C)"
    and "finished \<equiv> Suc (reads * A + (16 * B + 3 * C)) + (16 * B' + 3 * C')"
  obtains run where "run 0 = st" "\<And>j. next_slot_move n (run j) (run (Suc j))"
    "run (reads * A) = ready"
    "\<exists>p. active_slot (run local_apply) = Some p \<and> object_phase p = Local_Apply_Queued \<and>
      object_history p = h \<and> object_generation p = next_object_generation st \<and>
      object_incarnation p = incarnation (processes y n) \<and>
      matching_local_application n (slot_exec (run local_apply)) p (position h)"
    "h \<in> notifications (shared_state (slot_exec (run cleared)))"
    "installed (processes (slot_exec (run cleared)) n) = Some (position h)"
    "active_slot (run cleared) = None"
    "run (Suc cleared) = after_deferred_publication_work n max_seen retain (run cleared)"
    "stateless_next_ready n t h (run (Suc cleared))"
    "prefix h h'" "position h < position h'"
    "h' \<in> notifications (shared_state (slot_exec (run finished)))"
    "installed (processes (slot_exec (run finished)) n) = Some (position h')"
    "stateless_next_ready n t h' (run finished)"
proof -
  from changing_view_recovery_releases_slot[
    OF search_service search_time issue issue_time completion completion_time]
  obtain r where r: "r 0 = st" "\<And>j. next_slot_move n (r j) (r (Suc j))"
    and read: "r (reads * A) = ready"
    and app: "\<exists>p. active_slot (r local_apply) = Some p \<and> object_phase p = Local_Apply_Queued \<and>
      object_history p = h \<and> object_generation p = next_object_generation st \<and>
      object_incarnation p = incarnation (processes y n) \<and>
      matching_local_application n (slot_exec (r local_apply)) p (position h)"
    and result: "h \<in> notifications (shared_state (slot_exec (r cleared)))"
      "installed (processes (slot_exec (r cleared)) n) = Some (position h)"
      "stateless_next_ready n t h (r cleared)"
      "incarnation (processes (slot_exec (r cleared)) n) = incarnation (processes y n)"
    unfolding local_apply_def cleared_def by blast
  let ?done = "after_deferred_publication_work n max_seen retain (r cleared)"
  have same: "?done = r cleared"
    by (rule deferred_publication_work_keeps_ready[OF result(3) maximum retain])
  have reach_done: "stateless_slot_reachable n ?done"
    unfolding same by (rule stateless_slot_trace_reachable[of n r])
      (use r reached in \<open>simp_all add: next_slot_move_def\<close>)
  have next_tip: "stateless_update (endpoint (slot_exec ?done) n) t payload' F' h = h'"
    using same result(4) next_history by simp
  interpret successor: stateless_next_publication n t payload' h "?done" F' m' files'
    by unfold_locales (use reach_done result(3) same next_manifest next_tip in simp_all)
  obtain s where s: "s 0 = ?done" "\<And>j. next_slot_move n (s j) (s (Suc j))"
    and outcome: "h' \<in> notifications (shared_state (slot_exec (s (16 * B' + 3 * C'))))"
      "installed (processes (slot_exec (s (16 * B' + 3 * C'))) n) = Some (position h')"
      "stateless_next_ready n t h' (s (16 * B' + 3 * C'))"
    by (rule successor.subsequent_stateless_publication_releases_slot[
      unfolded next_tip, OF next_issue next_time next_completion next_completion_time]) blast
  let ?tail = "\<lambda>j. case j of 0 \<Rightarrow> r cleared | Suc k \<Rightarrow> s k"
  have advance: "next_slot_move n (?tail j) (?tail (Suc j))" for j
    by (cases j) (simp_all add: s deferred_publication_work_moves)
  let ?run = "\<lambda>j. if j < cleared then r j else ?tail (j - cleared)"
  have link: "r cleared = ?tail 0" by simp
  note path = concatenate_next_traces[where r=r and s="?tail" and k=cleared, OF r(2) advance link]
  have start: "?run 0 = st" using path(1) r(1) by simp
  have before: "?run j = r j" if "j \<le> cleared" for j using that by auto
  have read_cut: "reads * A \<le> cleared" unfolding cleared_def by simp
  have apply_cut: "local_apply \<le> cleared" unfolding local_apply_def cleared_def by simp
  have loaded: "?run (reads * A) = ready" unfolding before[OF read_cut] by (rule read)
  have at_clear: "?run cleared = r cleared" by (rule before) simp
  have empty_cut: "active_slot (?run cleared) = None"
    unfolding at_clear using result(3) by (simp add: stateless_next_ready_def Let_def)
  have handoff: "?run (Suc cleared) = ?done" by (simp add: s)
  have after: "stateless_next_ready n t h (?run (Suc cleared))"
    unfolding handoff same by (rule result(3))
  have at_end: "?run finished = s (16 * B' + 3 * C')" unfolding finished_def cleared_def by simp
  have prefix: "prefix h h'" unfolding next_history by (rule new_tip_fields)
  have newer: "position h < position h'" unfolding next_history
    by (rule new_tip_fields(5)) (simp add: new_tip_fields)
  show thesis by (rule that[OF start path(2) loaded _ _ _ empty_cut _ after prefix newer])
    (unfold before[OF apply_cut] at_clear at_end handoff, (rule app result outcome refl)+)
qed

end

section \<open>Retrying from the cleared candidate slot\<close>

text \<open>
  A new live reservation invalidates the old term's exact-fence premise
  even before Coordinator observes it. If the replacement is observed by
  the successful callback, deferred term handling leaves a free candidate
  slot. If an attempt reaches terminal failure in the current local term,
  its failure callback also leaves a free candidate slot. A reservation
  alone is insufficient to restore progress. The retry below schedules
  a successful claim, its confirmation, the local join and election
  entry, and the start of the storage search. The proposed term is above
  the greater of the recorded observation and the prior local term.
  Service of those jobs and of the renewed search is conditional.
\<close>

lemma higher_reservation_blocks_same_term_handoff:
  assumes "t < reserved_term (shared_state (slot_exec st))"
  shows "\<not> stateless_next_ready n t b st"
  using assms by (auto simp: stateless_next_ready_def Let_def)

theorem fresh_grant_restarts_changing_view_recovery:
  fixes select :: "nat \<Rightarrow> nat option"
  assumes reached: "stateless_slot_reachable n st"
    and candidate: "active_slot st = None" "\<not> slot_leading st"
    and proposal: "max max_seen (app_term (processes (slot_exec st) n)) < proposed"
    and effect: "lease_effect provider before live expected (Claim_Term (endpoint (slot_exec st) n) proposed) result"
    and rep: "lease_term (lease_value live) = reserved_term (shared_state (slot_exec st))"
    and warm: "warm \<in> insert [] (issued (shared_state (slot_exec st)))"
      "app_accepted (processes (slot_exec st) n) = position warm"
    and service: "bounded_service {..<5} (\<lambda>i. {..<i}) select B horizon"
    and time: "5 * B \<le> horizon"
  defines "new \<equiv> lease_term (lease_value result)"
  obtains run where "run 0 = st" "\<And>j. next_slot_move n (run j) (run (Suc j))"
    "stateless_slot_reachable n (run (5 * B))"
    "active_slot (run (5 * B)) = None" "slot_leading (run (5 * B))"
    "reserved_term (shared_state (slot_exec (run (5 * B)))) = new"
    "holds_grant (shared_state (slot_exec (run (5 * B)))) (endpoint (slot_exec (run (5 * B))) n) new"
    "searches (shared_state (slot_exec (run (5 * B)))) new = Some (Probe (new - 1))"
    "latest_issued (shared_state (slot_exec (run (5 * B)))) new = None"
    "warm \<in> insert [] (issued (shared_state (slot_exec (run (5 * B)))))" "term_of warm < new"
    "app_accepted (processes (slot_exec (run (5 * B))) n) = position warm"
    "processes (slot_exec (run (5 * B))) n = (processes (slot_exec st) n)\<lparr>app_term := new\<rparr>"
    "max_seen < new"
proof -
  let ?x = "slot_exec st"
  let ?s = "shared_state ?x"
  let ?who = "endpoint ?x n"
  let ?a = "processes ?x n"
  let ?s1 = "?s\<lparr>reserved_term := new, granted_to := (granted_to ?s)(new \<mapsto> ?who)\<rparr>"
  let ?s2 = "?s1\<lparr>confirmed_floor := max new (confirmed_floor ?s), confirmed_terms := insert new (confirmed_terms ?s)\<rparr>"
  let ?x1 = "?x\<lparr>shared_state := ?s1\<rparr>"
  let ?x2 = "?x\<lparr>shared_state := ?s2\<rparr>"
  let ?x3 = "?x2\<lparr>processes := (processes ?x)(n := ?a\<lparr>app_term := new\<rparr>)\<rparr>"
  let ?x5 = "exec_search ?x3 new (Probe (new - 1))"
  let ?st1 = "st\<lparr>slot_exec := ?x1\<rparr>"
  let ?st2 = "st\<lparr>slot_exec := ?x2\<rparr>"
  let ?st3 = "st\<lparr>slot_exec := ?x3, slot_leading := False\<rparr>"
  let ?st4 = "?st3\<lparr>slot_leading := True\<rparr>"
  let ?st5 = "?st4\<lparr>slot_exec := ?x5\<rparr>"
  have reserve: "stateless_exec_step ?x ?x1"
    unfolding new_def by (rule stateless_exec_reservation[OF effect rep])
  have confirms: "stateless_step ?s1 ?s2"
    using stateless_step.confirm[of ?s1 new ?who] by simp
  have confirm: "stateless_exec_step ?x1 ?x2"
    using stateless_exec_step.storage[where x="?x1" and s="?s2"] confirms by simp
  have grant: "holds_grant ?s2 ?who new" by (simp add: holds_grant_def)
  have reserved: "reserved_term ?s < new"
    using lease_claim_refines_reserve(2)[OF effect rep] unfolding new_def .
  have proposed: "proposed \<le> new"
    using effective_lease_write(2)[OF effect] by (simp add: new_def lease_value_def)
  have lower: "app_term ?a \<le> max max_seen (app_term ?a)" "max_seen \<le> max max_seen (app_term ?a)" by simp_all
  have local_term: "app_term ?a < new" and observation: "max_seen < new"
    using lower proposed proposal by linarith+
  have join: "stateless_exec_step ?x2 ?x3"
    using stateless_exec_step.join[where x="?x2" and who="?who" and t=new and n=n] grant local_term
    by simp
  have start: "stateless_exec_step ?x3 ?x5"
    unfolding exec_search_def
    by (rule stateless_exec_step.storage) (use stateless_step.start_search[OF grant] in simp_all)
  have s1: "next_slot_move n st ?st1"
    by (rule next_slot_core_move) (use window_move_real[OF reserve] in simp_all)
  have s2: "next_slot_move n ?st1 ?st2"
    using next_slot_core_move[of "?st1" "?x2" n] window_move_real[OF confirm] by simp
  have joined: "stateless_slot_step n ?st2 (?st2\<lparr>slot_exec := ?x3,
    slot_leading := (slot_leading ?st2 \<and> app_term (processes ?x3 n) = app_term (processes (slot_exec ?st2) n))\<rparr>)"
    by (rule stateless_slot_step.core) (use join in simp_all)
  have s3: "next_slot_move n ?st2 ?st3" using next_slot_real[OF joined] candidate by simp
  have s4: "next_slot_move n ?st3 ?st4"
    by (rule next_slot_real, rule stateless_slot_step.leader_entry) (use grant in simp)
  have s5: "next_slot_move n ?st4 ?st5"
    by (rule next_slot_core_move) (use window_move_real[OF start] in \<open>simp_all add: exec_search_def\<close>)
  have path4: "(next_slot_move n ^^ 4) st ?st4"
    by (rule four_steps[where R="next_slot_move n", OF s1 s2 s3 s4])
  have path: "(next_slot_move n ^^ 5) st ?st5"
    using relpowp_Suc_I[where P="next_slot_move n", OF path4 s5] by simp
  obtain run where run: "run 0 = st" "run (5 * B) = ?st5"
    "\<And>j. next_slot_move n (run j) (run (Suc j))"
    using service_slot_path[OF path service time] by blast
  have reachable: "stateless_slot_reachable n ?st5" by (rule next_slot_moves_reachable[OF reached path])
  have core: "stateless_reachable ?s"
    using stateless_execution_projection[OF slot_state_projects(1)[OF reached]] by blast
  from stateless_invariants[OF core] have ok: "lease_ok ?s" "issued_ok ?s"
    by (auto simp: stateless_ok_def)
  have older: "term_of h < new" if "h \<in> insert [] (issued ?s)" for h
  proof (cases "h = []")
    case True
    with reserved show ?thesis by simp
  next
    case False
    with that have "h \<in> issued ?s" by simp
    from issued_term_bound[OF ok this] stateless_floor_below_reservation[OF core] reserved
    show ?thesis by linarith
  qed
  have fresh: "latest_issued ?s new = None"
    using ok(2) older by (cases "latest_issued ?s new") (auto simp: issued_ok_def)
  show thesis by (rule that[OF run(1,3)])
    (use candidate grant fresh reachable older[OF warm(1)] warm observation in \<open>simp_all add: run(2) exec_search_def holds_grant_def\<close>)
qed

lemma cleared_failure_enters_recovery:
  assumes "stateless_slot_reachable n st"
    "active_slot st = Some p" "object_incarnation p = incarnation (processes (slot_exec st) n)"
    "object_phase p = Publication_Failed" "term_of (object_history p) = app_term (processes (slot_exec st) n)"
  defines "cleared \<equiv> dispatch_publication_signal n (object_generation p) Clear_Failure st"
  shows "next_slot_move n st cleared" "stateless_slot_reachable n cleared" "active_slot cleared = None"
    "\<not> slot_leading cleared" "slot_exec cleared = slot_exec st"
  unfolding cleared_def
  using failure_in_current_term_requires_recovery[OF assms(2-5)] assms(1)
  by (auto simp: next_slot_move_def intro: stateless_slot_reachable.step)

end
