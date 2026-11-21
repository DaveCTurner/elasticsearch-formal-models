theory Stateless_Changing_View_Liveness
  imports Stateless_Window_Liveness
begin

section \<open>Descending probes with independent complete responses\<close>

text \<open>
  Each requested term has its own complete-response witness. There is no
  shared provider snapshot. The logical storage state for a probe represents
  the completed images and the live frontier. A view below the frontier may
  already reflect cleanup, including an empty directory. At or above the
  frontier, the selected header must represent the logical tip for that term.
\<close>

definition serviced_header where
  "serviced_header s i view reply selected \<longleftrightarrow>
    first_listing_contract view reply \<and> checked_first_listing reply = Some view \<and>
    newest_manifest view selected \<and> directory_rep s i selected"

lemma serviced_header_step:
  assumes header: "serviced_header (shared_state x) i view reply selected"
    and pending: "searches (shared_state x) election = Some (Probe i)"
  shows "stateless_exec_step x
    (exec_search x election (case selected of None \<Rightarrow>
      if 1 < i then Probe (i - 1) else No_Stored_State | Some m \<Rightarrow> Found (manifest_history m)))"
proof -
  from header have reply: "first_listing_contract view reply" "checked_first_listing reply = Some view"
    and rep: "newest_manifest view selected" "directory_rep (shared_state x) i selected"
    unfolding serviced_header_def by blast+
  from checked_header_refines_scan(2)[OF reply pending rep]
  show ?thesis by (cases selected)
    (auto simp: exec_search_def intro!: stateless_exec_step.storage)
qed

lemma serviced_header_search_invariant:
  "serviced_header (shared_state (exec_search x election query)) i view reply selected =
    serviced_header (shared_state x) i view reply selected"
  by (simp add: serviced_header_def directory_rep_def exec_search_def)

abbreviation header_choices where
  "header_choices selected \<equiv> (\<lambda>i. map_option manifest_history (selected i))"

fun requested_headers where
  "requested_headers selected 0 = {0}"
| "requested_headers selected (Suc i) = insert (Suc i)
    (if selected (Suc i) = None \<and> i \<noteq> 0 then requested_headers selected i else {})"

lemma changing_scan_path:
  assumes pending: "searches (shared_state x) election = Some (Probe i)"
    and views: "\<And>j. j \<in> requested_headers selected i \<Longrightarrow>
      serviced_header (shared_state x) j (views j) (replies j) (selected j)"
    and embed: "\<And>z q. stateless_exec_step z (exec_search z election q) \<Longrightarrow> R z (exec_search z election q)"
  shows "(R ^^ stable_probe_count (header_choices selected) i) x
     (exec_search x election (stable_probe_result (header_choices selected) i))"
  using pending views
proof (induction i arbitrary: x)
  case 0
  have head: "0 \<in> requested_headers selected 0" by simp
  from embed[OF serviced_header_step[OF "0.prems"(2)[OF head] "0.prems"(1)]]
  show ?case by (cases "selected 0") (simp_all add: relcompp_apply)
next
  case (Suc i)
  have head: "Suc i \<in> requested_headers selected (Suc i)" by simp
  note first = embed[OF serviced_header_step[OF Suc.prems(2)[OF head] Suc.prems(1)]]
  show ?case
  proof (cases "selected (Suc i)")
    case (Some m)
    with first show ?thesis by (simp add: relcompp_apply)
  next
    case None
    show ?thesis
    proof (cases "i = 0")
      case True
      with first None show ?thesis by (simp add: relcompp_apply)
    next
      case False
      let ?y = "exec_search x election (Probe i)"
      from first None False have first_step: "R x ?y" by simp
      have probe: "searches (shared_state ?y) election = Some (Probe i)"
        by (simp add: exec_search_def)
      have available: "serviced_header (shared_state ?y) j (views j) (replies j) (selected j)"
        if "j \<in> requested_headers selected i" for j
      proof -
        have "j \<in> requested_headers selected (Suc i)" using None False that by simp
        from Suc.prems(2)[OF this] show ?thesis by (simp add: serviced_header_search_invariant)
      qed
      note path = relpowp_Suc_I2[OF first_step Suc.IH[OF probe available]]
      have terminal: "exec_search ?y election (stable_probe_result (header_choices selected) i) =
        exec_search x election (stable_probe_result (header_choices selected) i)"
        by (simp add: exec_search_def)
      from path[unfolded terminal] None False show ?thesis
        by (simp only: stable_probe_count.simps stable_probe_result.simps option.simps if_False)
    qed
  qed
qed

theorem changing_scan_finishes:
  assumes pending: "searches (shared_state x) election = Some (Probe i)"
    and views: "\<And>j. j \<in> requested_headers selected i \<Longrightarrow>
      serviced_header (shared_state x) j (views j) (replies j) (selected j)"
  shows "(stateless_exec_step ^^ stable_probe_count (header_choices selected) i) x
     (exec_search x election (stable_probe_result (header_choices selected) i))"
  by (rule changing_scan_path[OF pending views]) assumption

section \<open>Cleanup and a separately serviced download\<close>

definition cleanup_during_download where
  "cleanup_during_download x removed = x\<lparr>shared_state := (shared_state x)\<lparr>
    visible_image := (\<lambda>i. if i \<in> removed then None else visible_image (shared_state x) i)\<rparr>\<rparr>"

lemma cleanup_projects_between_reads:
  assumes "h \<in> notifications (shared_state x)" "\<And>i. i \<in> removed \<Longrightarrow> i < term_of h"
  shows "stateless_exec_step x (cleanup_during_download x removed)"
proof -
  let ?s = "shared_state x"
  let ?result = "?s\<lparr>visible_image := (\<lambda>i. if i \<in> removed then None else visible_image ?s i)\<rparr>"
  have effect: "stateless_step ?s ?result"
    by (rule term_cleanup_refines(1)[OF assms, where removed=removed])
  have issued: "issued ?result = issued ?s" by simp
  show ?thesis unfolding cleanup_during_download_def by (rule stateless_exec_step.storage[OF effect issued])
qed

lemma cleanup_preserves_frontier_image:
  assumes "stateless_reachable (shared_state x)" "h \<in> notifications (shared_state x)"
    "\<And>i. i \<in> removed \<Longrightarrow> i < term_of h"
  shows "visible_image (shared_state (cleanup_during_download x removed)) (term_of (frontier (shared_state x))) =
    visible_image (shared_state x) (term_of (frontier (shared_state x)))"
  using term_cleanup_refines(2)[OF assms(2,3,1)]
  by (simp add: cleanup_during_download_def)

definition complete_read where
  "complete_read view reply selected files \<longleftrightarrow>
    first_listing_contract view reply \<and> checked_first_listing reply = Some view \<and>
    newest_manifest view (Some selected) \<and> files_match files selected"

lemma incomplete_or_missing_data_is_not_complete_read:
  assumes "checked_first_listing reply = None \<or> \<not> files_match files selected"
  shows "\<not> complete_read view reply selected files"
  using assms by (auto simp: complete_read_def)

theorem changed_download_supplies_election_base:
  assumes search: "searches s election = Some (Found seen)"
    and remote: "manifest_history selected \<in> completed_images s"
      "term_of (manifest_history selected) = term_of seen"
    and ready: "complete_read view reply selected files"
    and present: "anchor \<in> original"
    and anchor: "term_of seen = term_of (frontier s) \<Longrightarrow> manifest_history anchor = frontier s"
    and first: "is_first \<Longrightarrow> \<forall>m\<in>original. extends_manifest anchor m"
    and trace: "rtranclp (fenced_manifest_step is_first anchor) ([], original) (renames, view)"
    and order: "\<And>m. m \<in> view \<Longrightarrow> manifest_generation m \<le> manifest_generation selected
        \<Longrightarrow> extends_manifest m selected"
  shows "election_base s election warm (newer_image warm (manifest_history selected))"
proof -
  from ready have reply: "first_listing_contract view reply" "checked_first_listing reply = Some view"
    and newest: "newest_manifest view (Some selected)" unfolding complete_read_def by auto
  show ?thesis
    by (rule complete_response_supplies_election_base[OF search remote reply newest present anchor first trace order])
qed

inductive serviced_base for s election warm where
  empty: "searches s election = Some No_Stored_State \<Longrightarrow> serviced_base s election warm warm"
| retain_local: "searches s election = Some (Found seen) \<Longrightarrow> position seen \<le> position warm \<Longrightarrow>
    serviced_base s election warm warm"
| download: "searches s election = Some (Found seen) \<Longrightarrow>
    manifest_history selected \<in> completed_images s \<Longrightarrow> term_of (manifest_history selected) = term_of seen \<Longrightarrow>
    complete_read view reply selected files \<Longrightarrow> anchor \<in> original \<Longrightarrow>
    (term_of seen = term_of (frontier s) \<Longrightarrow> manifest_history anchor = frontier s) \<Longrightarrow>
    (is_first \<Longrightarrow> \<forall>m\<in>original. extends_manifest anchor m) \<Longrightarrow>
    rtranclp (fenced_manifest_step is_first anchor) ([], original) (renames, view) \<Longrightarrow>
    (\<And>m. m \<in> view \<Longrightarrow> manifest_generation m \<le> manifest_generation selected
      \<Longrightarrow> extends_manifest m selected) \<Longrightarrow>
    serviced_base s election warm (newer_image warm (manifest_history selected))"

lemma serviced_base_projects:
  assumes "serviced_base s election warm base"
  shows "election_base s election warm base"
  using assms
  by cases (auto intro: election_base.empty election_base.retained_local changed_download_supplies_election_base)

section \<open>Registering and fencing a state recovered through changing views\<close>

lemma changing_base_commit_path:
  fixes F :: config and payload :: nat
  assumes reached: "stateless_execution_reachable y"
    and grant: "holds_grant (shared_state y) (endpoint y c) t"
    and process: "app_term (processes y c) = t" "app_accepted (processes y c) = position warm"
    and warm: "warm \<in> insert [] (issued (shared_state y))" "term_of warm < t"
    and first: "latest_issued (shared_state y) t = None"
    and recovered: "serviced_base (shared_state y) t warm base"
    and fence: "reserved_term (shared_state y) = t"
    and publication: "h = stateless_update (endpoint y c) t payload F base"
    and manifest: "manifest_history m = h" "files_match files m"
  obtains z where "(stateless_exec_step ^^ 6) y z"
    "stateless_execution_reachable z"
    "h \<in> notifications (shared_state z)"
    "app_accepted (processes z c) = position h"
    "\<And>p. p \<in> notifications (shared_state y) \<Longrightarrow> prefix p h"
proof -
  let ?s = "shared_state y"
  let ?a = "processes y c"
  let ?who = "endpoint y c"
  let ?published = "?s\<lparr>issued := insert h (issued ?s), latest_issued := (latest_issued ?s)(t \<mapsto> h)\<rparr>"
  let ?stored = "?published\<lparr>completed_images := insert h (completed_images ?published),
      visible_image := (visible_image ?published)(t \<mapsto> h)\<rparr>"
  let ?approved = "?stored\<lparr>approvals := insert h (approvals ?stored), frontier := h\<rparr>"
  let ?notified = "?approved\<lparr>notifications := insert h (notifications ?approved)\<rparr>"
  let ?y1 = "y\<lparr>shared_state := ?published\<rparr>"
  let ?y2 = "?y1\<lparr>in_flight := insert (State_Packet h ?who) (in_flight y)\<rparr>"
  let ?y3 = "?y2\<lparr>shared_state := ?stored\<rparr>"
  let ?y4 = "?y3\<lparr>processes := (processes y)(c := ?a\<lparr>app_accepted := position h\<rparr>)\<rparr>"
  let ?y5 = "?y4\<lparr>shared_state := ?approved\<rparr>"
  let ?z = "?y5\<lparr>shared_state := ?notified\<rparr>"
  have base: "election_base ?s t warm base" by (rule serviced_base_projects[OF recovered])
  have publish: "stateless_exec_step y ?y1"
    by (rule stateless_exec_step.first_publish[where n=c and t=t and warm=warm and base=base and payload=payload and F=F])
      (use grant process warm first base publication in simp_all)
  have send: "stateless_exec_step ?y1 ?y2"
    using stateless_exec_step.send_state[where x="?y1" and n=c and h=h] by simp
  have shared_run: "stateless_reachable ?s"
    using stateless_execution_projection[OF reached] by blast
  have stored_run: "stateless_reachable (shared_state ?y2)"
    using stateless_execution_projection[OF stateless_execution_reachable.step[
      OF stateless_execution_reachable.step[OF reached publish] send]] by blast
  have install: "stateless_exec_step ?y2 ?y3"
    using stateless_exec_manifest_install[where x="?y2" and t=t, OF stored_run _ manifest(2)]
    by (simp add: manifest(1))
  have term_h: "term_of h = t" unfolding publication by (simp add: new_tip_fields)
  have accept: "stateless_exec_step ?y3 ?y4"
    using stateless_exec_step.receive_state[where x="?y3" and n=c and h=h and a="?a"]
      term_h process warm by simp
  have floor: "confirmed_floor ?s \<le> t"
    using stateless_floor_below_reservation[OF shared_run] fence by simp
  have check: "stateless_step ?stored ?approved"
    by (rule stateless_step.approve) (use floor in simp_all)
  have approve: "stateless_exec_step ?y4 ?y5"
    using stateless_exec_step.storage[where x="?y4" and s="?approved"] check by simp
  have notify: "stateless_exec_step ?y5 ?z"
    using stateless_exec_step.storage[where x="?y5" and s="?notified"]
      stateless_step.notify_commit[where s="?approved" and h=h] by simp
  have prefix: "(stateless_exec_step ^^ 4) y ?y4"
    by (rule four_steps[where R=stateless_exec_step, OF publish send install accept])
  have path5: "(stateless_exec_step ^^ 5) y ?y5"
  proof -
    have n: "Suc (4::nat) = 5" by simp
    from relpowp_Suc_I[where P=stateless_exec_step, OF prefix approve] show ?thesis unfolding n .
  qed
  have path: "(stateless_exec_step ^^ 6) y ?z"
  proof -
    have n: "Suc (5::nat) = 6" by simp
    from relpowp_Suc_I[where P=stateless_exec_step, OF path5 notify] show ?thesis unfolding n .
  qed
  have extends: "prefix p h" if "p \<in> notifications ?s" for p
  proof -
    have parent: "publish_parent ?s t base" by (rule publish_parent.first[OF first warm base])
    have frontier: "term_of (frontier ?s) \<le> t"
    proof (cases "frontier ?s = []")
      case True
      then show ?thesis by simp
    next
      case False
      from stateless_invariants[OF shared_run] have ok: "issued_ok ?s" "lease_ok ?s" "frontier_ok ?s"
        unfolding stateless_ok_def by blast+
      from frontier_issued[OF ok(3) False] have member: "frontier ?s \<in> issued ?s" .
      from issued_term_bound[OF ok(2,1) member] floor show ?thesis by linarith
    qed
    from chosen_parent_extends_prior_commits[OF shared_run parent frontier that]
    show ?thesis unfolding publication stateless_update_def prefix_def by (auto simp: append_assoc)
  qed
  show thesis by (rule that[OF path stateless_exec_reachable_powers[OF reached path] _ _ extends]) simp_all
qed

text \<open>
  The interlude consists of projected effects and stutters between the
  last header and the download/base decision. It can include cleanup.
  Each provider response describes its own view. A separate serviced job
  accounts for returning a readable image under the retention bound, or
  selecting the warm or empty base. This is a
  bounded-service theorem from an already started search, under successful
  responses and an exact live lease through the publication suffix.
\<close>

theorem changing_view_commit_by_deadline:
  fixes x y :: stateless_execution
    and selected :: "nat \<Rightarrow> state_manifest option" and i t c payload :: nat and F :: config and base :: lineage
  assumes scan_count: "scan_count = stable_probe_count (header_choices selected) i"
    and scanned: "scanned = exec_search x t (stable_probe_result (header_choices selected) i)"
    and publication: "h = stateless_update (endpoint y c) t payload F base"
    and reached: "stateless_execution_reachable x"
    and pending: "searches (shared_state x) t = Some (Probe i)"
    and views: "\<And>j. j \<in> requested_headers selected i \<Longrightarrow>
      serviced_header (shared_state x) j (views j) (replies j) (selected j)"
    and interlude: "(window_move ^^ gap) scanned y"
    and grant: "holds_grant (shared_state y) (endpoint y c) t"
    and process: "app_term (processes y c) = t" "app_accepted (processes y c) = position warm"
    and warm: "warm \<in> insert [] (issued (shared_state y))" "term_of warm < t"
    and first: "latest_issued (shared_state y) t = None"
    and recovered: "serviced_base (shared_state y) t warm base"
    and fence: "reserved_term (shared_state y) = t"
    and manifest: "manifest_history m = h" "files_match files m"
    and service: "bounded_service {..<scan_count + (gap + 7)} (\<lambda>i. {..<i}) select B horizon"
    and bound: "(max 1 i + (gap + 7)) * B \<le> horizon"
  obtains run where "run 0 = x"
    "\<And>j. run j = run (Suc j) \<or> stateless_exec_step (run j) (run (Suc j))"
    "stateless_execution_reachable (run ((scan_count + (gap + 7)) * B))"
    "h \<in> notifications (shared_state (run ((scan_count + (gap + 7)) * B)))"
    "app_accepted (processes (run ((scan_count + (gap + 7)) * B)) c) = position h"
    "(scan_count + (gap + 7)) * B \<le> (max 1 i + (gap + 7)) * B"
proof -
  have scan: "(stateless_exec_step ^^ scan_count) x scanned"
    unfolding scan_count scanned by (rule changing_scan_finishes[OF pending views])
  have scan_reached: "stateless_execution_reachable scanned"
    by (rule stateless_exec_reachable_powers[OF reached scan])
  have y_reached: "stateless_execution_reachable y"
    by (rule window_moves_reachable[OF scan_reached interlude])
  obtain z where tail: "(stateless_exec_step ^^ 6) y z"
    and endpoint: "stateless_execution_reachable z" "h \<in> notifications (shared_state z)"
      "app_accepted (processes z c) = position h"
    by (rule changing_base_commit_path[OF y_reached grant process warm first recovered fence publication manifest])
  have read: "window_move y y" unfolding window_move_def by simp
  have publish: "(window_move ^^ 7) y z"
  proof -
    have n: "Suc (6::nat) = 7" by simp
    from relpowp_Suc_I2[where P=window_move, OF read window_moves_from_exec[OF tail]]
    show ?thesis unfolding n .
  qed
  have suffix: "(window_move ^^ (gap + 7)) scanned z"
    by (rule counted_path_append[where R=window_move, OF interlude publish])
  let ?n = "scan_count + (gap + 7)"
  from counted_path_append[where R=window_move, OF window_moves_from_exec[OF scan] suffix]
  obtain f where f: "f 0 = x" "f ?n = z" "\<And>j. j < ?n \<Longrightarrow> window_move (f j) (f (Suc j))"
    unfolding relpowp_fun_conv by blast
  have scan_bound: "scan_count \<le> max 1 i"
    unfolding scan_count by (rule stable_probe_count_le)
  have time: "?n * B \<le> (max 1 i + (gap + 7)) * B"
    by (rule mult_le_mono1) (use scan_bound in simp)
  let ?run = "serviced_stateless_trace ?n select f"
  have endpoint_run: "?run (?n * B) = z"
    using serviced_stateless_trace_end[OF service order_trans[OF time bound], of f] f(2) by simp
  have steps: "?run j = ?run (Suc j) \<or> stateless_exec_step (?run j) (?run (Suc j))" for j
    by (rule serviced_stateless_trace_projects) (use f(3) in \<open>simp add: window_move_def\<close>)
  show thesis
    by (rule that[of ?run, OF _ steps _ _ _ time])
      (use f(1) endpoint_run endpoint in \<open>simp_all add: serviced_stateless_trace_def\<close>)
qed

section \<open>Aborted reads and a later lease claim\<close>

text \<open>
  An incomplete response or a missing referenced file cannot supply the
  download premise. The failed read can abort without a publication.
  Work outside a failed attempt can still take effect in the register.
  The next successful claim compares against the live witness, including
  any such effect. Service of that later claim and its success callback
  are separate progress requirements. Coordinator's storage failure
  listener enters candidate mode. A new wakeup and service of its claim
  remain required, including availability of the storage executor and
  the single-concurrency state-read runner if the same node retries.
\<close>

lemma competing_effect_advances_live_reservation:
  assumes effect: "lease_effect backend before live expected (Claim_Term who proposed) result"
    and rep: "lease_term (lease_value live) = reserved_term (shared_state x)"
    and old: "old \<le> reserved_term (shared_state x)"
  defines "new \<equiv> lease_term (lease_value result)"
  obtains y where "stateless_exec_step x y" "reserved_term (shared_state y) = new"
    "old < new" "confirmed_floor (shared_state y) = confirmed_floor (shared_state x)"
    "granted_to (shared_state y) new = Some who"
proof -
  let ?s = "shared_state x"
  let ?y = "x\<lparr>shared_state := ?s\<lparr>reserved_term := new, granted_to := (granted_to ?s)(new \<mapsto> who)\<rparr>\<rparr>"
  have step: "stateless_exec_step x ?y"
    unfolding new_def by (rule stateless_exec_reservation[OF effect rep])
  have "old < new"
    using lease_claim_refines_reserve(2)[OF effect rep] old unfolding new_def by linarith
  with step show thesis by (intro that[of ?y]) simp_all
qed

lemma retry_callback_confirms_new_term:
  assumes claimed: "granted_to (shared_state z) new = Some who"
    and live: "reserved_term (shared_state z) = new"
  obtains ready where "stateless_exec_step z ready"
    "reserved_term (shared_state ready) = new"
    "holds_grant (shared_state ready) who new"
proof -
  let ?s = "shared_state z"
  let ?confirmed = "?s\<lparr>confirmed_floor := max new (confirmed_floor ?s),
    confirmed_terms := insert new (confirmed_terms ?s)\<rparr>"
  let ?ready = "z\<lparr>shared_state := ?confirmed\<rparr>"
  have effect: "stateless_step ?s ?confirmed" by (rule stateless_step.confirm[OF claimed])
  have issued: "issued ?confirmed = issued ?s" by simp
  have step: "stateless_exec_step z ?ready" by (rule stateless_exec_step.storage[OF effect issued])
  show thesis by (rule that[OF step]) (use live claimed in \<open>simp_all add: holds_grant_def\<close>)
qed

corollary failed_read_can_retry_above_late_effect:
  assumes failed: "checked_first_listing reply = None \<or> \<not> files_match files selected"
    and late: "lease_effect provider before live expected (Claim_Term who proposal) late_result"
    and rep: "lease_term (lease_value live) = reserved_term (shared_state x)"
    and old: "old \<le> reserved_term (shared_state x)"
    and retry: "lease_effect provider before_retry late_result expected_retry
        (Claim_Term retry_who retry_proposal) retry_result"
  obtains y z ready where "\<not> complete_read view reply selected files"
    "stateless_exec_step x y" "stateless_exec_step y z" "stateless_exec_step z ready"
    "old < reserved_term (shared_state y)"
    "reserved_term (shared_state y) < reserved_term (shared_state z)"
    "confirmed_floor (shared_state z) = confirmed_floor (shared_state x)"
    "reserved_term (shared_state ready) = reserved_term (shared_state z)"
    "holds_grant (shared_state ready) retry_who (reserved_term (shared_state z))"
proof -
  obtain y where mid: "stateless_exec_step x y"
    "reserved_term (shared_state y) = lease_term (lease_value late_result)"
    "old < lease_term (lease_value late_result)"
    "confirmed_floor (shared_state y) = confirmed_floor (shared_state x)"
    and "granted_to (shared_state y) (lease_term (lease_value late_result)) = Some who"
    by (rule competing_effect_advances_live_reservation[OF late rep old])
  obtain z where final: "stateless_exec_step y z"
    "reserved_term (shared_state z) = lease_term (lease_value retry_result)"
    "reserved_term (shared_state y) < lease_term (lease_value retry_result)"
    "confirmed_floor (shared_state z) = confirmed_floor (shared_state y)"
    "granted_to (shared_state z) (lease_term (lease_value retry_result)) = Some retry_who"
    by (rule competing_effect_advances_live_reservation[OF retry mid(2)[symmetric] le_refl])
  obtain ready where confirmed: "stateless_exec_step z ready"
    "reserved_term (shared_state ready) = reserved_term (shared_state z)"
    "holds_grant (shared_state ready) retry_who (reserved_term (shared_state z))"
    by (rule retry_callback_confirms_new_term[OF final(5)[folded final(2)] refl])
  show thesis
    by (rule that[OF incomplete_or_missing_data_is_not_complete_read[OF failed] mid(1) final(1)
        confirmed(1) _ _ _ confirmed(2,3)])
      (use mid(2-4) final(2-4) in simp_all)
qed

end
