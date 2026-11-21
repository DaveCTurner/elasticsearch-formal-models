theory Stateless_Window_Liveness
  imports Stateless_Execution Scheduler_Liveness
begin

section \<open>One stable descending scan\<close>

fun stable_probe_result where
  "stable_probe_result view 0 = (case view 0 of None \<Rightarrow> No_Stored_State | Some h \<Rightarrow> Found h)"
| "stable_probe_result view (Suc i) =
    (case view (Suc i) of Some h \<Rightarrow> Found h
      | None \<Rightarrow> if i = 0 then No_Stored_State else stable_probe_result view i)"

fun stable_probe_count where
  "stable_probe_count view 0 = 1"
| "stable_probe_count view (Suc i) =
    (case view (Suc i) of Some h \<Rightarrow> 1
      | None \<Rightarrow> if i = 0 then 1 else Suc (stable_probe_count view i))"

lemma stable_probe_count_le:
  "stable_probe_count view i \<le> max 1 i"
  by (induction i) (auto split: option.splits)

definition exec_search where
  "exec_search x t q = x\<lparr>shared_state := (shared_state x)
    \<lparr>searches := (searches (shared_state x))(t \<mapsto> q)\<rparr>\<rparr>"

lemma stable_scan_projects:
  assumes "searches (shared_state x) t = Some (Probe i)"
  shows "(stateless_exec_step ^^ stable_probe_count (visible_image (shared_state x)) i) x
    (exec_search x t (stable_probe_result (visible_image (shared_state x)) i))"
  using assms
proof (induction i arbitrary: x)
  case 0
  let ?s = "shared_state x"
  show ?case
  proof (cases "visible_image ?s 0")
    case None
    have "stateless_exec_step x (exec_search x t No_Stored_State)"
      unfolding exec_search_def using stateless_step.absent[OF 0] None
      by (intro stateless_exec_step.storage) simp_all
    with None show ?thesis by (simp add: relcompp_apply)
  next
    case (Some h)
    have "stateless_exec_step x (exec_search x t (Found h))"
      unfolding exec_search_def using stateless_step.header[OF 0] Some
      by (intro stateless_exec_step.storage) simp_all
    with Some show ?thesis by (simp add: relcompp_apply)
  qed
next
  case (Suc i)
  let ?s = "shared_state x"
  show ?case
  proof (cases "visible_image ?s (Suc i)")
    case (Some h)
    have "stateless_exec_step x (exec_search x t (Found h))"
      unfolding exec_search_def using stateless_step.header[OF Suc.prems] Some
      by (intro stateless_exec_step.storage) simp_all
    with Some show ?thesis by (simp add: relcompp_apply)
  next
    case None
    have first: "stateless_exec_step x
        (exec_search x t (if i = 0 then No_Stored_State else Probe i))"
      unfolding exec_search_def using stateless_step.absent[OF Suc.prems] None
      by (cases i) (intro stateless_exec_step.storage; simp_all)+
    show ?thesis
    proof (cases "i = 0")
      case True
      with first None show ?thesis by (simp add: relcompp_apply)
    next
      case False
      have head: "stateless_exec_step x (exec_search x t (Probe i))"
        using first False by simp
      have tail: "(stateless_exec_step ^^ stable_probe_count (visible_image ?s) i)
          (exec_search x t (Probe i))
          (exec_search x t (stable_probe_result (visible_image ?s) i))"
        using Suc.IH[of "exec_search x t (Probe i)"] by (simp add: exec_search_def)
      from relpowp_Suc_I2[OF head tail] None False show ?thesis
        by (simp only: stable_probe_count.simps stable_probe_result.simps option.simps if_False)
    qed
  qed
qed

lemma stable_scan_found:
  assumes "stable_probe_result view i = Found h"
  shows "\<exists>j\<le>i. view j = Some h"
  using assms by (induction i) (auto split: option.splits if_splits intro: le_SucI)

lemma stable_scan_terminal:
  "stable_probe_result view i = No_Stored_State \<or> (\<exists>h. stable_probe_result view i = Found h)"
  by (induction i) (auto split: option.splits)

definition stable_recovery_base where
  "stable_recovery_base result warm =
    (case result of Found h \<Rightarrow> newer_image warm h | _ \<Rightarrow> warm)"

lemma stable_scan_supplies_base:
  assumes store: "store_ok (shared_state x)"
    and scan: "q = stable_probe_result (visible_image (shared_state x)) i"
  shows "election_base (shared_state (exec_search x t q)) t warm (stable_recovery_base q warm)"
proof -
  let ?s = "shared_state (exec_search x t q)"
  have found: "searches ?s t = Some q" by (simp add: exec_search_def)
  have "q = No_Stored_State \<or> (\<exists>h. q = Found h)"
    using stable_scan_terminal[of "visible_image (shared_state x)" i] scan by simp
  then show ?thesis
  proof (elim disjE exE)
    assume "q = No_Stored_State"
    with found show ?thesis by (simp add: stable_recovery_base_def election_base.empty)
  next
    fix h
    assume q: "q = Found h"
    from stable_scan_found[of "visible_image (shared_state x)" i h] scan q
    obtain j where "visible_image (shared_state x) j = Some h" by metis
    with store have "h \<in> completed_images ?s" unfolding store_ok_def by (simp add: exec_search_def)
    with found q show ?thesis by (auto simp: stable_recovery_base_def intro: election_base.downloaded)
  qed
qed

section \<open>Serial bounded service\<close>

abbreviation serial_done where
  "serial_done n select \<equiv> completed_work {..<n} (\<lambda>i. {..<i}) select"

lemma serial_work_is_prefix:
  assumes "ordered_work {..<n} (\<lambda>i. {..<i}) D"
  shows "D = {..<card D}"
proof (cases "D = {}")
  case True
  then show ?thesis by simp
next
  case False
  from assms have sub: "D \<subseteq> {..<n}" and deps: "i \<in> D \<Longrightarrow> {..<i} \<subseteq> D" for i
    unfolding ordered_work_def by blast+
  have fin: "finite D" using sub by (rule finite_subset) simp
  have interval: "D = {..Max D}"
  proof
    show "D \<subseteq> {..Max D}" using Max_ge[OF fin] by auto
    from deps[OF Max_in[OF fin False]] Max_in[OF fin False] show "{..Max D} \<subseteq> D" by (auto simp: le_less)
  qed
  have size: "card D = Suc (Max D)" using arg_cong[OF interval, of card] by simp
  show ?thesis unfolding size lessThan_Suc_atMost by (rule interval)
qed

lemma serial_work_through:
  assumes service: "bounded_service {..<n} (\<lambda>i. {..<i}) select B horizon"
    and length: "k \<le> n" and bound: "k * B \<le> horizon"
  shows "{..<k} \<subseteq> serial_done n select (k * B)"
  using length bound
proof (induction k)
  case 0
  show ?case by simp
next
  case (Suc k)
  have smaller: "k \<le> n" "k * B \<le> horizon" using Suc.prems by auto
  from Suc.IH[OF smaller] have past: "{..<k} \<subseteq> serial_done n select (k * B)" .
  from Suc.prems have time: "k * B + B \<le> horizon" and job: "{k} \<subseteq> {..<n}" by simp_all
  have now: "{k} \<subseteq> serial_done n select (k * B + B)"
    by (rule bounded_service_finishes_group[OF service time job]) (use past in simp)
  from past completed_work_mono[of "k * B" "k * B + B" "{..<n}" "\<lambda>i. {..<i}" select]
  have "{..<k} \<subseteq> serial_done n select (k * B + B)" by simp
  with now show ?case by (simp add: lessThan_Suc add.commute)
qed

definition serviced_stateless_trace where
  "serviced_stateless_trace n select f tick = f (card (serial_done n select tick))"

lemma serviced_stateless_trace_projects:
  assumes path: "\<And>i. i < n \<Longrightarrow> f i = f (Suc i) \<or> stateless_exec_step (f i) (f (Suc i))"
  shows "serviced_stateless_trace n select f tick = serviced_stateless_trace n select f (Suc tick) \<or>
    stateless_exec_step (serviced_stateless_trace n select f tick) (serviced_stateless_trace n select f (Suc tick))"
proof -
  let ?D = "serial_done n select tick"
  from completed_work_change[of "{..<n}" "\<lambda>i. {..<i}" select tick]
  show ?thesis
  proof (elim disjE)
    assume "serial_done n select (Suc tick) = ?D"
    then show ?thesis by (simp add: serviced_stateless_trace_def)
  next
    assume "\<exists>a. select tick = Some a \<and> work_ready {..<n} (\<lambda>i. {..<i}) ?D a \<and>
      serial_done n select (Suc tick) = insert a ?D"
    then obtain a where ready: "work_ready {..<n} (\<lambda>i. {..<i}) ?D a"
      and insert: "serial_done n select (Suc tick) = insert a ?D" by blast
    have prefix: "?D = {..<card ?D}" by (rule serial_work_is_prefix[OF ordered_completed_work])
    from ready have job: "a < n" and new: "a \<notin> ?D" and deps: "{..<a} \<subseteq> ?D"
      by (auto simp: work_ready_def)
    have deps': "{..<a} \<subseteq> {..<card ?D}" by (subst prefix[symmetric]) (rule deps)
    have new': "a \<notin> {..<card ?D}" by (subst prefix[symmetric]) (rule new)
    have count: "card ?D < n" using deps' new' job by simp
    have sub: "?D \<subseteq> {..<n}" using ordered_completed_work by (rule ordered_work_def[THEN iffD1, THEN conjunct1])
    have fin: "finite ?D" by (rule finite_subset[OF sub]) simp
    have next_count: "card (serial_done n select (Suc tick)) = Suc (card ?D)"
      unfolding insert by (rule card_insert_disjoint[OF fin new])
    show ?thesis unfolding serviced_stateless_trace_def next_count by (rule path[OF count])
  qed
qed

lemma serviced_stateless_trace_end:
  assumes service: "bounded_service {..<n} (\<lambda>i. {..<i}) select B horizon"
    and bound: "n * B \<le> horizon"
  shows "serviced_stateless_trace n select f (n * B) = f n"
proof -
  have "{..<n} \<subseteq> serial_done n select (n * B)"
    by (rule serial_work_through[OF service le_refl bound])
  moreover have "serial_done n select (n * B) \<subseteq> {..<n}"
    using ordered_completed_work[of "{..<n}" "\<lambda>i. {..<i}" select "n * B"]
    by (simp add: ordered_work_def)
  ultimately have "serial_done n select (n * B) = {..<n}" by blast
  then show ?thesis by (simp add: serviced_stateless_trace_def)
qed

section \<open>Lease effect and candidate recovery\<close>

lemma stateless_floor_below_reservation:
  assumes "stateless_reachable s"
  shows "confirmed_floor s \<le> reserved_term s"
  using assms
proof induction
  case init
  show ?case by (simp add: stateless_initial_def)
next
  case (step s s')
  from step.hyps(2) show ?case
  proof cases
    case (confirm t who)
    from stateless_invariants[OF step.hyps(1)] confirm(2)
    have "t \<le> reserved_term s" unfolding stateless_ok_def lease_ok_def by blast
    with confirm(1) step.IH show ?thesis by simp
  qed (use step.IH in auto)
qed

lemma matching_window_fence_approves:
  assumes "seen = t" "seen = reserved_term s" "confirmed_floor s \<le> reserved_term s"
    "latest_issued s t = Some h" "visible_image s t = Some h"
  shows "stateless_step s (s\<lparr>approvals := insert h (approvals s), frontier := h\<rparr>)"
  by (rule stateless_step.approve[OF assms(4,5)]) (use assms(1-3) in simp)

lemma stateless_exec_reachable_powers:
  assumes "stateless_execution_reachable x" "(stateless_exec_step ^^ k) x y"
  shows "stateless_execution_reachable y"
  using assms(2)
  by (induction k arbitrary: y) (auto elim: relpowp_Suc_E intro: assms(1) stateless_execution_reachable.step)

definition window_move where
  "window_move x y \<longleftrightarrow> x = y \<or> stateless_exec_step x y"

lemma window_move_real: "stateless_exec_step x y \<Longrightarrow> window_move x y"
  by (simp add: window_move_def)

lemma window_moves_from_exec:
  assumes "(stateless_exec_step ^^ k) x y"
  shows "(window_move ^^ k) x y"
  using assms
proof (induction k arbitrary: y)
  case 0
  then show ?case by simp
next
  case (Suc k)
  from Suc.prems obtain z where "(stateless_exec_step ^^ k) x z" "stateless_exec_step z y"
    by (rule relpowp_Suc_E)
  from Suc.IH[OF this(1)] window_move_real[OF this(2)] show ?case by (rule relpowp_Suc_I)
qed

lemma window_moves_reachable:
  assumes start: "stateless_execution_reachable x" and path: "(window_move ^^ k) x y"
  shows "stateless_execution_reachable y"
  using path
proof (induction k arbitrary: y)
  case 0
  then show ?case using start by simp
next
  case (Suc k)
  from Suc.prems obtain z where prev: "(window_move ^^ k) x z" and move: "window_move z y"
    by (rule relpowp_Suc_E)
  from Suc.IH[OF prev] move show ?case unfolding window_move_def
    by (metis stateless_execution_reachable.step)
qed

lemma counted_path_append:
  "(R ^^ i) x y \<Longrightarrow> (R ^^ j) y z \<Longrightarrow> (R ^^ (i + j)) x z"
  by (auto simp: relpowp_add intro: relcomppI)

lemma four_steps:
  "R a b \<Longrightarrow> R b c \<Longrightarrow> R c d \<Longrightarrow> R d e \<Longrightarrow> (R ^^ 4) a e"
  by (simp add: numeral_eq_Suc relcompp_apply) blast

lemma window_move_worker:
  assumes "application_step c (stateless_application_history (shared_state x)) (processes x c) a"
    "applier_only (processes x c) a"
  shows "window_move x (x\<lparr>processes := (processes x)(c := a)\<rparr>)"
  by (intro window_move_real stateless_exec_step.worker[OF assms])

lemma window_local_queue:
  assumes "q \<in> self_ready (processes x c)"
  defines "a \<equiv> processes x c"
  shows "window_move x (x\<lparr>processes := (processes x)(c := a\<lparr>
    self_ready := self_ready a - {q}, queued_applications := insert q (queued_applications a)\<rparr>)\<rparr>)"
  unfolding a_def by (rule window_move_worker, rule application_step.queue_self[OF assms(1)])
    (use assms(1) in \<open>auto simp: applier_only_def\<close>)

lemma window_local_sample:
  assumes "q \<in> queued_applications (processes x c)" "running_application (processes x c) = None"
    "offered (processes x c) = Some k"
  defines "a \<equiv> processes x c"
  shows "window_move x (x\<lparr>processes := (processes x)(c := a\<lparr>
    queued_applications := queued_applications a - {q}, running_application := Some (q,k)\<rparr>)\<rparr>)"
  unfolding a_def by (rule window_move_worker, rule application_step.read_supplier[OF assms(1-3)])
    (auto simp: applier_only_def)

lemma window_local_apply:
  assumes "running_application (processes x c) = Some (q,k)"
  defines "a \<equiv> processes x c"
  shows "window_move x (x\<lparr>processes := (processes x)(c := a\<lparr>
    running_application := None, installed := Some k,
    application_successes := insert (incarnation a,q,k) (application_successes a)\<rparr>)\<rparr>)"
  unfolding a_def by (rule window_move_worker, rule application_step.apply_success[OF assms(1)])
    (auto simp: applier_only_def)

lemma window_local_ack:
  assumes "(incarnation (processes x c), q, k) \<in> application_successes (processes x c)"
  defines "a \<equiv> processes x c"
  shows "window_move x (x\<lparr>processes := (processes x)(c := a\<lparr>
    node_acknowledgements := insert (incarnation a,q,k) (node_acknowledgements a)\<rparr>)\<rparr>)"
  unfolding a_def by (rule window_move_worker, rule application_step.observe_ack[OF assms(1)])
    (auto simp: applier_only_def)

lemma window_move_rewrite_process:
  assumes "window_move x (x\<lparr>processes := (processes x)(c := b)\<rparr>)"
    and "processes x = (processes y)(c := a)"
  shows "window_move x (x\<lparr>processes := (processes y)(c := b)\<rparr>)"
  using assms(1) unfolding assms(2) by simp

text \<open>
  The selected eligible process survives this attempt. The storage view represents
  successful complete listings and a readable image for a download if
  needed. The scan and download see that same view. No interfering
  storage or term action invalidates the path. In particular the fence
  reads the exact granted term, even though a competing CAS with no
  successful callback could have advanced the real register. An
  effective claim alone does not confirm the grant. The subsequent
  callback needs successful service as a separate job.

  The indexed schedule serves successive operations of this successful
  path, including stutters for selecting the recovery base and waiting
  for publication target completion. Service entails the relevant RPCs,
  storage writes, and callbacks actually succeeding. Missing referenced
  files, incomplete listings, failed CAS callbacks, and a superseding
  fence read can therefore prevent a usable window. The local completion
  endpoint records the node acknowledgement. This execution state has
  no publication slot.
\<close>

locale stateless_publication_window =
  fixes x :: stateless_execution and c :: node and proposed payload :: nat and warm :: lineage
    and F :: config and m :: state_manifest
    and backend before live expected result fence_term files
  assumes reach: "stateless_execution_reachable x"
    and effect: "lease_effect backend before live expected (Claim_Term (endpoint x c) proposed) result"
    and represents: "lease_term (lease_value live) = reserved_term (shared_state x)"
    and term_fresh: "app_term (processes x c) < lease_term (lease_value result)"
    and warm: "warm \<in> insert [] (issued (shared_state x))" "app_accepted (processes x c) = position warm"
    and idle: "running_application (processes x c) = None"
    and fence_exact: "fence_term = lease_term (lease_value result)"
    and manifest:
      "manifest_history m = stateless_update (endpoint x c) (lease_term (lease_value result)) payload F
        (stable_recovery_base (stable_probe_result (visible_image (shared_state x)) (lease_term (lease_value result) - 1)) warm)"
    and synced: "files_match files m"
begin

abbreviation t where "t \<equiv> lease_term (lease_value result)"
abbreviation view where "view \<equiv> visible_image (shared_state x)"
abbreviation scanned where "scanned \<equiv> stable_probe_result view (t - 1)"
abbreviation scans where "scans \<equiv> stable_probe_count view (t - 1)"
abbreviation b where "b \<equiv> stable_recovery_base scanned warm"
abbreviation h where "h \<equiv> stateless_update (endpoint x c) t payload F b"
abbreviation q where "q \<equiv> Apply_Request c (position h)"
abbreviation s where "s \<equiv> shared_state x"

lemma stateless_window_length_bound: "4 + scans + 14 \<le> 18 + max 1 (t - 1)"
  using stable_probe_count_le[of view "t - 1"] by (simp add: algebra_simps)

lemma window_new_term: "reserved_term s < t"
  by (rule lease_claim_refines_reserve(2)[OF effect represents])

lemma window_shared_invariants:
  "stateless_reachable s"
  "stateless_ok s"
  using stateless_execution_projection[OF reach] stateless_invariants by blast+

lemma window_issued_earlier:
  assumes "g \<in> insert [] (issued s)"
  shows "term_of g < t"
proof (cases "g = []")
  case True
  with window_new_term show ?thesis by auto
next
  case False
  with assms have mem: "g \<in> issued s" by simp
  from window_shared_invariants(2) have "lease_ok s" "issued_ok s" unfolding stateless_ok_def by auto
  from issued_term_bound[OF this mem] stateless_floor_below_reservation[OF window_shared_invariants(1)]
    window_new_term show ?thesis by linarith
qed

lemma window_no_prior_issue: "latest_issued s t = None"
proof (cases "latest_issued s t")
  case None
  then show ?thesis .
next
  case (Some r)
  with window_shared_invariants(2) have "r \<in> issued s" "term_of r = t"
    unfolding stateless_ok_def issued_ok_def by auto
  with window_issued_earlier[of r] show ?thesis by simp
qed

lemma window_grant_and_scan:
  obtains y where "(stateless_exec_step ^^ (4 + scans)) x y"
    "holds_grant (shared_state y) (endpoint y c) t"
    "reserved_term (shared_state y) = fence_term" "confirmed_floor (shared_state y) = t"
    "latest_issued (shared_state y) t = None"
    "warm \<in> insert [] (issued (shared_state y))" "term_of warm < t"
    "election_base (shared_state y) t warm b"
    "processes y c = (processes x c)\<lparr>app_term := t\<rparr>"
proof -
  let ?reserved = "s\<lparr>reserved_term := t, granted_to := (granted_to s)(t \<mapsto> endpoint x c)\<rparr>"
  let ?confirmed = "?reserved\<lparr>confirmed_floor := t, confirmed_terms := insert t (confirmed_terms s)\<rparr>"
  let ?x1 = "x\<lparr>shared_state := ?reserved\<rparr>"
  let ?x2 = "x\<lparr>shared_state := ?confirmed\<rparr>"
  let ?x3 = "?x2\<lparr>processes := (processes x)(c := (processes x c)\<lparr>app_term := t\<rparr>)\<rparr>"
  let ?x4 = "exec_search ?x3 t (Probe (t - 1))"
  let ?y = "exec_search ?x4 t scanned"
  have reserve: "stateless_exec_step x ?x1"
    by (rule stateless_exec_reservation[OF effect represents])
  have floor: "max t (confirmed_floor s) = t"
    using stateless_floor_below_reservation[OF window_shared_invariants(1)] window_new_term by simp
  have confirmed: "stateless_step ?reserved ?confirmed"
    using stateless_step.confirm[of ?reserved t "endpoint x c"] by (simp add: floor)
  have confirm: "stateless_exec_step ?x1 ?x2"
    using stateless_exec_step.storage[where x="?x1" and s="?confirmed"] confirmed by simp
  have grant: "holds_grant ?confirmed (endpoint x c) t" by (simp add: holds_grant_def)
  have join: "stateless_exec_step ?x2 ?x3"
    using stateless_exec_step.join[where x="?x2" and who="endpoint x c" and n=c and t=t] grant term_fresh by simp
  have search: "stateless_exec_step ?x3 ?x4"
    unfolding exec_search_def by (rule stateless_exec_step.storage)
      (use stateless_step.start_search[OF grant] in simp_all)
  have prefix: "(stateless_exec_step ^^ 4) x ?x4"
    by (rule four_steps[where R=stateless_exec_step, OF reserve confirm join search])
  have scan: "(stateless_exec_step ^^ scans) ?x4 ?y"
    using stable_scan_projects[of ?x4 t "t - 1"] by (simp add: exec_search_def)
  have path: "(stateless_exec_step ^^ (4 + scans)) x ?y"
    using prefix scan by (auto simp: relpowp_add)
  from window_shared_invariants(2) have store: "store_ok (shared_state ?x4)"
    by (simp add: stateless_ok_def store_ok_def exec_search_def)
  have base: "election_base (shared_state ?y) t warm b"
    by (rule stable_scan_supplies_base[OF store, where i="t - 1"]) (simp add: exec_search_def)
  show thesis
    by (rule that[of ?y, OF path _ _ _ _ _ window_issued_earlier[OF warm(1)] base])
      (use grant window_no_prior_issue warm(1) fence_exact in \<open>simp_all add: exec_search_def holds_grant_def\<close>)
qed

lemma window_finishes_after_scan:
  assumes run: "stateless_execution_reachable y"
    and grant: "holds_grant (shared_state y) (endpoint y c) t"
    and reserved: "reserved_term (shared_state y) = fence_term"
    and floor: "confirmed_floor (shared_state y) = t"
    and fresh: "latest_issued (shared_state y) t = None"
    and warm_y: "warm \<in> insert [] (issued (shared_state y))" "term_of warm < t"
    and base: "election_base (shared_state y) t warm b"
    and process: "processes y c = (processes x c)\<lparr>app_term := t\<rparr>"
  obtains z where "(window_move ^^ 14) y z"
    "stateless_execution_reachable z"
    "h \<in> notifications (shared_state z)"
    "installed (processes z c) = Some (position h)"
    "(incarnation (processes z c), q, position h) \<in> node_acknowledgements (processes z c)"
proof -
  let ?s = "shared_state y"
  let ?k = "position h"
  let ?a = "processes y c"
  let ?who = "endpoint y c"
  let ?issued = "?s\<lparr>issued := insert h (issued ?s), latest_issued := (latest_issued ?s)(t \<mapsto> h)\<rparr>"
  let ?stored = "?issued\<lparr>completed_images := insert h (completed_images ?issued), visible_image := (visible_image ?issued)(t \<mapsto> h)\<rparr>"
  let ?approved = "?stored\<lparr>approvals := insert h (approvals ?stored), frontier := h\<rparr>"
  let ?notified = "?approved\<lparr>notifications := insert h (notifications ?approved)\<rparr>"
  let ?y1 = "y\<lparr>shared_state := ?issued\<rparr>"
  let ?y2 = "?y1\<lparr>in_flight := insert (State_Packet h ?who) (in_flight y)\<rparr>"
  let ?y3 = "?y2\<lparr>shared_state := ?stored\<rparr>"
  let ?accepted = "?a\<lparr>app_accepted := ?k\<rparr>"
  let ?y4 = "?y3\<lparr>processes := (processes y)(c := ?accepted)\<rparr>"
  let ?y5 = "?y4\<lparr>shared_state := ?approved\<rparr>"
  let ?y6 = "?y5\<lparr>shared_state := ?notified\<rparr>"
  define sent_commit_state where
    "sent_commit_state = ?y6\<lparr>in_flight := insert (Commit_Packet h ?who) (in_flight ?y6)\<rparr>"
  let ?y7 = "sent_commit_state"
  let ?offered = "?accepted\<lparr>offered := Some ?k, self_ready := insert q (self_ready ?accepted)\<rparr>"
  define self_commit_state where
    "self_commit_state = ?y7\<lparr>processes := (processes y)(c := ?offered)\<rparr>"
  let ?y8 = "self_commit_state"
  let ?queued = "?offered\<lparr>self_ready := self_ready ?offered - {q},
     queued_applications := insert q (queued_applications ?offered)\<rparr>"
  let ?sampled = "?queued\<lparr>queued_applications := queued_applications ?queued - {q},
     running_application := Some (q,?k)\<rparr>"
  let ?applied = "?sampled\<lparr>running_application := None, installed := Some ?k,
     application_successes := insert (incarnation ?sampled,q,?k) (application_successes ?sampled)\<rparr>"
  let ?replied = "?applied\<lparr>node_acknowledgements := insert (incarnation ?applied,q,?k) (node_acknowledgements ?applied)\<rparr>"

  have who: "?who = endpoint x c" using process by simp
  have term_h: "term_of h = t" and owner_h: "owner h = c" by (simp_all add: new_tip_fields)
  have registered: "stateless_exec_step y ?y1"
    by (rule stateless_exec_step.first_publish[where warm=warm and base=b and n=c and t=t and F=F and payload=payload])
      (use grant who process fresh warm_y base warm(2) in simp_all)
  have sent: "stateless_exec_step ?y1 ?y2"
    using stateless_exec_step.send_state[where x="?y1" and n=c and h=h] by simp
  have stored_run: "stateless_reachable (shared_state ?y2)"
    using stateless_execution_projection[OF stateless_execution_reachable.step[OF stateless_execution_reachable.step[OF run registered] sent]]
    by blast
  have stored: "stateless_exec_step ?y2 ?y3"
    using stateless_exec_manifest_install[where x="?y2" and t=t, OF stored_run _ synced]
    by (simp add: manifest)
  have accepted: "stateless_exec_step ?y3 ?y4"
    using stateless_exec_step.receive_state[where x="?y3" and n=c and h=h and a="?a"]
      process warm(2) warm_y(2) term_h by simp
  have approves: "stateless_step ?stored ?approved"
    using matching_window_fence_approves[where s="?stored" and h=h and t=t, OF fence_exact]
      floor reserved fence_exact by simp
  have approved: "stateless_exec_step ?y4 ?y5"
    using stateless_exec_step.storage[where x="?y4" and s="?approved"] approves by simp
  have notifies: "stateless_step ?approved ?notified"
    using stateless_step.notify_commit[where s="?approved" and h=h] by simp
  have notified: "stateless_exec_step ?y5 ?y6"
    using stateless_exec_step.storage[where x="?y5" and s="?notified"] notifies by simp
  have commit_sent: "stateless_exec_step ?y6 ?y7"
    using stateless_exec_step.send_commit[where x="?y6" and n=c and h=h]
    by (simp add: sent_commit_state_def)
  have published_process: "processes ?y7 = (processes y)(c := ?accepted)"
    by (simp add: sent_commit_state_def)
  have same_endpoint: "endpoint ?y7 c = ?who" by (simp add: published_process)
  have commit_packets: "in_flight ?y7 = insert (Commit_Packet h ?who) (in_flight ?y6)"
    using sent_commit_state_def by simp
  have wire: "Commit_Packet h (endpoint ?y7 c) \<in> in_flight ?y7"
    unfolding same_endpoint commit_packets by simp
  have offered: "stateless_exec_step ?y7 ?y8"
  proof -
    have accepted_process: "processes ?y7 c = ?accepted" by (simp add: published_process)
    have accepted_term: "term_of h = app_term ?accepted" using process term_h by simp
    have accepted_key: "position h = app_accepted ?accepted" by simp
    have offered_by_owner: "?offered = (if owner h = c then
          ?accepted\<lparr>offered := Some (position h), self_ready := insert q (self_ready ?accepted)\<rparr>
        else ?accepted\<lparr>offered := Some (position h),
          queued_applications := insert (Apply_Request (owner h) (position h)) (queued_applications ?accepted)\<rparr>)"
      by (simp only: if_P[OF owner_h])
    have offered_step: "stateless_exec_step ?y7 (?y7\<lparr>processes := (processes ?y7)(c := ?offered)\<rparr>)"
      by (rule stateless_exec_step.receive_commit[OF wire accepted_process[symmetric]
          accepted_term accepted_key offered_by_owner])
    have offered_processes: "(processes ?y7)(c := ?offered) = (processes y)(c := ?offered)"
      by (simp add: published_process)
    have offered_state: "?y8 = ?y7\<lparr>processes := (processes ?y7)(c := ?offered)\<rparr>"
      unfolding offered_processes by (simp add: self_commit_state_def)
    show ?thesis
      unfolding offered_state by (rule offered_step)
  qed
  have offered_process: "processes ?y8 = (processes y)(c := ?offered)"
    by (simp add: self_commit_state_def)
  define y9 where "y9 = ?y8\<lparr>processes := (processes y)(c := ?queued)\<rparr>"
  define y10 where "y10 = y9\<lparr>processes := (processes y)(c := ?sampled)\<rparr>"
  define y11 where "y11 = y10\<lparr>processes := (processes y)(c := ?applied)\<rparr>"
  define y12 where "y12 = y11\<lparr>processes := (processes y)(c := ?replied)\<rparr>"
  have y9_processes: "processes y9 = (processes y)(c := ?queued)" by (simp add: y9_def)
  have y10_processes: "processes y10 = (processes y)(c := ?sampled)" by (simp add: y10_def)
  have y11_processes: "processes y11 = (processes y)(c := ?applied)" by (simp add: y11_def)
  have y12_processes: "processes y12 = (processes y)(c := ?replied)" by (simp add: y12_def)
  have y12_shared: "shared_state y12 = ?notified"
    by (simp add: y12_def y11_def y10_def y9_def self_commit_state_def sent_commit_state_def)
  have queue: "window_move ?y8 y9"
  proof -
    have self_ready: "q \<in> self_ready (processes ?y8 c)" by (simp add: offered_process)
    from window_move_rewrite_process[OF window_local_queue[OF self_ready] offered_process]
    show ?thesis unfolding y9_def by (simp add: offered_process)
  qed
  have sample: "window_move y9 y10"
  proof -
    have queued: "q \<in> queued_applications (processes y9 c)" by (simp add: y9_processes)
    have not_running: "running_application (processes y9 c) = None"
      using idle process by (simp add: y9_processes)
    have offered_key: "offered (processes y9 c) = Some ?k" by (simp add: y9_processes)
    from window_move_rewrite_process[OF window_local_sample[OF queued not_running offered_key] y9_processes]
    show ?thesis unfolding y10_def by (simp add: y9_processes)
  qed
  have applied_move: "window_move y10 y11"
  proof -
    have running: "running_application (processes y10 c) = Some (q,?k)" by (simp add: y10_processes)
    from window_move_rewrite_process[OF window_local_apply[OF running] y10_processes]
    show ?thesis unfolding y11_def by (simp add: y10_processes)
  qed
  have reply: "window_move y11 y12"
  proof -
    have succeeded: "(incarnation (processes y11 c), q, ?k) \<in> application_successes (processes y11 c)"
      by (simp add: y11_processes)
    from window_move_rewrite_process[OF window_local_ack[OF succeeded] y11_processes]
    show ?thesis unfolding y12_def by (simp add: y11_processes)
  qed

  have prefix: "(stateless_exec_step ^^ (4 + 4)) y ?y8"
    by (rule counted_path_append[where R=stateless_exec_step,
      OF four_steps[where R=stateless_exec_step, OF registered sent stored accepted]
        four_steps[where R=stateless_exec_step, OF approved notified commit_sent offered]])
  have id_y: "window_move y y" by (simp add: window_move_def)
  have mid: "(window_move ^^ 9) y ?y8"
  proof -
    have "Suc (4 + 4) = (9::nat)" by simp
    from relpowp_Suc_I2[where P=window_move, OF id_y window_moves_from_exec[OF prefix]] show ?thesis
      unfolding \<open>Suc (4 + 4) = (9::nat)\<close> .
  qed
  have id_offered: "window_move ?y8 ?y8" by (simp add: window_move_def)
  have tail: "(window_move ^^ 5) ?y8 y12"
  proof -
    have "Suc 4 = (5::nat)" by simp
    from relpowp_Suc_I2[where P=window_move,
      OF id_offered four_steps[where R=window_move, OF queue sample applied_move reply]]
    show ?thesis unfolding \<open>Suc 4 = (5::nat)\<close> .
  qed
  have sum: "9 + 5 = (14::nat)" by simp
  have path: "(window_move ^^ 14) y y12"
    using counted_path_append[where R=window_move, OF mid tail] unfolding sum .
  have reached: "stateless_execution_reachable y12" by (rule window_moves_reachable[OF run path])
  show thesis by (rule that[of y12, OF path reached]) (simp_all add: y12_shared y12_processes)
qed

theorem stateless_window_completes_by_deadline:
  assumes service: "bounded_service {..<4 + scans + 14} (\<lambda>i. {..<i}) select B horizon"
    and time: "(18 + max 1 (t - 1)) * B \<le> horizon"
  obtains run where "run 0 = x"
    "\<And>i. run i = run (Suc i) \<or> stateless_exec_step (run i) (run (Suc i))"
    "stateless_execution_reachable (run ((4 + scans + 14) * B))"
    "h \<in> notifications (shared_state (run ((4 + scans + 14) * B)))"
    "installed (processes (run ((4 + scans + 14) * B)) c) = Some (position h)"
    "(incarnation (processes (run ((4 + scans + 14) * B)) c), q, position h)
       \<in> node_acknowledgements (processes (run ((4 + scans + 14) * B)) c)"
proof -
  obtain y where path: "(stateless_exec_step ^^ (4 + scans)) x y"
    and facts: "holds_grant (shared_state y) (endpoint y c) t"
      "reserved_term (shared_state y) = fence_term" "confirmed_floor (shared_state y) = t"
      "latest_issued (shared_state y) t = None"
      "warm \<in> insert [] (issued (shared_state y))" "term_of warm < t"
      "election_base (shared_state y) t warm b"
      "processes y c = (processes x c)\<lparr>app_term := t\<rparr>"
    by (rule window_grant_and_scan)
  from window_finishes_after_scan[OF stateless_exec_reachable_powers[OF reach path] facts]
  obtain z where tail: "(window_move ^^ 14) y z"
    and result: "stateless_execution_reachable z" "h \<in> notifications (shared_state z)"
    "installed (processes z c) = Some (position h)"
    "(incarnation (processes z c), q, position h) \<in> node_acknowledgements (processes z c)" by blast
  let ?n = "4 + scans + 14"
  from counted_path_append[where R=window_move, OF window_moves_from_exec[OF path] tail]
  obtain f where f: "f 0 = x" "f ?n = z" "\<And>i. i < ?n \<Longrightarrow> window_move (f i) (f (Suc i))"
    unfolding relpowp_fun_conv by blast
  let ?run = "serviced_stateless_trace ?n select f"
  have nbound: "?n * B \<le> horizon"
    by (rule order_trans[OF mult_le_mono1[OF stateless_window_length_bound] time])
  have finished_trace: "?run (?n * B) = z"
    using serviced_stateless_trace_end[OF service nbound, of f] f(2) by simp
  have transitions: "?run i = ?run (Suc i) \<or> stateless_exec_step (?run i) (?run (Suc i))" for i
    using serviced_stateless_trace_projects[of ?n f select i] f(3) unfolding window_move_def by blast
  show thesis by (rule that[of ?run, OF _ transitions]) (use f(1) finished_trace result in \<open>simp_all add: serviced_stateless_trace_def\<close>)
qed

theorem stateless_timer_window_completes:
  assumes timer: "timer_window contenders c timer_base draws extra duration own_next pending drained window_length"
    and start: "start = timer_base c + draws c + extra c"
    and service: "bounded_service {..<4 + scans + 14} (\<lambda>i. {..<i}) select B window_length"
    and time: "(18 + max 1 (t - 1)) * B \<le> window_length"
  defines "elapsed \<equiv> (4 + scans + 14) * B"
  obtains run where "run 0 = x"
    "\<And>i. run i = run (Suc i) \<or> stateless_exec_step (run i) (run (Suc i))"
    "stateless_execution_reachable (run elapsed)"
    "h \<in> notifications (shared_state (run elapsed))"
    "installed (processes (run elapsed) c) = Some (position h)"
    "(incarnation (processes (run elapsed) c), q, position h) \<in> node_acknowledgements (processes (run elapsed) c)"
    "start + elapsed \<le> start + window_length"
    "\<And>n. n \<in> contenders - {c} \<Longrightarrow> start + elapsed < timer_base n + draws n + extra n"
    "\<And>deadline. deadline \<in> pending \<Longrightarrow> start + elapsed < deadline"
    "start + elapsed < start + duration + own_next"
proof -
  have elapsed: "elapsed \<le> window_length"
    unfolding elapsed_def
    by (rule order_trans[OF mult_le_mono1[OF stateless_window_length_bound] time])
  have fits: "start + elapsed \<le> start + window_length" using elapsed by simp
  note cuts = timer_window_deadlines[OF timer start]
  have peers: "start + elapsed < timer_base n + draws n + extra n" if "n \<in> contenders - {c}" for n
    by (rule le_less_trans[OF fits bspec[OF cuts(2) that]])
  have armed: "start + elapsed < deadline" if "deadline \<in> pending" for deadline
    by (rule le_less_trans[OF fits bspec[OF cuts(3) that]])
  have own: "start + elapsed < start + duration + own_next" by (rule le_less_trans[OF fits cuts(1)])
  show thesis
  proof (rule stateless_window_completes_by_deadline[OF service time])
    fix run :: "nat \<Rightarrow> stateless_execution"
    let ?end = "run ((4 + scans + 14) * B)"
    assume path: "run 0 = x"
      and step: "\<And>i. run i = run (Suc i) \<or> stateless_exec_step (run i) (run (Suc i))"
      and result: "stateless_execution_reachable ?end"
        "h \<in> notifications (shared_state ?end)"
        "installed (processes ?end c) = Some (position h)"
        "(incarnation (processes ?end c), q, position h) \<in> node_acknowledgements (processes ?end c)"
    show thesis by (rule that[OF path step result[folded elapsed_def] fits peers armed own])
  qed
qed

end

end
