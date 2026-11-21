theory Stateless_Slot_Liveness
  imports Stateless_Window_Liveness
begin

section \<open>Stateless publication completion at Coordinator callback boundaries\<close>

datatype slot_phase =
    Waiting_For_Quorum | Waiting_For_Fence | Fence_Approved | Fence_Rejected
  | Local_Apply_Queued | Local_Apply_Reported rank | Local_Apply_Hook_Done rank | Publication_Failed

record stateless_publication_object =
  object_generation :: nat
  object_incarnation :: nat
  object_history :: lineage
  object_phase :: slot_phase
  object_self_reply :: "bool option"
  object_target_wait_ended :: bool

record stateless_slot_state =
  slot_exec :: stateless_execution
  active_slot :: "stateless_publication_object option"
  next_object_generation :: nat
  slot_leading :: bool

datatype publication_signal =
    Reach_Quorum | Finish_Fence bool | End_Target_Wait | Abort_Before_Quorum
  | Receive_Self_Reply bool | Queue_Local_Apply | Report_Application rank | Report_Application_Failure
  | Finish_Application_Hook | Clear_Success | Clear_Failure

definition slot_initial where
  "slot_initial = \<lparr>slot_exec = stateless_exec_initial, active_slot = None,
    next_object_generation = 0, slot_leading = False\<rparr>"

definition new_publication_object where
  "new_publication_object e i h = \<lparr>object_generation = i, object_incarnation = e, object_history = h,
    object_phase = Waiting_For_Quorum, object_self_reply = None, object_target_wait_ended = False\<rparr>"

abbreviation object_request where
  "object_request p \<equiv> Apply_Request (owner (object_history p)) (position (object_history p))"

definition matching_local_application where
  "matching_local_application n x p k \<longleftrightarrow>
    owner (object_history p) = n \<and> object_incarnation p = incarnation (processes x n) \<and>
    (object_incarnation p, object_request p,k) \<in> application_successes (processes x n)"

definition publication_waiting where
  "publication_waiting p \<longleftrightarrow>
    object_phase p \<in> {Waiting_For_Quorum, Waiting_For_Fence, Fence_Approved, Fence_Rejected}"

datatype publication_effect = Advance_Object stateless_publication_object | Release_Slot bool

fun publication_signal_effect where
  "publication_signal_effect n x p Reach_Quorum =
    (if object_phase p = Waiting_For_Quorum then Some (Advance_Object (p\<lparr>object_phase := Waiting_For_Fence\<rparr>)) else None)"
| "publication_signal_effect n x p (Finish_Fence success) =
    (if object_phase p = Waiting_For_Fence \<and>
       (success \<longrightarrow> object_history p \<in> notifications (shared_state x))
     then Some (Advance_Object (p\<lparr>object_phase := (if success then Fence_Approved else Fence_Rejected)\<rparr>)) else None)"
| "publication_signal_effect n x p End_Target_Wait =
    (if publication_waiting p \<and> object_phase p \<noteq> Waiting_For_Quorum \<and> \<not> object_target_wait_ended p
     then Some (Advance_Object (p\<lparr>object_target_wait_ended := True\<rparr>)) else None)"
| "publication_signal_effect n x p Abort_Before_Quorum =
    (if object_phase p = Waiting_For_Quorum then Some (Advance_Object
      (p\<lparr>object_target_wait_ended := True, object_self_reply := Some False, object_phase := Publication_Failed\<rparr>)) else None)"
| "publication_signal_effect n x p (Receive_Self_Reply success) =
    (if publication_waiting p \<and> object_self_reply p = None \<and>
       (success \<longrightarrow> object_phase p = Fence_Approved \<and> object_request p \<in> self_ready (processes x n))
     then Some (Advance_Object (p\<lparr>object_self_reply := Some success\<rparr>)) else None)"
| "publication_signal_effect n x p Queue_Local_Apply =
    (if object_target_wait_ended p \<and> publication_waiting p then
       (case object_self_reply p of None \<Rightarrow> None
        | Some success \<Rightarrow> Some (Advance_Object
            (p\<lparr>object_phase := (if success then Local_Apply_Queued else Publication_Failed)\<rparr>)))
     else None)"
| "publication_signal_effect n x p (Report_Application k) =
    (if object_phase p = Local_Apply_Queued \<and> matching_local_application n x p k
     then Some (Advance_Object (p\<lparr>object_phase := Local_Apply_Reported k\<rparr>)) else None)"
| "publication_signal_effect n x p Report_Application_Failure =
    (if object_phase p = Local_Apply_Queued
     then Some (Advance_Object (p\<lparr>object_phase := Publication_Failed\<rparr>)) else None)"
| "publication_signal_effect n x p Finish_Application_Hook =
    (case object_phase p of
       Local_Apply_Reported k \<Rightarrow> Some (Advance_Object (p\<lparr>object_phase := Local_Apply_Hook_Done k\<rparr>))
     | _ \<Rightarrow> None)"
| "publication_signal_effect n x p Clear_Success =
    (case object_phase p of Local_Apply_Hook_Done k \<Rightarrow> Some (Release_Slot True) | _ \<Rightarrow> None)"
| "publication_signal_effect n x p Clear_Failure =
    (if object_phase p = Publication_Failed then Some (Release_Slot False) else None)"

definition dispatch_publication_signal where
  "dispatch_publication_signal n i signal s =
    (case active_slot s of None \<Rightarrow> s
     | Some p \<Rightarrow>
       if i = object_generation p \<and> object_incarnation p = incarnation (processes (slot_exec s) n)
       then (case publication_signal_effect n (slot_exec s) p signal of None \<Rightarrow> s
             | Some (Advance_Object p') \<Rightarrow> s\<lparr>active_slot := Some p'\<rparr>
             | Some (Release_Slot success) \<Rightarrow> s\<lparr>active_slot := None,
                 slot_leading := (slot_leading s \<and> (success \<or>
                   term_of (object_history p) \<noteq> app_term (processes (slot_exec s) n)))\<rparr>)
       else s)"

inductive stateless_slot_step for n where
  core:
    "stateless_exec_step (slot_exec s) x \<Longrightarrow>
     incarnation (processes x n) = incarnation (processes (slot_exec s) n) \<Longrightarrow>
     (\<And>h. h \<in> issued (shared_state x) \<Longrightarrow> owner h = n \<Longrightarrow> h \<in> issued (shared_state (slot_exec s))) \<Longrightarrow>
     stateless_slot_step n s (s\<lparr>slot_exec := x,
       slot_leading := (slot_leading s \<and> app_term (processes x n) = app_term (processes (slot_exec s) n))\<rparr>)"
| restart:
    "stateless_exec_step (slot_exec s) x \<Longrightarrow>
     incarnation (processes x n) \<noteq> incarnation (processes (slot_exec s) n) \<Longrightarrow>
     stateless_slot_step n s (s\<lparr>slot_exec := x, active_slot := None, slot_leading := False\<rparr>)"
| leader_entry:
    "holds_grant (shared_state (slot_exec s)) (endpoint (slot_exec s) n) (app_term (processes (slot_exec s) n)) \<Longrightarrow>
     stateless_slot_step n s (s\<lparr>slot_leading := True\<rparr>)"
| step_down: "stateless_slot_step n s (s\<lparr>slot_leading := False\<rparr>)"
| register:
    "active_slot s = None \<Longrightarrow> slot_leading s \<Longrightarrow> stateless_exec_step (slot_exec s) x \<Longrightarrow>
     h \<in> issued (shared_state x) - issued (shared_state (slot_exec s)) \<Longrightarrow> owner h = n \<Longrightarrow>
     app_term (processes x n) = app_term (processes (slot_exec s) n) \<Longrightarrow> term_of h = app_term (processes x n) \<Longrightarrow>
     incarnation (processes x n) = incarnation (processes (slot_exec s) n) \<Longrightarrow>
     p = new_publication_object (incarnation (processes x n)) (next_object_generation s) h \<Longrightarrow>
     stateless_slot_step n s (s\<lparr>slot_exec := x, active_slot := Some p,
       next_object_generation := Suc (next_object_generation s)\<rparr>)"
| dispatch: "stateless_slot_step n s (dispatch_publication_signal n i signal s)"

inductive stateless_slot_reachable for n where
  init: "stateless_slot_reachable n slot_initial"
| step: "stateless_slot_reachable n s \<Longrightarrow> stateless_slot_step n s s' \<Longrightarrow> stateless_slot_reachable n s'"

text \<open>
  The local slot stores a publication object rather than just its term
  and version. The generation is a ghost identity for a fresh Java
  object. The successful start projects the local issue and installation
  of the object together. Coordinator installs it with an empty slot under
  its mutex. The two completion paths clear that object under the
  mutex. A term change alone can leave the old object in place. Restart
  discards the old process and its slot.

  Receiving the quorum result creates a future, before the lease fence
  has completed. A successful self reply requires the approved fence
  and successful self commit handling. Publication's target wait ends
  when its targets are terminal or it is cancelled. After quorum the
  cancellation does not bypass the self reply or local application.
  Queue_Local_Apply is the completion decision for the local applier
  callback, or the failure branch of localNodeAckEvent. Application work
  and the actual queue update are separate steps of the existing
  stateless execution relation.

  Report_Application consumes evidence that the applier has successfully
  installed a state sampled for this request. Finish_Application_Hook
  represents the work before slot clearing, including the mutex use inside
  onClusterStateApplied, its remaining work outside that mutex, and
  publication timing bookkeeping. Clear_Success represents service of
  the later mutex entry. The success path clears the slot before
  notifying the master service and counting the final publisher
  acknowledgement. Deferred term changes and any follow-up reconfiguration
  after slot clearing require separate service.

  Dispatch stutters on stale input. This is a model boundary, not a Java
  runtime identity check: the check at completion is an assertion. The
  Java mapping needs the lifecycle property that no second slot-clearing
  callback can execute for an already completed object. Publication's
  completion flag is set before invoking onCompletion. The local reply
  is one-shot in SubscribableListener, and the applier's callback wrapper
  catches exceptions from the listener instead of delivering a second
  failure result. A new publication is rejected while this slot is
  occupied. These are source bindings for the staged transition model.
\<close>

section \<open>Identity, stale input, and service of completion\<close>

lemma advance_effect_preserves_identity:
  assumes "publication_signal_effect n x p signal = Some (Advance_Object p')"
  shows "object_generation p' = object_generation p \<and>
    object_incarnation p' = object_incarnation p \<and> object_history p' = object_history p"
  using assms by (cases signal) (auto split: if_splits option.splits slot_phase.splits)

lemma dispatch_generation_unchanged [simp]:
  "next_object_generation (dispatch_publication_signal n i signal s) = next_object_generation s"
  by (simp add: dispatch_publication_signal_def split: option.splits if_splits publication_effect.splits)

lemma dispatch_exec_unchanged [simp]:
  "slot_exec (dispatch_publication_signal n i signal s) = slot_exec s"
  by (simp add: dispatch_publication_signal_def split: option.splits if_splits publication_effect.splits)

lemma dispatch_preserves_object_identity:
  assumes "active_slot (dispatch_publication_signal n i signal s) = Some p'"
  obtains p where "active_slot s = Some p" "object_generation p' = object_generation p"
    "object_incarnation p' = object_incarnation p" "object_history p' = object_history p"
  using assms by (auto simp: dispatch_publication_signal_def
    split: option.splits if_splits publication_effect.splits dest: advance_effect_preserves_identity)

lemma stale_publication_input_stutters:
  assumes "active_slot s = Some p"
    "i \<noteq> object_generation p \<or> object_incarnation p \<noteq> incarnation (processes (slot_exec s) n)"
  shows "dispatch_publication_signal n i signal s = s"
  using assms by (auto simp: dispatch_publication_signal_def)

lemma slot_state_projects:
  assumes "stateless_slot_reachable n s"
  shows "stateless_execution_reachable (slot_exec s)"
    "\<And>p. active_slot s = Some p \<Longrightarrow>
      object_generation p < next_object_generation s \<and> object_incarnation p = incarnation (processes (slot_exec s) n)"
proof -
  have "stateless_execution_reachable (slot_exec s) \<and>
    (\<forall>p. active_slot s = Some p \<longrightarrow>
      object_generation p < next_object_generation s \<and> object_incarnation p = incarnation (processes (slot_exec s) n))"
    using assms
  proof induction
    case init
    show ?case by (simp add: slot_initial_def stateless_execution_reachable.init)
  next
    case (step s s')
    show ?case using step.hyps(2) step.IH
      by (cases rule: stateless_slot_step.cases)
        (auto simp: new_publication_object_def intro: stateless_execution_reachable.step elim: dispatch_preserves_object_identity)
  qed
  then show "stateless_execution_reachable (slot_exec s)" and
    "\<And>p. active_slot s = Some p \<Longrightarrow>
      object_generation p < next_object_generation s \<and> object_incarnation p = incarnation (processes (slot_exec s) n)"
    by auto
qed

lemma slot_step_identity_or_new:
  assumes "stateless_slot_step n s s'"
    "active_slot s' = Some p'"
  shows "(\<exists>p. active_slot s = Some p \<and> object_generation p' = object_generation p) \<or>
    next_object_generation s \<le> object_generation p'"
  using assms by (cases rule: stateless_slot_step.cases)
    (auto simp: new_publication_object_def elim: dispatch_preserves_object_identity)

lemma slot_step_generation_grows:
  "stateless_slot_step n s s' \<Longrightarrow> next_object_generation s \<le> next_object_generation s'"
  by (cases rule: stateless_slot_step.cases) auto

lemma restart_preserves_issued_histories:
  assumes "stateless_exec_step x y"
    "incarnation (processes y n) \<noteq> incarnation (processes x n)"
  shows "issued (shared_state y) = issued (shared_state x)"
  using assms
  by (cases rule: stateless_exec_step.cases) (auto simp: applier_only_def)

lemma local_issue_requires_free_slot:
  assumes "stateless_slot_step n s s'" "owner h = n"
    "h \<in> issued (shared_state (slot_exec s')) - issued (shared_state (slot_exec s))"
  shows "active_slot s = None \<and> slot_leading s"
  using assms by (cases rule: stateless_slot_step.cases)
    (auto dest: restart_preserves_issued_histories)

lemma retired_generation_stays_retired:
  assumes path: "rtranclp (stateless_slot_step n) s s'"
    and old: "i < next_object_generation s" "\<And>p. active_slot s = Some p \<Longrightarrow> object_generation p \<noteq> i"
  shows "\<And>p. active_slot s' = Some p \<Longrightarrow> object_generation p \<noteq> i"
proof -
  have "i < next_object_generation s' \<and>
    (\<forall>p. active_slot s' = Some p \<longrightarrow> object_generation p \<noteq> i)"
    using path
  proof induction
    case base
    then show ?case using old by auto
  next
    case (step a b)
    then have below: "i < next_object_generation b"
      using slot_step_generation_grows[OF step.hyps(2)] by auto
    have "object_generation p \<noteq> i" if "active_slot b = Some p" for p
      using slot_step_identity_or_new[OF step.hyps(2) that] step.IH by auto
    with below show ?case by blast
  qed
  then show "\<And>p. active_slot s' = Some p \<Longrightarrow> object_generation p \<noteq> i" by blast
qed

corollary old_callback_after_release_stutters:
  assumes live: "stateless_slot_reachable n s" "active_slot s = Some p"
    and freed: "a = dispatch_publication_signal n (object_generation p) terminal s" "active_slot a = None"
    and path: "rtranclp (stateless_slot_step n) a b"
  shows "dispatch_publication_signal n (object_generation p) signal b = b"
proof (cases "active_slot b")
  case None
  then show ?thesis by (simp add: dispatch_publication_signal_def)
next
  case (Some p')
  have "object_generation p < next_object_generation a"
    using slot_state_projects(2)[OF live] freed(1) by simp
  from retired_generation_stays_retired[OF path this _ Some] freed(2)
  have "object_generation p' \<noteq> object_generation p" by simp
  then show ?thesis by (intro stale_publication_input_stutters[OF Some]) auto
qed

lemma failed_publication_releases:
  assumes "active_slot s = Some p" "object_incarnation p = incarnation (processes (slot_exec s) n)"
    "object_phase p = Publication_Failed"
  defines "s' \<equiv> dispatch_publication_signal n (object_generation p) Clear_Failure s"
  shows "active_slot s' = None"
    "slot_leading s' \<longleftrightarrow> slot_leading s \<and> term_of (object_history p) \<noteq> app_term (processes (slot_exec s) n)"
  using assms by (simp_all add: dispatch_publication_signal_def)

lemma failed_fence_with_terminal_targets_releases:
  assumes live: "active_slot s = Some p" "object_incarnation p = incarnation (processes (slot_exec s) n)"
    and ready: "object_phase p = Fence_Rejected" "object_self_reply p = Some False" "object_target_wait_ended p"
  defines "b \<equiv> dispatch_publication_signal n (object_generation p) Clear_Failure
    (dispatch_publication_signal n (object_generation p) Queue_Local_Apply s)"
  shows "active_slot b = None" "slot_exec b = slot_exec s"
  using live ready unfolding b_def
  by (simp_all add: dispatch_publication_signal_def publication_waiting_def)

lemma postquorum_cancellation_cannot_bypass_pending_fence:
  assumes "active_slot s = Some p"
    "object_incarnation p = incarnation (processes (slot_exec s) n)"
    "object_phase p = Waiting_For_Fence" "object_self_reply p = None"
    "\<not> object_target_wait_ended p"
  defines "a \<equiv> dispatch_publication_signal n (object_generation p) End_Target_Wait s"
  shows "active_slot a = Some (p\<lparr>object_target_wait_ended := True\<rparr>)"
    "dispatch_publication_signal n (object_generation p) Queue_Local_Apply a = a"
  using assms by (simp_all add: dispatch_publication_signal_def publication_waiting_def)

lemma stateless_application_ack_supplies_completion_evidence:
  assumes reach: "stateless_execution_reachable x"
    and local_ack: "(incarnation (processes x n), Apply_Request n (position h),k) \<in> node_acknowledgements (processes x n)"
    and object: "object_history p = h" "owner h = n" "object_incarnation p = incarnation (processes x n)"
  shows "matching_local_application n x p k"
proof -
  have app: "application_reachable n (stateless_application_history (shared_state x)) 0 rank_zero (processes x n)"
    using stateless_execution_projection[OF reach] by blast
  show ?thesis
    using object successful_node_ack(1)[OF app local_ack] by (simp add: matching_local_application_def)
qed

definition completion_jobs where
  "completion_jobs k = {Report_Application k, Finish_Application_Hook, Clear_Success}"

fun completion_dependencies where
  "completion_dependencies k Finish_Application_Hook = {Report_Application k}"
| "completion_dependencies k Clear_Success = {Finish_Application_Hook}"
| "completion_dependencies k _ = {}"

definition completion_projection where
  "completion_projection n s i k D =
    (let a = if Report_Application k \<in> D then dispatch_publication_signal n i (Report_Application k) s else s;
         b = if Finish_Application_Hook \<in> D then dispatch_publication_signal n i Finish_Application_Hook a else a
     in if Clear_Success \<in> D then dispatch_publication_signal n i Clear_Success b else b)"

lemma completion_projection_advance:
  assumes "ordered_work (completion_jobs k) (completion_dependencies k) D"
    "work_ready (completion_jobs k) (completion_dependencies k) D signal"
  shows "completion_projection n s i k (insert signal D) =
    dispatch_publication_signal n i signal (completion_projection n s i k D)"
  using assms by (auto simp: completion_jobs_def completion_projection_def ordered_work_def work_ready_def Let_def)

lemma completion_projection_preserves_exec [simp]:
  "slot_exec (completion_projection n s i k D) = slot_exec s"
  by (simp add: completion_projection_def Let_def)

lemma completion_projection_preserves_leadership:
  assumes "active_slot s = Some p" "object_phase p = Local_Apply_Queued"
    "object_incarnation p = incarnation (processes (slot_exec s) n)"
    "matching_local_application n (slot_exec s) p k"
  shows "slot_leading (completion_projection n s (object_generation p) k D) = slot_leading s"
  using assms by (auto simp: completion_projection_def Let_def dispatch_publication_signal_def)

lemma bounded_service_finishes_completion:
  assumes service: "bounded_service (completion_jobs k) (completion_dependencies k) select B horizon"
    and time: "3 * B \<le> horizon"
  shows "completion_jobs k \<subseteq> completed_work (completion_jobs k) (completion_dependencies k) select (3 * B)"
proof -
  let ?waves = "[{Report_Application k}, {Finish_Application_Hook}, {Clear_Success}]"
  have valid: "a \<in> completion_jobs k \<and> completion_dependencies k a \<subseteq> \<Union>(set before)"
    if "?waves = before @ group # after" "a \<in> group" for a before group after
    using that by (cases before; auto simp: Cons_eq_append_conv completion_jobs_def)
  have "\<Union>(set ?waves) \<subseteq> completed_work (completion_jobs k) (completion_dependencies k) select (length ?waves * B)"
    by (rule bounded_service_finishes_plan[OF service valid, where rest="[]"]) (use time in simp_all)
  then show ?thesis by (simp add: completion_jobs_def numeral_eq_Suc)
qed

theorem serviced_stateless_callback_clears_slot:
  fixes select :: "nat \<Rightarrow> publication_signal option"
  assumes active: "active_slot s = Some p" "object_phase p = Local_Apply_Queued"
    and matching: "matching_local_application n (slot_exec s) p k"
    and service: "bounded_service (completion_jobs k) (completion_dependencies k) select B horizon"
    and time: "3 * B \<le> horizon"
  defines "run \<equiv> (\<lambda>j. completion_projection n s (object_generation p) k
    (completed_work (completion_jobs k) (completion_dependencies k) select j))"
  shows "run 0 = s" "\<And>j. run j = run (Suc j) \<or> stateless_slot_step n (run j) (run (Suc j))"
    "active_slot (run (3 * B)) = None"
    "slot_exec (run (3 * B)) = slot_exec s"
    "slot_leading (run (3 * B)) = slot_leading s"
proof -
  show "run 0 = s" by (simp add: run_def completion_projection_def)
  fix j
  let ?D = "completed_work (completion_jobs k) (completion_dependencies k) select j"
  let ?D' = "completed_work (completion_jobs k) (completion_dependencies k) select (Suc j)"
  from completed_work_change[of "completion_jobs k" "completion_dependencies k" select j]
  show "run j = run (Suc j) \<or> stateless_slot_step n (run j) (run (Suc j))"
  proof (elim disjE)
    assume "?D' = ?D"
    then show ?thesis by (simp add: run_def)
  next
    assume "\<exists>a. select j = Some a \<and> work_ready (completion_jobs k) (completion_dependencies k) ?D a \<and> ?D' = insert a ?D"
    then obtain a where ready: "work_ready (completion_jobs k) (completion_dependencies k) ?D a"
      and update: "?D' = insert a ?D" by blast
    have "run (Suc j) = dispatch_publication_signal n (object_generation p) a (run j)"
      unfolding run_def update by (rule completion_projection_advance[OF ordered_completed_work ready])
    then show ?thesis by (auto intro: stateless_slot_step.dispatch)
  qed
  let ?finished = "completed_work (completion_jobs k) (completion_dependencies k) select (3 * B)"
  from bounded_service_finishes_completion[OF service time]
  have steps: "Report_Application k \<in> ?finished" "Finish_Application_Hook \<in> ?finished" "Clear_Success \<in> ?finished"
    by (auto simp: completion_jobs_def)
  show "active_slot (run (3 * B)) = None" using active matching steps
    by (auto simp: run_def completion_projection_def matching_local_application_def dispatch_publication_signal_def)
  show "slot_exec (run (3 * B)) = slot_exec s" by (simp add: run_def)
  show "slot_leading (run (3 * B)) = slot_leading s"
    unfolding run_def by (rule completion_projection_preserves_leadership[OF active _ matching])
      (use matching in \<open>simp add: matching_local_application_def\<close>)
qed

lemma stateless_slot_trace_reachable:
  assumes initial: "stateless_slot_reachable n (run 0)"
    and advance: "\<And>j. run j = run (Suc j) \<or> stateless_slot_step n (run j) (run (Suc j))"
  shows "stateless_slot_reachable n (run i)"
proof (induction i)
  case 0
  show ?case by (rule initial)
next
  case (Suc j)
  from advance[of j] show ?case
    by (elim disjE) (use Suc.IH in simp, rule stateless_slot_reachable.step[OF Suc.IH])
qed

corollary serviced_stateless_completion_from_window_ack:
  assumes reach: "stateless_slot_reachable n s"
    and active: "active_slot s = Some p" "object_phase p = Local_Apply_Queued"
    and object: "object_history p = h" "owner h = n"
    and ack: "(incarnation (processes (slot_exec s) n), Apply_Request n (position h),k)
      \<in> node_acknowledgements (processes (slot_exec s) n)"
    and service: "bounded_service (completion_jobs k) (completion_dependencies k) select B horizon"
    and time: "3 * B \<le> horizon"
  obtains a where "stateless_slot_reachable n a" "active_slot a = None"
    "slot_exec a = slot_exec s" "slot_leading a = slot_leading s"
proof -
  have incarnation: "object_incarnation p = incarnation (processes (slot_exec s) n)"
    using slot_state_projects(2)[OF reach active(1)] by simp
  have matching: "matching_local_application n (slot_exec s) p k"
    by (rule stateless_application_ack_supplies_completion_evidence[OF slot_state_projects(1)[OF reach] ack object incarnation])
  let ?run = "\<lambda>j. completion_projection n s (object_generation p) k
    (completed_work (completion_jobs k) (completion_dependencies k) select j)"
  note completion = serviced_stateless_callback_clears_slot[OF active matching service time]
  have start: "stateless_slot_reachable n (?run 0)"
    using reach by (simp add: completion_projection_def)
  have advance: "?run j = ?run (Suc j) \<or> stateless_slot_step n (?run j) (?run (Suc j))" for j
    by (rule completion(2))
  have endpoint: "stateless_slot_reachable n (?run (3 * B))"
    by (rule stateless_slot_trace_reachable[OF start advance])
  show thesis by (rule that[OF endpoint completion(3-5)])
qed

end
