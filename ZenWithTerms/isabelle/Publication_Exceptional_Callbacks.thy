theory Publication_Exceptional_Callbacks
  imports Publication_Callback_Identity
begin

section \<open>Rejection after scheduling the cancellation timeout\<close>

datatype publication_timeout =
    Installed_Timeout nat
  | Abandoned_Timeout nat

datatype construction_outcome =
    First_Schedule_Rejected
  | Second_Schedule_Rejected
  | Construction_Installed

text \<open>
  Construction and assignment to currentPublication run under the
  Coordinator mutex. The cancellation closure may be submitted during
  construction, but its cancel call must acquire that same mutex. At
  dispatch it can therefore see a completed installation or the aftermath
  of rejection. Failed allocations have distinct Java identities; the
  Abandoned_Timeout constructor keeps those references disjoint from the
  numbers assigned to successfully installed objects in the projection.
  Cancelling the scheduler handle on rejection may remove the timer. A
  callback already dispatched to the worker or waiting on the mutex is
  still possible and must pass the ownership check at dispatch.
\<close>

fun constructor_timer where
  "constructor_timer First_Schedule_Rejected i = None"
| "constructor_timer Second_Schedule_Rejected i = Some (Abandoned_Timeout i)"
| "constructor_timer Construction_Installed i = Some (Installed_Timeout i)"

fun guarded_publication_timeout where
  "guarded_publication_timeout s (Installed_Timeout i) =
    (if callback_slot s = Some i then run_callback_input s i Cancel_Publication else s)"
| "guarded_publication_timeout s (Abandoned_Timeout i) = s"

lemma rejected_construction_has_no_slot_effect:
  assumes "outcome \<noteq> Construction_Installed"
    "constructor_timer outcome i = Some timeout"
  shows "guarded_publication_timeout s timeout = s"
  using assms by (cases outcome) auto

lemma dispatched_timeout_projects:
  "guarded_publication_timeout s timeout = s \<or>
    callback_step s (guarded_publication_timeout s timeout)"
  by (cases timeout) (auto intro: callback_step.input)

lemma owning_timeout_preserves_cancel:
  assumes "callback_slot s = Some i"
  shows "guarded_publication_timeout s (Installed_Timeout i) =
    run_callback_input s i Cancel_Publication"
  using assms by simp

lemma retired_timeout_cannot_cancel_replacement:
  assumes "callback_slot s = Some j" "j \<noteq> i"
  shows "guarded_publication_timeout s (Installed_Timeout i) = s"
  using assms by simp

text \<open>
  The source check is object reference equality under the mutex, so it
  applies with assertions disabled. If the cancellation timer was never
  created (including single-node discovery) there is no such dispatch.
  With the check, an escaped timer has no control effect even if handle
  cancellation loses the dispatch race. The constructor's failure is
  still delivered by the enclosing publication exception path. This
  projection does not roll back the preceding handleClientValue or
  promise cleanup of a stopped process.
\<close>

section \<open>Application result delivery and trailing exceptions\<close>

datatype changed_apply_phase =
    Applying_Changes
  | Changes_Returned
  | Delivered_Success
  | Apply_Finished bool

datatype changed_apply_action =
    Changes_Return
  | Changes_Throw
  | Report_Success
  | Finish_Bookkeeping
  | Throw_After_Success

inductive changed_apply_step where
  changes_return: "changed_apply_step Applying_Changes Changes_Return None Changes_Returned"
| changes_throw: "changed_apply_step Applying_Changes Changes_Throw (Some False) (Apply_Finished False)"
| report_success: "changed_apply_step Changes_Returned Report_Success (Some True) Delivered_Success"
| finish_bookkeeping: "changed_apply_step Delivered_Success Finish_Bookkeeping None (Apply_Finished True)"
| throw_after_success: "changed_apply_step Delivered_Success Throw_After_Success None (Apply_Finished True)"

fun emitted_result where
  "emitted_result None = []"
| "emitted_result (Some result) = [result]"

inductive changed_apply_trace where
  start: "changed_apply_trace Applying_Changes []"
| extend: "changed_apply_trace phase results \<Longrightarrow> changed_apply_step phase action output phase' \<Longrightarrow>
    changed_apply_trace phase' (results @ emitted_result output)"

fun delivered_results where
  "delivered_results Applying_Changes = []"
| "delivered_results Changes_Returned = []"
| "delivered_results Delivered_Success = [True]"
| "delivered_results (Apply_Finished result) = [result]"

lemma changed_apply_trace_results:
  assumes "changed_apply_trace phase results"
  shows "results = delivered_results phase"
  using assms
  by (induction rule: changed_apply_trace.induct) (auto elim: changed_apply_step.cases)

theorem changed_apply_reports_at_most_once:
  assumes "changed_apply_trace phase results"
  shows "length results \<le> 1"
  using changed_apply_trace_results[OF assms] by (cases phase) auto

fun dispatch_apply_result where
  "dispatch_apply_result s i None = s"
| "dispatch_apply_result s i (Some ok) = run_callback_input s i (Applier_Result ok)"

lemma changed_apply_step_projects:
  "dispatch_apply_result s i output = s \<or> callback_step s (dispatch_apply_result s i output)"
  by (cases "output") (simp_all add: callback_step.input)

theorem trailing_exception_preserves_success_and_slot:
  assumes "changed_apply_trace phase results"
    "changed_apply_step phase Throw_After_Success output phase'"
  shows "results = [True]"
    "phase' = Apply_Finished True"
    "results @ emitted_result output = [True]"
    "dispatch_apply_result s i output = s"
  using assms(2) changed_apply_trace_results[OF assms(1)]
  by (auto elim: changed_apply_step.cases)

lemma completed_changes_do_not_report_failure:
  assumes "phase \<in> {Changes_Returned, Delivered_Success, Apply_Finished True}"
    "changed_apply_step phase action output phase'"
  shows "output \<noteq> Some False"
    "phase' \<in> {Changes_Returned, Delivered_Success, Apply_Finished True}"
  using assms by (auto elim: changed_apply_step.cases)

text \<open>
  Changes_Returned means that the application call returned normally.
  It is not the atomic write of the applied-state field inside that call.
  A failure before the call returns may already have performed effects
  of applying. The changed-state path in ClusterApplierService catches
  exceptions around setting the applying flag and calling applyChanges.
  If that block throws, it takes only the failure branch. Success
  delivery and later timing and logging are outside that catch, and the
  outer finally still clears the applying flag in either case. The
  no-change branch already delivers success outside the failure catch.

  A post-success exception has no second listener delivery, even if the
  first delivery has already released the slot and another publication
  is installed. The proof allows that exception to propagate outside this
  update task. It neither requires bookkeeping to return normally nor
  promises that listener code which fails before releasing the slot will
  finish publication. A successful delivery step denotes invocation of
  the existing success handler, whose subsequent work is still governed
  by the callback service and phase premises.
\<close>

section \<open>Slot and mode at the exceptional dispatch boundary\<close>

text \<open>
  These are the projected Coordinator effects of the old failure
  callback once it reaches the writes. The projection assumes the
  cancellation or failure path gets that far, and that the term check
  holds when a same-term mode change is exhibited. It does not assert
  that production logging throws or that a particular scheduler shutdown
  necessarily lets an escaped timeout run.
\<close>

definition unguarded_failure_effect where
  "unguarded_failure_effect s same_term =
    s\<lparr>callback_slot := None, callback_leading := callback_leading s \<and> \<not> same_term\<rparr>"

lemma unguarded_old_failure_can_displace_replacement:
  assumes "callback_slot s = Some j" "i \<noteq> j"
    "callback_objects s i = Some Retired_Publication"
    "callback_leading s"
  shows "callback_slot (unguarded_failure_effect s True) \<noteq> callback_slot s"
    "\<not> callback_leading (unguarded_failure_effect s True)"
  using assms by (simp_all add: unguarded_failure_effect_def)

theorem exceptional_callbacks_preserve_replacement:
  assumes rejected: "outcome \<noteq> Construction_Installed" "constructor_timer outcome k = Some timeout"
    and success: "changed_apply_trace phase results" "changed_apply_step phase Throw_After_Success output phase'"
  shows "guarded_publication_timeout (dispatch_apply_result s i output) timeout = s"
    "results @ emitted_result output = [True]"
proof -
  have unchanged: "dispatch_apply_result s i output = s"
    by (rule trailing_exception_preserves_success_and_slot(4)[OF success])
  show "guarded_publication_timeout (dispatch_apply_result s i output) timeout = s"
    unfolding unchanged by (rule rejected_construction_has_no_slot_effect[OF rejected])
  show "results @ emitted_result output = [True]"
    by (rule trailing_exception_preserves_success_and_slot(3)[OF success])
qed

corollary exceptional_callbacks_then_owned_clear:
  fixes i :: nat
  assumes reached: "callback_reachable c" "stateless_slot_reachable n s"
    and slot: "callback_slot c = map_option object_generation (active_slot s)"
    and clear: "callback_objects c j = Some (Ready_To_Clear ok)"
    and phase: "\<And>p. active_slot s = Some p \<Longrightarrow>
      if ok then (\<exists>k. object_phase p = Local_Apply_Hook_Done k) else object_phase p = Publication_Failed"
    and rejected: "outcome \<noteq> Construction_Installed" "constructor_timer outcome k = Some timeout"
    and late: "changed_apply_trace a results" "changed_apply_step a Throw_After_Success output a'"
  defines "c' \<equiv> guarded_publication_timeout (dispatch_apply_result c i output) timeout"
  shows "callback_slot c' = Some j"
    "stateless_slot_step n s (dispatch_publication_signal n j (clear_signal ok) s)"
    "callback_slot (clear_callback_slot c' j) =
       map_option object_generation (active_slot (dispatch_publication_signal n j (clear_signal ok) s))"
proof -
  have "c' = c" unfolding c'_def
    by (rule exceptional_callbacks_preserve_replacement(1)[OF rejected late])
  then show "callback_slot c' = Some j"
    using clearing_callback_owns_slot(1)[OF reached(1) clear] by simp
  from owned_clear_supplies_projected_guard[OF reached slot clear phase]
  show "stateless_slot_step n s (dispatch_publication_signal n j (clear_signal ok) s)"
    "callback_slot (clear_callback_slot c' j) =
       map_option object_generation (active_slot (dispatch_publication_signal n j (clear_signal ok) s))"
    by (simp_all add: \<open>c' = c\<close>)
qed

end
