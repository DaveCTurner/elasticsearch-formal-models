theory Worker_Listener_Handoff
  imports Master_Service_Queue_Liveness Publication_Callback_Identity
begin

section \<open>After a batch has acquired its task\<close>

text \<open>
  This is the changed-state path for a task whose executor selected success,
  together with the early exits of a master-only batch. A release callback
  identifies the batch's own publication. It clears under the Coordinator
  mutex. Deferred term and leadership work runs before the successful
  callback leaves that mutex. Cancellation of timers and the local
  acknowledgement callback precede the publication listener. The MasterService
  listener reports individual task outcomes and its runAfter continuation
  completes the batch. Processor.run clears its executing entries before
  queuesProcessor.onCompletion clears currentlyExecutingBatch and decrements
  the outstanding batch count. Only then can the worker fork or reject the
  next batch. This is a boundary projection of those calls, with execution
  and delivery of callbacks that return still requiring service. A completed
  publication uses a single publication listener invocation. The success
  path leaves the mutex before invoking it, while the self-failure path can
  invoke it under the mutex. The slot-work phase marks both boundaries
  without requiring all branches to release the mutex there.

  Shutdown has two different ways to lose the acquired task's result.
  executeAndPublishBatch may see a stopped lifecycle after Processor.run
  acquired the task, although the queue processor saw it started. Alternatively
  the publication listener may be supplied an executor shutdown rejection.
  Both paths can return the worker and omit task notification. The publication
  listener also has an unexpected-exception branch that logs rather than
  calling task listeners. An assertion can fire there, so its continuation
  below is scoped to execution with assertions disabled. This is a
  classification of supplied exceptions at the source boundary. The standard
  ClusterApplierService itself can instead silently return when stopped, or
  swallow a shutdown rejection from submission. Such a missing callback can
  leave the slot held and cannot be modeled as a reported rejection.
  Ordinary mastership loss arrives as NotMasterException or
  FailedToCommitClusterStateException and reports a retryable task failure.
\<close>

datatype handoff_omission =
    Stopped_After_Claim
  | Publication_Executor_Shutdown
  | Unexpected_Publication_Exception

datatype handoff_verdict = Handoff_Deliver master_task_result | Handoff_Omit handoff_omission

datatype handoff_publication =
    Handoff_Published
  | Handoff_Not_Master
  | Handoff_Failed_To_Commit
  | Handoff_Shutdown_Rejection
  | Handoff_Unexpected_Failure

fun publication_handoff_verdict where
  "publication_handoff_verdict Handoff_Published = Handoff_Deliver Task_Published"
| "publication_handoff_verdict Handoff_Not_Master = Handoff_Deliver (Task_Rejected No_Longer_Master)"
| "publication_handoff_verdict Handoff_Failed_To_Commit =
    Handoff_Deliver (Task_Rejected Publication_Failed_To_Commit)"
| "publication_handoff_verdict Handoff_Shutdown_Rejection = Handoff_Omit Publication_Executor_Shutdown"
| "publication_handoff_verdict Handoff_Unexpected_Failure = Handoff_Omit Unexpected_Publication_Exception"

datatype handoff_round = Handoff_Idle | Handoff_Fork | Handoff_Reject_Queue

definition handoff_next_round where
  "handoff_next_round running accepting remaining =
    (if remaining = (0::nat) then Handoff_Idle
     else if running \<and> accepting then Handoff_Fork else Handoff_Reject_Queue)"

datatype worker_handoff_phase =
    Handoff_Claimed
  | Handoff_Owns_Slot
  | Handoff_Cleared handoff_publication
  | Handoff_After_Slot_Work handoff_publication
  | Handoff_In_Listener handoff_publication
  | Handoff_Result master_task_result
  | Handoff_In_Finalizer handoff_verdict
  | Handoff_Worker_Free handoff_verdict
  | Handoff_Next_Round handoff_verdict handoff_round

datatype worker_handoff_event =
    Install_Publication
  | Stop_At_Execution_Check
  | Fail_Mastership_Check
  | Fail_Before_Installation
  | Clear_Own_Publication handoff_publication
  | Complete_Coordinator_Slot_Work
  | Invoke_Publication_Listener
  | Resolve_Publication_Result
  | Invoke_Task_Continuation
  | Complete_Batch_Listener
  | Check_Next_Batch bool bool nat
  | Suppress_Stopped_Applier_Callback
  | No_Handoff_Work

fun begin_handoff_finalizer where
  "begin_handoff_finalizer (Handoff_Deliver result) = Handoff_Result result"
| "begin_handoff_finalizer (Handoff_Omit why) = Handoff_In_Finalizer (Handoff_Omit why)"

primrec worker_handoff_step where
  "worker_handoff_step Install_Publication p =
    (if p = Handoff_Claimed then Handoff_Owns_Slot else p)"
| "worker_handoff_step Stop_At_Execution_Check p =
    (if p = Handoff_Claimed then Handoff_In_Finalizer (Handoff_Omit Stopped_After_Claim) else p)"
| "worker_handoff_step Fail_Mastership_Check p =
    (if p = Handoff_Claimed then Handoff_Result (Task_Rejected No_Longer_Master) else p)"
| "worker_handoff_step Fail_Before_Installation p =
    (if p = Handoff_Claimed then Handoff_In_Listener Handoff_Not_Master else p)"
| "worker_handoff_step (Clear_Own_Publication out) p =
    (if p = Handoff_Owns_Slot then Handoff_Cleared out else p)"
| "worker_handoff_step Complete_Coordinator_Slot_Work p =
    (case p of Handoff_Cleared out \<Rightarrow> Handoff_After_Slot_Work out | _ \<Rightarrow> p)"
| "worker_handoff_step Invoke_Publication_Listener p =
    (case p of Handoff_After_Slot_Work out \<Rightarrow> Handoff_In_Listener out | _ \<Rightarrow> p)"
| "worker_handoff_step Resolve_Publication_Result p =
    (case p of Handoff_In_Listener out \<Rightarrow> begin_handoff_finalizer (publication_handoff_verdict out) | _ \<Rightarrow> p)"
| "worker_handoff_step Invoke_Task_Continuation p =
    (case p of Handoff_Result result \<Rightarrow> Handoff_In_Finalizer (Handoff_Deliver result) | _ \<Rightarrow> p)"
| "worker_handoff_step Complete_Batch_Listener p =
    (case p of Handoff_In_Finalizer verdict \<Rightarrow> Handoff_Worker_Free verdict | _ \<Rightarrow> p)"
| "worker_handoff_step (Check_Next_Batch running accepting remaining) p =
    (case p of Handoff_Worker_Free verdict \<Rightarrow>
       Handoff_Next_Round verdict (handoff_next_round running accepting remaining) | _ \<Rightarrow> p)"
| "worker_handoff_step Suppress_Stopped_Applier_Callback p = p"
| "worker_handoff_step No_Handoff_Work p = p"

fun worker_handoff_trace where
  "worker_handoff_trace init input 0 = init"
| "worker_handoff_trace init input (Suc i) = worker_handoff_step (input i) (worker_handoff_trace init input i)"

fun worker_handoff_rank where
  "worker_handoff_rank Handoff_Claimed = (8::nat)"
| "worker_handoff_rank Handoff_Owns_Slot = 7"
| "worker_handoff_rank (Handoff_Cleared out) = 6"
| "worker_handoff_rank (Handoff_After_Slot_Work out) = 5"
| "worker_handoff_rank (Handoff_In_Listener out) = 4"
| "worker_handoff_rank (Handoff_Result r) = 3"
| "worker_handoff_rank (Handoff_In_Finalizer v) = 2"
| "worker_handoff_rank (Handoff_Worker_Free v) = 1"
| "worker_handoff_rank (Handoff_Next_Round v r) = 0"

fun planned_handoff_verdict where
  "planned_handoff_verdict (Handoff_Cleared out) = Some (publication_handoff_verdict out)"
| "planned_handoff_verdict (Handoff_After_Slot_Work out) = Some (publication_handoff_verdict out)"
| "planned_handoff_verdict (Handoff_In_Listener out) = Some (publication_handoff_verdict out)"
| "planned_handoff_verdict (Handoff_Result result) = Some (Handoff_Deliver result)"
| "planned_handoff_verdict (Handoff_In_Finalizer v) = Some v"
| "planned_handoff_verdict (Handoff_Worker_Free v) = Some v"
| "planned_handoff_verdict (Handoff_Next_Round v r) = Some v"
| "planned_handoff_verdict p = None"

fun handoff_master_task where
  "handoff_master_task (Handoff_Result result) = Task_Resolved result"
| "handoff_master_task (Handoff_In_Finalizer verdict) =
    (case verdict of Handoff_Deliver r \<Rightarrow> Task_Delivered r | Handoff_Omit why \<Rightarrow> Task_Dropped)"
| "handoff_master_task (Handoff_Worker_Free verdict) =
    (case verdict of Handoff_Deliver r \<Rightarrow> Task_Delivered r | Handoff_Omit why \<Rightarrow> Task_Dropped)"
| "handoff_master_task (Handoff_Next_Round verdict decision) =
    (case verdict of Handoff_Deliver r \<Rightarrow> Task_Delivered r | Handoff_Omit why \<Rightarrow> Task_Dropped)"
| "handoff_master_task p = Task_Admitted"

lemma begin_handoff_finalizer_properties [simp]:
  "worker_handoff_rank (begin_handoff_finalizer v) < 4"
  "begin_handoff_finalizer v \<noteq> Handoff_In_Listener out"
  "planned_handoff_verdict (begin_handoff_finalizer v) = Some v"
  by (cases v; simp)+

lemma worker_handoff_rank_decreases:
  assumes "worker_handoff_step e p \<noteq> p"
  shows "worker_handoff_rank (worker_handoff_step e p) < worker_handoff_rank p"
  using assms by (cases e; cases p) simp_all

lemma worker_handoff_enabled_cases:
  "worker_handoff_step e (Handoff_Cleared out) \<noteq> Handoff_Cleared out \<longleftrightarrow>
     e = Complete_Coordinator_Slot_Work"
  "worker_handoff_step e (Handoff_After_Slot_Work out) \<noteq> Handoff_After_Slot_Work out \<longleftrightarrow>
     e = Invoke_Publication_Listener"
  "worker_handoff_step e (Handoff_In_Listener out) \<noteq> Handoff_In_Listener out \<longleftrightarrow>
     e = Resolve_Publication_Result"
  "worker_handoff_step e (Handoff_Result result) \<noteq> Handoff_Result result \<longleftrightarrow>
     e = Invoke_Task_Continuation"
  "worker_handoff_step e (Handoff_In_Finalizer verdict) \<noteq> Handoff_In_Finalizer verdict \<longleftrightarrow>
     e = Complete_Batch_Listener"
  "worker_handoff_step e (Handoff_Worker_Free verdict) \<noteq> Handoff_Worker_Free verdict \<longleftrightarrow>
     (\<exists>running accepting remaining. e = Check_Next_Batch running accepting remaining)"
  by (cases e; simp)+

lemma worker_handoff_preserve_verdict:
  assumes "planned_handoff_verdict p = Some v"
  shows "planned_handoff_verdict (worker_handoff_step e p) = Some v"
  using assms by (cases e; cases p) simp_all

definition handoff_task_event where
  "handoff_task_event e p =
    (case e of Stop_At_Execution_Check \<Rightarrow> if p = Handoff_Claimed then Some Drop_On_Shutdown else None
      | Fail_Mastership_Check \<Rightarrow>
          if p = Handoff_Claimed then Some (Finish_Transaction (Task_Rejected No_Longer_Master)) else None
      | Resolve_Publication_Result \<Rightarrow>
          (case p of Handoff_In_Listener out \<Rightarrow>
             (case publication_handoff_verdict out of
                Handoff_Deliver r \<Rightarrow> Some (Finish_Transaction r)
              | Handoff_Omit why \<Rightarrow> if why = Publication_Executor_Shutdown then Some Drop_On_Shutdown else None)
           | _ \<Rightarrow> None)
      | Invoke_Task_Continuation \<Rightarrow> (case p of Handoff_Result r \<Rightarrow> Some Notify_Task_Listener | _ \<Rightarrow> None)
      | _ \<Rightarrow> None)"

lemma worker_handoff_task_projection:
  assumes "planned_handoff_verdict (worker_handoff_step e p) \<noteq>
    Some (Handoff_Omit Unexpected_Publication_Exception)"
  shows "handoff_master_task (worker_handoff_step e p) =
    (case handoff_task_event e p of None \<Rightarrow> handoff_master_task p
     | Some useful \<Rightarrow> master_task_step useful (handoff_master_task p))"
proof (cases e)
  case Resolve_Publication_Result
  then show ?thesis
  proof (cases p)
    case (Handoff_In_Listener out)
    with Resolve_Publication_Result assms show ?thesis
      by (cases out) (simp_all add: handoff_task_event_def)
  qed (simp_all add: handoff_task_event_def)
qed (cases p; simp add: handoff_task_event_def)+

lemma worker_handoff_verdict_from:
  assumes "i \<le> j" "planned_handoff_verdict (worker_handoff_trace init input i) = Some v"
  shows "planned_handoff_verdict (worker_handoff_trace init input j) = Some v"
  using assms(1)
  by (induction rule: dec_induct)
    (use assms(2) in \<open>auto intro: worker_handoff_preserve_verdict\<close>)

lemma worker_handoff_rank_mono:
  assumes "i \<le> j"
  shows "worker_handoff_rank (worker_handoff_trace init input j)
    \<le> worker_handoff_rank (worker_handoff_trace init input i)"
proof -
  have single: "worker_handoff_rank (worker_handoff_trace init input (Suc j))
      \<le> worker_handoff_rank (worker_handoff_trace init input j)" for j
    using worker_handoff_rank_decreases[of "input j" "worker_handoff_trace init input j"]
    by (cases "worker_handoff_step (input j) (worker_handoff_trace init input j) =
          worker_handoff_trace init input j") auto
  from assms show ?thesis
  proof (induction rule: dec_induct)
    case base
    then show ?case by simp
  next
    case (step k)
    show ?case by (rule order_trans[OF single[of k] step.IH])
  qed
qed

lemma worker_handoff_phase_still:
  assumes "i \<le> j" "worker_handoff_rank (worker_handoff_trace init input j) =
    worker_handoff_rank (worker_handoff_trace init input i)"
  shows "worker_handoff_trace init input j = worker_handoff_trace init input i"
  using assms(1,2)
proof (induction rule: dec_induct)
  case base
  then show ?case by simp
next
  case (step k)
  have next_le: "worker_handoff_rank (worker_handoff_trace init input (Suc k)) \<le>
    worker_handoff_rank (worker_handoff_trace init input k)"
    by (rule worker_handoff_rank_mono) simp
  have same: "worker_handoff_rank (worker_handoff_trace init input k) =
    worker_handoff_rank (worker_handoff_trace init input i)"
    using worker_handoff_rank_mono[OF step.hyps(1), of init input]
      next_le step.prems by linarith
  then have previous: "worker_handoff_trace init input k = worker_handoff_trace init input i"
    by (rule step.IH)
  from same step.prems
  have "worker_handoff_step (input k) (worker_handoff_trace init input k) =
        worker_handoff_trace init input k"
    using worker_handoff_rank_decreases[of "input k" "worker_handoff_trace init input k"] by auto
  with previous show ?case by simp
qed

definition worker_handoff_bounded_service where
  "worker_handoff_bounded_service init input B \<longleftrightarrow>
    (\<forall>i. 0 < worker_handoff_rank (worker_handoff_trace init input i) \<longrightarrow>
      (\<exists>j. i \<le> j \<and> j < i + B \<and>
        worker_handoff_step (input j) (worker_handoff_trace init input i) \<noteq>
          worker_handoff_trace init input i))"

text \<open>
  Service means observing a next action enabled at the stage within the
  stated time, as enumerated by worker_handoff_enabled_cases. If the stage
  already changed before that action, the required progress took place even
  earlier. This condition covers callback entry and return, not a bound on
  queuing alone. The final action observes the actual lifecycle, whether
  scheduling is admitted, and the count remaining after release. It may
  fork a worker or take the lifecycle or executor rejection drain.
\<close>

lemma worker_handoff_service_reduces_rank:
  assumes service: "worker_handoff_bounded_service init input B"
    and positive: "0 < worker_handoff_rank (worker_handoff_trace init input i)"
  shows "worker_handoff_rank (worker_handoff_trace init input (i+B)) <
    worker_handoff_rank (worker_handoff_trace init input i)"
proof -
  obtain j where j: "i \<le> j" "j < i+B"
    and event: "worker_handoff_step (input j) (worker_handoff_trace init input i)
      \<noteq> worker_handoff_trace init input i"
    using service positive by (auto simp: worker_handoff_bounded_service_def)
  have less: "worker_handoff_rank (worker_handoff_trace init input (Suc j)) <
    worker_handoff_rank (worker_handoff_trace init input i)"
  proof (cases "worker_handoff_rank (worker_handoff_trace init input j) =
    worker_handoff_rank (worker_handoff_trace init input i)")
    case True
    have "worker_handoff_trace init input j = worker_handoff_trace init input i"
      by (rule worker_handoff_phase_still[OF j(1) True])
    with event show ?thesis by (simp add: worker_handoff_rank_decreases)
  next
    case False
    have earlier_drop: "worker_handoff_rank (worker_handoff_trace init input j) <
      worker_handoff_rank (worker_handoff_trace init input i)"
      using worker_handoff_rank_mono[OF j(1), of init input] False by (simp add: less_le)
    have next_le: "worker_handoff_rank (worker_handoff_trace init input (Suc j)) \<le>
      worker_handoff_rank (worker_handoff_trace init input j)"
      by (rule worker_handoff_rank_mono) simp
    show ?thesis by (rule le_less_trans[OF next_le earlier_drop])
  qed
  show ?thesis by (rule le_less_trans[OF worker_handoff_rank_mono[OF Suc_leI[OF j(2)]] less])
qed

lemma worker_handoff_completed_by_bound:
  assumes service: "worker_handoff_bounded_service init input B"
    and rank: "worker_handoff_rank (worker_handoff_trace init input i) \<le> r"
  shows "worker_handoff_rank (worker_handoff_trace init input (i + r * B)) = 0"
  using rank
proof (induction r arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc r)
  have after_block: "worker_handoff_rank (worker_handoff_trace init input (i+B)) \<le> r"
  proof (cases "worker_handoff_rank (worker_handoff_trace init input i) = 0")
    case True
    have le: "worker_handoff_rank (worker_handoff_trace init input (i+B)) \<le>
      worker_handoff_rank (worker_handoff_trace init input i)"
      by (rule worker_handoff_rank_mono) simp
    from le True show ?thesis by simp
  next
    case False
    then have positive: "0 < worker_handoff_rank (worker_handoff_trace init input i)" by simp
    from worker_handoff_service_reduces_rank[OF service positive] Suc.prems
    show ?thesis by linarith
  qed
  from Suc.IH[OF after_block] show ?case by (simp add: algebra_simps)
qed

theorem cleared_publication_to_next_queue_round:
  assumes service: "worker_handoff_bounded_service init input B"
    and cleared: "worker_handoff_trace init input i = Handoff_Cleared out"
  obtains decision where
    "worker_handoff_trace init input (i + 6 * B) =
      Handoff_Next_Round (publication_handoff_verdict out) decision"
    "handoff_master_task (worker_handoff_trace init input (i + 6 * B)) =
      (case publication_handoff_verdict out of
          Handoff_Deliver result \<Rightarrow> Task_Delivered result
        | Handoff_Omit why \<Rightarrow> Task_Dropped)"
proof -
  have rank: "worker_handoff_rank (worker_handoff_trace init input i) \<le> 6"
    using cleared by simp
  have final: "worker_handoff_rank (worker_handoff_trace init input (i + 6*B)) = 0"
    by (rule worker_handoff_completed_by_bound[OF service rank])
  have result: "planned_handoff_verdict (worker_handoff_trace init input (i + 6*B)) =
       Some (publication_handoff_verdict out)"
    by (rule worker_handoff_verdict_from[where i=i]) (simp_all add: cleared)
  from final result obtain decision where reached: "worker_handoff_trace init input (i + 6*B) =
    Handoff_Next_Round (publication_handoff_verdict out) decision"
    by (cases "worker_handoff_trace init input (i+6*B)") auto
  show thesis using reached by (intro that[of decision]) simp_all
qed

lemma next_batch_forks_or_drains:
  assumes "0 < remaining"
  shows "worker_handoff_step (Check_Next_Batch running accepting remaining) (Handoff_Worker_Free result) =
    Handoff_Next_Round result (if running \<and> accepting then Handoff_Fork else Handoff_Reject_Queue)"
  using assms by (simp add: handoff_next_round_def)

lemma stopped_between_claim_and_execution_can_omit_result:
  "worker_handoff_step (Check_Next_Batch False accepting (Suc queued))
     (worker_handoff_step Complete_Batch_Listener
       (worker_handoff_step Stop_At_Execution_Check Handoff_Claimed)) =
     Handoff_Next_Round (Handoff_Omit Stopped_After_Claim) Handoff_Reject_Queue"
  by (simp add: handoff_next_round_def)

lemma reported_shutdown_can_omit_result_with_next_worker:
  "worker_handoff_step (Check_Next_Batch True True (Suc queued))
     (worker_handoff_step Complete_Batch_Listener
       (worker_handoff_step Resolve_Publication_Result
         (worker_handoff_step Invoke_Publication_Listener
           (worker_handoff_step Complete_Coordinator_Slot_Work
              (Handoff_Cleared Handoff_Shutdown_Rejection))))) =
   Handoff_Next_Round (Handoff_Omit Publication_Executor_Shutdown) Handoff_Fork"
  by (simp add: handoff_next_round_def)

lemma missing_applier_callback_does_not_release_worker:
  "worker_handoff_trace Handoff_Owns_Slot
    (\<lambda>j. if j = 0 then Suppress_Stopped_Applier_Callback else No_Handoff_Work) i = Handoff_Owns_Slot"
  by (induction i) (simp_all split: if_splits)

lemma loss_of_master_after_claim_notifies_before_next_round:
  "worker_handoff_step (Check_Next_Batch running accepting remaining)
     (worker_handoff_step Complete_Batch_Listener
       (worker_handoff_step Invoke_Task_Continuation
         (worker_handoff_step Fail_Mastership_Check Handoff_Claimed))) =
   Handoff_Next_Round (Handoff_Deliver (Task_Rejected No_Longer_Master))
     (handoff_next_round running accepting remaining)"
  by simp

lemma worker_handoff_retry_is_a_new_submission:
  assumes "state = Handoff_Next_Round (Handoff_Deliver result) decision"
    "master_caller_retry attempt result permitted observes_master = Some next"
  shows "handoff_master_task state = Task_Delivered result" "next \<noteq> attempt"
  using assms by (simp_all add: master_caller_retry_def split: if_splits)

theorem owned_stateless_clear_starts_handoff:
  assumes reach: "callback_reachable c" "stateless_slot_reachable n s"
    and slot: "callback_slot c = map_option object_generation (active_slot s)"
    and clear: "callback_objects c i = Some (Ready_To_Clear (out = Handoff_Published))"
    and phase: "\<And>p. active_slot s = Some p \<Longrightarrow>
      if out = Handoff_Published then (\<exists>k. object_phase p = Local_Apply_Hook_Done k)
      else object_phase p = Publication_Failed"
  defines "signal \<equiv> clear_signal (out = Handoff_Published)"
  shows "stateless_slot_step n s (dispatch_publication_signal n i signal s)"
    "active_slot (dispatch_publication_signal n i signal s) = None"
    "worker_handoff_step (Clear_Own_Publication out) Handoff_Owns_Slot = Handoff_Cleared out"
  unfolding signal_def
  using owned_clear_supplies_projected_guard[OF reach slot clear phase] by auto

end
