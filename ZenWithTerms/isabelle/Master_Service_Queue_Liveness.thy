theory Master_Service_Queue_Liveness
  imports Main
begin

section \<open>Admission of a submitted MasterService task\<close>

text \<open>
  MasterService.BatchingTaskQueue.submitTask appends an entry before
  incrementing its queue size. A transition from zero offers a processor
  to PerPriorityQueue, whose own transition from zero forks the single
  MasterService processor. Processor.run and Processor.onRejection each
  reserve a snapshot of the size and poll that many FIFO entries. A
  concurrently appended entry can be covered by another submitter's
  increment. We use conservation of these counts at a cut after the
  target and its FIFO predecessors have all registered their counts.
  At that cut the remaining prefix is covered by the reserved drain
  and the next snapshot together, regardless of the order of the
  increments. For example, a submitter can pause after appending ahead
  of the target. The target's increment can then cause that earlier
  entry to be polled while the target waits for the earlier increment.
  Bounded service of those submissions and of offering the processor
  for a positive size are separate premises. The projection uses
  natural-number counts, so queue sizes must fit the Java counters.

  MasterService.takeNextBatch scans the EnumMap in Priority declaration
  order and polls a FIFO queue at each priority. Each higher-priority
  processor that appears in time to be selected can delay the target
  once. Later processors at the target priority join behind it.
  Although the scans are separate polls, every dispatch while a pending
  target is offered either selects a higher-priority processor or polls
  the target's priority. The input in this projection counts additional
  higher-priority processors before each dispatch, including arrivals
  that race the scan. An arrival too late for its priority's poll in one
  scan can be counted before the following dispatch. The initial count includes the higher-priority
  work already ahead. We use an upper bound on this combined competing
  work measured in processor occurrences, including empty drains whose
  task holders have timed out. The starvation watcher logs and leaves
  the choice of priority intact.
\<close>

record master_queue_counts =
  registered_entries :: "nat set"
  available_entries :: nat
  reserved_entries :: nat
  removed_entries :: nat

datatype master_queue_count_event = Register_Queue_Entry nat | Reserve_Queue_Snapshot | Poll_Queue_Entry

fun master_queue_count_step where
  "master_queue_count_step (Register_Queue_Entry index) s =
    (if index \<in> registered_entries s then s
      else s\<lparr>registered_entries := insert index (registered_entries s),
        available_entries := Suc (available_entries s)\<rparr>)"
| "master_queue_count_step Reserve_Queue_Snapshot s =
    (if reserved_entries s = 0 then
      s\<lparr>reserved_entries := available_entries s, available_entries := 0\<rparr> else s)"
| "master_queue_count_step Poll_Queue_Entry s =
    (case reserved_entries s of 0 \<Rightarrow> s
      | Suc entries \<Rightarrow> s\<lparr>reserved_entries := entries, removed_entries := Suc (removed_entries s)\<rparr>)"

definition master_queue_counts_valid where
  "master_queue_counts_valid s \<longleftrightarrow> finite (registered_entries s) \<and>
    removed_entries s + reserved_entries s + available_entries s = card (registered_entries s)"

fun master_queue_count_trace where
  "master_queue_count_trace input 0 =
    \<lparr>registered_entries = {}, available_entries = 0, reserved_entries = 0, removed_entries = 0\<rparr>"
| "master_queue_count_trace input (Suc i) =
    (case input i of None \<Rightarrow> master_queue_count_trace input i
     | Some ev \<Rightarrow> master_queue_count_step ev (master_queue_count_trace input i))"

lemma master_queue_count_trace_valid:
  "master_queue_counts_valid (master_queue_count_trace input i)"
proof (induction i)
  case 0
  show ?case by (simp add: master_queue_counts_valid_def)
next
  case (Suc i)
  have "master_queue_counts_valid (master_queue_count_step ev (master_queue_count_trace input i))" for ev
    using Suc.IH by (cases ev) (auto simp: master_queue_counts_valid_def split: nat.splits)
  with Suc.IH show ?case by (cases "input i") auto
qed

lemma master_queue_registered_prefix_covered:
  fixes removed reserved available registered target_index :: nat
  assumes "Suc target_index \<le> registered"
    "removed + reserved + available = registered"
    "removed \<le> target_index"
  shows "target_index - removed < reserved + available"
  using assms by arith

lemma master_queue_registered_prefix_drain:
  fixes removed reserved available registered target_index :: nat
  assumes registered: "Suc target_index \<le> registered"
    and counts: "removed + reserved + available = registered"
    and pending: "removed \<le> target_index"
  shows "target_index < removed + reserved \<or>
    (available > 0 \<and> target_index - (removed + reserved) < available)"
  using master_queue_registered_prefix_covered[OF registered counts pending] by arith

corollary master_queue_next_drains_cover_registered_prefix:
  assumes registered: "{..target_index} \<subseteq> registered_entries (master_queue_count_trace input i)"
    and pending: "removed_entries (master_queue_count_trace input i) \<le> target_index"
  defines "s \<equiv> master_queue_count_trace input i"
  shows "target_index < removed_entries s + reserved_entries s \<or>
    (available_entries s > 0 \<and> target_index - (removed_entries s + reserved_entries s) < available_entries s)"
proof -
  have valid: "master_queue_counts_valid s" by (simp add: s_def master_queue_count_trace_valid)
  from valid card_mono[of "registered_entries s" "{..target_index}"] registered
  have "Suc target_index \<le> card (registered_entries s)" by (simp add: master_queue_counts_valid_def s_def)
  from master_queue_registered_prefix_drain[OF this _ pending[folded s_def]] valid
  show ?thesis by (simp add: master_queue_counts_valid_def)
qed

lemma master_queue_paused_predecessor_can_delay_registration:
  defines "s \<equiv> master_queue_count_trace
    (\<lambda>i. if i = 0 then Some (Register_Queue_Entry 1)
       else if i = 1 then Some Reserve_Queue_Snapshot else Some Poll_Queue_Entry) 3"
  shows "removed_entries s = 1" "registered_entries s = {1}"
    "reserved_entries s = 0" "available_entries s = 0"
  by (simp_all add: s_def numeral_eq_Suc)

datatype master_queue_wait = Waiting_For_Processor nat nat | Processor_Selected

fun master_queue_dispatch where
  "master_queue_dispatch arrivals Processor_Selected = Processor_Selected"
| "master_queue_dispatch arrivals (Waiting_For_Processor higher peers) =
    (case higher + arrivals of Suc h \<Rightarrow> Waiting_For_Processor h peers
      | 0 \<Rightarrow> (case peers of Suc p \<Rightarrow> Waiting_For_Processor 0 p | 0 \<Rightarrow> Processor_Selected))"

fun master_queue_dispatches where
  "master_queue_dispatches incoming 0 higher peers = Waiting_For_Processor higher peers"
| "master_queue_dispatches incoming (Suc r) higher peers =
    master_queue_dispatch (incoming r) (master_queue_dispatches incoming r higher peers)"

lemma master_queue_dispatch_account:
  assumes "master_queue_dispatch arrivals s = Waiting_For_Processor h p"
  obtains higher peers where "s = Waiting_For_Processor higher peers" "Suc (h + p) = higher + peers + arrivals"
  using assms by (cases s) (auto split: nat.splits)

lemma master_queue_dispatches_account:
  assumes "master_queue_dispatches incoming r higher peers = Waiting_For_Processor h p"
  shows "r + h + p = higher + peers + (\<Sum>i<r. incoming i)"
  using assms
proof (induction r arbitrary: h p)
  case 0
  then show ?case by simp
next
  case (Suc r)
  from master_queue_dispatch_account[of "incoming r" "master_queue_dispatches incoming r higher peers" h p]
    Suc.prems obtain h' p' where before:
      "master_queue_dispatches incoming r higher peers = Waiting_For_Processor h' p'"
      "Suc (h + p) = h' + p' + incoming r" by auto
  from Suc.IH[OF before(1)] before(2) show ?case by (simp add: add.assoc)
qed

theorem master_queue_processor_selected_by_load_bound:
  assumes "(\<Sum>i<Suc (higher + peers + load). incoming i) \<le> load"
  shows "master_queue_dispatches incoming (Suc (higher + peers + load)) higher peers = Processor_Selected"
  using assms master_queue_dispatches_account[of incoming "Suc (higher + peers + load)" higher peers]
  by (cases "master_queue_dispatches incoming (Suc (higher + peers + load)) higher peers") auto

theorem master_queue_higher_priority_can_starve:
  "master_queue_dispatches (\<lambda>_. 1) rounds 0 peers = Waiting_For_Processor 0 peers"
  by (induction rounds) simp_all

text \<open>
  The starvation trace needs only one higher-priority queue. Its next
  submission can offer a new processor after the preceding snapshot
  reset the count. Every service round may then complete, with the
  lower-priority processor still waiting.

  A service round includes the release of any earlier active batch,
  the worker scheduling delay and the next poll or rejection drain.
  A bound requires service of the callbacks that let the active batch
  release the worker, including publication and synchronous listener
  work where it blocks the processor. A reserved snapshot must finish
  polling its prefix within a separate bound. This is a local bound
  for a processor already offered, so the registration and offer
  cut precedes the first round counted here.
\<close>

lemma master_queue_bounded_round_time:
  fixes time :: "nat \<Rightarrow> nat"
  assumes "\<And>i. i < r \<Longrightarrow> time (Suc i) \<le> time i + delay"
  shows "time r \<le> time 0 + r * delay"
  using assms
proof (induction r)
  case 0
  then show ?case by simp
next
  case (Suc r)
  have "time r \<le> time 0 + r * delay"
    by (rule Suc.IH) (use Suc.prems in auto)
  with Suc.prems[of r] show ?case by simp
qed

corollary master_queue_processor_selected_by_time_bound:
  fixes higher peers load :: nat
  defines "r \<equiv> Suc (higher + peers + load)"
  assumes load: "(\<Sum>i<r. incoming i) \<le> load"
    and rounds: "\<And>i. i < r \<Longrightarrow> time (Suc i) \<le> time i + delay"
  shows "master_queue_dispatches incoming r higher peers = Processor_Selected"
    and "time r \<le> time 0 + r * delay"
proof -
  show "master_queue_dispatches incoming r higher peers = Processor_Selected"
    using load unfolding r_def by (rule master_queue_processor_selected_by_load_bound)
  show "time r \<le> time 0 + r * delay"
    by (rule master_queue_bounded_round_time) (rule rounds)
qed

section \<open>Ownership and terminal service of one attempt\<close>

datatype master_task_rejection =
    Before_Batch_Closed
  | Task_Wait_Timeout
  | Timeout_Executor_Closed
  | No_Longer_Master
  | Publication_Failed_To_Commit
  | Task_Execution_Failed

datatype master_task_result = Task_Published | Task_Unchanged | Task_Rejected master_task_rejection

datatype master_task_stage =
    Task_Queued | Task_Admitted | Task_Resolved master_task_result | Task_Delivered master_task_result | Task_Dropped

datatype master_task_event =
    Acquire_Task
  | Reject_Queued_Task
  | Service_Task_Timeout
  | Reject_Task_Timeout
  | Finish_Transaction master_task_result
  | Drop_On_Shutdown
  | Notify_Task_Listener

fun master_transaction_result where
  "master_transaction_result (Task_Rejected Before_Batch_Closed) = False"
| "master_transaction_result (Task_Rejected Task_Wait_Timeout) = False"
| "master_transaction_result (Task_Rejected Timeout_Executor_Closed) = False"
| "master_transaction_result result = True"

fun master_task_step where
  "master_task_step Acquire_Task Task_Queued = Task_Admitted"
| "master_task_step Reject_Queued_Task Task_Queued = Task_Resolved (Task_Rejected Before_Batch_Closed)"
| "master_task_step Service_Task_Timeout Task_Queued = Task_Resolved (Task_Rejected Task_Wait_Timeout)"
| "master_task_step Reject_Task_Timeout Task_Queued = Task_Resolved (Task_Rejected Timeout_Executor_Closed)"
| "master_task_step (Finish_Transaction result) Task_Admitted =
    (if master_transaction_result result then Task_Resolved result else Task_Admitted)"
| "master_task_step Drop_On_Shutdown Task_Admitted = Task_Dropped"
| "master_task_step Notify_Task_Listener (Task_Resolved result) = Task_Delivered result"
| "master_task_step ev s = s"

fun master_task_trace where
  "master_task_trace input 0 = Task_Queued"
| "master_task_trace input (Suc i) =
    (case input i of None \<Rightarrow> master_task_trace input i | Some ev \<Rightarrow> master_task_step ev (master_task_trace input i))"

text \<open>
  Entry.acquireForExecution and the timeout handler both exchange the
  same taskHolder for null. The rejection drain also acquires this
  holder before reporting NotMasterException. The first such exchange
  wins. Service of a timeout event projects an enabled timer actually
  executing at or after its deadline. A timeout scheduler rejection
  before queue insertion returns a failure from submitTask and precedes
  the initial queue state in this theory. An executor shutdown rejection
  of a previously scheduled timeout handler can win ownership from a
  queued entry.

  For master-only executors, executeAndPublishBatch rejects loss of
  leadership at the execution check. The changed-state path can also
  fail in the publisher with NotMasterException or
  FailedToCommitClusterStateException. The unchanged-state and successful
  publication paths call the corresponding success continuation if the
  executor selected it for this task, and notify task failure otherwise.
  A successful task here refers to this execution continuation. Ack
  countdown and any client response have their own service conditions.
  A result and invocation of its listener are separated to make that
  service assumption explicit, even where Java invokes it inline.

  Shutdown of the local MasterService differs from loss of mastership
  while the component still runs. executeAndPublishBatch can observe a
  stop after Processor.run acquired the entries, return to the queue,
  and omit task callbacks. The publication listener also explicitly
  omits task failure notification on executor shutdown rejection (the
  TODO for issue 94930). Drop_On_Shutdown models these paths. A continuing
  leader is only needed for the success branch. Terminal service of the
  original attempt excludes paths that drop its listener on shutdown.
\<close>

lemma master_task_trace_preserves:
  assumes "i \<le> j" "P (master_task_trace input i)"
    "\<And>ev s. P s \<Longrightarrow> P (master_task_step ev s)"
  shows "P (master_task_trace input j)"
  using assms(1)
proof (induction rule: dec_induct)
  case base
  then show ?case by (rule assms(2))
next
  case (step k)
  then show ?case by (cases "input k") (auto intro: assms(3))
qed

lemma master_task_claim_is_final:
  "i \<le> j \<Longrightarrow> master_task_trace input i \<noteq> Task_Queued
    \<Longrightarrow> master_task_trace input j \<noteq> Task_Queued"
proof (rule master_task_trace_preserves)
  fix ev s
  assume "s \<noteq> Task_Queued"
  then show "master_task_step ev s \<noteq> Task_Queued"
    by (cases ev; cases s) auto
qed

lemma master_task_result_persists:
  assumes "i \<le> j"
    "master_task_trace input i \<in> {Task_Resolved result, Task_Delivered result}"
  shows "master_task_trace input j \<in> {Task_Resolved result, Task_Delivered result}"
proof (rule master_task_trace_preserves[where P="\<lambda>s. s \<in> {Task_Resolved result, Task_Delivered result}", OF assms])
  fix ev s
  assume "s \<in> {Task_Resolved result, Task_Delivered result}"
  then show "master_task_step ev s \<in> {Task_Resolved result, Task_Delivered result}"
    by (cases ev; cases s) auto
qed

lemma master_task_delivery_persists:
  "i \<le> j \<Longrightarrow> master_task_trace input i = Task_Delivered result
    \<Longrightarrow> master_task_trace input j = Task_Delivered result"
  by (rule master_task_trace_preserves) (cases rule: master_task_step.cases, simp_all)

lemma master_task_delivery_once:
  assumes "i < j" "master_task_trace input (Suc i) = Task_Delivered result"
  shows "master_task_trace input j = Task_Delivered result"
  by (rule master_task_delivery_persists[OF Suc_leI[OF assms(1)] assms(2)])

lemma master_task_no_silent_loss:
  assumes "\<forall>k<i. input k \<noteq> Some Drop_On_Shutdown"
  shows "master_task_trace input i \<noteq> Task_Dropped"
proof -
  have preserve: "master_task_step ev s \<noteq> Task_Dropped"
    if "ev \<noteq> Drop_On_Shutdown" "s \<noteq> Task_Dropped" for ev s
    using that by (cases ev; cases s) auto
  from assms show ?thesis
  proof (induction i)
    case 0
    show ?case by simp
  next
    case (Suc i)
    have before: "master_task_trace input i \<noteq> Task_Dropped"
      by (rule Suc.IH) (use Suc.prems in auto)
    show ?case
    proof (cases "input i")
      case None
      with before show ?thesis by simp
    next
      case (Some ev)
      have "ev \<noteq> Drop_On_Shutdown" using Suc.prems[rule_format, of i] Some by simp
      from preserve[OF this before] Some show ?thesis by simp
    qed
  qed
qed

lemma master_task_registered_drain_ends_wait:
  assumes "input i \<in> {Some Acquire_Task, Some Reject_Queued_Task}"
  shows "master_task_trace input (Suc i) \<noteq> Task_Queued"
  using assms by (cases "master_task_trace input i") auto

lemma master_task_finish_transaction:
  assumes "master_task_trace input i = Task_Admitted"
    "input i = Some (Finish_Transaction result)" "master_transaction_result result"
  shows "master_task_trace input (Suc i) = Task_Resolved result"
  using assms by simp

lemma master_task_delivered_by_bound:
  assumes terminal: "master_task_trace input i \<in> {Task_Resolved result, Task_Delivered result}"
    and delivery: "master_task_trace input i = Task_Resolved result \<Longrightarrow>
      \<exists>j\<ge>i. j < i + delay \<and> input j = Some Notify_Task_Listener"
  shows "master_task_trace input (i + delay) = Task_Delivered result"
proof (cases "master_task_trace input i = Task_Delivered result")
  case True
  then show ?thesis by (rule master_task_delivery_persists[rotated]) simp
next
  case False
  with terminal have "master_task_trace input i = Task_Resolved result" by simp
  from delivery[OF this] obtain j where j: "i \<le> j" "j < i + delay" "input j = Some Notify_Task_Listener" by blast
  from master_task_result_persists[OF j(1) terminal] j(3)
  have "master_task_trace input (Suc j) = Task_Delivered result" by auto
  then show ?thesis by (rule master_task_delivery_persists[OF Suc_leI[OF j(2)]])
qed

theorem master_submitted_task_terminal_service:
  assumes poll: "poll < admission" "input poll \<in> {Some Acquire_Task, Some Reject_Queued_Task}"
    and live: "\<forall>i<admission + compute. input i \<noteq> Some Drop_On_Shutdown"
    and transaction: "master_task_trace input admission = Task_Admitted \<Longrightarrow>
      \<exists>r k. admission \<le> k \<and> k < admission + compute \<and>
        master_transaction_result r \<and> input k = Some (Finish_Transaction r)"
    and notify: "\<And>r. master_task_trace input (admission + compute) = Task_Resolved r \<Longrightarrow>
      \<exists>j\<ge>admission + compute. j < admission + compute + delivery \<and> input j = Some Notify_Task_Listener"
  shows "\<exists>r. master_task_trace input (admission + compute + delivery) = Task_Delivered r"
proof -
  have left_queue: "master_task_trace input admission \<noteq> Task_Queued"
  proof (rule master_task_claim_is_final[OF Suc_leI[OF poll(1)]])
    show "master_task_trace input (Suc poll) \<noteq> Task_Queued"
      by (rule master_task_registered_drain_ends_wait[where input=input, OF poll(2)])
  qed
  have not_dropped: "master_task_trace input admission \<noteq> Task_Dropped"
    by (rule master_task_no_silent_loss) (use live in auto)
  obtain r k where k: "k \<le> admission + compute"
    "master_task_trace input k \<in> {Task_Resolved r, Task_Delivered r}"
  proof (cases "master_task_trace input admission = Task_Admitted")
    case True
    then obtain r j where j: "admission \<le> j" "j < admission + compute"
      "master_transaction_result r" "input j = Some (Finish_Transaction r)"
      using transaction by blast
    have "master_task_trace input j \<noteq> Task_Queued"
      by (rule master_task_claim_is_final[OF j(1) left_queue])
    moreover have "master_task_trace input j \<noteq> Task_Dropped"
      by (rule master_task_no_silent_loss) (use j(2) live in auto)
    ultimately obtain result where "master_task_trace input (Suc j) \<in> {Task_Resolved result, Task_Delivered result}"
      using j(3,4) that by (cases "master_task_trace input j") auto
    then show thesis by (rule that[OF Suc_leI[OF j(2)]])
  next
    case False
    with left_queue not_dropped obtain r where result:
      "master_task_trace input admission \<in> {Task_Resolved r, Task_Delivered r}"
      by (cases "master_task_trace input admission") auto
    show thesis by (rule that[OF _ result]) simp
  qed
  from master_task_result_persists[OF k] notify
  have "master_task_trace input (admission + compute + delivery) = Task_Delivered r"
    by (rule master_task_delivered_by_bound)
  then show ?thesis by blast
qed

theorem master_queue_submission_to_listener:
  fixes r higher peers load delay drain registration_limit :: nat
    and time :: "nat \<Rightarrow> nat"
    and count_input :: "nat \<Rightarrow> master_queue_count_event option"
  defines "r \<equiv> Suc (higher + peers + load)"
    and "admission \<equiv> registration_limit + r * delay + drain"
    and "s \<equiv> master_queue_count_trace count_input (time 0)"
  assumes registration_time: "time 0 \<le> registration_limit"
    and registered: "{..target_index} \<subseteq> registered_entries s"
    and load: "(\<Sum>i<r. incoming i) \<le> load"
    and rounds: "\<And>i. i < r \<Longrightarrow> time (Suc i) \<le> time i + delay"
    and current_drain: "target_index < removed_entries s + reserved_entries s \<Longrightarrow>
      \<exists>poll<time 0 + drain. input poll \<in> {Some Acquire_Task, Some Reject_Queued_Task}"
    and next_drain: "target_index - (removed_entries s + reserved_entries s) < available_entries s \<Longrightarrow>
      available_entries s > 0 \<Longrightarrow>
      master_queue_dispatches incoming r higher peers = Processor_Selected \<Longrightarrow>
      \<exists>poll<time r + drain. input poll \<in> {Some Acquire_Task, Some Reject_Queued_Task}"
    and live: "\<forall>i<admission + compute. input i \<noteq> Some Drop_On_Shutdown"
    and transaction: "master_task_trace input admission = Task_Admitted \<Longrightarrow>
      \<exists>r k. admission \<le> k \<and> k < admission + compute \<and>
        master_transaction_result r \<and> input k = Some (Finish_Transaction r)"
    and notify: "\<And>r. master_task_trace input (admission + compute) = Task_Resolved r \<Longrightarrow>
      \<exists>j\<ge>admission + compute. j < admission + compute + delivery \<and> input j = Some Notify_Task_Listener"
  shows "\<exists>result. master_task_trace input (admission + compute + delivery) = Task_Delivered result"
proof -
  have coverage: "target_index < removed_entries s + reserved_entries s \<or>
    (available_entries s > 0 \<and> target_index - (removed_entries s + reserved_entries s) < available_entries s)"
  proof (cases "removed_entries s \<le> target_index")
    case True
    from registered True show ?thesis unfolding s_def
      by (rule master_queue_next_drains_cover_registered_prefix)
  next
    case False
    then show ?thesis by arith
  qed
  from coverage
  obtain poll where poll: "poll < admission" "input poll \<in> {Some Acquire_Task, Some Reject_Queued_Task}"
  proof (elim disjE)
    assume "target_index < removed_entries s + reserved_entries s"
    from current_drain[OF this] obtain p where p: "p < time 0 + drain"
      "input p \<in> {Some Acquire_Task, Some Reject_Queued_Task}" by blast
    from p(1) registration_time have "p < admission" unfolding admission_def by arith
    from that[OF this p(2)] show thesis .
  next
    assume available: "available_entries s > 0 \<and> target_index - (removed_entries s + reserved_entries s) < available_entries s"
    from load have selected: "master_queue_dispatches incoming r higher peers = Processor_Selected"
      unfolding r_def by (rule master_queue_processor_selected_by_load_bound)
    have timeliness: "time r \<le> time 0 + r * delay"
      by (rule master_queue_bounded_round_time) (rule rounds)
    from next_drain[OF available[THEN conjunct2] available[THEN conjunct1] selected]
    obtain p where p: "p < time r + drain" "input p \<in> {Some Acquire_Task, Some Reject_Queued_Task}" by blast
    from p(1) timeliness registration_time have "p < admission" unfolding admission_def by arith
    from that[OF this p(2)] show thesis .
  qed
  show ?thesis by (rule master_submitted_task_terminal_service[where input=input, OF poll live transaction notify])
qed

lemma master_queue_timeout_does_not_need_dispatch:
  assumes queued: "master_task_trace input i = Task_Queued"
    and timer: "input i = Some Service_Task_Timeout"
    and notify: "\<exists>j\<ge>Suc i. j < Suc i + delay \<and> input j = Some Notify_Task_Listener"
  shows "master_task_trace input (Suc i + delay) = Task_Delivered (Task_Rejected Task_Wait_Timeout)"
proof -
  have "master_task_trace input (Suc i) = Task_Resolved (Task_Rejected Task_Wait_Timeout)"
    using queued timer by simp
  then show ?thesis by (intro master_task_delivered_by_bound) (use notify in auto)
qed

lemma master_task_step_down_before_execution:
  assumes "master_task_trace input i = Task_Admitted"
    "input i = Some (Finish_Transaction (Task_Rejected No_Longer_Master))"
  shows "master_task_trace input (Suc i) = Task_Resolved (Task_Rejected No_Longer_Master)"
  using master_task_finish_transaction assms by simp

lemma master_task_shutdown_can_omit_result:
  "master_task_trace (\<lambda>i. if i = 0 then Some Acquire_Task
      else if i = 1 then Some Drop_On_Shutdown else Some Notify_Task_Listener) (2 + n) = Task_Dropped"
  by (induction n) (simp_all add: numeral_eq_Suc)

section \<open>Retry is a separate caller attempt\<close>

text \<open>
  TransportMasterNodeAction tests MasterService.isPublishFailureException
  for NotMasterException and FailedToCommitClusterStateException. The
  waiting task timeout is a ProcessClusterEventTimeoutException.
  Task_Execution_Failed represents other executor failures after
  classifying any NotMasterException or FailedToCommitClusterStateException
  by its exception type.
  For a retryable failure the caller waits for an observed state with
  a master and re-enters doStart. Its remaining request timeout,
  cancellation and service closure can end the wait. Retry requires
  a serviced qualifying observation and resubmission by the caller.
  Numbers here distinguish separate submissions for the same caller;
  the original submission keeps its delivered rejection. Executing a
  retry successfully requires the queue and service hypotheses for
  the new attempt.
\<close>

fun master_task_retryable where
  "master_task_retryable (Task_Rejected Before_Batch_Closed) = True"
| "master_task_retryable (Task_Rejected No_Longer_Master) = True"
| "master_task_retryable (Task_Rejected Publication_Failed_To_Commit) = True"
| "master_task_retryable result = False"

definition master_caller_retry where
  "master_caller_retry attempt result permitted observes_master =
    (if master_task_retryable result \<and> permitted \<and> observes_master then Some (Suc attempt) else None)"

theorem master_task_retry_has_distinct_attempt:
  assumes delivered: "master_task_trace input i = Task_Delivered result"
    and order: "i \<le> j"
    and retry: "master_caller_retry attempt result permitted observes_master = Some next"
  shows "next = Suc attempt" "next \<noteq> attempt" "master_task_retryable result"
    "master_task_trace input j = Task_Delivered result"
  using retry master_task_delivery_persists[OF order delivered]
  by (auto simp: master_caller_retry_def split: if_splits)

end
