theory Task_Ack_Liveness
  imports Task_Acknowledgements
begin

section \<open>Service of acknowledgement callbacks\<close>

datatype ack_callback =
    Target_Callback node "(nat \<times> rank) option"
  | Commit_Bookkeeping nat
  | Dispatch_Deadline
  | Deliver_Result

record timed_task_acks =
  countdown :: task_acks
  due_at :: "nat option"
  delivered_result :: "task_ack_result option"

definition timed_acks_initial where
  "timed_acks_initial R =
    \<lparr>countdown = task_acks_initial R, due_at = None, delivered_result = None\<rparr>"

text \<open>
  A tick records service at the countdown or listener boundary. The optional
  allowance is the task acknowledgement timeout. None represents the disabled
  timeout. Commit_Bookkeeping carries the elapsed publication time supplied to
  MasterService.TaskAckListener.onCommit. A positive remaining allowance arms
  a timer relative to service of that callback if target slots remain. Zero remaining allowance
  attempts timeout directly, without first counting the commit slot. The
  due time is the earliest time a timer can win; service can be later.
  An armed time retained after a terminal countdown is ghost information.

  Publication may invoke onCommit in stateless coordination while the
  beforeCommit fence future is pending. An acknowledgement from a node still
  requires evidence of application for the matching request. At the production
  boundary a successful target callback is serviced after that evidence is
  established. PublicationTarget.ackOnce supplies at most one callback per
  target. The premise that a callback is serviced includes service of the
  transport, applier, or failure path that produces it.

  A publication timeout can cause target failures through cancellation. The
  task acknowledgement timer starts with commit bookkeeping and races against
  these target callbacks. Delivery is a separate event once the countdown has
  a winner. Delivery means invoking the task listener, whose own return is
  outside the model.
\<close>

fun waiting_ack_callback where
  "waiting_ack_callback q E limit tick (Target_Callback n result) s =
    (let a = countdown s in
     if n \<notin> pending_acks a then s
     else case result of None \<Rightarrow>
       s\<lparr>countdown := finish_acks (a\<lparr>pending_acks := pending_acks a - {n},
         received_failures := insert n (received_failures a)\<rparr>)\<rparr>
     | Some (e,k) \<Rightarrow> if (e,q,k) \<in> E n then
       s\<lparr>countdown := finish_acks (a\<lparr>pending_acks := pending_acks a - {n},
         received_successes := (received_successes a)(n := Some (e,k))\<rparr>)\<rparr> else s)"
| "waiting_ack_callback q E limit tick (Commit_Bookkeeping elapsed) s =
    (let a = countdown s in if commit_counted a then s
      else case limit of None \<Rightarrow>
        s\<lparr>countdown := finish_acks (a\<lparr>commit_counted := True, timer_enabled := False\<rparr>)\<rparr>
      | Some timeout \<Rightarrow> if timeout \<le> elapsed
        then s\<lparr>countdown := a\<lparr>task_ack_result := Task_Ack_Timeout\<rparr>\<rparr>
        else s\<lparr>countdown := finish_acks (a\<lparr>commit_counted := True, timer_enabled := True\<rparr>),
          due_at := (if pending_acks a = {} then None else Some (tick + (timeout - elapsed)))\<rparr>)"
| "waiting_ack_callback q E limit tick Dispatch_Deadline s =
    (if timer_enabled (countdown s) \<and> (\<exists>d. due_at s = Some d \<and> d \<le> tick)
     then s\<lparr>countdown := (countdown s)\<lparr>task_ack_result := Task_Ack_Timeout\<rparr>\<rparr> else s)"
| "waiting_ack_callback q E limit tick Deliver_Result s = s"

definition service_ack_callback where
  "service_ack_callback q E limit tick ev s =
    (if task_ack_result (countdown s) = Waiting_For_Acks then waiting_ack_callback q E limit tick ev s
     else if ev = Deliver_Result \<and> delivered_result s = None
          then s\<lparr>delivered_result := Some (task_ack_result (countdown s))\<rparr> else s)"

fun timed_ack_run where
  "timed_ack_run q E limit R input 0 = timed_acks_initial R"
| "timed_ack_run q E limit R input (Suc i) =
    (case input i of None \<Rightarrow> timed_ack_run q E limit R input i
     | Some ev \<Rightarrow> service_ack_callback q E limit i ev (timed_ack_run q E limit R input i))"

lemma service_ack_projects:
  "countdown (service_ack_callback q E limit i ev s) = countdown s \<or>
    task_ack_step q E (countdown s) (countdown (service_ack_callback q E limit i ev s))"
  by (cases ev)
    (auto simp: service_ack_callback_def Let_def split: option.splits prod.splits if_splits
      intro: task_ack_step.node_success task_ack_step.node_failure task_ack_step.commit_timeout
        task_ack_step.scheduled_timeout task_ack_step.on_commit[where budget=No_Deadline, simplified]
        task_ack_step.on_commit[where budget=Deadline_Remains, simplified])

lemma timed_ack_run_projects:
  "rtranclp (task_ack_step q E) (task_acks_initial R) (countdown (timed_ack_run q E limit R input i))"
proof (induction i)
  case 0
  show ?case by (simp add: timed_acks_initial_def)
next
  case (Suc i)
  show ?case
  proof (cases "input i")
    case None
    with Suc.IH show ?thesis by simp
  next
    case (Some ev)
    have path: "countdown (timed_ack_run q E limit R input (Suc i)) = countdown (timed_ack_run q E limit R input i) \<or>
      task_ack_step q E (countdown (timed_ack_run q E limit R input i))
        (countdown (timed_ack_run q E limit R input (Suc i)))"
      using service_ack_projects[where ev=ev and s="timed_ack_run q E limit R input i" and q=q and E=E and limit=limit and i=i] Some by simp
    from path show ?thesis
    proof (elim disjE)
      assume "countdown (timed_ack_run q E limit R input (Suc i)) = countdown (timed_ack_run q E limit R input i)"
      then show ?thesis using Suc.IH by (simp only:)
    next
      assume advance: "task_ack_step q E (countdown (timed_ack_run q E limit R input i))
        (countdown (timed_ack_run q E limit R input (Suc i)))"
      show ?thesis by (rule rtranclp.rtrancl_into_rtrancl[OF Suc.IH advance])
    qed
  qed
qed

lemma service_ack_result_persists:
  "task_ack_result (countdown s) \<noteq> Waiting_For_Acks \<Longrightarrow>
   task_ack_result (countdown (service_ack_callback q E limit i ev s)) = task_ack_result (countdown s)"
  by (simp add: service_ack_callback_def)

lemma service_ack_delivery_persists:
  "delivered_result s = Some r \<Longrightarrow>
    delivered_result (service_ack_callback q E limit i ev s) = Some r"
  by (cases ev)
    (auto simp: service_ack_callback_def Let_def split: option.splits prod.splits if_splits)

lemma service_ack_delivery_correct:
  assumes "delivered_result s = None \<or>
    (delivered_result s = Some (task_ack_result (countdown s)) \<and> task_ack_result (countdown s) \<noteq> Waiting_For_Acks)"
  shows "let u = service_ack_callback q E limit i ev s in delivered_result u = None \<or>
    (delivered_result u = Some (task_ack_result (countdown u)) \<and> task_ack_result (countdown u) \<noteq> Waiting_For_Acks)"
  using assms by (cases ev)
    (auto simp: service_ack_callback_def Let_def split: option.splits prod.splits if_splits)

lemma timed_ack_delivery_correct:
  "let u = timed_ack_run q E limit R input i in delivered_result u = None \<or>
    (delivered_result u = Some (task_ack_result (countdown u)) \<and> task_ack_result (countdown u) \<noteq> Waiting_For_Acks)"
proof (induction i)
  case 0
  show ?case by (simp add: timed_acks_initial_def)
next
  case (Suc i)
  show ?case
  proof (cases "input i")
    case None
    with Suc.IH show ?thesis by simp
  next
    case (Some ev)
    from service_ack_delivery_correct[OF Suc.IH[unfolded Let_def], where q=q and E=E and limit=limit and i=i and ev=ev]
    show ?thesis by (simp add: Some)
  qed
qed

lemma timed_ack_trace_preserves:
  assumes order: "i \<le> j" and initial: "P (timed_ack_run q E limit R input i)"
    and preserve: "\<And>tick ev s. P s \<Longrightarrow> P (service_ack_callback q E limit tick ev s)"
  shows "P (timed_ack_run q E limit R input j)"
  using order
proof (induction rule: dec_induct)
  case base
  show ?case by (rule initial)
next
  case (step k)
  show ?case
  proof (cases "input k")
    case None
    with step.IH show ?thesis by simp
  next
    case (Some ev)
    from preserve[OF step.IH, of k ev] Some show ?thesis by simp
  qed
qed

lemma timed_ack_result_persists:
  assumes order: "i \<le> j" and won: "task_ack_result (countdown (timed_ack_run q E limit R input i)) \<noteq> Waiting_For_Acks"
  shows "task_ack_result (countdown (timed_ack_run q E limit R input j)) =
    task_ack_result (countdown (timed_ack_run q E limit R input i))"
  by (rule timed_ack_trace_preserves[OF order refl]) (use won in \<open>simp add: service_ack_result_persists\<close>)

lemma timed_ack_delivery_persists:
  "i \<le> j \<Longrightarrow> delivered_result (timed_ack_run q E limit R input i) = Some r \<Longrightarrow>
   delivered_result (timed_ack_run q E limit R input j) = Some r"
  by (erule (1) timed_ack_trace_preserves) (rule service_ack_delivery_persists)

theorem task_terminal_result_is_delivered:
  assumes won: "task_ack_result (countdown (timed_ack_run q E limit R input i)) = r" "r \<noteq> Waiting_For_Acks"
    and service: "i \<le> j" "input j = Some Deliver_Result"
  shows "delivered_result (timed_ack_run q E limit R input (Suc j)) = Some r"
proof -
  let ?s = "timed_ack_run q E limit R input j"
  have status: "task_ack_result (countdown ?s) = r"
    using timed_ack_result_persists[OF service(1), of q E limit R input] won by simp
  from timed_ack_delivery_correct[of q E limit R input j] have existing:
    "delivered_result ?s = None \<or> delivered_result ?s = Some r" using won(2) by (simp add: status Let_def)
  from status existing won(2) service(2) show ?thesis by (auto simp: service_ack_callback_def)
qed

corollary task_terminal_result_delivery_by_bound:
  assumes won: "task_ack_result (countdown (timed_ack_run q E limit R input i)) = r" "r \<noteq> Waiting_For_Acks"
    and service: "delivered_result (timed_ack_run q E limit R input i) = None \<Longrightarrow>
      \<exists>j\<ge>i. j < i + B \<and> input j = Some Deliver_Result"
  shows "delivered_result (timed_ack_run q E limit R input (i + B)) = Some r"
proof (cases "delivered_result (timed_ack_run q E limit R input i)")
  case None
  with service obtain j where event: "i \<le> j" "j < i + B" "input j = Some Deliver_Result" by blast
  show ?thesis
    by (rule timed_ack_delivery_persists[OF Suc_leI[OF event(2)] task_terminal_result_is_delivered[OF won event(1,3)]])
next
  case (Some observed)
  from timed_ack_delivery_correct[of q E limit R input i] Some won
  have "delivered_result (timed_ack_run q E limit R input i) = Some r" by (simp add: Let_def)
  then show ?thesis by (rule timed_ack_delivery_persists[rotated]) simp
qed

lemma timed_ack_delivery_once:
  assumes "i < j"
    "delivered_result (timed_ack_run q E limit R input (Suc i)) = Some r"
  shows "delivered_result (timed_ack_run q E limit R input j) \<noteq> None"
  using timed_ack_delivery_persists[OF Suc_leI[OF assms(1)] assms(2)] by simp

lemma service_ack_pending_decreases:
  "pending_acks (countdown (service_ack_callback q E limit i ev s)) \<subseteq> pending_acks (countdown s)"
  by (cases ev)
    (auto simp: service_ack_callback_def Let_def split: option.splits prod.splits if_splits)

lemma service_ack_commit_persists:
  "commit_counted (countdown s) \<Longrightarrow> commit_counted (countdown (service_ack_callback q E limit i ev s))"
  by (cases ev)
    (auto simp: service_ack_callback_def Let_def split: option.splits prod.splits if_splits)

lemma service_ack_failures_grow:
  "received_failures (countdown s) \<subseteq> received_failures (countdown (service_ack_callback q E limit i ev s))"
  by (cases ev)
    (auto simp: service_ack_callback_def Let_def split: option.splits prod.splits if_splits)

lemma timed_ack_pending_decreases:
  "i \<le> j \<Longrightarrow> pending_acks (countdown (timed_ack_run q E limit R input j)) \<subseteq>
    pending_acks (countdown (timed_ack_run q E limit R input i))"
  by (erule timed_ack_trace_preserves[OF _ subset_refl]) (rule subset_trans[OF service_ack_pending_decreases])

lemma timed_ack_pending_subset:
  "pending_acks (countdown (timed_ack_run q E limit R input i)) \<subseteq> R"
  using timed_ack_pending_decreases[where i=0 and j=i and q=q and E=E and limit=limit and R=R and input=input]
  by (simp add: timed_acks_initial_def task_acks_initial_def)

lemma timed_ack_commit_persists:
  "i \<le> j \<Longrightarrow> commit_counted (countdown (timed_ack_run q E limit R input i)) \<Longrightarrow>
    commit_counted (countdown (timed_ack_run q E limit R input j))"
  by (erule (1) timed_ack_trace_preserves) (rule service_ack_commit_persists)

lemma timed_ack_failures_grow:
  "i \<le> j \<Longrightarrow> received_failures (countdown (timed_ack_run q E limit R input i)) \<subseteq>
    received_failures (countdown (timed_ack_run q E limit R input j))"
  by (erule timed_ack_trace_preserves[OF _ subset_refl]) (rule subset_trans[OF _ service_ack_failures_grow])

section \<open>Counting before the deadline\<close>

definition ack_deadline_after where
  "ack_deadline_after limit elapsed i H \<longleftrightarrow>
    (case limit of None \<Rightarrow> True | Some l \<Rightarrow> elapsed < l \<and> H \<le> i + (l - elapsed))"

definition quiet_ack_deadline where
  "quiet_ack_deadline limit input H \<longleftrightarrow>
    (\<forall>i<H. \<forall>elapsed. input i = Some (Commit_Bookkeeping elapsed) \<longrightarrow>
      ack_deadline_after limit elapsed i H)"

lemma quiet_ack_run_no_timeout:
  assumes quiet: "quiet_ack_deadline limit input H" and time: "i \<le> H"
  shows "let s = timed_ack_run q E limit R input i in task_ack_result (countdown s) \<noteq> Task_Ack_Timeout
    \<and> (\<forall>d. due_at s = Some d \<longrightarrow> H \<le> d)"
  using time
proof (induction i)
  case 0
  show ?case by (simp add: timed_acks_initial_def task_acks_initial_def)
next
  case (Suc i)
  from Suc.IH Suc.prems have less: "i < H" and existing:
    "task_ack_result (countdown (timed_ack_run q E limit R input i)) \<noteq> Task_Ack_Timeout"
    "\<And>d. due_at (timed_ack_run q E limit R input i) = Some d \<Longrightarrow> H \<le> d"
    by (auto simp: Let_def)
  show ?case
  proof (cases "input i")
    case None
    then show ?thesis using existing by (simp add: Let_def)
  next
    case (Some ev)
    then have book: "ack_deadline_after limit elapsed i H" if "ev = Commit_Bookkeeping elapsed" for elapsed
      using quiet less that unfolding quiet_ack_deadline_def by blast
    from Some existing less show ?thesis
      by (cases ev)
        (auto simp: service_ack_callback_def ack_deadline_after_def Let_def
          split: option.splits prod.splits if_splits dest: book)
  qed
qed

lemma observed_target_is_counted:
  assumes quiet: "quiet_ack_deadline limit input H" and earlier: "i < H"
    and arrival: "input i = Some (Target_Callback n result)"
    and valid: "\<And>e k. result = Some (e,k) \<Longrightarrow> (e,q,k) \<in> E n"
  shows "n \<notin> pending_acks (countdown (timed_ack_run q E limit R input H))"
proof -
  let ?a = "countdown (timed_ack_run q E limit R input i)"
  have nxt: "n \<notin> pending_acks (countdown (timed_ack_run q E limit R input (Suc i)))"
  proof (cases "task_ack_result ?a = Waiting_For_Acks")
    case True
    from arrival valid True show ?thesis by (cases result) (auto simp: service_ack_callback_def Let_def split: prod.splits)
  next
    case False
    from quiet_ack_run_no_timeout[OF quiet less_imp_le[OF earlier], of q E R] have
      "task_ack_result ?a \<noteq> Task_Ack_Timeout" by (simp add: Let_def)
    with False task_ack_invariants[OF timed_ack_run_projects[of q E R limit input i]] arrival
    show ?thesis by (cases "task_ack_result ?a") (auto simp: service_ack_callback_def task_acks_ok_def)
  qed
  from timed_ack_pending_decreases[OF Suc_leI[OF earlier], where q=q and E=E and limit=limit and R=R and input=input] nxt show ?thesis by blast
qed

lemma observed_commit_is_counted:
  assumes quiet: "quiet_ack_deadline limit input H" and earlier: "i < H"
    and arrival: "input i = Some (Commit_Bookkeeping elapsed)"
  shows "commit_counted (countdown (timed_ack_run q E limit R input H))"
proof -
  let ?a = "countdown (timed_ack_run q E limit R input i)"
  have nxt: "commit_counted (countdown (timed_ack_run q E limit R input (Suc i)))"
  proof (cases "task_ack_result ?a = Waiting_For_Acks")
    case True
    from quiet earlier arrival have "ack_deadline_after limit elapsed i H" unfolding quiet_ack_deadline_def by blast
    with arrival True show ?thesis by (cases limit) (auto simp: service_ack_callback_def ack_deadline_after_def Let_def)
  next
    case False
    from quiet_ack_run_no_timeout[OF quiet less_imp_le[OF earlier], of q E R] have
      "task_ack_result ?a \<noteq> Task_Ack_Timeout" by (simp add: Let_def)
    with False task_ack_invariants[OF timed_ack_run_projects[of q E R limit input i]] arrival show ?thesis
      by (cases "task_ack_result ?a") (auto simp: service_ack_callback_def task_acks_ok_def)
  qed
  from timed_ack_commit_persists[OF Suc_leI[OF earlier] nxt] show ?thesis .
qed

theorem task_countdown_completed_before_deadline:
  assumes quiet: "quiet_ack_deadline limit input H"
    and book: "\<exists>i<H. \<exists>elapsed. input i = Some (Commit_Bookkeeping elapsed)"
    and targets: "\<And>n. n \<in> R \<Longrightarrow> \<exists>i<H. \<exists>result. input i = Some (Target_Callback n result)
       \<and> (\<forall>e k. result = Some (e,k) \<longrightarrow> (e,q,k) \<in> E n)"
  shows "task_ack_result (countdown (timed_ack_run q E limit R input H)) =
    (if received_failures (countdown (timed_ack_run q E limit R input H)) = {} then Task_Ack_Success else Task_Ack_Failure)"
proof -
  let ?a = "countdown (timed_ack_run q E limit R input H)"
  from book obtain i elapsed where arrival: "i < H" "input i = Some (Commit_Bookkeeping elapsed)" by blast
  have committed: "commit_counted ?a"
    by (rule observed_commit_is_counted[OF quiet arrival])
  have none: "pending_acks ?a = {}"
  proof (rule ccontr)
    assume "pending_acks ?a \<noteq> {}"
    with timed_ack_pending_subset[of q E limit R input H]
    obtain n where n: "n \<in> R" "n \<in> pending_acks ?a" by blast
    from targets[OF n(1)] obtain i result where event: "i < H" "input i = Some (Target_Callback n result)"
      and valid: "\<And>e k. result = Some (e,k) \<Longrightarrow> (e,q,k) \<in> E n" by blast
    have "n \<notin> pending_acks ?a"
      by (rule observed_target_is_counted[OF quiet event]) (rule valid)
    with n(2) show False by contradiction
  qed
  from quiet_ack_run_no_timeout[OF quiet le_refl, of q E R] have "task_ack_result ?a \<noteq> Task_Ack_Timeout"
    by (simp add: Let_def)
  with committed none task_ack_invariants[OF timed_ack_run_projects[of q E R limit input H]]
  show ?thesis by (cases "task_ack_result ?a") (auto simp: task_acks_ok_def)
qed

lemma only_successful_inputs_preserve_no_failures:
  assumes "\<And>i n. i < H \<Longrightarrow> n \<in> R \<Longrightarrow> input i \<noteq> Some (Target_Callback n None)"
  shows "received_failures (countdown (timed_ack_run q E limit R input H)) = {}"
  using assms
proof (induction H)
  case 0
  show ?case by (simp add: timed_acks_initial_def task_acks_initial_def)
next
  case (Suc i)
  from Suc.IH Suc.prems have prev:
    "received_failures (countdown (timed_ack_run q E limit R input i)) = {}" by simp
  show ?case
  proof (cases "input i")
    case None
    with prev show ?thesis by simp
  next
    case (Some ev)
    have not_failed: "ev \<noteq> Target_Callback n None" if "n \<in> R" for n
      using Suc.prems[OF lessI that] Some by simp
    show ?thesis
    proof (cases ev)
      case (Target_Callback n result)
      moreover have "n \<in> pending_acks (countdown (timed_ack_run q E limit R input i)) \<Longrightarrow> result \<noteq> None"
      proof -
        assume pending: "n \<in> pending_acks (countdown (timed_ack_run q E limit R input i))"
        have "n \<in> R" by (rule subsetD[OF timed_ack_pending_subset pending])
        from not_failed[OF this] Target_Callback show "result \<noteq> None" by simp
      qed
      ultimately show ?thesis using Some prev
        by (auto simp: service_ack_callback_def Let_def split: option.splits prod.splits if_splits)
    qed (use Some prev in \<open>auto simp: service_ack_callback_def Let_def split: option.splits if_splits\<close>)
  qed
qed

theorem timely_successful_acks_delivered:
  assumes quiet: "quiet_ack_deadline limit input H"
    and book: "\<exists>i<H. \<exists>elapsed. input i = Some (Commit_Bookkeeping elapsed)"
    and targets: "\<And>n. n \<in> R \<Longrightarrow> \<exists>i<H. \<exists>e k. input i = Some (Target_Callback n (Some (e,k))) \<and> (e,q,k) \<in> E n"
    and good: "\<And>i n. i < H \<Longrightarrow> n \<in> R \<Longrightarrow> input i \<noteq> Some (Target_Callback n None)"
    and delivery: "H \<le> j" "input j = Some Deliver_Result"
  shows "delivered_result (timed_ack_run q E limit R input (Suc j)) = Some Task_Ack_Success"
proof -
  have completed: "task_ack_result (countdown (timed_ack_run q E limit R input H)) =
      (if received_failures (countdown (timed_ack_run q E limit R input H)) = {} then Task_Ack_Success else Task_Ack_Failure)"
  proof (rule task_countdown_completed_before_deadline[OF quiet book])
    fix n
    assume "n \<in> R"
    from targets[OF this] obtain i e k where event: "i < H"
      "input i = Some (Target_Callback n (Some (e,k)))" "(e,q,k) \<in> E n" by blast
    show "\<exists>i<H. \<exists>result. input i = Some (Target_Callback n result) \<and>
      (\<forall>e k. result = Some (e,k) \<longrightarrow> (e,q,k) \<in> E n)"
      by (intro exI[of _ i] conjI event(1) exI[of _ "Some (e,k)"]) (use event in auto)
  qed
  have count: "task_ack_result (countdown (timed_ack_run q E limit R input H)) = Task_Ack_Success"
    using completed only_successful_inputs_preserve_no_failures[OF good, where q=q and E=E and limit=limit and R=R] by simp
  show ?thesis by (rule task_terminal_result_is_delivered[OF count _ delivery]) simp
qed

lemma serviced_failed_ack_stays_failed:
  assumes quiet: "quiet_ack_deadline limit input H" and time: "i < H"
    and arrival: "input i = Some (Target_Callback n None)"
    and pending: "n \<in> pending_acks (countdown (timed_ack_run q E limit R input i))"
  shows "n \<in> received_failures (countdown (timed_ack_run q E limit R input H))"
proof -
  let ?a = "countdown (timed_ack_run q E limit R input i)"
  from quiet_ack_run_no_timeout[OF quiet less_imp_le[OF time], of q E R] have no_timeout:
    "task_ack_result ?a \<noteq> Task_Ack_Timeout" by (simp add: Let_def)
  have wait: "task_ack_result ?a = Waiting_For_Acks"
    using no_timeout pending task_ack_invariants[OF timed_ack_run_projects[of q E R limit input i]]
    by (cases "task_ack_result ?a") (auto simp: task_acks_ok_def)
  from arrival pending wait have "n \<in> received_failures (countdown (timed_ack_run q E limit R input (Suc i)))"
    by (simp add: service_ack_callback_def Let_def)
  with timed_ack_failures_grow[OF Suc_leI[OF time], where q=q and E=E and limit=limit and R=R and input=input] show ?thesis by blast
qed

theorem timely_failed_ack_delivered:
  assumes quiet: "quiet_ack_deadline limit input H"
    and book: "\<exists>i<H. \<exists>elapsed. input i = Some (Commit_Bookkeeping elapsed)"
    and targets: "\<And>n. n \<in> R \<Longrightarrow> \<exists>i<H. \<exists>result. input i = Some (Target_Callback n result)
      \<and> (\<forall>e k. result = Some (e,k) \<longrightarrow> (e,q,k) \<in> E n)"
    and bad: "i < H" "input i = Some (Target_Callback n None)"
      "n \<in> pending_acks (countdown (timed_ack_run q E limit R input i))"
    and delivery: "H \<le> j" "input j = Some Deliver_Result"
  shows "delivered_result (timed_ack_run q E limit R input (Suc j)) = Some Task_Ack_Failure"
proof -
  have count: "task_ack_result (countdown (timed_ack_run q E limit R input H)) = Task_Ack_Failure"
    using task_countdown_completed_before_deadline[OF quiet book targets]
      serviced_failed_ack_stays_failed[OF quiet bad] by auto
  show ?thesis by (rule task_terminal_result_is_delivered[OF count _ delivery]) simp
qed

section \<open>Expiry and missing callbacks\<close>

lemma missing_ack_remains_pending:
  assumes "n \<in> R" "\<And>i result. i < H \<Longrightarrow> input i \<noteq> Some (Target_Callback n result)"
  shows "n \<in> pending_acks (countdown (timed_ack_run q E limit R input H))"
  using assms
proof (induction H)
  case 0
  show ?case using 0 by (simp add: timed_acks_initial_def task_acks_initial_def)
next
  case (Suc i)
  from Suc.IH Suc.prems have prev:
    "n \<in> pending_acks (countdown (timed_ack_run q E limit R input i))" by simp
  show ?case
  proof (cases "input i")
    case None
    with prev show ?thesis by simp
  next
    case (Some ev)
    have unseen: "ev \<noteq> Target_Callback n result" for result
      using Suc.prems(2)[OF lessI, of result] Some by simp
    show ?thesis
    proof (cases ev)
      case (Target_Callback target result)
      from unseen[of result] Target_Callback have "target \<noteq> n" by auto
      with Target_Callback Some prev show ?thesis
        by (auto simp: service_ack_callback_def Let_def split: prod.splits option.splits if_splits)
    qed (use Some prev in \<open>auto simp: service_ack_callback_def Let_def split: option.splits if_splits\<close>)
  qed
qed

lemma armed_ack_timer_persists:
  assumes "i \<le> j" "commit_counted (countdown (timed_ack_run q E limit R input i))"
    "timer_enabled (countdown (timed_ack_run q E limit R input i))"
    "due_at (timed_ack_run q E limit R input i) = Some d"
  shows "timer_enabled (countdown (timed_ack_run q E limit R input j)) \<and>
    due_at (timed_ack_run q E limit R input j) = Some d"
proof -
  have initial: "commit_counted (countdown (timed_ack_run q E limit R input i)) \<and>
    timer_enabled (countdown (timed_ack_run q E limit R input i)) \<and>
    due_at (timed_ack_run q E limit R input i) = Some d" using assms by simp
  have remaining: "commit_counted (countdown (timed_ack_run q E limit R input j)) \<and>
    timer_enabled (countdown (timed_ack_run q E limit R input j)) \<and>
    due_at (timed_ack_run q E limit R input j) = Some d"
  proof (rule timed_ack_trace_preserves[where P="\<lambda>s. commit_counted (countdown s) \<and>
      timer_enabled (countdown s) \<and> due_at s = Some d", OF assms(1) initial])
    fix tick ev s
    let ?u = "service_ack_callback q E limit tick ev s"
    assume "commit_counted (countdown s) \<and> timer_enabled (countdown s) \<and> due_at s = Some d"
    then show "commit_counted (countdown ?u) \<and> timer_enabled (countdown ?u) \<and> due_at ?u = Some d"
      by (cases ev) (auto simp: service_ack_callback_def Let_def finish_acks_def split: option.splits prod.splits if_splits)
  qed
  then show ?thesis by simp
qed

lemma timely_bookkeeping_arms_waiting:
  assumes arrival: "input i = Some (Commit_Bookkeeping elapsed)" and remaining: "elapsed < l"
    and waiting: "task_ack_result (countdown (timed_ack_run q E (Some l) R input i)) = Waiting_For_Acks"
    and first: "\<not> commit_counted (countdown (timed_ack_run q E (Some l) R input i))"
    and outstanding: "pending_acks (countdown (timed_ack_run q E (Some l) R input i)) \<noteq> {}"
  shows "commit_counted (countdown (timed_ack_run q E (Some l) R input (Suc i)))"
    "timer_enabled (countdown (timed_ack_run q E (Some l) R input (Suc i)))"
    "due_at (timed_ack_run q E (Some l) R input (Suc i)) = Some (i + (l - elapsed))"
  using assms by (simp_all add: service_ack_callback_def Let_def finish_acks_def)

theorem expired_at_bookkeeping_delivers_timeout:
  assumes arrival: "input i = Some (Commit_Bookkeeping elapsed)" and expired: "l \<le> elapsed"
    and waiting: "task_ack_result (countdown (timed_ack_run q E (Some l) R input i)) = Waiting_For_Acks"
    and first: "\<not> commit_counted (countdown (timed_ack_run q E (Some l) R input i))"
    and delivery: "Suc i \<le> j" "input j = Some Deliver_Result"
  shows "delivered_result (timed_ack_run q E (Some l) R input (Suc j)) = Some Task_Ack_Timeout"
proof -
  from arrival expired waiting first have at_commit:
    "task_ack_result (countdown (timed_ack_run q E (Some l) R input (Suc i))) = Task_Ack_Timeout"
    by (simp add: service_ack_callback_def Let_def)
  show ?thesis by (rule task_terminal_result_is_delivered[OF at_commit _ delivery]) simp
qed

theorem missing_ack_at_serviced_deadline_delivers_timeout:
  assumes arrival: "input i = Some (Commit_Bookkeeping elapsed)" and remaining: "elapsed < l"
    and waiting: "task_ack_result (countdown (timed_ack_run q E (Some l) R input i)) = Waiting_For_Acks"
    and first: "\<not> commit_counted (countdown (timed_ack_run q E (Some l) R input i))"
    and expires: "Suc i \<le> j" "i + (l - elapsed) \<le> j" "input j = Some Dispatch_Deadline"
    and missing: "n \<in> R" "\<And>t result. t < j \<Longrightarrow> input t \<noteq> Some (Target_Callback n result)"
    and delivery: "Suc j \<le> k" "input k = Some Deliver_Result"
  shows "delivered_result (timed_ack_run q E (Some l) R input (Suc k)) = Some Task_Ack_Timeout"
proof -
  let ?s = "timed_ack_run q E (Some l) R input j"
  have pending_at_commit: "n \<in> pending_acks (countdown (timed_ack_run q E (Some l) R input i))"
    by (rule missing_ack_remains_pending[OF missing(1)]) (use expires(1) missing(2) in auto)
  then have outstanding: "pending_acks (countdown (timed_ack_run q E (Some l) R input i)) \<noteq> {}" by auto
  from timely_bookkeeping_arms_waiting[OF arrival remaining waiting first outstanding]
  have at_j: "timer_enabled (countdown ?s) \<and> due_at ?s = Some (i + (l - elapsed))"
    by (rule armed_ack_timer_persists[OF expires(1)])
  have pending: "n \<in> pending_acks (countdown ?s)" by (rule missing_ack_remains_pending[OF missing])
  have at_timeout: "task_ack_result (countdown (timed_ack_run q E (Some l) R input (Suc j))) = Task_Ack_Timeout"
  proof (cases "task_ack_result (countdown ?s)")
    case Waiting_For_Acks
    with expires(2,3) at_j show ?thesis by (simp add: service_ack_callback_def)
  next
    case Task_Ack_Timeout
    with expires(3) show ?thesis by (simp add: service_ack_callback_def)
  qed (use pending task_ack_invariants[OF timed_ack_run_projects[of q E R "Some l" input j]] in
    \<open>auto simp: task_acks_ok_def\<close>)
  show ?thesis by (rule task_terminal_result_is_delivered[OF at_timeout _ delivery]) simp
qed

theorem disabled_timeout_can_leave_a_missing_ack_pending:
  assumes missing: "n \<in> R" "\<And>i result. i < H \<Longrightarrow> input i \<noteq> Some (Target_Callback n result)"
  shows "task_ack_result (countdown (timed_ack_run q E None R input H)) = Waiting_For_Acks"
    "delivered_result (timed_ack_run q E None R input H) = None"
proof -
  let ?a = "countdown (timed_ack_run q E None R input H)"
  have quiet: "quiet_ack_deadline None input H" by (simp add: quiet_ack_deadline_def ack_deadline_after_def)
  from quiet_ack_run_no_timeout[OF quiet le_refl, of q E R] have no_timeout:
    "task_ack_result ?a \<noteq> Task_Ack_Timeout" by (simp add: Let_def)
  from missing_ack_remains_pending[OF missing, where q=q and E=E and limit=None] have pending: "n \<in> pending_acks ?a" .
  from no_timeout pending task_ack_invariants[OF timed_ack_run_projects[of q E R None input H]]
  show "task_ack_result ?a = Waiting_For_Acks" by (cases "task_ack_result ?a") (auto simp: task_acks_ok_def)
  with timed_ack_delivery_correct[of q E None R input H] show
    "delivered_result (timed_ack_run q E None R input H) = None" by (simp add: Let_def)
qed

end
