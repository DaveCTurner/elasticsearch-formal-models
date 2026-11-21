theory Publication_Callback_Identity
  imports Stateless_Slot_Liveness
begin

section \<open>One Coordinator instance and its publication objects\<close>

datatype callback_stage =
    Before_Completion "bool option"
  | Waiting_Self_Result "bool option"
  | Applier_Queued
  | Running_Application_Hook
  | Ready_To_Clear bool
  | Retired_Publication

datatype callback_input =
    Select_Completion
  | Cancel_Publication
  | Self_Result bool
  | Deliver_Self_Result
  | Applier_Result bool
  | Complete_Application_Hook

fun select_completion_stage where
  "select_completion_stage (Before_Completion result) = Some (Waiting_Self_Result result)"
| "select_completion_stage _ = None"

fun callback_advance where
  "callback_advance Select_Completion st = select_completion_stage st"
| "callback_advance Cancel_Publication st = select_completion_stage st"
| "callback_advance (Self_Result ok) (Before_Completion None) = Some (Before_Completion (Some ok))"
| "callback_advance (Self_Result ok) (Waiting_Self_Result None) = Some (Waiting_Self_Result (Some ok))"
| "callback_advance Deliver_Self_Result (Waiting_Self_Result (Some ok)) =
    Some (if ok then Applier_Queued else Ready_To_Clear False)"
| "callback_advance (Applier_Result ok) Applier_Queued =
    Some (if ok then Running_Application_Hook else Ready_To_Clear False)"
| "callback_advance Complete_Application_Hook Running_Application_Hook = Some (Ready_To_Clear True)"
| "callback_advance _ _ = None"

record publication_callbacks =
  callback_slot :: "nat option"
  callback_next :: nat
  callback_objects :: "nat \<Rightarrow> callback_stage option"
  callback_leading :: bool

definition callbacks_initial where
  "callbacks_initial = \<lparr>callback_slot = None, callback_next = 0,
    callback_objects = (\<lambda>_. None), callback_leading = False\<rparr>"

definition run_callback_input where
  "run_callback_input s i input =
    (case callback_objects s i of None \<Rightarrow> s
     | Some st \<Rightarrow> (case callback_advance input st of None \<Rightarrow> s
                   | Some st' \<Rightarrow> s\<lparr>callback_objects := (callback_objects s)(i := Some st')\<rparr>))"

definition clear_callback_slot where
  "clear_callback_slot s i = s\<lparr>callback_slot := None,
    callback_objects := (callback_objects s)(i := Some Retired_Publication)\<rparr>"

inductive callback_step where
  mode:
    "callback_step s (s\<lparr>callback_leading := new_mode\<rparr>)"
| install:
    "callback_slot s = None \<Longrightarrow> callback_leading s \<Longrightarrow> i = callback_next s \<Longrightarrow>
     callback_step s (s\<lparr>callback_slot := Some i, callback_next := Suc i,
       callback_objects := (callback_objects s)(i := Some (Before_Completion None))\<rparr>)"
| input:
    "callback_step s (run_callback_input s i input)"
| clear:
    "callback_objects s i = Some (Ready_To_Clear ok) \<Longrightarrow>
     callback_step s (clear_callback_slot s i)"

definition callback_reachable where
  "callback_reachable s \<longleftrightarrow> rtranclp callback_step callbacks_initial s"

text \<open>
  A number identifies a fresh allocation. The object table retains a ghost
  phase even after retirement so queued work can still address the old
  object. The event input reads the object captured by its Java closure.
  The slot write is unconditional once the clearing listener reaches it.
  No rule for a callback to read or compare the slot is needed.

  The bindings are for one normally operating Coordinator and the built-in
  ClusterApplierService. Coordinator.publish holds mutex across the empty
  slot runtime test, construction, and installation. The successfully
  constructed publication's timeout cannot enter cancel under mutex before
  installation. A process restart creates a different Coordinator and its
  callbacks cannot refer to the new instance's slot. This trace starts with
  a fresh Coordinator and models operations on that instance only.

  Publication.onPossibleCompletion writes isCompleted before onCompletion.
  The Select_Completion event denotes a call that passed the target or
  cancellation test. Publication.cancel returns after completion and can
  select completion before all targets finish. Becoming a candidate or
  follower can request cancellation under mutex. A mode change itself
  leaves the slot in place. The model allows any ordering of mode changes
  around the cancellation and allows cancellation to call the completion
  routine before the result of the self request is available.
  The callback trace tracks ownership across mode changes. The failure
  path's term comparison and any resulting candidate transition belong to
  Coordinator's mode logic.

  CoordinatorPublication.onCompletion registers one listener on the
  publication's localNodeAckEvent. That SubscribableListener atomically
  chooses a result and either serves a registered listener or lets a
  racing registration see the settled result. The selected branch is
  delivered once, whether the result arrives before or after registration.
  Self failure reaches removePublicationAndPossiblyBecomeCandidate. Self
  success queues one task with one applier listener. The applier failure
  branch reaches the same removal method. The success branch runs
  onClusterStateApplied and the elapsed-time update before reacquiring the
  mutex and clearing. Separate steps allow these callbacks to stall.

  ClusterApplierService executes a serviced update task once. Its
  ClusterApplyActionListener and TimedListener catch exceptions thrown
  by the response listener so they cannot themselves propagate back into
  the apply-failure branch. The source binding additionally requires that
  trailing timing, logging, and recording in the changed-state success
  branch do not throw an exception into that branch's catch after response
  delivery. The binding also requires that no cancellation timeout from
  a failed constructor be serviced. CoordinatorPublication schedules
  its cancellation timeout before the informational timeout; a failure
  during the second scheduling call would leave a partially constructed
  object outside the successful-installation rule if its first timeout ran.
  These requirements delimit the Java correspondence of this trace;
  the model does not supply either exceptional-path guarantee.
\<close>

section \<open>The clearing listener owns the slot\<close>

lemma advance_callback_is_live:
  assumes "callback_advance input st = Some st'"
  shows "st \<noteq> Retired_Publication" "st' \<noteq> Retired_Publication"
proof -
  have select: "s \<noteq> Retired_Publication \<and> t \<noteq> Retired_Publication"
    if "select_completion_stage s = Some t" for s t
    using that by (cases s) auto
  have "st \<noteq> Retired_Publication \<and> st' \<noteq> Retired_Publication"
    using assms by (induction input st rule: callback_advance.induct) (auto dest: select split: if_splits)
  then show "st \<noteq> Retired_Publication" "st' \<noteq> Retired_Publication" by auto
qed

definition callback_slot_invariant where
  "callback_slot_invariant s \<longleftrightarrow>
    (\<forall>i st. callback_objects s i = Some st \<longrightarrow>
       i < callback_next s \<and> (callback_slot s = Some i \<longleftrightarrow> st \<noteq> Retired_Publication))"

lemma callback_slot_invariant_initial:
  "callback_slot_invariant callbacks_initial"
  by (simp add: callback_slot_invariant_def callbacks_initial_def)

lemma callback_slot_invariant_step:
  assumes "callback_step s s'" "callback_slot_invariant s"
  shows "callback_slot_invariant s'"
  using assms
  apply (cases rule: callback_step.cases)
  apply (auto simp: callback_slot_invariant_def run_callback_input_def clear_callback_slot_def
    split: option.splits if_splits dest: advance_callback_is_live)
  subgoal premises facts for i st
    using facts(1)[rule_format, OF facts(6)] by (blast intro: less_SucI)
  subgoal premises facts for i ok j st
  proof -
    have "callback_slot s = Some i" using facts(1)[rule_format, OF facts(3)] by simp
    then show "st = Retired_Publication"
      using facts(1)[rule_format, OF facts(5)] facts(4) by simp
  qed
  done

lemma reachable_callback_slot_invariant:
  "callback_reachable s \<Longrightarrow> callback_slot_invariant s"
  unfolding callback_reachable_def
  by (induction rule: rtranclp_induct) (auto intro: callback_slot_invariant_initial callback_slot_invariant_step)

theorem clearing_callback_owns_slot:
  assumes "callback_reachable s" "callback_objects s i = Some (Ready_To_Clear ok)"
  shows "callback_slot s = Some i"
    "callback_slot (clear_callback_slot s i) = None"
    "callback_objects (clear_callback_slot s i) i = Some Retired_Publication"
  using reachable_callback_slot_invariant[OF assms(1)] assms(2)
  by (auto simp: callback_slot_invariant_def clear_callback_slot_def)

lemma occupied_slot_cannot_be_replaced:
  assumes "callback_step s s'" "callback_slot s = Some i" "callback_slot s' = Some j"
  shows "j = i"
  using assms by (cases rule: callback_step.cases)
    (auto simp: run_callback_input_def clear_callback_slot_def split: option.splits)

theorem pending_application_prevents_replacement:
  assumes "callback_reachable s" "callback_objects s i = Some st"
    "st \<in> {Applier_Queued, Running_Application_Hook, Ready_To_Clear ok}"
  shows "callback_slot s = Some i"
    "run_callback_input s i Cancel_Publication = s"
    "callback_slot (s\<lparr>callback_leading := False\<rparr>) = Some i"
  using reachable_callback_slot_invariant[OF assms(1)] assms(2,3)
  by (auto simp: callback_slot_invariant_def run_callback_input_def)

lemma cancelled_publication_still_waits_for_self_result:
  assumes "callback_reachable s" "callback_objects s i = Some (Before_Completion None)"
  defines "s' \<equiv> run_callback_input s i Cancel_Publication"
  shows "callback_slot s' = Some i"
    "callback_objects s' i = Some (Waiting_Self_Result None)"
    "run_callback_input s' i Deliver_Self_Result = s'"
  using reachable_callback_slot_invariant[OF assms(1)] assms(2)
  by (auto simp: callback_slot_invariant_def run_callback_input_def s'_def)

lemma retired_callback_input_stutters:
  assumes "callback_objects s i = Some Retired_Publication"
  shows "run_callback_input s i input = s"
  using assms by (cases input) (simp_all add: run_callback_input_def)

lemma callback_retirement_persists_one_step:
  assumes "callback_step s s'" "callback_slot_invariant s"
    "callback_objects s i = Some Retired_Publication"
  shows "callback_objects s' i = Some Retired_Publication"
  using assms
  by (cases rule: callback_step.cases)
    (auto simp: callback_slot_invariant_def run_callback_input_def clear_callback_slot_def
      split: option.splits if_splits dest: advance_callback_is_live)

lemma callback_retirement_persists:
  assumes "rtranclp callback_step s s'" "callback_reachable s"
    "callback_objects s i = Some Retired_Publication"
  shows "callback_reachable s' \<and> callback_objects s' i = Some Retired_Publication"
  using assms(1)
proof induction
  case base
  show ?case using assms(2,3) by simp
next
  case (step a b)
  then have reach: "callback_reachable a" and retired: "callback_objects a i = Some Retired_Publication"
    by auto
  have "callback_reachable b"
    using reach step.hyps(2) unfolding callback_reachable_def by (rule rtranclp.rtrancl_into_rtrancl)
  moreover have "callback_objects b i = Some Retired_Publication"
    by (rule callback_retirement_persists_one_step[OF step.hyps(2) reachable_callback_slot_invariant[OF reach] retired])
  ultimately show ?case by simp
qed

theorem callback_queued_before_retirement_cannot_clear_again:
  assumes "callback_reachable s" "callback_objects s i = Some (Ready_To_Clear ok)"
    "rtranclp callback_step (clear_callback_slot s i) s'"
  shows "run_callback_input s' i input = s'"
    "callback_objects s' i \<noteq> Some (Ready_To_Clear ok')"
    "callback_slot s' \<noteq> Some i"
proof -
  have cleared: "callback_step s (clear_callback_slot s i)"
    by (rule callback_step.clear[OF assms(2)])
  have reached: "callback_reachable (clear_callback_slot s i)"
    using assms(1) cleared unfolding callback_reachable_def by (rule rtranclp.rtrancl_into_rtrancl)
  have at_clear: "callback_objects (clear_callback_slot s i) i = Some Retired_Publication"
    by (simp add: clear_callback_slot_def)
  have retired: "callback_objects s' i = Some Retired_Publication" and reach': "callback_reachable s'"
    using callback_retirement_persists[OF assms(3) reached at_clear] by auto
  show "run_callback_input s' i input = s'"
    by (rule retired_callback_input_stutters[OF retired])
  show "callback_objects s' i \<noteq> Some (Ready_To_Clear ok')" using retired by simp
  show "callback_slot s' \<noteq> Some i"
    using reachable_callback_slot_invariant[OF reach'] retired by (auto simp: callback_slot_invariant_def)
qed

section \<open>Clear at the stateless slot projection boundary\<close>

definition clear_signal where
  "clear_signal ok = (if ok then Clear_Success else Clear_Failure)"

theorem owned_clear_supplies_projected_guard:
  assumes reach: "callback_reachable c" "stateless_slot_reachable n s"
    and slot: "callback_slot c = map_option object_generation (active_slot s)"
    and clear: "callback_objects c i = Some (Ready_To_Clear ok)"
    and phase: "\<And>p. active_slot s = Some p \<Longrightarrow>
      if ok then (\<exists>k. object_phase p = Local_Apply_Hook_Done k) else object_phase p = Publication_Failed"
  shows "stateless_slot_step n s (dispatch_publication_signal n i (clear_signal ok) s)"
    "active_slot (dispatch_publication_signal n i (clear_signal ok) s) = None"
    "callback_slot (clear_callback_slot c i) =
       map_option object_generation (active_slot (dispatch_publication_signal n i (clear_signal ok) s))"
proof -
  have "callback_slot c = Some i" by (rule clearing_callback_owns_slot(1)[OF reach(1) clear])
  then obtain p where active: "active_slot s = Some p" and generation: "object_generation p = i"
    using slot by (cases "active_slot s") auto
  have epoch: "object_incarnation p = incarnation (processes (slot_exec s) n)"
    using slot_state_projects(2)[OF reach(2) active] by simp
  have effect: "publication_signal_effect n (slot_exec s) p (clear_signal ok) = Some (Release_Slot ok)"
    using phase[OF active] by (cases ok) (auto simp: clear_signal_def)
  show "stateless_slot_step n s (dispatch_publication_signal n i (clear_signal ok) s)"
    by (rule stateless_slot_step.dispatch)
  show released: "active_slot (dispatch_publication_signal n i (clear_signal ok) s) = None"
    using active generation epoch effect by (simp add: dispatch_publication_signal_def)
  show "callback_slot (clear_callback_slot c i) =
       map_option object_generation (active_slot (dispatch_publication_signal n i (clear_signal ok) s))"
    using released by (simp add: clear_callback_slot_def)
qed

corollary retired_callback_agrees_with_projected_stutter:
  assumes "callback_reachable c" "callback_objects c i = Some (Ready_To_Clear ok)"
    "rtranclp callback_step (clear_callback_slot c i) c'"
    "callback_slot c' = map_option object_generation (active_slot s)"
  shows "run_callback_input c' i input = c'"
    "dispatch_publication_signal n i signal s = s"
proof -
  show "run_callback_input c' i input = c'"
    by (rule callback_queued_before_retirement_cannot_clear_again(1)[OF assms(1-3)])
  have "callback_slot c' \<noteq> Some i"
    by (rule callback_queued_before_retirement_cannot_clear_again(3)[OF assms(1-3)])
  then show "dispatch_publication_signal n i signal s = s"
    using assms(4) by (cases "active_slot s") (auto simp: dispatch_publication_signal_def)
qed

text \<open>
  The bridge uses phase correspondence at the clear, namely successful
  application and a finished hook or a failed self result or application.
  Slot identity is derived for the callback that reached that phase. In
  particular, a cancellation already queued before retirement can run
  while a different object occupies the slot. It is handled by the old
  object's completion flag. A late self result also leaves its first result
  unchanged. The designated slot-clearing listener itself cannot still be
  pending after its own object has been retired by a clear.
\<close>

end
