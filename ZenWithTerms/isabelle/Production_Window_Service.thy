theory Production_Window_Service
  imports Dynamic_Window_Liveness Stateless_Window_Liveness
begin

section \<open>Dispatch and successful completion at a production boundary\<close>

datatype 'a work_event =
    Enqueue 'a
  | Dispatch_Work 'a
  | Work_Succeeded 'a
  | Work_Rejected 'a
  | Other_Work

definition window_events where
  "window_events generation trace_log tick_limit =
    {event. \<exists>k<tick_limit. trace_log k = (generation, event)}"

lemma window_events_next [simp]:
  "window_events generation trace_log (Suc i) = window_events generation trace_log i \<union>
     (if fst (trace_log i) = generation then {snd (trace_log i)} else {})"
  unfolding window_events_def by (cases "trace_log i") (auto simp: less_Suc_eq)

definition observed_successes where
  "observed_successes generation trace_log tick_limit = {a. Work_Succeeded a \<in> window_events generation trace_log tick_limit}"

definition successful_selection where
  "successful_selection generation trace_log i =
     (case trace_log i of (g, Work_Succeeded a) \<Rightarrow> if g = generation then Some a else None | _ \<Rightarrow> None)"

lemma observed_next:
  "observed_successes generation trace_log (Suc i) =
     observed_successes generation trace_log i \<union> set_option (successful_selection generation trace_log i)"
  unfolding observed_successes_def successful_selection_def
  by (cases "trace_log i") (auto split: work_event.splits)

lemma selected_success_iff:
  "successful_selection generation trace_log i = Some a \<longleftrightarrow>
    trace_log i = (generation, Work_Succeeded a)"
  by (cases "trace_log i") (auto simp: successful_selection_def split: work_event.splits if_splits)

lemma success_has_event:
  "a \<in> observed_successes generation trace_log tick_limit \<longleftrightarrow>
    (\<exists>k<tick_limit. successful_selection generation trace_log k = Some a)"
  unfolding observed_successes_def window_events_def by (simp add: selected_success_iff)

definition enqueued_work where
  "enqueued_work queued_before generation trace_log tick_limit a \<longleftrightarrow>
    a \<in> queued_before \<or> Enqueue a \<in> window_events generation trace_log tick_limit"

definition dispatched_work where
  "dispatched_work started_before generation trace_log tick_limit a \<longleftrightarrow>
    a \<in> started_before \<or> Dispatch_Work a \<in> window_events generation trace_log tick_limit"

text \<open>
  A tick is a serialised observation of an enqueue, dispatch, successful
  completion, failure or other work. It can include transport and storage
  work represented by the corresponding source callback. An operation
  is identified within the active publication or election attempt.
  Work already queued or in flight for that generation can be carried
  into the window. Older generations and rejected work yield no
  successful operation. A projection must separately justify that
  those events have no effect on the state it observes inside the window.

  The source boundary must justify the causal order on first successful
  completions. Once protocol prerequisites hold, we require a bound on
  availability of resources and healthy endpoints for eligible work, a
  bound on enqueue or discovery of the request already queued, a bound
  on starting queued work, and a bound on observing its successful
  completion. Completion includes delivery and dispatch of a needed
  callback. A Java timeout or cancellation supplies a completion only
  when it effects the modeled operation, such as ending the target
  wait after commit. An exception or shutdown rejection alone is not
  successful service. Work outside the chosen healthy path need not
  receive any of these bounds.
\<close>

locale production_window_service =
  fixes jobs :: "'a set"
    and dependencies :: "'a \<Rightarrow> 'a set"
    and trace_log :: "nat \<Rightarrow> nat \<times> 'a work_event"
    and generation horizon enqueue_delay dispatch_delay completion_delay :: nat
    and queued_before started_before :: "'a set"
    and healthy resources :: "'a \<Rightarrow> nat \<Rightarrow> bool"
  assumes causal_completion:
    "i < horizon \<Longrightarrow> successful_selection generation trace_log i = Some a \<Longrightarrow>
      a \<notin> observed_successes generation trace_log i \<Longrightarrow>
      a \<in> jobs \<and> dependencies a \<subseteq> observed_successes generation trace_log i \<and>
        dispatched_work started_before generation trace_log i a"
    and dispatch_origin:
    "i < horizon \<Longrightarrow> trace_log i = (generation, Dispatch_Work a) \<Longrightarrow>
      enqueued_work queued_before generation trace_log i a"
    and carried_origin: "started_before \<subseteq> queued_before"
    and availability:
    "i + (enqueue_delay + dispatch_delay + completion_delay) \<le> horizon \<Longrightarrow>
      work_ready jobs dependencies (observed_successes generation trace_log i) a \<Longrightarrow>
      i \<le> j \<Longrightarrow> j \<le> i + (enqueue_delay + dispatch_delay + completion_delay) \<Longrightarrow>
      healthy a j \<and> resources a j"
    and enqueue_bound:
    "i + enqueue_delay \<le> horizon \<Longrightarrow>
      work_ready jobs dependencies (observed_successes generation trace_log i) a \<Longrightarrow>
      healthy a i \<Longrightarrow> resources a i \<Longrightarrow>
      enqueued_work queued_before generation trace_log (i + enqueue_delay) a"
    and dispatch_bound:
    "i + dispatch_delay \<le> horizon \<Longrightarrow> enqueued_work queued_before generation trace_log i a \<Longrightarrow>
      a \<in> jobs \<Longrightarrow> healthy a i \<Longrightarrow> resources a i \<Longrightarrow>
      dispatched_work started_before generation trace_log (i + dispatch_delay) a"
    and completion_bound:
    "i + completion_delay \<le> horizon \<Longrightarrow> dispatched_work started_before generation trace_log i a \<Longrightarrow>
      a \<in> jobs \<Longrightarrow> healthy a i \<Longrightarrow> resources a i \<Longrightarrow>
      a \<in> observed_successes generation trace_log (i + completion_delay)"
begin

abbreviation select where "select \<equiv> successful_selection generation trace_log"
abbreviation observed where "observed \<equiv> observed_successes generation trace_log"
abbreviation service_delay where "service_delay \<equiv> enqueue_delay + dispatch_delay + completion_delay"

lemma launched_work_has_queue_origin:
  assumes "i \<le> horizon" "dispatched_work started_before generation trace_log i a"
  shows "enqueued_work queued_before generation trace_log i a"
proof -
  from assms(2) consider (old) "a \<in> started_before" | (new) j where "j < i" "trace_log j = (generation, Dispatch_Work a)"
    unfolding dispatched_work_def window_events_def by blast
  then show ?thesis
  proof cases
    case old
    with carried_origin show ?thesis by (auto simp: enqueued_work_def)
  next
    case (new j)
    have "j < horizon" using new(1) assms(1) by simp
    from dispatch_origin[OF this new(2)] new(1)
    show ?thesis unfolding enqueued_work_def window_events_def by (blast intro: less_trans)
  qed
qed

lemma first_success_has_queue_origin:
  assumes "i < horizon" "select i = Some a" "a \<notin> observed i"
  shows "enqueued_work queued_before generation trace_log i a"
proof (rule launched_work_has_queue_origin)
  from assms(1) show "i \<le> horizon" by simp
  from causal_completion[OF assms] show "dispatched_work started_before generation trace_log i a" by blast
qed

lemma production_success_projection:
  assumes "i \<le> horizon"
  shows "observed i = completed_work jobs dependencies select i"
  using assms
proof (induction i)
  case 0
  show ?case by (simp add: observed_successes_def window_events_def)
next
  case (Suc i)
  have within: "i < horizon" using Suc.prems by simp
  have ih: "observed i = completed_work jobs dependencies select i"
    by (rule Suc.IH) (use within in simp)
  show ?case
  proof (cases "select i")
    case None
    then show ?thesis by (simp add: observed_next ih)
  next
    case (Some a)
    show ?thesis
    proof (cases "a \<in> observed i")
      case True
      with Some ih show ?thesis by (auto simp: observed_next work_ready_def)
    next
      case False
      from causal_completion[OF within Some False] False
      have "work_ready jobs dependencies (observed i) a" unfolding work_ready_def by blast
      with Some ih show ?thesis by (simp add: observed_next)
    qed
  qed
qed

theorem production_supplies_bounded_service:
  "bounded_service jobs dependencies select service_delay horizon"
  unfolding bounded_service_def
proof (intro allI impI)
  fix i a
  assume time: "i + service_delay \<le> horizon"
    and ready: "work_ready jobs dependencies (completed_work jobs dependencies select i) a"
  let ?queued = "i + enqueue_delay"
  let ?started = "?queued + dispatch_delay"
  let ?end = "i + service_delay"
  have order: "i \<le> ?queued" "?queued \<le> ?started" "?started \<le> ?end" by simp_all
  have started_bound: "?started \<le> horizon" by (rule order_trans[OF order(3) time])
  have queued_bound: "?queued \<le> horizon" by (rule order_trans[OF order(2) started_bound])
  have first_bound: "i \<le> horizon" by (rule order_trans[OF order(1) queued_bound])
  have finish_bound: "?started + completion_delay \<le> horizon" using time by (simp add: add.assoc)
  have observed_ready: "work_ready jobs dependencies (observed i) a"
    unfolding production_success_projection[OF first_bound] by (rule ready)
  have member: "a \<in> jobs" using observed_ready unfolding work_ready_def by simp
  have live_first: "healthy a i \<and> resources a i"
    by (rule availability[OF time observed_ready le_refl])
      (rule order_trans[OF order(1) order_trans[OF order(2,3)]])
  have live_queue: "healthy a ?queued \<and> resources a ?queued"
    by (rule availability[OF time observed_ready order(1) order_trans[OF order(2,3)]])
  have live_start: "healthy a ?started \<and> resources a ?started"
    by (rule availability[OF time observed_ready order_trans[OF order(1,2)] order(3)])
  have queued: "enqueued_work queued_before generation trace_log ?queued a"
    by (rule enqueue_bound[OF queued_bound observed_ready live_first[THEN conjunct1] live_first[THEN conjunct2]])
  have dispatched: "dispatched_work started_before generation trace_log ?started a"
    by (rule dispatch_bound[OF started_bound queued member live_queue[THEN conjunct1] live_queue[THEN conjunct2]])
  have success: "a \<in> observed ?end"
    using completion_bound[OF finish_bound dispatched member live_start[THEN conjunct1] live_start[THEN conjunct2]]
    by (simp only: add.assoc)
  from success_has_event[THEN iffD1, OF success] obtain j where hit: "j < ?end" "select j = Some a"
    by (elim exE conjE) assumption
  have "i \<le> j"
  proof (rule ccontr)
    assume "\<not> i \<le> j"
    then have early: "j < i" by simp
    have "a \<in> observed i" by (rule success_has_event[THEN iffD2])
      (rule exI[of _ j]; rule conjI[OF early hit(2)])
    with observed_ready show False unfolding work_ready_def by simp
  qed
  with hit show "\<exists>j. i \<le> j \<and> j < ?end \<and> select j = Some a" by blast
qed

end

section \<open>State projection at successful source callbacks\<close>

definition source_effects where
  "source_effects generation trace_log horizon project snapshot \<longleftrightarrow>
    project 0 = snapshot {} \<and>
    (\<forall>i<horizon. project i = snapshot (observed_successes generation trace_log i) \<longrightarrow>
      project (Suc i) =
        (case successful_selection generation trace_log i of
           None \<Rightarrow> project i
         | Some a \<Rightarrow> snapshot (insert a (observed_successes generation trace_log i))))"

lemma source_effects_project:
  assumes effects: "source_effects generation trace_log horizon project snapshot"
    and horizon: "i \<le> horizon"
  shows "project i = snapshot (observed_successes generation trace_log i)"
  using horizon
proof (induction i)
  case 0
  then show ?case using effects unfolding source_effects_def observed_successes_def window_events_def by simp
next
  case (Suc i)
  then have time: "i < horizon" and before:
    "project i = snapshot (observed_successes generation trace_log i)" by auto
  have after: "project (Suc i) =
        (case successful_selection generation trace_log i of
           None \<Rightarrow> project i
         | Some a \<Rightarrow> snapshot (insert a (observed_successes generation trace_log i)))"
    using effects time before unfolding source_effects_def by blast
  show ?case using after before by (cases "successful_selection generation trace_log i") (simp_all add: observed_next)
qed

lemma ignored_event_stutters:
  assumes effects: "source_effects generation trace_log horizon project snapshot"
    and time: "i < horizon"
    and ignored: "successful_selection generation trace_log i = None"
  shows "project (Suc i) = project i"
proof -
  from time have "i \<le> horizon" by simp
  from source_effects_project[OF effects this] effects time ignored show ?thesis
    unfolding source_effects_def by simp
qed

lemma production_execution_projects:
  assumes service: "production_window_service jobs dependencies trace_log generation horizon enqueue_delay dispatch_delay
      completion_delay queued_before started_before healthy resources"
    and effects: "source_effects generation trace_log horizon project snapshot"
    and horizon: "i \<le> horizon"
  shows "project i = snapshot (completed_work jobs dependencies (successful_selection generation trace_log) i)"
  using source_effects_project[OF effects horizon]
    production_window_service.production_success_projection[OF service horizon] by simp

text \<open>
  These boundary conditions are about individual successful callbacks and
  their order. The fixed and dynamic windows use the following source
  correspondence. Prevote is accepted evidence in the current
  StatefulPreVoteCollector round. Choose_Term uses Coordinator's fresh
  term at startElection. Persist_Join covers return from handleStartJoin
  with the term durably written, and Collect_Votes covers processing the
  needed joins. Register is installation of the publication by
  Coordinator.publish. Persist_Accept covers the successful publish handler
  and its durable setter. Collect_Receipts is successful processing of
  publish responses up to quorum. In a dynamic window the additional fresh
  joins needed by the new configuration must be processed before Register.

  Handle_Self_Commit is the local apply-commit handler and reply, distinct
  from the task acknowledgement. Finish_Target is a terminal publication
  target, and End_Target_Wait is a serviced cancellation after quorum.
  Queue_Local occurs when the publication-completion path can enqueue
  local application. Sample_Local reads the live supplied state in
  ClusterApplierService. Run_Local ends its successful application. Release_Slot
  includes servicing the successful completion callback through mutex entry
  and clearing the matching slot. These observe the source paths in
  Coordinator, Publication and ClusterApplierService. The trace projection
  must establish the isolated window and generation association, including
  that unrelated work does not interfere. The service theorem does not
  derive resource or clock bounds from Java.
\<close>

context fixed_publication_window
begin

theorem fixed_production_window_completes:
  assumes service: "production_window_service jobs deps trace_log generation horizon enqueue_delay dispatch_delay
      completion_delay queued_before started_before healthy resources"
    and effects: "source_effects generation trace_log horizon project
      (\<lambda>K. (core K, installed (window_applier K), window_slot K))"
    and time: "(if fresh then 12 else 8) * (enqueue_delay + dispatch_delay + completion_delay) \<le> horizon"
  defines "deadline \<equiv> (if fresh then 12 else 8) * (enqueue_delay + dispatch_delay + completion_delay)"
  shows "h \<in> committed (fst (project deadline))"
    "fst (snd (project deadline)) = Some key"
    "snd (snd (project deadline)) = None"
proof -
  let ?d = "enqueue_delay + dispatch_delay + completion_delay"
  let ?sel = "successful_selection generation trace_log"
  have bound: "deadline \<le> horizon" using time unfolding deadline_def .
  have projection: "project deadline =
      (core (finished ?sel deadline), installed (window_applier (finished ?sel deadline)), window_slot (finished ?sel deadline))"
    by (rule production_execution_projects[OF service effects bound])
  note svc = production_window_service.production_supplies_bounded_service[OF service]
  have completed: "h \<in> committed (core (finished ?sel deadline)) \<and>
    installed (window_applier (finished ?sel deadline)) = Some key \<and> window_slot (finished ?sel deadline) = None"
  proof (cases fresh)
    case True
    then have "deadline = 12 * ?d" unfolding deadline_def by simp
    with fixed_first_publication_local_completion[OF True svc] bound show ?thesis by simp
  next
    case False
    then have "deadline = 8 * ?d" unfolding deadline_def by simp
    with fixed_incumbent_local_completion[OF False svc] bound show ?thesis by simp
  qed
  show "h \<in> committed (fst (project deadline))" "fst (snd (project deadline)) = Some key"
    "snd (snd (project deadline)) = None" using completed unfolding projection by simp_all
qed

end

context dynamic_publication_window
begin

theorem dynamic_production_window_completes:
  assumes service: "production_window_service jobs deps trace_log generation horizon enqueue_delay dispatch_delay
      completion_delay queued_before started_before healthy resources"
    and effects: "source_effects generation trace_log horizon project
      (\<lambda>K. (dynamic_snapshot K, Run_Local \<in> K, dynamic_window_slot K))"
    and time: "12 * (enqueue_delay + dispatch_delay + completion_delay) \<le> horizon"
  defines "deadline \<equiv> 12 * (enqueue_delay + dispatch_delay + completion_delay)"
  shows "hist \<in> quorum_commits (fst (project deadline))"
    "committed_config (fst (project deadline)) c = D"
    "fst (snd (project deadline))"
    "snd (snd (project deadline)) = None"
proof -
  let ?sel = "successful_selection generation trace_log"
  have bound: "deadline \<le> horizon" using time unfolding deadline_def .
  have projection: "project deadline =
      (dynamic_snapshot (finished ?sel deadline), Run_Local \<in> finished ?sel deadline, dynamic_window_slot (finished ?sel deadline))"
    by (rule production_execution_projects[OF service effects bound])
  note completed = dynamic_window_local_completion[OF production_window_service.production_supplies_bounded_service[OF service] time]
  show "hist \<in> quorum_commits (fst (project deadline))" "committed_config (fst (project deadline)) c = D"
    "fst (snd (project deadline))" "snd (snd (project deadline)) = None"
    unfolding projection using completed by (simp_all add: deadline_def)
qed

end

section \<open>Serial source correspondence for the stateless path\<close>

text \<open>
  The first four indices of the stateless plan represent the effect of
  compareAndSetRegister, its success callback, the term advance, and the
  start of recovery. The scan indices represent successive successful
  directory probes in StatelessPersistedState. A download and election
  base selection can contribute a state-preserving operation. First
  publication, state send, manifest installation and local durable
  acceptance precede the exact-term fence callback from beforeCommit.
  Notification, apply-commit send and self handling follow the fence.
  Target completion or cancellation permits local queuing and is
  state-preserving in this projection. Supplier sampling, application
  and acknowledgement supply the final operations. An ordinary quorum
  callback cannot stand in for the fence. The source correspondence
  must identify the operations of this attempt and establish each
  projected state change, including the order of manifest installation
  and acceptance. Source callbacks can be coalesced or split into
  distinct logical observations before applying the service bounds.
\<close>

context stateless_publication_window
begin

abbreviation plan_length where "plan_length \<equiv> 4 + scans + 14"

lemma stateless_source_plan:
  obtains f :: "nat \<Rightarrow> stateless_execution" where
    "f 0 = x"
    "\<And>i. i < plan_length \<Longrightarrow> window_move (f i) (f (Suc i))"
    "stateless_execution_reachable (f plan_length)"
    "h \<in> notifications (shared_state (f plan_length))"
    "installed (processes (f plan_length) c) = Some (position h)"
    "(incarnation (processes (f plan_length) c), q, position h)
      \<in> node_acknowledgements (processes (f plan_length) c)"
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
      "(incarnation (processes z c), q, position h) \<in> node_acknowledgements (processes z c)"
    by blast
  from counted_path_append[where R=window_move, OF window_moves_from_exec[OF path] tail]
  obtain f where "f 0 = x" "f plan_length = z" "\<And>i. i < plan_length \<Longrightarrow> window_move (f i) (f (Suc i))"
    unfolding relpowp_fun_conv by blast
  with result show thesis by (intro that[of f]) simp_all
qed

theorem stateless_production_window_completes:
  assumes service: "production_window_service {..<plan_length} (\<lambda>i. {..<i}) trace_log generation horizon
    enqueue_delay dispatch_delay completion_delay queued_before started_before healthy resources"
    and time: "(18 + max 1 (t - 1)) * (enqueue_delay + dispatch_delay + completion_delay) \<le> horizon"
  defines "deadline \<equiv> plan_length * (enqueue_delay + dispatch_delay + completion_delay)"
  obtains f :: "nat \<Rightarrow> stateless_execution" where
    "f 0 = x"
    "\<And>i. i < plan_length \<Longrightarrow> window_move (f i) (f (Suc i))"
    "\<And>project. source_effects generation trace_log horizon project (\<lambda>K. f (card K)) \<Longrightarrow>
      stateless_execution_reachable (project deadline) \<and>
      h \<in> notifications (shared_state (project deadline)) \<and>
      installed (processes (project deadline) c) = Some (position h) \<and>
      (incarnation (processes (project deadline) c), q, position h)
        \<in> node_acknowledgements (processes (project deadline) c)"
proof -
  have bound: "deadline \<le> horizon" unfolding deadline_def
    by (rule order_trans[OF mult_le_mono1[OF stateless_window_length_bound] time])
  show thesis
  proof (rule stateless_source_plan)
    fix f :: "nat \<Rightarrow> stateless_execution"
    assume path: "f 0 = x" "\<And>i. i < plan_length \<Longrightarrow> window_move (f i) (f (Suc i))"
      and terminal: "stateless_execution_reachable (f plan_length)"
      "h \<in> notifications (shared_state (f plan_length))"
      "installed (processes (f plan_length) c) = Some (position h)"
      "(incarnation (processes (f plan_length) c), q, position h)
        \<in> node_acknowledgements (processes (f plan_length) c)"
    show thesis
    proof (rule that[OF path])
      fix project :: "nat \<Rightarrow> stateless_execution"
      assume effects: "source_effects generation trace_log horizon project (\<lambda>K. f (card K))"
      let ?sel = "successful_selection generation trace_log"
      have "project deadline = serviced_stateless_trace plan_length ?sel f deadline"
        using production_execution_projects[OF service effects bound] unfolding serviced_stateless_trace_def .
      also have "\<dots> = f plan_length" unfolding deadline_def
        by (rule serviced_stateless_trace_end[OF production_window_service.production_supplies_bounded_service[OF service]])
          (rule bound[unfolded deadline_def])
      finally show "stateless_execution_reachable (project deadline) \<and>
        h \<in> notifications (shared_state (project deadline)) \<and>
        installed (processes (project deadline) c) = Some (position h) \<and>
        (incarnation (processes (project deadline) c), q, position h)
          \<in> node_acknowledgements (processes (project deadline) c)"
        using terminal by simp
    qed
  qed
qed

end

end
