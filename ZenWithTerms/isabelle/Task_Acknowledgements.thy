theory Task_Acknowledgements
  imports Stateless_Execution Default_Application
begin

section \<open>MasterService's publication-scoped countdown\<close>

datatype task_ack_result = Waiting_For_Acks | Task_Ack_Success | Task_Ack_Failure | Task_Ack_Timeout
datatype ack_budget = No_Deadline | Deadline_Expired | Deadline_Remains

record task_acks =
  pending_acks :: "node set"
  received_successes :: "node \<Rightarrow> (nat \<times> rank) option"
  received_failures :: "node set"
  commit_counted :: bool
  timer_enabled :: bool
  task_ack_result :: task_ack_result

definition required_acks where
  "required_acks targets master must_ack = {n \<in> targets. n = master \<or> must_ack n}"

definition task_acks_initial where
  "task_acks_initial R = \<lparr>pending_acks = R, received_successes = (\<lambda>_. None), received_failures = {},
    commit_counted = False, timer_enabled = False, task_ack_result = Waiting_For_Acks\<rparr>"

definition finish_acks where
  "finish_acks a = (if commit_counted a \<and> pending_acks a = {} then
    a\<lparr>task_ack_result := (if received_failures a = {} then Task_Ack_Success else Task_Ack_Failure)\<rparr> else a)"

lemma finish_acks_fields [simp]:
  "pending_acks (finish_acks a) = pending_acks a"
  "received_successes (finish_acks a) = received_successes a"
  "received_failures (finish_acks a) = received_failures a"
  "commit_counted (finish_acks a) = commit_counted a"
  "task_ack_result (finish_acks a) = (if commit_counted a \<and> pending_acks a = {} then
    (if received_failures a = {} then Task_Ack_Success else Task_Ack_Failure) else task_ack_result a)"
  by (simp_all add: finish_acks_def split: if_splits)

text \<open>
  The target set and mustAck selection are frozen for this listener.
  PublicationTarget.ackOnce supplies one callback per target. The model
  records the winner of CountDown or fastForward, abstracting away the
  delay before invoking the task listener. The onCommit slot represents
  Publication's bookkeeping callback, which can precede the stateless
  fence. Only node success carries the matching application witness.
  Deadline_Remains can arm a future timeout; the zero-budget onCommit
  path attempts the timeout without decrementing the commit slot.
\<close>

inductive task_ack_step for q evidence where
  node_success:
    "task_ack_result a = Waiting_For_Acks \<Longrightarrow> n \<in> pending_acks a \<Longrightarrow>
     (e,q,k) \<in> evidence n \<Longrightarrow>
     task_ack_step q evidence a
       (finish_acks (a\<lparr>pending_acks := pending_acks a - {n}, received_successes := (received_successes a)(n := Some (e,k))\<rparr>))"
| node_failure:
    "task_ack_result a = Waiting_For_Acks \<Longrightarrow> n \<in> pending_acks a \<Longrightarrow>
     task_ack_step q evidence a
       (finish_acks (a\<lparr>pending_acks := pending_acks a - {n}, received_failures := insert n (received_failures a)\<rparr>))"
| on_commit:
    "task_ack_result a = Waiting_For_Acks \<Longrightarrow> \<not> commit_counted a \<Longrightarrow>
     budget \<noteq> Deadline_Expired \<Longrightarrow>
     task_ack_step q evidence a (finish_acks (a\<lparr>commit_counted := True, timer_enabled := (budget = Deadline_Remains)\<rparr>))"
| commit_timeout:
    "task_ack_result a = Waiting_For_Acks \<Longrightarrow> \<not> commit_counted a \<Longrightarrow>
     task_ack_step q evidence a (a\<lparr>task_ack_result := Task_Ack_Timeout\<rparr>)"
| scheduled_timeout:
    "task_ack_result a = Waiting_For_Acks \<Longrightarrow> timer_enabled a \<Longrightarrow>
     task_ack_step q evidence a (a\<lparr>task_ack_result := Task_Ack_Timeout\<rparr>)"

definition task_acks_ok where
  "task_acks_ok R q evidence a \<longleftrightarrow>
    R = pending_acks a \<union> dom (received_successes a) \<union> received_failures a \<and>
    pending_acks a \<inter> dom (received_successes a) = {} \<and>
    pending_acks a \<inter> received_failures a = {} \<and>
    dom (received_successes a) \<inter> received_failures a = {} \<and>
    (\<forall>n e k. received_successes a n = Some (e,k) \<longrightarrow> (e,q,k) \<in> evidence n) \<and>
    (case task_ack_result a of
       Waiting_For_Acks \<Rightarrow> \<not> commit_counted a \<or> pending_acks a \<noteq> {}
     | Task_Ack_Success \<Rightarrow> commit_counted a \<and> pending_acks a = {} \<and> received_failures a = {}
     | Task_Ack_Failure \<Rightarrow> commit_counted a \<and> pending_acks a = {} \<and> received_failures a \<noteq> {}
     | Task_Ack_Timeout \<Rightarrow> \<not> commit_counted a \<or> pending_acks a \<noteq> {})"

lemma task_ack_step_preserves:
  assumes step: "task_ack_step q evidence a b" and ok: "task_acks_ok R q evidence a"
  shows "task_acks_ok R q evidence b"
proof -
  from ok have partition:
    "R = pending_acks a \<union> dom (received_successes a) \<union> received_failures a"
    "pending_acks a \<inter> dom (received_successes a) = {}"
    "pending_acks a \<inter> received_failures a = {}"
    "dom (received_successes a) \<inter> received_failures a = {}"
    unfolding task_acks_ok_def by blast+
  from step partition have partition':
    "R = pending_acks b \<union> dom (received_successes b) \<union> received_failures b"
    "pending_acks b \<inter> dom (received_successes b) = {}"
    "pending_acks b \<inter> received_failures b = {}"
    "dom (received_successes b) \<inter> received_failures b = {}"
    by (cases rule: task_ack_step.cases; auto)+
  from ok have evidence: "received_successes a n = Some (e,k) \<Longrightarrow> (e,q,k) \<in> evidence n" for n e k
    unfolding task_acks_ok_def by blast
  have evidence': "received_successes b n = Some (e,k) \<Longrightarrow> (e,q,k) \<in> evidence n" for n e k
    using step by cases (auto simp: fun_upd_apply split: if_splits intro: evidence)
  from ok have waiting: "\<not> commit_counted a \<or> pending_acks a \<noteq> {}" if "task_ack_result a = Waiting_For_Acks"
    using that unfolding task_acks_ok_def by simp
  have status: "case task_ack_result b of
       Waiting_For_Acks \<Rightarrow> \<not> commit_counted b \<or> pending_acks b \<noteq> {}
     | Task_Ack_Success \<Rightarrow> commit_counted b \<and> pending_acks b = {} \<and> received_failures b = {}
     | Task_Ack_Failure \<Rightarrow> commit_counted b \<and> pending_acks b = {} \<and> received_failures b \<noteq> {}
     | Task_Ack_Timeout \<Rightarrow> \<not> commit_counted b \<or> pending_acks b \<noteq> {}"
    using step by cases (auto split: if_splits dest: waiting)
  show ?thesis unfolding task_acks_ok_def using partition' evidence' status by blast
qed

lemma task_ack_invariants:
  assumes "rtranclp (task_ack_step q evidence) (task_acks_initial R) a"
  shows "task_acks_ok R q evidence a"
  using assms
proof induction
  case base
  show ?case by (simp add: task_acks_initial_def task_acks_ok_def)
next
  case (step a b)
  show ?case by (rule task_ack_step_preserves[OF step.hyps(2) step.IH])
qed

theorem task_ack_outcomes:
  assumes "rtranclp (task_ack_step q evidence) (task_acks_initial R) a"
  shows "task_ack_result a = Task_Ack_Success \<Longrightarrow>
    commit_counted a \<and> (\<forall>n\<in>R. \<exists>e k. (e,q,k) \<in> evidence n)"
    "task_ack_result a = Task_Ack_Failure \<Longrightarrow> commit_counted a \<and>
      pending_acks a = {} \<and> (\<exists>n\<in>R. n \<in> received_failures a)"
    "task_ack_result a = Task_Ack_Timeout \<Longrightarrow> \<not> commit_counted a \<or> pending_acks a \<noteq> {}"
  using task_ack_invariants[OF assms]
  by (auto simp: task_acks_ok_def dom_def, blast)

lemma terminal_task_ack_stops:
  "task_ack_step q evidence a b \<Longrightarrow> task_ack_result a = Waiting_For_Acks"
  by (cases rule: task_ack_step.cases) auto

definition remaining_ack_slots where
  "remaining_ack_slots a = card (pending_acks a) + (if commit_counted a then 0 else 1)"

lemma waiting_count_is_positive:
  assumes "task_acks_ok R q evidence a" "task_ack_result a = Waiting_For_Acks" "finite R"
  shows "0 < remaining_ack_slots a"
proof -
  from assms(1,3) have "finite (pending_acks a)" unfolding task_acks_ok_def by (auto intro: finite_subset)
  then show ?thesis using assms(1,2)
    by (auto simp: task_acks_ok_def remaining_ack_slots_def card_gt_0_iff)
qed

lemma counted_callback_decrements_once:
  assumes step: "task_ack_step q evidence a b" and finite: "finite (pending_acks a)"
    and counted: "task_ack_result b \<noteq> Task_Ack_Timeout"
  shows "Suc (remaining_ack_slots b) = remaining_ack_slots a"
proof -
  have decrement: "Suc (card (pending_acks a - {n})) = card (pending_acks a)"
    if "n \<in> pending_acks a" for n
  proof -
    have "0 < card (pending_acks a)" using that finite by (auto simp: card_gt_0_iff)
    with that finite show ?thesis by (simp add: card_Diff_singleton)
  qed
  show ?thesis using step
  proof cases
    case (node_success n e k)
    from node_success decrement[OF node_success(3)] show ?thesis
      by (simp add: remaining_ack_slots_def)
  next
    case (node_failure n)
    from node_failure decrement[OF node_failure(3)] show ?thesis
      by (simp add: remaining_ack_slots_def)
  qed (use counted in \<open>simp_all add: remaining_ack_slots_def\<close>)
qed

lemma task_ack_step_weaken:
  assumes "task_ack_step q evidence a b" "\<And>n. evidence n \<subseteq> later n"
  shows "task_ack_step q later a b"
  using assms by (cases rule: task_ack_step.cases)
    (auto intro: task_ack_step.intros subsetD)

lemma task_ack_trace_weaken:
  assumes "rtranclp (task_ack_step q evidence) a b" "\<And>n. evidence n \<subseteq> later n"
  shows "rtranclp (task_ack_step q later) a b"
  using assms(1) by induction
    (auto intro: rtranclp.rtrancl_into_rtrancl task_ack_step_weaken[OF _ assms(2)])

section \<open>Application witnesses for successful task results\<close>

theorem stateless_task_acknowledges_committed_prefix:
  assumes run: "stateless_execution_reachable x"
    and task: "rtranclp (task_ack_step q (\<lambda>n. node_acknowledgements (processes x n)))
      (task_acks_initial (required_acks targets master must_ack)) a"
    and success: "task_ack_result a = Task_Ack_Success"
    and target: "n \<in> required_acks targets master must_ack"
  obtains h p where "h \<in> notifications (shared_state x)" "p \<in> notifications (shared_state x)"
    "owner h = apply_source q" "position h = apply_key q" "prefix h p"
    "\<exists>e. (e,q,position p) \<in> node_acknowledgements (processes x n)"
proof -
  from task_ack_outcomes(1)[OF task success] target obtain e k where
    ack: "(e,q,k) \<in> node_acknowledgements (processes x n)" by blast
  obtain h p where commits: "h \<in> notifications (shared_state x)" "p \<in> notifications (shared_state x)"
    and req: "owner h = apply_source q" "position h = apply_key q" and key: "position p = k" and pref: "prefix h p"
    by (rule stateless_node_acknowledges_committed_prefix[OF run ack])
  have witness: "\<exists>e. (e,q,position p) \<in> node_acknowledgements (processes x n)"
    using ack unfolding key by blast
  show thesis by (rule that[OF commits req pref witness])
qed

theorem stock_task_acknowledges_committed_prefix:
  assumes run: "stock_reachable N E V C v versions marker paths roles x"
    and separated: "\<And>n. roles n \<noteq> None \<Longrightarrow> n \<notin> N"
    and applications: "\<And>n. n \<in> required_acks targets master must_ack \<Longrightarrow>
      application_reachable n (voting_traffic (mixed_state x)) (initial_term n) (initial_key n) (applied n)"
    and task: "rtranclp (task_ack_step q (\<lambda>n. node_acknowledgements (applied n)))
      (task_acks_initial (required_acks targets master must_ack)) a"
    and success: "task_ack_result a = Task_Ack_Success"
    and target: "n \<in> required_acks targets master must_ack"
  obtains d h p where "dynamic_reachable C d" "h \<in> quorum_commits d" "p \<in> quorum_commits d"
    "owner h = apply_source q" "position h = apply_key q" "prefix h p"
    "\<exists>e. (e,q,position p) \<in> node_acknowledgements (applied n)"
proof -
  from stock_execution_projection[OF separated run] have mixed:
    "mixed_reachable N E V C v versions marker paths roles (mixed_state x)" by blast
  from task_ack_outcomes(1)[OF task success] target obtain e k where
    ack: "(e,q,k) \<in> node_acknowledgements (applied n)" by blast
  obtain d h p where reach: "dynamic_reachable C d" and commits: "h \<in> quorum_commits d" "p \<in> quorum_commits d"
    and req: "position h = apply_key q" "owner h = apply_source q" and key: "position p = k" and pref: "prefix h p"
    by (rule mixed_node_acknowledges_committed_prefix[OF mixed separated applications[OF target] ack])
  have witness: "\<exists>e. (e,q,position p) \<in> node_acknowledgements (applied n)"
    using ack unfolding key by blast
  show thesis by (rule that[OF reach commits req(2,1) pref witness])
qed

theorem stock_task_success:
  assumes run: "stock_reachable N E V C v versions marker paths roles x"
    and separated: "\<And>n. roles n \<noteq> None \<Longrightarrow> n \<notin> N"
    and publisher: "apply_source q \<in> targets"
    and applications: "\<And>n. n \<in> required_acks targets (apply_source q) must_ack \<Longrightarrow>
      application_reachable n (voting_traffic (mixed_state x)) (initial_term n) (initial_key n) (applied n)"
    and task: "rtranclp (task_ack_step q (\<lambda>n. node_acknowledgements (applied n)))
      (task_acks_initial (required_acks targets (apply_source q) must_ack)) a"
    and success: "task_ack_result a = Task_Ack_Success"
  obtains d h where "dynamic_reachable C d" "h \<in> quorum_commits d" "owner h = apply_source q" "position h = apply_key q"
    "\<forall>n\<in>required_acks targets (apply_source q) must_ack.
      \<exists>p\<in>quorum_commits d. prefix h p \<and>
        (\<exists>e. (e,q,position p) \<in> node_acknowledgements (applied n))"
proof -
  let ?s = "mixed_state x"
  let ?H = "voting_traffic ?s"
  let ?R = "required_acks targets (apply_source q) must_ack"
  note successes = task_ack_outcomes(1)[OF task success]
  from stock_execution_projection[OF separated run] have mixed:
    "mixed_reachable N E V C v versions marker paths roles ?s" by blast
  have durable: "durable_execution N E V C v versions paths (voting ?s) ?H (voting_disks ?s)"
    by (rule mixed_role_durability[OF _ mixed]) (rule separated)
  have transport: "transport_reachable N E V C v versions (voting ?s) ?H"
    by (rule durable_execution_invariants[OF durable, THEN conjunct1])
  obtain t where t: "tla_reachable N V C v versions t" "coordination (voting ?s) = project_java E t"
    using transport_refines_tla[OF transport] by blast
  obtain d where d: "dynamic_reachable C d" "linked C t d" using tla_dynamic_refinement[OF t(1)] by blast
  have master: "apply_source q \<in> ?R" using publisher unfolding required_acks_def by simp
  from successes master obtain e k where first: "(e,q,k) \<in> node_acknowledgements (applied (apply_source q))" by blast
  from successful_node_ack(2)[OF applications[OF master] first] have commit: "Returned_Commit (apply_source q) (apply_key q) \<in> ?H"
    unfolding authentic_request_def .
  obtain h where h: "h \<in> quorum_commits d" "position h = apply_key q" "owner h = apply_source q"
    by (rule returned_commit_has_quorum_history[OF transport d(2) t(2) commit])
  have pubs: "publications_ok C d" using dynamic_invariants[OF d(1)] by blast
  from publicationsD(5)[OF pubs h(1)] have hp: "h \<in> insert [] (publications d)" by blast
  have "\<exists>p\<in>quorum_commits d. prefix h p \<and> (\<exists>e. (e,q,position p) \<in> node_acknowledgements (applied n))"
    if n: "n \<in> ?R" for n
  proof -
    obtain e k where ack: "(e,q,k) \<in> node_acknowledgements (applied n)" using successes n by blast
    note witness = successful_node_ack[OF applications[OF n] ack]
    obtain c where packet: "Returned_Commit c k \<in> ?H" using witness(3) unfolding quorum_key_def by blast
    obtain p where p: "p \<in> quorum_commits d" "position p = k" "owner p = c"
      by (rule returned_commit_has_quorum_history[OF transport d(2) t(2) packet])
    have "prefix h p" using dynamic_committed_states_form_chain[OF d(1) h(1) p(1)]
      lineage_prefix[OF pubs hp, of p] witness(4) h(2) p(2) by (auto simp: not_less)
    with p ack show ?thesis by blast
  qed
  from that[OF d(1) h(1,3,2)] this show thesis by blast
qed

text \<open>
  A running task can count evidence available at the time of its
  transition. Coordinator, storage and application work may advance
  independently while the listener waits.
\<close>

inductive stateless_task_execution for q targets must_ack where
  start:
    "stateless_execution_reachable x \<Longrightarrow> apply_source q \<in> targets \<Longrightarrow>
     (\<exists>h\<in>issued (shared_state x). owner h = apply_source q \<and> position h = apply_key q) \<Longrightarrow>
     stateless_task_execution q targets must_ack x (task_acks_initial (required_acks targets (apply_source q) must_ack))"
| cluster:
    "stateless_task_execution q targets must_ack x a \<Longrightarrow> stateless_exec_step x y \<Longrightarrow>
     stateless_task_execution q targets must_ack y a"
| listener:
    "stateless_task_execution q targets must_ack x a \<Longrightarrow>
     task_ack_step q (\<lambda>n. node_acknowledgements (processes x n)) a b \<Longrightarrow>
     stateless_task_execution q targets must_ack x b"

lemma stateless_task_projection:
  assumes "stateless_task_execution q targets must_ack x a"
  shows "stateless_execution_reachable x \<and> apply_source q \<in> targets \<and>
    rtranclp (task_ack_step q (\<lambda>n. node_acknowledgements (processes x n)))
      (task_acks_initial (required_acks targets (apply_source q) must_ack)) a"
  using assms
proof induction
  case start
  then show ?case by simp
next
  case (cluster x a y)
  then have run: "stateless_execution_reachable x" by blast
  from stateless_execution_projection[OF run] have wire: "stateless_packets_ok x" by blast
  have growth: "node_acknowledgements (processes x n) \<subseteq> node_acknowledgements (processes y n)" for n
    using stateless_exec_application_step[OF cluster.hyps(2) wire, of n]
    by (elim disjE) (simp, erule application_step_grows_history[THEN conjunct2])
  from cluster.IH have before: "rtranclp (task_ack_step q (\<lambda>n. node_acknowledgements (processes x n)))
    (task_acks_initial (required_acks targets (apply_source q) must_ack)) a" by blast
  from task_ack_trace_weaken[OF before growth] stateless_execution_reachable.step[OF run cluster.hyps(2)] cluster.IH
  show ?case by blast
next
  case listener
  then show ?case by (blast intro: rtranclp.rtrancl_into_rtrancl)
qed

theorem coupled_stateless_task_success:
  assumes run: "stateless_task_execution q targets must_ack x a"
    and success: "task_ack_result a = Task_Ack_Success"
  obtains h where "h \<in> notifications (shared_state x)" "owner h = apply_source q" "position h = apply_key q"
    "\<forall>n\<in>required_acks targets (apply_source q) must_ack.
      \<exists>p\<in>notifications (shared_state x). prefix h p \<and>
        (\<exists>e. (e,q,position p) \<in> node_acknowledgements (processes x n))"
proof -
  from stateless_task_projection[OF run] have cluster: "stateless_execution_reachable x"
    and master: "apply_source q \<in> required_acks targets (apply_source q) must_ack"
    and task: "rtranclp (task_ack_step q (\<lambda>n. node_acknowledgements (processes x n)))
      (task_acks_initial (required_acks targets (apply_source q) must_ack)) a"
    by (auto simp: required_acks_def)
  let ?s = "shared_state x"
  obtain h p where h: "h \<in> notifications ?s" and "p \<in> notifications ?s"
    and req: "owner h = apply_source q" "position h = apply_key q"
    and "prefix h p" "\<exists>e. (e,q,position p) \<in> node_acknowledgements (processes x (apply_source q))"
    by (rule stateless_task_acknowledges_committed_prefix[OF cluster task success master])
  from stateless_execution_projection[OF cluster] have reach: "stateless_reachable ?s" by blast
  from stateless_invariants[OF reach] have issued: "u \<in> notifications ?s \<Longrightarrow> u \<in> issued ?s" for u
    unfolding stateless_ok_def frontier_ok_def by blast
  have "\<exists>p\<in>notifications ?s. prefix h p \<and>
    (\<exists>e. (e,q,position p) \<in> node_acknowledgements (processes x n))"
    if n: "n \<in> required_acks targets (apply_source q) must_ack" for n
  proof -
    obtain u p where u: "u \<in> notifications ?s" and p: "p \<in> notifications ?s"
      and "owner u = apply_source q" and key: "position u = apply_key q" and pref: "prefix u p"
      and ack: "\<exists>e. (e,q,position p) \<in> node_acknowledgements (processes x n)"
      by (rule stateless_task_acknowledges_committed_prefix[OF cluster task success n])
    have "u = h" by (rule stateless_unique_publication[OF reach issued[OF u] issued[OF h]]) (simp add: key req(2))
    with p pref ack show ?thesis by blast
  qed
  from that[OF h req] this show thesis by blast
qed


section \<open>Stock listeners driven by the default publication and applier paths\<close>

inductive stock_task_execution for N E V C v versions marker paths roles q targets must_ack where
  start:
    "stock_applier_execution N E V C v versions marker paths roles x A \<Longrightarrow> apply_source q \<in> targets \<Longrightarrow>
     Registered_State p u \<in> voting_traffic (mixed_state x) \<Longrightarrow>
     pub_owner p = apply_source q \<Longrightarrow> request_key p = apply_key q \<Longrightarrow>
     stock_task_execution N E V C v versions marker paths roles q targets must_ack x A
       (task_acks_initial (required_acks targets (apply_source q) must_ack))"
| cluster:
    "stock_task_execution N E V C v versions marker paths roles q targets must_ack x A a \<Longrightarrow>
     stock_applier_step N E V C v marker paths roles x A y B \<Longrightarrow>
     stock_task_execution N E V C v versions marker paths roles q targets must_ack y B a"
| listener:
    "stock_task_execution N E V C v versions marker paths roles q targets must_ack x A a \<Longrightarrow>
     task_ack_step q (\<lambda>n. node_acknowledgements (A n)) a b \<Longrightarrow>
     stock_task_execution N E V C v versions marker paths roles q targets must_ack x A b"

lemma stock_task_projection:
  assumes run: "stock_task_execution N E V C v versions marker paths roles q targets must_ack x A a"
    and separated: "\<And>n. roles n \<noteq> None \<Longrightarrow> n \<notin> N"
  shows "stock_applier_execution N E V C v versions marker paths roles x A \<and> apply_source q \<in> targets \<and>
    rtranclp (task_ack_step q (\<lambda>n. node_acknowledgements (A n)))
      (task_acks_initial (required_acks targets (apply_source q) must_ack)) a"
  using run
proof induction
  case start
  then show ?case by simp
next
  case (cluster x A a y B)
  from cluster.IH have app: "stock_applier_execution N E V C v versions marker paths roles x A"
    and trace: "rtranclp (task_ack_step q (\<lambda>n. node_acknowledgements (A n)))
      (task_acks_initial (required_acks targets (apply_source q) must_ack)) a" by auto
  have growth: "node_acknowledgements (A n) \<subseteq> node_acknowledgements (B n)" for n
    by (rule stock_applier_ack_history_grows[OF cluster.hyps(2)])
      (use stock_applier_projection[OF app separated] in blast)
  from stock_applier_execution.advance[OF app cluster.hyps(2)] task_ack_trace_weaken[OF trace growth] cluster.IH
  show ?case by blast
next
  case listener
  then show ?case by (blast intro: rtranclp.rtrancl_into_rtrancl)
qed

theorem production_stock_task_success:
  assumes run: "stock_task_execution N E V C v versions marker paths roles q targets must_ack x A a"
    and separated: "\<And>n. roles n \<noteq> None \<Longrightarrow> n \<notin> N"
    and success: "task_ack_result a = Task_Ack_Success"
  obtains d h where "dynamic_reachable C d" "h \<in> quorum_commits d" "owner h = apply_source q" "position h = apply_key q"
    "\<forall>n\<in>required_acks targets (apply_source q) must_ack.
      \<exists>p\<in>quorum_commits d. prefix h p \<and> (\<exists>e. (e,q,position p) \<in> node_acknowledgements (A n))"
proof -
  from stock_task_projection[OF run separated] have app: "stock_applier_execution N E V C v versions marker paths roles x A"
    and publisher: "apply_source q \<in> targets"
    and listener: "rtranclp (task_ack_step q (\<lambda>n. node_acknowledgements (A n)))
      (task_acks_initial (required_acks targets (apply_source q) must_ack)) a" by auto
  from stock_applier_projection[OF app separated] have stock: "stock_reachable N E V C v versions marker paths roles x"
    and traces: "application_reachable n (voting_traffic (mixed_state x)) 0 \<lparr>rank_term = 0, rank_version = (if roles n = None then versions n else 0)\<rparr> (A n)"
      for n by auto
  show thesis
  proof (rule stock_task_success[where initial_term="\<lambda>_. 0"
      and initial_key="\<lambda>n. \<lparr>rank_term = 0, rank_version = (if roles n = None then versions n else 0)\<rparr>", OF stock _ publisher _ listener success])
    show "\<And>n. roles n \<noteq> None \<Longrightarrow> n \<notin> N" by (rule separated)
    show "\<And>n. n \<in> required_acks targets (apply_source q) must_ack \<Longrightarrow>
      application_reachable n (voting_traffic (mixed_state x)) 0 \<lparr>rank_term = 0, rank_version = (if roles n = None then versions n else 0)\<rparr> (A n)"
      by (rule traces)
    fix d h
    assume "dynamic_reachable C d" "h \<in> quorum_commits d" "owner h = apply_source q" "position h = apply_key q"
      "\<forall>n\<in>required_acks targets (apply_source q) must_ack.
        \<exists>p\<in>quorum_commits d. prefix h p \<and> (\<exists>e. (e,q,position p) \<in> node_acknowledgements (A n))"
    then show thesis by (rule that)
  qed
qed

end
