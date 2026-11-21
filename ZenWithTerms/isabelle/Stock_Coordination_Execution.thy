theory Stock_Coordination_Execution
  imports Master_Service_Executors Mixed_Role_Durability
begin

section \<open>Stock batches in a mixed-role execution\<close>

record ('v, 'p) stock_cluster =
  mixed_state :: "('v, 'p) mixed_cluster"
  open_batches :: "node \<Rightarrow> 'v coordinator_state option"

definition stock_initial where
  "stock_initial v versions = \<lparr>mixed_state = mixed_initial v versions, open_batches = (\<lambda>_. None)\<rparr>"

definition keep_stock_batches where
  "keep_stock_batches N E V C v x s' B \<longleftrightarrow>
    (\<forall>n start. B n = Some start \<longrightarrow> open_batches x n = Some start \<and>
      (voting (mixed_state x) = voting s' \<or> batch_step N E V C v n (voting (mixed_state x)) (voting s')))"

definition stock_publication where
  "stock_publication N E V C v x n master mv task changed u begin p \<longleftrightarrow>
    (\<exists>start. open_batches x n = Some start \<and>
      (let input = executor_snapshot start n master mv ();
           r = builtin_result task changed input;
           finish = voting (mixed_state x)
       in executable_task_for input n (current_term (batch_node start n)) task \<and>
          runtime_publication_admission finish n (executor_term r) (executor_version r) u (executor_accepted r) (executor_committed r) \<and>
          n \<in> N \<and> u \<in> V \<and> executor_accepted r \<subseteq> E \<and>
          begin = Begin_Publication n (executor_term r) (executor_version r) u (executor_accepted r) (executor_committed r) True \<and>
          p = request n (executor_term r) (executor_version r) (executor_accepted r) (executor_committed r)))"

text \<open>
  A batch captures the actual voting state of this execution. Interleaved
  work can retain that capture across allowed Coordinator transitions,
  or drop it if the batch is abandoned. Every new transport registration
  is produced by the stock publication rule. Failed starts that create
  no registration are part of the background projection.
\<close>

inductive stock_step for N E V C v marker paths roles where
  capture:
    "open_batches x n = None \<Longrightarrow> batch_slot (voting (mixed_state x)) n = None \<Longrightarrow>
     election_won (batch_node (voting (mixed_state x)) n) \<Longrightarrow>
     stock_step N E V C v marker paths roles x (x\<lparr>open_batches := (open_batches x)(n := Some (voting (mixed_state x)))\<rparr>)"
| background:
    "mixed_step N E V C v marker paths roles (mixed_state x) s' \<Longrightarrow>
     (\<And>p u. Registered_State p u \<in> voting_traffic s' \<Longrightarrow> Registered_State p u \<in> voting_traffic (mixed_state x)) \<Longrightarrow>
     keep_stock_batches N E V C v x s' B \<Longrightarrow>
     stock_step N E V C v marker paths roles x (\<lparr>mixed_state = s', open_batches = B\<rparr>)"
| install:
    "stock_publication N E V C v x n master mv task changed u begin p \<Longrightarrow>
     s' = (mixed_state x)\<lparr>voting := coordinator_execute N E (voting (mixed_state x)) begin,
        voting_traffic := insert (Registered_State p u) (voting_traffic (mixed_state x))\<rparr> \<Longrightarrow>
     keep_stock_batches N E V C v x s' B \<Longrightarrow> B n = None \<Longrightarrow>
     stock_step N E V C v marker paths roles x (\<lparr>mixed_state = s', open_batches = B\<rparr>)"

inductive stock_reachable for N E V C v versions marker paths roles where
  init:
    "mixed_reachable N E V C v versions marker paths roles (mixed_initial v versions) \<Longrightarrow>
     stock_reachable N E V C v versions marker paths roles (stock_initial v versions)"
| step:
    "stock_reachable N E V C v versions marker paths roles x \<Longrightarrow>
     stock_step N E V C v marker paths roles x y \<Longrightarrow> stock_reachable N E V C v versions marker paths roles y"

definition valid_stock_batches where
  "valid_stock_batches N E V C v versions x \<longleftrightarrow>
    (\<forall>n start. open_batches x n = Some start \<longrightarrow>
      coordinator_reachable N E V C v versions start \<and> batch_slot start n = None \<and>
      election_won (batch_node start n) \<and>
      rtranclp (batch_step N E V C v n) start (voting (mixed_state x)))"

lemma kept_stock_batches_valid:
  assumes "valid_stock_batches N E V C v versions x" "keep_stock_batches N E V C v x s' B"
  shows "valid_stock_batches N E V C v versions \<lparr>mixed_state = s', open_batches = B\<rparr>"
  unfolding valid_stock_batches_def
proof (simp only: stock_cluster.select_convs, intro allI impI)
  fix n start
  assume "B n = Some start"
  with assms(2) have captured: "open_batches x n = Some start" and advance:
    "voting (mixed_state x) = voting s' \<or> batch_step N E V C v n (voting (mixed_state x)) (voting s')"
    unfolding keep_stock_batches_def by blast+
  from assms(1) captured have ready: "coordinator_reachable N E V C v versions start"
    "batch_slot start n = None" "election_won (batch_node start n)"
    and path: "rtranclp (batch_step N E V C v n) start (voting (mixed_state x))"
    unfolding valid_stock_batches_def by blast+
  from advance path have "rtranclp (batch_step N E V C v n) start (voting s')"
    by (elim disjE) (simp, rule rtranclp.rtrancl_into_rtrancl)
  with ready show "coordinator_reachable N E V C v versions start \<and> batch_slot start n = None \<and>
    election_won (batch_node start n) \<and> rtranclp (batch_step N E V C v n) start (voting s')" by blast
qed

lemma valid_stock_publication:
  assumes batches: "valid_stock_batches N E V C v versions x"
    and produced: "stock_publication N E V C v x n master mv task changed u begin p"
  obtains start and r :: "('v, unit) executor_state" where "open_batches x n = Some start"
    "executor_parent r = accepted_base (batch_node (voting (mixed_state x)) n)"
    "executor_parent r = accepted_base (batch_node start n)"
    "begin = Begin_Publication n (executor_term r) (executor_version r) u (executor_accepted r) (executor_committed r) True"
    "p = request n (executor_term r) (executor_version r) (executor_accepted r) (executor_committed r)"
    "coordinator_enabled N E V C v (voting (mixed_state x)) begin"
proof -
  let ?finish = "voting (mixed_state x)"
  obtain start where slot: "open_batches x n = Some start" and args:
    "executable_task_for (executor_snapshot start n master mv ()) n (current_term (batch_node start n)) task"
    "runtime_publication_admission ?finish n
      (executor_term (builtin_result task changed (executor_snapshot start n master mv ())))
      (executor_version (builtin_result task changed (executor_snapshot start n master mv ()))) u
      (executor_accepted (builtin_result task changed (executor_snapshot start n master mv ())))
      (executor_committed (builtin_result task changed (executor_snapshot start n master mv ())))"
    "n \<in> N" "u \<in> V"
    "executor_accepted (builtin_result task changed (executor_snapshot start n master mv ())) \<subseteq> E"
    "begin = Begin_Publication n
      (executor_term (builtin_result task changed (executor_snapshot start n master mv ())))
      (executor_version (builtin_result task changed (executor_snapshot start n master mv ()))) u
      (executor_accepted (builtin_result task changed (executor_snapshot start n master mv ())))
      (executor_committed (builtin_result task changed (executor_snapshot start n master mv ()))) True"
    "p = request n
      (executor_term (builtin_result task changed (executor_snapshot start n master mv ())))
      (executor_version (builtin_result task changed (executor_snapshot start n master mv ())))
      (executor_accepted (builtin_result task changed (executor_snapshot start n master mv ())))
      (executor_committed (builtin_result task changed (executor_snapshot start n master mv ())))"
    using produced unfolding stock_publication_def Let_def by blast
  let ?r = "builtin_result task changed (executor_snapshot start n master mv ())"
  from batches slot have capture: "coordinator_reachable N E V C v versions start"
    "batch_slot start n = None" "election_won (batch_node start n)"
    "rtranclp (batch_step N E V C v n) start ?finish" unfolding valid_stock_batches_def by blast+
  note valid = admitted_builtin_executor_refines_publication[OF capture(4,1,2,3) args(1,2,3,4,5)]
  have parent: "executor_parent ?r = accepted_base (batch_node start n)"
    using builtin_publication_fields(1)[OF args(1), of changed] by (simp add: executor_snapshot_def)
  have enabled: "coordinator_enabled N E V C v ?finish begin"
    unfolding args(6) by (rule valid(2))
  from that[of start "?r"] slot valid(1) parent args(6,7) enabled show thesis by blast
qed

lemma stock_install_is_mixed_step:
  fixes x :: "('v, 'p) stock_cluster"
  assumes batches: "valid_stock_batches N E V C v versions x"
    and publication: "stock_publication N E V C v x n master mv task changed u begin p"
  shows "mixed_step N E V C v marker paths roles (mixed_state x)
    ((mixed_state x)\<lparr>voting := coordinator_execute N E (voting (mixed_state x)) begin,
      voting_traffic := insert (Registered_State p u) (voting_traffic (mixed_state x))\<rparr>)"
proof -
  obtain start and r :: "('v, unit) executor_state" where
    "open_batches x n = Some start"
    "executor_parent r = accepted_base (batch_node (voting (mixed_state x)) n)"
    "executor_parent r = accepted_base (batch_node start n)"
    and event: "begin = Begin_Publication n (executor_term r) (executor_version r) u (executor_accepted r) (executor_committed r) True"
    and packet: "p = request n (executor_term r) (executor_version r) (executor_accepted r) (executor_committed r)"
    and enabled: "coordinator_enabled N E V C v (voting (mixed_state x)) begin"
    by (rule valid_stock_publication[OF batches publication])
  show ?thesis
  proof (rule mixed_step.voting_transient)
    from enabled show "transport_step N E V C v (voting (mixed_state x)) (voting_traffic (mixed_state x))
      (coordinator_execute N E (voting (mixed_state x)) begin) (insert (Registered_State p u) (voting_traffic (mixed_state x)))"
      unfolding event packet by (rule transport_step.begin_publication)
    show "node_disk (coordinator_execute N E (voting (mixed_state x)) begin) = node_disk (voting (mixed_state x))"
      unfolding event by (rule non_dispatch_keeps_disk) simp
  qed
qed

lemma stock_execution_projection:
  assumes separated: "\<And>n. roles n \<noteq> None \<Longrightarrow> n \<notin> N"
    and run: "stock_reachable N E V C v versions marker paths roles x"
  shows "mixed_reachable N E V C v versions marker paths roles (mixed_state x) \<and>
    valid_stock_batches N E V C v versions x"
  using run
proof induction
  case init
  then show ?case by (simp add: stock_initial_def valid_stock_batches_def)
next
  case (step x y)
  from step.IH have run: "mixed_reachable N E V C v versions marker paths roles (mixed_state x)"
    and batches: "valid_stock_batches N E V C v versions x" by auto
  show ?case using step.hyps(2)
  proof cases
    case capture
    have reach: "transport_reachable N E V C v versions (voting (mixed_state x)) (voting_traffic (mixed_state x))"
      using durable_execution_invariants[OF mixed_role_durability[OF separated run]] by blast
    from transport_invariants[OF reach] have "coordinator_reachable N E V C v versions (voting (mixed_state x))" by blast
    with capture run batches show ?thesis by (auto simp: valid_stock_batches_def)
  next
    case background
    then show ?thesis using run kept_stock_batches_valid[OF batches]
      by (auto intro: mixed_reachable.step)
  next
    case install
    have mixed: "mixed_step N E V C v marker paths roles (mixed_state x) (mixed_state y)"
      using stock_install_is_mixed_step[OF batches install(2)] install(1,3) by simp
    from mixed_reachable.step[OF run mixed] kept_stock_batches_valid[OF batches install(4)] install(1) show ?thesis by simp
  qed
qed

theorem stock_execution_refines_tla:
  assumes separated: "\<And>n. roles n \<noteq> None \<Longrightarrow> n \<notin> N"
    and run: "stock_reachable N E V C v versions marker paths roles x"
  shows "\<exists>t. tla_reachable N V C v versions t \<and> configurations_ok E t \<and>
    coordination (voting (mixed_state x)) = project_java E t"
  using stock_execution_projection[OF separated run]
  by (blast intro: mixed_role_refines_tla[OF separated])

corollary stock_execution_publication_parent:
  assumes separated: "\<And>n. roles n \<noteq> None \<Longrightarrow> n \<notin> N"
    and run: "stock_reachable N E V C v versions marker paths roles x"
    and produced: "stock_publication N E V C v x n master mv task changed u begin p"
  obtains start and r :: "('v, unit) executor_state" where "open_batches x n = Some start"
    "executor_parent r = accepted_base (batch_node (voting (mixed_state x)) n)"
    "executor_parent r = accepted_base (batch_node start n)"
    "p = request n (executor_term r) (executor_version r) (executor_accepted r) (executor_committed r)"
    "coordinator_enabled N E V C v (voting (mixed_state x)) begin"
  using stock_execution_projection[OF separated run] valid_stock_publication[OF _ produced] that by blast

theorem stock_registration_uses_captured_parent:
  assumes separated: "\<And>n. roles n \<noteq> None \<Longrightarrow> n \<notin> N"
    and run: "stock_reachable N E V C v versions marker paths roles x"
    and step: "stock_step N E V C v marker paths roles x y"
    and added: "Registered_State p u \<in> voting_traffic (mixed_state y)"
      "Registered_State p u \<notin> voting_traffic (mixed_state x)"
  obtains n start and r :: "('v, unit) executor_state" where "open_batches x n = Some start"
    "p = request n (executor_term r) (executor_version r) (executor_accepted r) (executor_committed r)"
    "executor_parent r = accepted_base (batch_node start n)"
    "executor_parent r = accepted_base (batch_node (voting (mixed_state x)) n)"
  using step
proof cases
  case capture
  with added show thesis by simp
next
  case background
  with added show thesis by auto
next
  case (install n master mv task changed payload event registered s' B)
  from install added have produced: "stock_publication N E V C v x n master mv task changed u event p"
    by auto
  from stock_execution_publication_parent[OF separated run produced] that show thesis by blast
qed

end
