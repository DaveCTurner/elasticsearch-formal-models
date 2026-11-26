theory Coordination_State_Refinement
  imports Coordination_State_Java Zen_With_Terms_Refinement
begin

section \<open>Relating the Java transcription to the TLA+ translation\<close>

text \<open>
  A Java call that changes the state is a step of the TLA+ translation. The Java state of a
  TLA+ state \<open>s\<close> is \<open>project_java s\<close>: the in-memory state of each node (its \<open>memory_state\<close>),
  what each node has on disk (the persisted fields of its \<open>nodes_at\<close>), and the messages. The
  TLA+ action that a Java call performs is \<open>abstract_action\<close>. The Java call must also respect
  the caller contract of \<open>Coordination_State_Java\<close>.
\<close>

fun abstract_action :: "'v java_action \<Rightarrow> 'v tla_action" where
  "abstract_action (Java_Set_Initial_State
                        node
                        initial_position
                        new_value
                        initial_accepted_config
                        initial_committed_config)
   =
    Set_Initial_State node"
| "abstract_action (Java_Handle_Start_Join voter candidate new_term)
   = Handle_Start_Join voter candidate new_term"
| "abstract_action (Java_Handle_Join voter voter_role candidate join_term voter_position)
   = Handle_Join voter voter_role candidate join_term voter_position"
| "abstract_action (Java_Handle_Client_Value
                        leader
                        new_term
                        version
                        new_value
                        new_config
                        previous_config)
   =
    Handle_Client_Value leader new_term version new_value new_config"
| "abstract_action (Java_Handle_Publish_Request node request new_value)
   = Handle_Publish_Request node request new_value"
| "abstract_action (Java_Handle_Publish_Response voter voter_role leader position)
   = Handle_Publish_Response voter voter_role leader position"
| "abstract_action (Java_Handle_Commit node leader position) = Handle_Commit leader node position"
| "abstract_action (Java_Restart node new_role new_value) = Restart_Node node new_role"
| "abstract_action (Java_Persist_Term node) = Persist_Term node"
| "abstract_action (Java_Persist_State node) = Persist_State node"

definition project_java :: "'v tla_state \<Rightarrow> 'v java_state" where
  "project_java state =
    \<lparr>
      java_memory   = memory_state state,
      java_disk     = (\<lambda>node. disk_of (nodes_at state node)),
      java_messages = messages state
    \<rparr>"

lemma project_java_select[simp]:
  "java_memory (project_java s) n = memory_state s n"
  "java_disk (project_java s) n = disk_of (nodes_at s n)"
  "java_messages (project_java s) = messages s"
  by (simp_all add: project_java_def)

lemma has_quorum_eq: "has_quorum D Q = quorum D Q"
  unfolding has_quorum_def quorum_def majority_def by auto

lemma empty_votes_before_bootstrap:
  assumes "tla_reachable initial_configuration initial_value versions s"
  shows "last_accepted_configuration (nodes_at s n) = {} \<Longrightarrow>
    join_votes (nodes_at s n) = {} \<and> publish_votes (nodes_at s n) = {}"
  using assms
proof (induction arbitrary: n rule: tla_reachable.induct)
  case init
  show ?case by (simp add: tla_initial_def initial_node_def)
next
  case (advance s a)
  obtain d where "linked initial_configuration s d" using tla_dynamic_refinement[OF advance.hyps(1)] by blast
  then have pub: "Publish_Msg i p v \<in> messages s \<Longrightarrow> publication_config p \<noteq> {}" for i p v
    using linkedD(3)[of initial_configuration s d "Publish_Msg i p v"] by simp
  have won: "election_won (nodes_at s i) \<Longrightarrow> last_accepted_configuration (nodes_at s i) \<noteq> {}" for i
    using node_linkD(9)[OF linkedD(1)[OF \<open>linked initial_configuration s d\<close>, of i]]
    unfolding is_election_quorum_def by (auto dest: quorum_nonempty)
  from advance.hyps(2) advance.IH advance.prems pub won
  show ?case
    by (cases a) (auto simp: Let_def put_node_def put_memory_def put_memory_state_def memory_state_def
        reset_transient_def restarted_disk_def restarted_memory_def empty_node_def loaded_node_def
        queue_term_def queue_state_def split: if_splits)
qed

text \<open>
  The quorum checks of the default election strategy agree with the TLA+ definitions.
\<close>

locale default_strategy =
  fixes initial_configuration :: config
  assumes initial_config: "initial_configuration \<subseteq> range ConfigNode" "initial_configuration \<noteq> {}"
begin

declare [[record_sort_updates = true]]

lemma election_eq: "java_is_election_quorum x Q = is_election_quorum x Q"
  by (simp add: java_is_election_quorum_def is_election_quorum_def has_quorum_eq)

lemma response_eq: "java_is_publish_quorum x Q = is_publish_quorum x Q"
  by (simp add: java_is_publish_quorum_def is_publish_quorum_def has_quorum_eq)

section \<open>Simulation of each call that changes the state\<close>

text \<open>
  If a call changes the state, and the caller contract holds, then the matching TLA+
  action is enabled and its result is the projection of the Java result. A call that
  changes nothing is a stuttering step. The conditions that the call checks are the ones
  that it passes to \<open>java_put\<close> or \<open>java_persist\<close>, and they are what makes the TLA+ action enabled.
\<close>

lemma commit_configuration_unchanged:
  assumes "node_role (nodes_at s n) = Master_Eligible"
  assumes "last_committed_configuration (nodes_at s n) = last_accepted_configuration (nodes_at s n)"
  shows "java_call (project_java s) (Java_Handle_Commit n c k) = project_java s"
proof -
  have master: "memory_state s n = nodes_at s n" using assms(1) by (simp add: memory_state_def)
  have same: "(nodes_at s n)\<lparr>last_committed_configuration := last_accepted_configuration (nodes_at s n)\<rparr> = nodes_at s n"
    using assms(2) by (cases "nodes_at s n") auto
  show ?thesis
    using assms(1) master same
    by (auto simp: project_java_def java_put_def Let_def queue_state_def fun_eq_iff)
qed

theorem changing_call_simulates:
  assumes reach: "tla_reachable initial_configuration initial_value versions s"
  assumes changes: "java_call (project_java s) a \<noteq> project_java s"
  assumes caller: "caller_contract initial_configuration initial_value (project_java s) a"
  shows "enabled s (abstract_action a)
         \<and> java_call (project_java s) a = project_java (execute
                                                            initial_configuration
                                                            initial_value
                                                            s
                                                            (abstract_action a))"
proof -
  obtain d where linked: "linked initial_configuration s d" using tla_dynamic_refinement[OF reach] by blast
  have role_memory: "node_role (memory_state s n) = node_role (nodes_at s n)" for n
    using linkedD(6)[OF linked, of n] by (simp add: memory_state_def)
  have master_of: "node_role (memory_state s n) = Master_Eligible \<Longrightarrow> node_role (nodes_at s n) = Master_Eligible" for n
    using role_memory by simp
  have mem_master: "node_role (nodes_at s n) = Master_Eligible \<Longrightarrow> memory_state s n = nodes_at s n" for n
    by (simp add: memory_state_def)
  have mem_other: "node_role (nodes_at s n) \<noteq> Master_Eligible \<Longrightarrow> memory_state s n = memory_at s n" for n
    by (simp add: memory_state_def)
  show ?thesis
  proof (cases a)
    case (Java_Set_Initial_State n k v D F)
    note checks = java_put_changed[OF changes[unfolded Java_Set_Initial_State java_call.simps Let_def], simplified]
    from caller Java_Set_Initial_State have master_mem: "node_role (memory_state s n) = Master_Eligible"
      by (simp add: Let_def)
    then have master: "node_role (nodes_at s n) = Master_Eligible" by (rule master_of)
    note mm = mem_master[OF master]
    from checks mm have empty: "last_accepted_configuration (nodes_at s n) = {}" by simp
    from caller mm Java_Set_Initial_State have e: "enabled s (Set_Initial_State n)"
      and args: "k = last_accepted_position (nodes_at s n)" "v = initial_value" "D = initial_configuration" "F = initial_configuration"
      using empty_votes_before_bootstrap[OF reach empty] master empty by (auto simp: Let_def)
    have commutes: "java_call (project_java s) a = project_java (execute
                                                                     initial_configuration
                                                                     initial_value
                                                                     s
                                                                     (Set_Initial_State n))"
      using master mm empty
      by (auto simp: Java_Set_Initial_State args project_java_def java_put_def put_node_def memory_state_def
          disk_of_def fun_eq_iff)
    show ?thesis using Java_Set_Initial_State e commutes by simp
  next
    case (Java_Handle_Start_Join n c t)
    note checks = java_put_changed[OF changes[unfolded Java_Handle_Start_Join java_call.simps Let_def], simplified]
    from caller checks Java_Handle_Start_Join have e: "enabled s (Handle_Start_Join n c t)" by (simp add: Let_def)
    have commutes: "java_call (project_java s) a = project_java (execute
                                                                     initial_configuration
                                                                     initial_value
                                                                     s
                                                                     (Handle_Start_Join n c t))"
    proof (cases "node_role (nodes_at s n) = Master_Eligible")
      case True
      then show ?thesis using checks
        by (auto simp: Java_Handle_Start_Join project_java_def java_put_def put_node_def put_memory_state_def
            memory_state_def disk_of_def queue_term_def reset_transient_def Let_def fun_eq_iff)
    next
      case False
      then show ?thesis using checks linkedD(6)[OF linked, of n]
        by (auto simp: Java_Handle_Start_Join project_java_def java_put_def put_node_def put_memory_def
            put_memory_state_def memory_state_def disk_of_def queue_term_def reset_transient_def
            Let_def fun_eq_iff)
    qed
    show ?thesis using Java_Handle_Start_Join e commutes by simp
  next
    case (Java_Handle_Join n nr c t k)
    note checks = java_put_changed[OF changes[unfolded Java_Handle_Join java_call.simps Let_def], simplified]
    from caller Java_Handle_Join have master_mem: "node_role (memory_state s c) = Master_Eligible"
      by (simp add: Let_def)
    then have master: "node_role (nodes_at s c) = Master_Eligible" by (rule master_of)
    note mm = mem_master[OF master]
    from caller checks mm master Java_Handle_Join have e: "enabled s (Handle_Join n nr c t k)"
      by (simp add: Let_def)
    have outcomes: "\<And>Q. java_is_election_quorum (nodes_at s c) Q = is_election_quorum (nodes_at s c) Q"
      by (rule election_eq)
    have commutes: "java_call (project_java s) a = project_java (execute
                                                                     initial_configuration
                                                                     initial_value
                                                                     s
                                                                     (Handle_Join n nr c t k))"
      using checks mm master outcomes
      by (auto simp: Java_Handle_Join project_java_def java_put_def put_node_def memory_state_def disk_of_def
          Let_def fun_eq_iff)
    show ?thesis using Java_Handle_Join e commutes by simp
  next
    case (Java_Handle_Client_Value n t v x D F)
    note checks = java_put_changed[OF changes[unfolded Java_Handle_Client_Value java_call.simps Let_def], simplified]
    from caller Java_Handle_Client_Value have master_mem: "node_role (memory_state s n) = Master_Eligible"
      and sub: "D \<subseteq> range ConfigNode" and F: "F = last_committed_configuration (memory_state s n)"
      by (auto simp: Let_def)
    then have master: "node_role (nodes_at s n) = Master_Eligible" by (auto intro: master_of)
    note mm = mem_master[OF master]
    have "quorum D (join_votes (nodes_at s n))" using checks mm Java_Handle_Client_Value
      by (simp add: Let_def has_quorum_eq)
    then have "D \<noteq> {}" by (rule quorum_nonempty)
    with checks caller mm master Java_Handle_Client_Value sub
    have e: "enabled s (Handle_Client_Value n t v x D)"
      by (auto simp: Let_def has_quorum_eq)
    have commutes: "java_call (project_java s) a = project_java (execute
                                                                     initial_configuration
                                                                     initial_value
                                                                     s
                                                                     (Handle_Client_Value n t v x D))"
      using checks mm master F
      by (auto simp: Java_Handle_Client_Value project_java_def java_put_def put_node_def memory_state_def
          disk_of_def Let_def fun_eq_iff)
    show ?thesis using Java_Handle_Client_Value e commutes by simp
  next
    case (Java_Handle_Publish_Request n p x)
    note checks = java_put_changed[OF changes[unfolded Java_Handle_Publish_Request java_call.simps Let_def], simplified]
    from caller Java_Handle_Publish_Request have cfg: "publication_config p \<subseteq> range ConfigNode" "publication_previous_config p \<subseteq> range ConfigNode"
      by (auto simp: Let_def)
    from caller checks Java_Handle_Publish_Request
    have e: "enabled s (Handle_Publish_Request n p x)"
      by (auto simp: Let_def)
    have commutes: "java_call (project_java s) a = project_java (execute
                                                                     initial_configuration
                                                                     initial_value
                                                                     s
                                                                     (Handle_Publish_Request n p x))"
    proof (cases "node_role (nodes_at s n) = Master_Eligible")
      case True
      then show ?thesis using checks
        by (auto simp: Java_Handle_Publish_Request project_java_def java_put_def put_node_def put_memory_state_def
            memory_state_def disk_of_def queue_state_def Let_def fun_eq_iff)
    next
      case False
      then show ?thesis using checks linkedD(6)[OF linked, of n]
        by (auto simp: Java_Handle_Publish_Request project_java_def java_put_def put_node_def put_memory_def
            put_memory_state_def memory_state_def disk_of_def queue_state_def Let_def fun_eq_iff)
    qed
    show ?thesis using Java_Handle_Publish_Request e commutes by simp
  next
    case (Java_Handle_Publish_Response n nr c k)
    note checks = java_put_changed[OF changes[unfolded Java_Handle_Publish_Response java_call.simps Let_def], simplified]
    from caller Java_Handle_Publish_Response have master_mem: "node_role (memory_state s c) = Master_Eligible"
      by (simp add: Let_def)
    then have master: "node_role (nodes_at s c) = Master_Eligible" by (rule master_of)
    note mm = mem_master[OF master]
    from caller checks mm master Java_Handle_Publish_Response
    have e: "enabled s (Handle_Publish_Response n nr c k)"
      by (simp add: Let_def)
    have outcomes: "\<And>Q. java_is_publish_quorum (nodes_at s c) Q = is_publish_quorum (nodes_at s c) Q"
      by (rule response_eq)
    have commutes: "java_call (project_java s) a = project_java (execute
                                                                     initial_configuration
                                                                     initial_value
                                                                     s
                                                                     (Handle_Publish_Response
                                                                          n
                                                                          nr
                                                                          c
                                                                          k))"
      using checks mm master outcomes
      by (auto simp: Java_Handle_Publish_Response project_java_def java_put_def put_node_def memory_state_def
          disk_of_def Let_def fun_eq_iff split: if_splits)
    show ?thesis using Java_Handle_Publish_Response e commutes by simp
  next
    case (Java_Handle_Commit n c k)
    note checks = java_put_changed[OF changes[unfolded Java_Handle_Commit java_call.simps Let_def], simplified]
    show ?thesis
    proof (cases "node_role (nodes_at s n) = Master_Eligible
                  \<and> election_won (nodes_at s n)
                  \<and> position_version k \<noteq> last_published_version (nodes_at s n)")
      case True
      then have master: "node_role (nodes_at s n) = Master_Eligible"
        and won: "election_won (nodes_at s n)" and late: "position_version k \<noteq> last_published_version (nodes_at s n)"
        by simp_all
      from caller Java_Handle_Commit mem_master[OF master] won late
      have local: "last_committed_configuration (nodes_at s n) = last_accepted_configuration (nodes_at s n)"
        by (simp add: Let_def)
      from commit_configuration_unchanged[OF master local, where c = c and k = k]
      have "java_call (project_java s) a = project_java s" by (simp add: Java_Handle_Commit)
      with changes show ?thesis by contradiction
    next
      case False
      have e: "enabled s (Handle_Commit c n k)"
      proof (cases "node_role (nodes_at s n) = Master_Eligible")
        case True
        with False have "\<not> election_won (nodes_at s n)
                         \<or> position_version k = last_published_version (nodes_at s n)" by auto
        then show ?thesis using caller checks mem_master[OF True] Java_Handle_Commit by (auto simp: Let_def)
      next
        case False
        then have "\<not> election_won (memory_at s n)" using linkedD(8)[OF linked, of n] by simp
        then show ?thesis using caller checks mem_other[OF False] Java_Handle_Commit by (auto simp: Let_def)
      qed
      have commutes: "java_call (project_java s) a = project_java (execute
                                                                       initial_configuration
                                                                       initial_value
                                                                       s
                                                                       (Handle_Commit c n k))"
      proof (cases "node_role (nodes_at s n) = Master_Eligible")
        case True
        then show ?thesis using checks
          by (auto simp: Java_Handle_Commit project_java_def java_put_def put_node_def put_memory_state_def
              memory_state_def disk_of_def queue_state_def Let_def fun_eq_iff)
      next
        case False
        then show ?thesis using checks linkedD(6)[OF linked, of n]
          by (auto simp: Java_Handle_Commit project_java_def java_put_def put_node_def put_memory_def
              put_memory_state_def memory_state_def disk_of_def queue_state_def Let_def fun_eq_iff)
      qed
      show ?thesis using Java_Handle_Commit e commutes by simp
    qed
  next
    case (Java_Restart n r u)
    from caller Java_Restart have e: "enabled s (Restart_Node n r)" and same: "u = initial_value" by simp_all
    have commutes: "java_call (project_java s) a = project_java (execute
                                                                     initial_configuration
                                                                     initial_value
                                                                     s
                                                                     (Restart_Node n r))"
      using same
    proof (cases "r = Coordinating_Only")
      case True
      show ?thesis
      proof (cases "current_term (nodes_at s n) = 0")
        case True
        with \<open>r = Coordinating_Only\<close> show ?thesis
          by (auto simp: Java_Restart same project_java_def restarted_disk_def restarted_memory_def
              empty_node_def memory_of_disk_def empty_disk_def reset_transient_def put_node_def
              memory_state_def disk_of_def Let_def fun_eq_iff split: if_splits)
      next
        case False
        with \<open>r = Coordinating_Only\<close> show ?thesis
          by (auto simp: Java_Restart same project_java_def restarted_disk_def restarted_memory_def
              empty_node_def loaded_node_def memory_of_disk_def empty_disk_def reset_transient_def put_node_def
              memory_state_def disk_of_def Let_def fun_eq_iff split: if_splits)
      qed
    next
      case False
      then show ?thesis
        by (auto simp: Java_Restart same project_java_def restarted_disk_def restarted_memory_def
            loaded_node_def memory_of_disk_def reset_transient_def put_node_def memory_state_def disk_of_def
            Let_def fun_eq_iff)
    qed
    show ?thesis using Java_Restart e commutes by simp
  next
    case (Java_Persist_Term n)
    note checks = java_persist_changed[OF changes[unfolded Java_Persist_Term java_call.simps Let_def], simplified]
    have data: "node_role (nodes_at s n) = Data_Only"
      using checks role_memory[of n] by simp
    have e: "enabled s (Persist_Term n)"
      using checks mem_other[of n] data by (simp add: Let_def disk_of_def)
    have commutes: "java_call (project_java s) a = project_java (execute
                                                                     initial_configuration
                                                                     initial_value
                                                                     s
                                                                     (Persist_Term n))"
      using checks data mem_other[of n]
      by (auto simp: Java_Persist_Term project_java_def java_persist_def put_node_def memory_state_def disk_of_def
          Let_def fun_eq_iff)
    show ?thesis using Java_Persist_Term e commutes by simp
  next
    case (Java_Persist_State n)
    note checks = java_persist_changed[OF changes[unfolded Java_Persist_State java_call.simps Let_def], simplified]
    have data: "node_role (nodes_at s n) = Data_Only"
      using checks role_memory[of n] by simp
    have e: "enabled s (Persist_State n)"
      using checks mem_other[of n] data by (simp add: Let_def disk_of_def)
    have commutes: "java_call (project_java s) a = project_java (execute
                                                                     initial_configuration
                                                                     initial_value
                                                                     s
                                                                     (Persist_State n))"
      using checks data mem_other[of n]
      by (auto simp: Java_Persist_State project_java_def java_persist_def put_node_def memory_state_def disk_of_def
          Let_def fun_eq_iff)
    show ?thesis using Java_Persist_State e commutes by simp
  qed
qed

end

theorem coordination_state_refines_tla:
  assumes reach: "java_reachable initial_configuration initial_value versions j"
  shows "\<exists>s. tla_reachable initial_configuration initial_value versions s
             \<and> j = project_java s"
  using reach
proof (induction rule: java_reachable.induct)
  case init
  have "tla_reachable
            initial_configuration
            initial_value
            versions
            (tla_initial initial_value versions)"
    by (rule tla_reachable.init[OF init.hyps(1,2)])
  then show ?case by (intro exI[of _ "tla_initial initial_value versions"])
    (auto simp: tla_initial_def initial_node_def java_initial_def project_java_def
      memory_state_def disk_of_def fun_eq_iff)
next
  case (advance j a)
  from advance.IH obtain s where s: "tla_reachable initial_configuration initial_value versions s"
    "j = project_java s" by blast
  have "default_strategy initial_configuration" using advance.hyps(1)
    by (induction rule: java_reachable.induct) (auto simp: default_strategy_def)
  then interpret default_strategy initial_configuration .
  show ?case
  proof (cases "java_call j a = j")
    case True
    with s show ?thesis by (intro exI[of _ s]) simp
  next
    case False
    then have changes: "java_call (project_java s) a \<noteq> project_java s"
      and good: "caller_contract initial_configuration initial_value (project_java s) a"
      using advance.hyps(2) s(2) by auto
    from changing_call_simulates[OF s(1) changes good]
    show ?thesis using s by (intro exI[of _ "execute
                                                 initial_configuration
                                                 initial_value
                                                 s
                                                 (abstract_action a)"])
      (auto intro: tla_reachable.advance)
  qed
qed

section \<open>Correctness of the Java model\<close>

text \<open>
  The safety properties of the protocol hold of every state that the Java model can reach, that is,
  after any sequence of calls that respects the caller contract, with arbitrary restarts, delays,
  duplication and reordering of messages. The messages that a node can ever receive are those in
  the messages set.

  \<^item> The nodes never disagree about who leads. Two nodes that have won an election in the same
    term are the same node, and any two publication requests in the same term come from the same
    leader. A node that won, and then lost its election state by restarting or moving to a
    later term, still has its publication requests in the messages.
  \<^item> The nodes never disagree about what was published. Two publication requests with the same
    position (term and version) are the same request, and carry the same value.
  \<^item> The committed history never diverges. The positions of any two committed publications are
    the same, or one was published as a descendant of the other: they are related by the symmetric
    reflexive closure of \<open>descends\<close>. The Java state does not record ancestry, so \<open>descends\<close> is
    the \<open>descendant\<close> history variable of the TLA+ specification, in the TLA+ state that the Java
    state is the projection of.

  A publication is committed when a commit for its position is in the messages.

  The theorems are in the locale \<open>java_run\<close>, which fixes a reachable Java state \<open>j\<close>:
  \<open>one_leader_per_term\<close>, \<open>one_publisher_per_term\<close>, \<open>publications_agree\<close> and
  \<open>committed_history_never_diverges\<close>.
\<close>

definition java_committed :: "'v java_state \<Rightarrow> publication \<Rightarrow> bool" where
  "java_committed state request \<longleftrightarrow>
    (\<exists>leader destination.
      Commit_Msg leader destination (publication_position request) \<in> java_messages state)"

locale java_run =
  fixes initial_configuration :: config
  fixes initial_value :: 'v
  fixes versions :: "node \<Rightarrow> nat"
  fixes j :: "'v java_state"
  assumes reach: "java_reachable initial_configuration initial_value versions j"
begin

text \<open>
  The TLA+ state that the Java state is the projection of. Its nodes and its messages are those
  of the Java state.
\<close>

definition tla_state :: "'v tla_state" where
  "tla_state = (SOME s. tla_reachable initial_configuration initial_value versions s
                \<and> j = project_java s)"

lemma tla_state:
  shows "tla_reachable initial_configuration initial_value versions tla_state"
    and "java_memory j = memory_state tla_state"
    and "java_messages j = messages tla_state"
proof -
  have "\<exists>s. tla_reachable initial_configuration initial_value versions s \<and> j = project_java s"
    using coordination_state_refines_tla[OF reach] by blast
  then have "tla_reachable initial_configuration initial_value versions tla_state
             \<and> j = project_java tla_state"
    unfolding tla_state_def by (rule someI_ex)
  then have reachable: "tla_reachable initial_configuration initial_value versions tla_state"
    and projection: "j = project_java tla_state"
    by simp_all
  show "tla_reachable initial_configuration initial_value versions tla_state" by (rule reachable)
  have "java_memory j = java_memory (project_java tla_state)" by (rule arg_cong[OF projection])
  then show "java_memory j = memory_state tla_state" by (simp add: project_java_def)
  have "java_messages j = java_messages (project_java tla_state)" by (rule arg_cong[OF projection])
  then show "java_messages j = messages tla_state" by (simp add: project_java_def)
qed

text \<open>
  A publication request is published, with a value, when it is in the messages in a message to
  some node.
\<close>

definition is_Published :: "publication \<Rightarrow> 'v \<Rightarrow> bool" where
  "is_Published request value \<longleftrightarrow>
    (\<exists>destination. Publish_Msg destination request value \<in> java_messages j)"

text \<open>
  The positions of published states, related to the positions of the states that they were published
  on top of, and the positions of those states' ancestors. This is the TLA+ history variable
  \<open>descendant\<close>, which has no counterpart in the Java state.
\<close>

definition descends :: "(position \<times> position) set" where
  "descends = descendant tla_state"

theorem one_leader_per_term:
  fixes node_1 node_2 :: node
  defines node_state_1_def: "node_state_1 \<equiv> java_memory j node_1"
  defines node_state_2_def: "node_state_2 \<equiv> java_memory j node_2"
  assumes won_1: "election_won node_state_1"
  assumes won_2: "election_won node_state_2"
  assumes same_term: "current_term node_state_1 = current_term node_state_2"
  shows "node_1 = node_2"
proof -
  obtain a where linked: "linked initial_configuration tla_state a" using tla_dynamic_refinement[OF tla_state(1)] by blast
  have won_node: "node_role (nodes_at tla_state x) = Master_Eligible
                  \<and> memory_state tla_state x = nodes_at tla_state x" if "election_won (memory_state tla_state x)" for x
  proof (cases "node_role (nodes_at tla_state x) = Master_Eligible")
    case True
    then show ?thesis by (simp add: memory_state_def)
  next
    case False
    then have "memory_state tla_state x = memory_at tla_state x" by (simp add: memory_state_def)
    with linkedD(8)[OF linked, of x] False that show ?thesis by simp
  qed
  have "election_won (memory_state tla_state node_1)" "election_won (memory_state tla_state node_2)"
    "current_term (memory_state tla_state node_1) = current_term (memory_state tla_state node_2)"
    using won_1 won_2 same_term unfolding node_state_1_def node_state_2_def tla_state(2) by simp_all
  then show ?thesis
    using won_node tla_one_election_candidate_per_term[OF tla_state(1) rtranclp.rtrancl_refl, of node_1 node_2]
    by auto
qed

theorem one_publisher_per_term:
  assumes published_1: "\<exists>value. is_Published publication_1 value"
  assumes published_2: "\<exists>value. is_Published publication_2 value"
  assumes same_term: "position_term (publication_position publication_1) = position_term (publication_position publication_2)"
  shows "publication_owner publication_1 = publication_owner publication_2"
proof -
  obtain destination_1 value_1 where
    "Publish_Msg destination_1 publication_1 value_1 \<in> messages tla_state"
    using published_1 unfolding is_Published_def tla_state(3) by blast
  moreover obtain destination_2 value_2 where
    "Publish_Msg destination_2 publication_2 value_2 \<in> messages tla_state"
    using published_2 unfolding is_Published_def tla_state(3) by blast
  ultimately show ?thesis using same_term by (rule tla_one_publisher_per_term[OF tla_state(1)])
qed

theorem publications_agree:
  assumes published_1: "is_Published publication_1 value_1"
  assumes published_2: "is_Published publication_2 value_2"
  assumes same_position: "publication_position publication_1 = publication_position publication_2"
  shows "publication_1 = publication_2 \<and> value_1 = value_2"
proof -
  obtain destination_1 where
    "Publish_Msg destination_1 publication_1 value_1 \<in> messages tla_state"
    using published_1 unfolding is_Published_def tla_state(3) by blast
  moreover obtain destination_2 where
    "Publish_Msg destination_2 publication_2 value_2 \<in> messages tla_state"
    using published_2 unfolding is_Published_def tla_state(3) by blast
  ultimately show ?thesis using same_position by (rule tla_log_matching[OF tla_state(1)])
qed

theorem committed_history_never_diverges:
  assumes published_1: "\<exists>value. is_Published publication_1 value"
  assumes published_2: "\<exists>value. is_Published publication_2 value"
  assumes committed_1: "java_committed j publication_1"
  assumes committed_2: "java_committed j publication_2"
  shows "(publication_position publication_1, publication_position publication_2)
           \<in> (descends \<union> descends\<inverse>)\<^sup>="
proof (cases "publication_position publication_1 = publication_position publication_2")
  case True
  then show ?thesis by simp
next
  case False
  obtain destination_1 value_1 where
    in_1: "Publish_Msg destination_1 publication_1 value_1 \<in> messages tla_state"
    using published_1 unfolding is_Published_def tla_state(3) by blast
  obtain destination_2 value_2 where
    in_2: "Publish_Msg destination_2 publication_2 value_2 \<in> messages tla_state"
    using published_2 unfolding is_Published_def tla_state(3) by blast
  have commit_1: "commit_for tla_state publication_1" and commit_2: "commit_for tla_state publication_2"
    using committed_1 committed_2 unfolding java_committed_def commit_for_def tla_state(3) by simp_all
  show ?thesis
    using tla_committed_values_form_chain[OF tla_state(1) in_1 in_2 commit_1 commit_2] False
    by (auto simp: descends_def)
qed

end

end
