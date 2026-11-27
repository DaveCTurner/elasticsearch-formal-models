theory Disk
  imports "../Link"
begin

context simulation
begin

lemma simulate_set_initial_state:
  assumes contract: "caller_contract
                         initial_configuration
                         initial_value
                         state
                         (Java_Set_Initial_State
                              node
                              initial_position
                              new_value
                              initial_accepted_config
                              initial_committed_config)"
  shows "\<exists>next_abstract_state. (next_abstract_state = abstract_state
                                \<or> abstract_model.transition
                                      initial_configuration
                                      abstract_state
                                      next_abstract_state)
                               \<and> linked
                                     initial_configuration
                                     (java_call state (Java_Set_Initial_State
                                                           node
                                                           initial_position
                                                           new_value
                                                           initial_accepted_config
                                                           initial_committed_config))
                                     next_abstract_state"
proof (cases "last_accepted_configuration (java_memory state node) = {}")
  case False
  then have "java_call state (Java_Set_Initial_State
                                  node
                                  initial_position
                                  new_value
                                  initial_accepted_config
                                  initial_committed_config)
             =
              state" by (simp add: java_put_def)
  then show ?thesis using link by (intro exI[of _ abstract_state]) simp
next
  case cfg: True
  let ?node_state = "java_memory state node"
  let ?new_node_state = "?node_state\<lparr>
    last_accepted_position       := initial_position,
    last_accepted_value          := new_value,
    last_accepted_configuration  := initial_accepted_config,
    last_committed_configuration := initial_committed_config
  \<rparr>"
  from contract have master: "node_role ?node_state = Master_Eligible" and votes: "publish_votes ?node_state = {}"
    and off: "\<not> election_won ?node_state" and args: "initial_position = last_accepted_position ?node_state" "initial_accepted_config = initial_configuration"
    "initial_committed_config = initial_configuration" "new_value = initial_value"
    by (simp_all add: Let_def)
  have call_result: "java_call state (Java_Set_Initial_State
                                          node
                                          initial_position
                                          new_value
                                          initial_accepted_config
                                          initial_committed_config)
                     =
      state\<lparr>
        java_memory   := (java_memory state)(node := ?new_node_state),
        java_disk     := (java_disk state)(node := disk_of ?new_node_state),
        java_messages := java_messages state
      \<rparr>"
    using cfg master by (simp add: java_put_def)
  have view: "disk_view state node = ?node_state" by (rule disk_view_master[OF master])
  have node_linked: "node_link initial_configuration abstract_state node ?node_state" using linkedD(1)[OF link, of node] view by simp
  have empty: "publications_accepted abstract_state node = []" "last_committed_configuration ?node_state = {}"
    using node_linkD(5)[OF node_linked cfg] by simp_all
  have "node_link initial_configuration abstract_state node ?new_node_state"
  proof -
    have node: "node_link initial_configuration abstract_state node ?node_state" by (rule node_linked)
    have "transient_link initial_configuration abstract_state node ?new_node_state"
      using node off unfolding node_link_def transient_link_def by simp
    moreover have "persisted_link initial_configuration abstract_state node ?new_node_state"
      using node boot cfg empty args unfolding node_link_def persisted_link_def by (simp add: stale_config_def)
    ultimately show ?thesis unfolding node_link_def by blast
  qed
  then have "linked
                 initial_configuration
                 (java_call state (Java_Set_Initial_State
                                       node
                                       initial_position
                                       new_value
                                       initial_accepted_config
                                       initial_committed_config))
                 abstract_state"
    unfolding call_result
    by (intro link_update[OF link grows_refl, where node = node]) (use master votes linkedD(4)[OF link] in \<open>auto simp: disk_view_def\<close>)
  then show ?thesis by (intro exI[of _ abstract_state]) simp
qed

text \<open>
  A node that is restarted, or that reads its state back from disk, has the role that it was
  started with. This is a proof aid with no Java counterpart.
\<close>

lemma memory_of_disk_role[simp]: "node_role (memory_of_disk role node_disk_state) = role"
  by (simp add: memory_of_disk_def)

text \<open>
  \<open>persisted_link\<close> only looks at the fields that are persisted, so it cannot tell apart two
  node states that have the same disk state. This is a proof aid with no Java counterpart.
\<close>

lemma persisted_link_depends_on_disk:
  assumes "disk_of first_state = disk_of second_state"
  shows "persisted_link initial_configuration abstract_state node first_state
         = persisted_link initial_configuration abstract_state node second_state"
proof -
  have "current_term first_state = current_term second_state" "last_accepted_position first_state = last_accepted_position second_state"
    "last_accepted_configuration first_state = last_accepted_configuration second_state"
    "last_committed_configuration first_state = last_committed_configuration second_state"
    using assms unfolding disk_of_def by (simp_all add: fun_eq_iff)
  then show ?thesis unfolding persisted_link_def by simp
qed

lemma simulate_restart_node:
  assumes contract: "caller_contract
                         initial_configuration
                         initial_value
                         state
                         (Java_Restart node new_role new_value)"
  shows "\<exists>next_abstract_state. (next_abstract_state = abstract_state
                                \<or> abstract_model.transition
                                      initial_configuration
                                      abstract_state
                                      next_abstract_state)
                               \<and> linked
                                     initial_configuration
                                     (java_call state (Java_Restart node new_role new_value))
                                     next_abstract_state"
proof -
  let ?node_state = "disk_view state node"
  let ?new_disk = "if disk_term (java_disk state node) = 0 \<and> new_role = Coordinating_Only
             then empty_disk initial_value else java_disk state node"
  let ?disk_node_state = "memory_of_disk new_role ?new_disk"
  let ?new_memory = "memory_of_disk new_role (if new_role = Coordinating_Only then empty_disk initial_value else ?new_disk)"
  from contract have new_value: "new_value = initial_value" by simp
  have call_result: "java_call state (Java_Restart node new_role new_value) =
      state\<lparr>
        java_memory := (java_memory state)(node := ?new_memory),
        java_disk   := (java_disk state)(node := ?new_disk)
      \<rparr>"
    using new_value by (cases "disk_term (java_disk state node) = 0 \<and> new_role = Coordinating_Only") (auto simp: Let_def)
  obtain new_state where new_state_def: "new_state = java_call state (Java_Restart
                                                                          node
                                                                          new_role
                                                                          new_value)" by simp
  have new_state_eq: "new_state = state\<lparr>
    java_memory := (java_memory state)(node := ?new_memory),
    java_disk   := (java_disk state)(node := ?new_disk)
  \<rparr>"
    using call_result new_state_def by simp
  have nl: "node_link initial_configuration abstract_state node ?node_state" by (rule linkedD(1)[OF link])
  have disk_of_node_state: "disk_of ?node_state = java_disk state node" by (rule linked_disk_view_disk[OF link])
  have publications_ok_fact: "abstract_model.publications_ok initial_configuration abstract_state"
    and messages_ok_fact: "abstract_model.messages_ok initial_configuration abstract_state"
    using abstract_model.dynamic_invariants[OF reach] by auto
  have disk: "node_link initial_configuration abstract_state node ?disk_node_state"
  proof (cases "disk_term (java_disk state node) = 0 \<and> new_role = Coordinating_Only")
    case True
    have current_term_zero: "current_term ?node_state = 0" using arg_cong[where f = disk_term, OF disk_of_node_state] True by (simp add: disk_of_def)
    have term0: "current_term_of abstract_state node = 0" using node_linkD(1)[OF nl] current_term_zero by simp
    have empty: "publications_accepted abstract_state node = []"
    proof (rule ccontr)
      assume "publications_accepted abstract_state node \<noteq> []"
      then have "publications_accepted abstract_state node \<in> publications_sent abstract_state" using abstract_model.messagesD(1)[OF messages_ok_fact, of node] by simp
      from publication_positive[OF publications_ok_fact this] abstract_model.messagesD(2)[OF messages_ok_fact, of node] term0
      show False by simp
    qed
    have committed: "last_committed_configuration_of abstract_state node = initial_configuration"
      using abstract_model.messagesD(3)[OF messages_ok_fact, of node] empty by (auto simp: abstract_model.effective_config_def)
    show ?thesis
      using True term0 empty committed
      unfolding node_link_defs memory_of_disk_def empty_disk_def abstract_model.active_leader_def
        abstract_model.fresh_votes_def
      by (auto simp: normalized_def split: if_splits)
  next
    case False
    then have new_disk_unchanged: "?new_disk = java_disk state node" by (rule if_not_P)
    have node_persisted_link: "persisted_link initial_configuration abstract_state node ?node_state" using nl unfolding node_link_def by blast
    have persisted: "persisted_link initial_configuration abstract_state node ?disk_node_state"
      using persisted_link_depends_on_disk[of ?disk_node_state ?node_state] node_persisted_link disk_of_node_state new_disk_unchanged by simp
    have transient: "transient_link initial_configuration abstract_state node ?disk_node_state"
      by (cases new_role) (simp_all add: transient_link_def memory_of_disk_def
          abstract_model.active_leader_def abstract_model.fresh_votes_def)
    show ?thesis using persisted transient unfolding node_link_def by simp
  qed
  have view: "disk_view new_state node = ?disk_node_state"
  proof (cases "new_role = Coordinating_Only")
    case True
    then show ?thesis by (simp add: new_state_eq disk_view_def memory_of_disk_def)
  next
    case False
    then show ?thesis by (simp add: new_state_eq disk_view_def memory_of_disk_def)
  qed
  have memory_link_holds: "new_role = Data_Only \<Longrightarrow> memory_link abstract_state ?disk_node_state ?new_memory"
  proof -
    assume new_role: "new_role = Data_Only"
    then have same_memory: "?new_memory = ?disk_node_state" by simp
    have key: "normalized (last_accepted_position ?disk_node_state) = position_of_tip_of (publications_accepted abstract_state node)"
      using node_linkD(4)[OF disk] by simp
    have "position_term (last_accepted_position ?disk_node_state) = 0
          \<or> (\<exists>publication_history\<in>publications_sent abstract_state. position_of_tip_of publication_history = last_accepted_position ?disk_node_state)"
    proof (cases "position_term (last_accepted_position ?disk_node_state) = 0")
      case True
      then show ?thesis by simp
    next
      case False
      then have "normalized (last_accepted_position ?disk_node_state) = last_accepted_position ?disk_node_state"
        by (simp add: normalized_def)
      with key have "position_of_tip_of (publications_accepted abstract_state node) = last_accepted_position ?disk_node_state" by simp
      moreover have "publications_accepted abstract_state node \<noteq> []"
        using False key by (auto simp: normalized_def split: if_splits)
      ultimately show ?thesis using abstract_model.messagesD(1)[OF messages_ok_fact, of node] by auto
    qed
    moreover have "position_term (last_accepted_position ?disk_node_state) \<le> current_term ?disk_node_state"
    proof -
      have "position_term (last_accepted_position ?disk_node_state) = term_of_tip_of (publications_accepted abstract_state node)"
        using arg_cong[where f = position_term, OF key] by simp
      then show ?thesis
        using abstract_model.messagesD(2)[OF messages_ok_fact, of node] node_linkD(1)[OF disk] by auto
    qed
    ultimately show "memory_link abstract_state ?disk_node_state ?new_memory" using same_memory unfolding memory_link_def by simp
  qed
  have "linked initial_configuration new_state abstract_state"
  proof (rule link_update[OF link grows_refl, where node = node])
    show "\<And>other_node. other_node \<noteq> node \<Longrightarrow> java_memory new_state other_node = java_memory state other_node
                                           \<and> java_disk new_state other_node = java_disk state other_node" by (simp add: new_state_eq)
    show "node_link initial_configuration abstract_state node (disk_view new_state node)"
      using disk view by simp
    show "\<And>other_node. other_node \<noteq> node \<Longrightarrow> node_frame abstract_state abstract_state other_node" by simp
    show "node_role (java_memory new_state node) = Master_Eligible \<Longrightarrow>
        java_disk new_state node = disk_of (java_memory new_state node)"
      by (cases "new_role = Coordinating_Only") (simp_all add: new_state_eq memory_of_disk_role)
    show "\<forall>voter\<in>publish_votes (disk_view new_state node).
        Response_Msg voter Master_Eligible node (last_published_position (disk_view new_state node))
          \<in> java_messages new_state"
      using view by (simp add: memory_of_disk_def)
    show "node_role (java_memory new_state node) = Data_Only \<Longrightarrow>
        memory_link abstract_state (disk_view new_state node) (java_memory new_state node)"
      using memory_link_holds view by (simp add: new_state_eq memory_of_disk_def)
    show "node_role (java_memory new_state node) \<noteq> Master_Eligible \<Longrightarrow>
        \<not> election_won (java_memory new_state node)"
      by (simp add: new_state_eq memory_of_disk_def)
    show "java_messages state \<subseteq> java_messages new_state" by (simp add: new_state_eq)
    show "\<And>message. message \<in> java_messages new_state \<Longrightarrow> message \<notin> java_messages state \<Longrightarrow> wire_link abstract_state message"
      by (simp add: new_state_eq)
    show "wire_unique (java_messages new_state)"
      using linkedD(4)[OF link] by (simp add: new_state_eq)
  qed
  then show ?thesis unfolding new_state_def by (intro exI[of _ abstract_state]) simp
qed

text \<open>
  The writes of the worker of a data node that is not master-eligible. The state that it writes is
  the disk state that the abstract model describes. A write of the term is a vote in a term, as
  far as the abstract model is concerned, though nobody counts it, and a write of the last
  accepted state is the acceptance of a publication.
\<close>

lemma simulate_persist_term:
  assumes contract: "caller_contract
                         initial_configuration
                         initial_value
                         state
                         (Java_Persist_Term node)"
  shows "\<exists>next_abstract_state. (next_abstract_state = abstract_state
                                \<or> abstract_model.transition
                                      initial_configuration
                                      abstract_state
                                      next_abstract_state)
                               \<and> linked
                                     initial_configuration
                                     (java_call state (Java_Persist_Term node))
                                     next_abstract_state"
proof (cases "node_role (java_memory state node) = Data_Only
              \<and> term_queued (java_memory state node)
              \<and> disk_term (java_disk state node) < current_term (java_memory state node)")
  case False
  then have "java_call state (Java_Persist_Term node) = state" using False by (auto simp: java_persist_def Let_def)
  then show ?thesis using link by (intro exI[of _ abstract_state]) simp
next
  case True
  let ?memory_state = "java_memory state node"
  let ?node_state = "disk_view state node"
  let ?queued_term = "current_term ?memory_state"
  let ?new_node_state = "?node_state\<lparr>current_term := ?queued_term\<rparr>"
  let ?new_memory_state = "?memory_state\<lparr>term_queued := False\<rparr>"
  let ?next_abstract_state = "abstract_state\<lparr>
    current_term_of := (current_term_of abstract_state)(node := ?queued_term),
    joins_sent      := insert (node,node,?queued_term,position_of_tip_of (publications_accepted abstract_state node)) (joins_sent abstract_state)
  \<rparr>"
  obtain new_state where new_state_def: "new_state = java_call state (Java_Persist_Term node)" by simp
  from True have data: "node_role ?memory_state = Data_Only" and disk_term_behind: "disk_term (java_disk state node) < ?queued_term" by simp_all
  have new_state_eq: "new_state = state\<lparr>
    java_memory := (java_memory state)(node := ?new_memory_state),
    java_disk   := (java_disk state)(node := (java_disk state node)\<lparr>disk_term := ?queued_term\<rparr>)
  \<rparr>"
    using True new_state_def by (simp add: java_persist_def Let_def)
  have not_master: "node_role ?memory_state \<noteq> Master_Eligible" using data by simp
  have disk_view_as_memory_of_disk: "?node_state = memory_of_disk Data_Only (java_disk state node)" using disk_view_other[OF not_master] data by simp
  have new_disk_view: "disk_view new_state node = ?new_node_state" using data by (simp add: new_state_eq disk_view_def disk_view_as_memory_of_disk memory_of_disk_def)
  have nl: "node_link initial_configuration abstract_state node ?node_state" by (rule linkedD(1)[OF link])
  have not_won: "\<not> election_won ?node_state" using disk_view_as_memory_of_disk by (simp add: memory_of_disk_def)
  have no_votes: "join_votes ?node_state = {}" using disk_view_as_memory_of_disk by (simp add: memory_of_disk_def)
  have no_publish_votes: "publish_votes ?node_state = {}" using disk_view_as_memory_of_disk by (simp add: memory_of_disk_def)
  have inc: "current_term_of abstract_state node < ?queued_term"
    using disk_term_behind node_linkD(1)[OF nl] disk_view_as_memory_of_disk by (simp add: memory_of_disk_def)
  have step: "abstract_model.transition initial_configuration abstract_state ?next_abstract_state" by (rule abstract_model.transition.start_join[OF inc])
  have grow: "grows abstract_state ?next_abstract_state" by (rule transition_grows[OF step])
  have new_link: "node_link initial_configuration ?next_abstract_state node ?new_node_state"
  proof -
    have pl: "persisted_link initial_configuration ?next_abstract_state node ?new_node_state"
      using nl[unfolded node_link_def, THEN conjunct1] unfolding persisted_link_def by (auto split: if_splits)
    have tl: "transient_link initial_configuration ?next_abstract_state node ?new_node_state"
      using not_won no_votes no_publish_votes data disk_view_as_memory_of_disk
      unfolding transient_link_def abstract_model.fresh_votes_def by (simp add: memory_of_disk_def)
    show ?thesis using pl tl unfolding node_link_def by blast
  qed
  have frame: "other_node \<noteq> node \<Longrightarrow> node_frame abstract_state ?next_abstract_state other_node" for other_node
    unfolding node_frame_def abstract_model.active_leader_def by auto
  have mem_link: "memory_link ?next_abstract_state ?new_node_state ?new_memory_state"
    using linkedD(6)[OF link data] memory_link_frame[OF _ grow] by (auto simp: memory_link_def grows_def)
  have "linked initial_configuration new_state ?next_abstract_state"
  proof (rule link_update[OF link grow, where node = node])
    show "\<And>other_node. other_node \<noteq> node \<Longrightarrow> java_memory new_state other_node = java_memory state other_node
                                           \<and> java_disk new_state other_node = java_disk state other_node"
      by (simp add: new_state_eq)
    show "node_link initial_configuration ?next_abstract_state node (disk_view new_state node)" using new_link new_disk_view by simp
    show "\<And>other_node. other_node \<noteq> node \<Longrightarrow> node_frame abstract_state ?next_abstract_state other_node" by (rule frame)
    show "node_role (java_memory new_state node) = Master_Eligible \<Longrightarrow> java_disk new_state node = disk_of (java_memory new_state node)"
      using data by (simp add: new_state_eq)
    show "\<forall>voter\<in>publish_votes (disk_view new_state node).
        Response_Msg voter Master_Eligible node (last_published_position (disk_view new_state node)) \<in> java_messages new_state"
      using no_publish_votes new_disk_view by simp
    show "node_role (java_memory new_state node) = Data_Only \<Longrightarrow> memory_link ?next_abstract_state (disk_view new_state node) (java_memory new_state node)"
      using mem_link new_disk_view by (simp add: new_state_eq)
    show "node_role (java_memory new_state node) \<noteq> Master_Eligible \<Longrightarrow> \<not> election_won (java_memory new_state node)"
      using linkedD(7)[OF link, of node] not_master by (simp add: new_state_eq)
    show "java_messages state \<subseteq> java_messages new_state" by (simp add: new_state_eq)
    show "\<And>message. message \<in> java_messages new_state \<Longrightarrow> message \<notin> java_messages state \<Longrightarrow> wire_link ?next_abstract_state message" by (simp add: new_state_eq)
    show "wire_unique (java_messages new_state)" using linkedD(4)[OF link] by (simp add: new_state_eq)
  qed
  with step show ?thesis unfolding new_state_def by (intro exI[of _ ?next_abstract_state]) simp
qed

text \<open>
  Only \<open>position_zero\<close> normalizes to a position that is at most \<open>position_zero\<close>. This is a proof
  aid with no Java counterpart.
\<close>

lemma normalized_zero_least:
  assumes "normalized position \<le> position_zero"
  shows "normalized position = position_zero"
  using assms by (cases position) (auto simp: normalized_def position_le_iff)

lemma simulate_persist_state:
  assumes contract: "caller_contract
                         initial_configuration
                         initial_value
                         state
                         (Java_Persist_State node)"
  shows "\<exists>next_abstract_state. (next_abstract_state = abstract_state
                                \<or> abstract_model.transition
                                      initial_configuration
                                      abstract_state
                                      next_abstract_state)
                               \<and> linked
                                     initial_configuration
                                     (java_call state (Java_Persist_State node))
                                     next_abstract_state"
proof (cases "node_role (java_memory state node) = Data_Only
              \<and> state_queued (java_memory state node)
              \<and> disk_term (java_disk state node) = position_term (last_accepted_position (java_memory state node))")
  case False
  then have "java_call state (Java_Persist_State node) = state" using False by (auto simp: java_persist_def Let_def)
  then show ?thesis using link by (intro exI[of _ abstract_state]) simp
next
  case True
  let ?memory_state = "java_memory state node"
  let ?node_state = "disk_view state node"
  let ?new_node_state = "?node_state\<lparr>
    last_accepted_position       := last_accepted_position ?memory_state,
    last_accepted_value          := last_accepted_value ?memory_state,
    last_accepted_configuration  := stale_config,
    last_committed_configuration := stale_config,
    last_published_configuration := stale_config
  \<rparr>"
  let ?new_memory_state = "?memory_state\<lparr>state_queued := False\<rparr>"
  obtain new_state where new_state_def: "new_state = java_call state (Java_Persist_State node)" by simp
  from True have data: "node_role ?memory_state = Data_Only"
    and term_eq: "disk_term (java_disk state node) = position_term (last_accepted_position ?memory_state)" by simp_all
  have new_state_eq: "new_state = state\<lparr>
    java_memory := (java_memory state)(node := ?new_memory_state),
    java_disk   := (java_disk state)(node := (java_disk state node)\<lparr>
      disk_position                := last_accepted_position ?memory_state,
      disk_value                   := last_accepted_value ?memory_state,
      disk_accepted_configuration  := stale_config,
      disk_committed_configuration := stale_config
    \<rparr>)
  \<rparr>"
    using True new_state_def by (simp add: java_persist_def Let_def)
  have not_master: "node_role ?memory_state \<noteq> Master_Eligible" using data by simp
  have disk_view_as_memory_of_disk: "?node_state = memory_of_disk Data_Only (java_disk state node)" using disk_view_other[OF not_master] data by simp
  have new_disk_view: "disk_view new_state node = ?new_node_state" using data by (simp add: new_state_eq disk_view_def disk_view_as_memory_of_disk memory_of_disk_def)
  have nl: "node_link initial_configuration abstract_state node ?node_state" by (rule linkedD(1)[OF link])
  have not_won: "\<not> election_won ?node_state" using disk_view_as_memory_of_disk by (simp add: memory_of_disk_def)
  have no_votes: "join_votes ?node_state = {}" using disk_view_as_memory_of_disk by (simp add: memory_of_disk_def)
  have no_publish_votes: "publish_votes ?node_state = {}" using disk_view_as_memory_of_disk by (simp add: memory_of_disk_def)
  have term_eq': "current_term ?node_state = position_term (last_accepted_position ?memory_state)"
    using term_eq disk_view_as_memory_of_disk by (simp add: memory_of_disk_def)
  from linkedD(6)[OF link data]
  have known: "position_term (last_accepted_position ?memory_state) = 0
               \<or> (\<exists>publication_history\<in>publications_sent abstract_state. position_of_tip_of publication_history = last_accepted_position ?memory_state)"
    and ge: "normalized (last_accepted_position ?node_state) \<le> normalized (last_accepted_position ?memory_state)"
    and le: "position_term (last_accepted_position ?memory_state) \<le> current_term ?memory_state"
    unfolding memory_link_def by auto
  have disk_common: "node_role ?memory_state = Data_Only \<Longrightarrow> node_role (java_memory new_state node) = Data_Only"
    by (simp add: new_state_eq)
  have link_gen: "\<And>next_abstract_state. grows abstract_state next_abstract_state \<Longrightarrow> (\<And>other_node. other_node \<noteq> node \<Longrightarrow> node_frame
                                                                                                                         abstract_state
                                                                                                                         next_abstract_state
                                                                                                                         other_node) \<Longrightarrow>
      node_link initial_configuration next_abstract_state node ?new_node_state \<Longrightarrow> memory_link next_abstract_state ?new_node_state ?new_memory_state \<Longrightarrow>
      linked initial_configuration new_state next_abstract_state"
  proof -
    fix next_abstract_state
    assume grow: "grows abstract_state next_abstract_state" and frame: "\<And>other_node. other_node \<noteq> node \<Longrightarrow> node_frame
                                                                                                             abstract_state
                                                                                                             next_abstract_state
                                                                                                             other_node"
      and nlb: "node_link initial_configuration next_abstract_state node ?new_node_state" and ml: "memory_link next_abstract_state ?new_node_state ?new_memory_state"
    show "linked initial_configuration new_state next_abstract_state"
    proof (rule link_update[OF link grow, where node = node])
      show "\<And>other_node. other_node \<noteq> node \<Longrightarrow> java_memory new_state other_node = java_memory state other_node
                                             \<and> java_disk new_state other_node = java_disk state other_node"
        by (simp add: new_state_eq)
      show "node_link initial_configuration next_abstract_state node (disk_view new_state node)" using nlb new_disk_view by simp
      show "\<And>other_node. other_node \<noteq> node \<Longrightarrow> node_frame
                                                 abstract_state
                                                 next_abstract_state
                                                 other_node" by (rule frame)
      show "node_role (java_memory new_state node) = Master_Eligible \<Longrightarrow> java_disk new_state node = disk_of (java_memory new_state node)"
        using data by (simp add: new_state_eq)
      show "\<forall>voter\<in>publish_votes (disk_view new_state node).
          Response_Msg
              voter
              Master_Eligible
              node
              (last_published_position (disk_view new_state node)) \<in> java_messages new_state"
        using no_publish_votes new_disk_view by simp
      show "node_role (java_memory new_state node) = Data_Only \<Longrightarrow> memory_link
                                                                     next_abstract_state
                                                                     (disk_view new_state node)
                                                                     (java_memory new_state node)"
        using ml new_disk_view by (simp add: new_state_eq)
      show "node_role (java_memory new_state node) \<noteq> Master_Eligible \<Longrightarrow> \<not> election_won (java_memory new_state node)"
        using linkedD(7)[OF link, of node] not_master by (simp add: new_state_eq)
      show "java_messages state \<subseteq> java_messages new_state" by (simp add: new_state_eq)
      show "\<And>message. message \<in> java_messages new_state \<Longrightarrow> message \<notin> java_messages state \<Longrightarrow> wire_link next_abstract_state message" by (simp add: new_state_eq)
      show "wire_unique (java_messages new_state)" using linkedD(4)[OF link] by (simp add: new_state_eq)
    qed
  qed
  show ?thesis
  proof (cases "normalized (last_accepted_position ?node_state) = normalized (last_accepted_position ?memory_state)")
    case True
    have new_link: "node_link initial_configuration abstract_state node ?new_node_state"
      using nl not_won no_votes data True disk_view_as_memory_of_disk
      unfolding node_link_defs abstract_model.active_leader_def abstract_model.fresh_votes_def
      by (auto simp: stale_config_def memory_of_disk_def split: if_splits)
    have mem_link: "memory_link abstract_state ?new_node_state ?new_memory_state"
      using known le True data unfolding memory_link_def by auto
    have "linked initial_configuration new_state abstract_state" by (rule link_gen[OF grows_refl _ new_link mem_link]) simp
    then show ?thesis unfolding new_state_def by (intro exI[of _ abstract_state]) simp
  next
    case False
    with ge have lt: "normalized (last_accepted_position ?node_state) < normalized (last_accepted_position ?memory_state)" by simp
    have term_pos: "position_term (last_accepted_position ?memory_state) \<noteq> 0"
    proof
      assume "position_term (last_accepted_position ?memory_state) = 0"
      then have "normalized (last_accepted_position ?memory_state) = position_zero" by (simp add: normalized_def)
      with ge have "normalized (last_accepted_position ?node_state) \<le> position_zero" by simp
      from normalized_zero_least[OF this] False \<open>normalized (last_accepted_position ?memory_state) = position_zero\<close>
      show False by simp
    qed
    from known term_pos obtain publication_history where pub: "publication_history \<in> publications_sent abstract_state"
      and hpos: "position_of_tip_of publication_history = last_accepted_position ?memory_state" by auto
    have norm_m: "normalized (last_accepted_position ?memory_state) = last_accepted_position ?memory_state"
      using term_pos by (simp add: normalized_def)
    have inc: "position_of_tip_of (publications_accepted abstract_state node) < position_of_tip_of publication_history"
      using lt norm_m hpos node_linkD(4)[OF nl] by simp
    have term_h: "term_of_tip_of publication_history = current_term_of abstract_state node"
      using hpos term_eq' node_linkD(1)[OF nl] by simp
    let ?next_abstract_state = "abstract_state\<lparr>
      publications_accepted           := (publications_accepted abstract_state)(node := publication_history),
      last_committed_configuration_of := (last_committed_configuration_of abstract_state)(node := previous_config_of_tip_of initial_configuration publication_history),
      publish_responses_sent          := insert (node,publication_history) (publish_responses_sent abstract_state)
    \<rparr>"
    have step: "abstract_model.transition initial_configuration abstract_state ?next_abstract_state" by (rule abstract_model.transition.receive[OF pub term_h inc])
    have grow: "grows abstract_state ?next_abstract_state" by (rule transition_grows[OF step])
    have new_link: "node_link initial_configuration ?next_abstract_state node ?new_node_state"
      using nl not_won no_votes data norm_m hpos disk_view_as_memory_of_disk
      unfolding node_link_defs abstract_model.active_leader_def abstract_model.fresh_votes_def
      by (auto simp: stale_config_def memory_of_disk_def split: if_splits)
    have frame: "other_node \<noteq> node \<Longrightarrow> node_frame abstract_state ?next_abstract_state other_node" for other_node
      unfolding node_frame_def abstract_model.active_leader_def by auto
    have mem_link: "memory_link ?next_abstract_state ?new_node_state ?new_memory_state"
      using known le pub hpos data unfolding memory_link_def by (auto simp: normalized_def split: if_splits)
    have "linked initial_configuration new_state ?next_abstract_state" by (rule link_gen[OF grow frame new_link mem_link])
    with step show ?thesis unfolding new_state_def by (intro exI[of _ ?next_abstract_state]) simp
  qed
qed

end

end
