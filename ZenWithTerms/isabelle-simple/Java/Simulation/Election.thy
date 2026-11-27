theory Election
  imports "../Link"
begin

section \<open>Simulation of \<open>handleStartJoin\<close> and \<open>handleJoin\<close>\<close>

context simulation
begin

text \<open>
  A proof aid, which has no equivalent in Java: the update of one master-eligible node, which \<open>java_put\<close>
  writes through to the disk. It specialises \<open>link_update\<close> to a new in-memory state
  \<open>new_node_state\<close> for \<open>node\<close> whose disk is \<open>disk_of new_node_state\<close>, and to a new set of messages
  \<open>new_messages\<close>. \<open>next_abstract_state\<close> is the abstract state that the update is simulated by.
\<close>

lemma master_node_update:
  assumes grown: "grows abstract_state next_abstract_state"
  assumes master: "node_role new_node_state = Master_Eligible"
    "node_role (java_memory state node) = Master_Eligible"
  assumes node_linked: "node_link initial_configuration next_abstract_state node new_node_state"
  assumes frame: "\<And>other_node. other_node \<noteq> node \<Longrightarrow> node_frame
                                                       abstract_state
                                                       next_abstract_state
                                                       other_node"
  assumes replies: "\<forall>publish_voter\<in>publish_votes new_node_state.
    Response_Msg publish_voter Master_Eligible node (last_published_position new_node_state) \<in> new_messages"
  assumes messages: "java_messages state \<subseteq> new_messages"
  assumes news: "\<And>message. message \<in> new_messages \<Longrightarrow> message \<notin> java_messages state \<Longrightarrow>
    wire_link next_abstract_state message"
  assumes unique: "wire_unique new_messages"
  shows "linked
             initial_configuration
             (state\<lparr>
               java_memory   := (java_memory state)(node := new_node_state),
               java_disk     := (java_disk state)(node := disk_of new_node_state),
               java_messages := new_messages
             \<rparr>)
             next_abstract_state"
proof (rule link_update[OF link grown _ _ frame])
  show "\<And>other_node. other_node \<noteq> node \<Longrightarrow> java_memory (state\<lparr>
    java_memory   := (java_memory state)(node := new_node_state),
    java_disk     := (java_disk state)(node := disk_of new_node_state),
    java_messages := new_messages
  \<rparr>) other_node = java_memory state other_node
                                         \<and> java_disk (state\<lparr>
                                           java_memory   := (java_memory state)(node := new_node_state),
                                           java_disk     := (java_disk state)(node := disk_of new_node_state),
                                           java_messages := new_messages
                                         \<rparr>) other_node = java_disk state other_node"
    by simp
  show "node_link
            initial_configuration
            next_abstract_state
            node
            (disk_view (state\<lparr>
              java_memory   := (java_memory state)(node := new_node_state),
              java_disk     := (java_disk state)(node := disk_of new_node_state),
              java_messages := new_messages
            \<rparr>) node)"
    using node_linked master(1) by (simp add: disk_view_def)
qed (use master replies messages news unique in \<open>simp_all add: disk_view_def\<close>)

text \<open>
  A proof aid: the join that a master-eligible \<open>voter\<close> sends to \<open>candidate\<close> in \<open>join_term\<close> is
  linked to the abstract state in which the \<open>start_join\<close> transition has recorded it in \<open>joins_sent\<close>.
  The position that the join carries is the last accepted position of \<open>voter_state\<close>.
\<close>

lemma join_message_wire_link:
  assumes "node_link initial_configuration abstract_state voter voter_state"
  shows "wire_link (abstract_state\<lparr>joins_sent := insert
                        (voter, candidate, join_term, position_of_tip_of (publications_accepted abstract_state voter))
                        (joins_sent abstract_state)\<rparr>)
           (Join_Msg voter Master_Eligible candidate join_term (last_accepted_position voter_state))"
  using node_linkD(4)[OF assms] by simp

text \<open>
  \<open>handleStartJoin\<close> is the abstract \<open>start_join\<close> transition on a master-eligible node. On a node that
  is not master-eligible it only changes the node's in-memory state, which the abstract model does not
  track, and sends a join that nobody counts.
\<close>

lemma simulate_handle_start_join:
  assumes contract: "caller_contract
                         initial_configuration
                         initial_value
                         state
                         (Java_Handle_Start_Join voter candidate new_term)"
  shows "\<exists>next_abstract_state. (next_abstract_state = abstract_state
                                \<or> abstract_model.transition
                                      initial_configuration
                                      abstract_state
                                      next_abstract_state)
                               \<and> linked
                                     initial_configuration
                                     (java_call state (Java_Handle_Start_Join
                                                           voter
                                                           candidate
                                                           new_term))
                                     next_abstract_state"
proof (cases "current_term (java_memory state voter) < new_term")
  case False
  then show ?thesis by (intro exI[of _ abstract_state]) (simp add: Let_def java_put_def link)
next
  case newer_term: True
  let ?voter_state = "java_memory state voter"
  let ?joined_voter_state = "?voter_state\<lparr>
    current_term                   := new_term,
    join_votes                     := {},
    election_won                   := False,
    last_published_version         := 0,
    last_published_configuration   := last_accepted_configuration ?voter_state,
    publish_votes                  := {},
    started_join_since_last_reboot := True
  \<rparr>"
  let ?new_voter_state = "queue_term ?joined_voter_state"
  let ?join_message = "Join_Msg
                           voter
                           (node_role ?voter_state)
                           candidate
                           new_term
                           (last_accepted_position ?voter_state)"
  have new_role: "node_role ?new_voter_state = node_role ?voter_state" by (simp add: queue_term_def)
  show ?thesis
  proof (cases "node_role ?voter_state = Master_Eligible")
    case True
    have unqueued: "?new_voter_state = ?joined_voter_state" using True by (simp add: queue_term_def)
    have call_result: "java_call state (Java_Handle_Start_Join voter candidate new_term) =
        state\<lparr>
          java_memory   := (java_memory state)(voter := ?joined_voter_state),
          java_disk     := (java_disk state)(voter := disk_of ?joined_voter_state),
          java_messages := insert ?join_message (java_messages state)
        \<rparr>"
      using newer_term True by (simp add: java_put_def Let_def queue_term_def)
    let ?next_abstract_state = "abstract_state\<lparr>
      current_term_of := (current_term_of abstract_state)(voter := new_term),
      joins_sent      := insert
                           (voter, candidate, new_term, position_of_tip_of (publications_accepted abstract_state voter))
                           (joins_sent abstract_state)
    \<rparr>"
    let ?messages_after = "insert ?join_message (java_messages state)"
    have view_is_memory: "disk_view state voter = ?voter_state" using True by (rule disk_view_master)
    have voter_link: "node_link initial_configuration abstract_state voter ?voter_state"
      using linkedD(1)[OF link, of voter] view_is_memory by simp
    have abstract_newer_term: "current_term_of abstract_state voter < new_term"
      using node_linkD(1)[OF voter_link] newer_term by simp
    have step: "abstract_model.transition initial_configuration abstract_state ?next_abstract_state"
      by (rule abstract_model.transition.start_join[OF abstract_newer_term])
    have new_voter_link: "node_link initial_configuration ?next_abstract_state voter ?joined_voter_state"
    proof -
      have positive_term: "0 < new_term" using abstract_newer_term by simp
      have "persisted_link initial_configuration ?next_abstract_state voter ?joined_voter_state"
        using conjunct1[OF voter_link[unfolded node_link_def]] unfolding persisted_link_def
        by (auto split: if_splits)
      moreover have "transient_link initial_configuration ?next_abstract_state voter ?joined_voter_state"
      proof -
        have inactive: "\<not> abstract_model.active_leader ?next_abstract_state voter"
          using certificate_future[OF reach abstract_newer_term] unfolding abstract_model.active_leader_def
          by simp
        show ?thesis
          using inactive positive_term True
          unfolding transient_link_def abstract_model.fresh_votes_def by simp
      qed
      ultimately show ?thesis unfolding node_link_def by blast
    qed
    have frame: "other_node \<noteq> voter \<Longrightarrow> node_frame abstract_state ?next_abstract_state other_node"
      for other_node
      unfolding node_frame_def abstract_model.active_leader_def by auto
    have news: "\<And>message. message \<in> ?messages_after \<Longrightarrow> message \<notin> java_messages state \<Longrightarrow>
        wire_link ?next_abstract_state message"
      using join_message_wire_link[OF voter_link, of candidate new_term] True by auto
    have unique: "wire_unique ?messages_after"
      using wire_unique_control[OF linkedD(4)[OF link], of "{?join_message}"] by simp
    have "linked initial_configuration
        (state\<lparr>
          java_memory   := (java_memory state)(voter := ?joined_voter_state),
          java_disk     := (java_disk state)(voter := disk_of ?joined_voter_state),
          java_messages := ?messages_after
        \<rparr>) ?next_abstract_state"
      by (rule master_node_update[OF transition_grows[OF step] _ True new_voter_link frame _ _ news unique])
         (use True in \<open>auto\<close>)
    then show ?thesis using step call_result by (intro exI[of _ ?next_abstract_state]) simp
  next
    case False
    have call_result: "java_call state (Java_Handle_Start_Join voter candidate new_term) =
        state\<lparr>
          java_memory   := (java_memory state)(voter := ?new_voter_state),
          java_messages := insert ?join_message (java_messages state)
        \<rparr>"
      using newer_term False new_role by (simp add: java_put_def Let_def)
    let ?messages_after = "insert ?join_message (java_messages state)"
    let ?new_state = "state\<lparr>
      java_memory   := (java_memory state)(voter := ?new_voter_state),
      java_messages := ?messages_after
    \<rparr>"
    have view: "disk_view ?new_state voter = disk_view state voter"
      using False new_role by (simp add: disk_view_def)
    have news: "\<And>message. message \<in> ?messages_after \<Longrightarrow> message \<notin> java_messages state \<Longrightarrow>
        wire_link abstract_state message"
      using False by auto
    have unique: "wire_unique ?messages_after"
      using wire_unique_control[OF linkedD(4)[OF link], of "{?join_message}"] by simp
    have "linked initial_configuration ?new_state abstract_state"
    proof (rule link_update[OF link grows_refl])
      show "\<And>other_node. other_node \<noteq> voter \<Longrightarrow>
          java_memory ?new_state other_node = java_memory state other_node
          \<and> java_disk ?new_state other_node = java_disk state other_node"
        by simp
      show "node_link initial_configuration abstract_state voter (disk_view ?new_state voter)"
        using view linkedD(1)[OF link] by simp
      show "\<And>other_node. other_node \<noteq> voter \<Longrightarrow> node_frame abstract_state abstract_state other_node"
        by simp
      show "node_role (java_memory ?new_state voter) = Master_Eligible \<Longrightarrow>
          java_disk ?new_state voter = disk_of (java_memory ?new_state voter)"
        using False new_role by simp
      show "\<forall>publish_voter\<in>publish_votes (disk_view ?new_state voter).
          Response_Msg
              publish_voter
              Master_Eligible
              voter
              (last_published_position (disk_view ?new_state voter))
            \<in> java_messages ?new_state"
        using view linkedD(2)[OF link, of _ voter] by auto
      show "node_role (java_memory ?new_state voter) = Data_Only \<Longrightarrow> memory_link
                                                                       abstract_state
                                                                       (disk_view ?new_state voter)
                                                                       (java_memory ?new_state voter)"
        using view linkedD(6)[OF link, of voter] newer_term False new_role
        by (auto simp: memory_link_def queue_term_def)
      show "node_role (java_memory ?new_state voter) \<noteq> Master_Eligible \<Longrightarrow>
          \<not> election_won (java_memory ?new_state voter)"
        using False new_role by (simp add: queue_term_def)
      show "java_messages state \<subseteq> java_messages ?new_state" by auto
      show "\<And>message. message \<in> java_messages ?new_state \<Longrightarrow> message \<notin> java_messages state \<Longrightarrow>
          wire_link abstract_state message"
        using news by simp
      show "wire_unique (java_messages ?new_state)" using unique by simp
    qed
    then show ?thesis using call_result by (intro exI[of _ abstract_state]) simp
  qed
qed

text \<open>
  \<open>handleJoin\<close> on a candidate that is master-eligible. A join that the call rejects changes nothing.
  A join that adds a vote without winning the election, or that adds a vote to an election
  that is already won, does not change the abstract state. A join that wins the election is the abstract
  \<open>win_election\<close> transition.
\<close>

lemma simulate_handle_join:
  assumes contract: "caller_contract
                         initial_configuration
                         initial_value
                         state
                         (Java_Handle_Join voter voter_role candidate join_term voter_position)"
  shows "\<exists>next_abstract_state. (next_abstract_state = abstract_state
                                \<or> abstract_model.transition
                                      initial_configuration
                                      abstract_state
                                      next_abstract_state)
                               \<and> linked
                                     initial_configuration
                                     (java_call state (Java_Handle_Join
                                                           voter
                                                           voter_role
                                                           candidate
                                                           join_term
                                                           voter_position))
                                     next_abstract_state"
proof -
  let ?candidate_state = "java_memory state candidate"
  let ?new_votes = "if voter_role = Master_Eligible
                    then insert voter (join_votes ?candidate_state) else join_votes ?candidate_state"
  let ?won = "java_is_election_quorum ?candidate_state ?new_votes"
  let ?join_guard = "join_term = current_term ?candidate_state
                     \<and> started_join_since_last_reboot ?candidate_state
                     \<and> voter_position \<le> last_accepted_position ?candidate_state
                     \<and> last_accepted_configuration ?candidate_state \<noteq> {}"
  from contract have role: "node_role ?candidate_state = Master_Eligible"
    and sent: "Join_Msg voter voter_role candidate join_term voter_position \<in> java_messages state"
    by simp_all
  have view_is_memory: "disk_view state candidate = ?candidate_state" using role by (rule disk_view_master)
  have candidate_link: "node_link initial_configuration abstract_state candidate ?candidate_state"
    using linkedD(1)[OF link, of candidate] view_is_memory by simp
  have sent_response: "\<And>publish_voter. publish_voter \<in> publish_votes ?candidate_state \<Longrightarrow>
      Response_Msg
          publish_voter
          Master_Eligible
          candidate
          (last_published_position ?candidate_state)
        \<in> java_messages state"
    using linkedD(2)[OF link, of _ candidate] view_is_memory by simp
  show ?thesis
  proof (cases ?join_guard)
    case False
    then have "java_call state (Java_Handle_Join voter voter_role candidate join_term voter_position) = state"
      unfolding java_call.simps Let_def java_put_def by (rule if_not_P)
    then show ?thesis using link by (intro exI[of _ abstract_state]) simp
  next
    case guard: True
    then have term_match: "join_term = current_term_of abstract_state candidate"
      and fresh: "voter_position \<le> last_accepted_position ?candidate_state"
      and started_flag: "started_join_since_last_reboot ?candidate_state"
      and accepted_configuration_nonempty: "last_accepted_configuration ?candidate_state \<noteq> {}"
      using node_linkD(1)[OF candidate_link] by simp_all
    have started: "0 < current_term_of abstract_state candidate"
      using node_linkD(2)[OF candidate_link role started_flag] .
    have normalized_voter_position:
      "normalized voter_position \<le> position_of_tip_of (publications_accepted abstract_state candidate)"
      using normalized_mono[OF fresh] node_linkD(4)[OF candidate_link] by simp
    have votes: "abstract_model.fresh_votes
                     abstract_state
                     candidate
                     (current_term_of abstract_state candidate)
                     (publications_accepted abstract_state candidate)
                     ?new_votes"
    proof (cases "voter_role = Master_Eligible")
      case True
      then have join_sent: "(voter, candidate, current_term_of abstract_state candidate, normalized voter_position)
                              \<in> joins_sent abstract_state"
        using linkedD(3)[OF link sent] term_match by simp
      show ?thesis
        using True fresh_vote_insert[OF node_linkD(8)[OF candidate_link] join_sent normalized_voter_position]
        by simp
    next
      case False
      then show ?thesis using node_linkD(8)[OF candidate_link] by simp
    qed
    have retained: "election_won ?candidate_state \<Longrightarrow> ?won"
    proof (cases "voter_role = Master_Eligible")
      case True
      then show "election_won ?candidate_state \<Longrightarrow> ?won"
        using is_election_quorum_insert[OF node_linkD(9)[OF candidate_link]] by simp
    next
      case False
      then show "election_won ?candidate_state \<Longrightarrow> ?won" using node_linkD(9)[OF candidate_link] by simp
    qed
    show ?thesis
    proof (cases "\<not> election_won ?candidate_state \<and> ?won")
      case False
      then have won: "?won = election_won ?candidate_state" using retained by blast
      let ?new_candidate_state = "?candidate_state\<lparr>join_votes := ?new_votes\<rparr>"
      have call_result: "java_call state (Java_Handle_Join
                                              voter
                                              voter_role
                                              candidate
                                              join_term
                                              voter_position)
                         =
          state\<lparr>
            java_memory   := (java_memory state)(candidate := ?new_candidate_state),
            java_disk     := (java_disk state)(candidate := disk_of ?new_candidate_state),
            java_messages := java_messages state
          \<rparr>"
      proof -
        have unchanged_flags: "?candidate_state\<lparr>
          join_votes             := ?new_votes,
          election_won           := ?won,
          last_published_version := (if ?won \<and> \<not> election_won ?candidate_state
            then position_version (last_accepted_position ?candidate_state)
            else last_published_version ?candidate_state)
        \<rparr> = ?new_candidate_state"
          using won by simp
        show ?thesis using guard role unchanged_flags by (simp add: Let_def java_put_def)
      qed
      have known: "election_won ?candidate_state \<Longrightarrow>
          known_tip initial_configuration abstract_state candidate ?new_candidate_state"
      proof (cases "voter_role = Master_Eligible")
        case True
        then show "election_won ?candidate_state \<Longrightarrow>
            known_tip initial_configuration abstract_state candidate ?new_candidate_state"
          using known_tip_insert_join[OF node_linkD(10)[OF candidate_link], of voter] by simp
      next
        case False
        then show "election_won ?candidate_state \<Longrightarrow>
            known_tip initial_configuration abstract_state candidate ?new_candidate_state"
          using node_linkD(10)[OF candidate_link] unfolding known_tip_def by simp
      qed
      have new_candidate_link:
        "node_link initial_configuration abstract_state candidate ?new_candidate_state"
      proof -
        have persisted: "persisted_link initial_configuration abstract_state candidate ?new_candidate_state"
          using conjunct1[OF candidate_link[unfolded node_link_def]] unfolding persisted_link_def
          by (auto split: if_splits)
        have old_transient: "transient_link initial_configuration abstract_state candidate ?candidate_state"
          using candidate_link unfolding node_link_def by blast
        have election_quorum: "election_won ?candidate_state \<Longrightarrow>
            java_is_election_quorum ?new_candidate_state (join_votes ?new_candidate_state)"
          using won retained unfolding java_is_election_quorum_def by simp
        have old_transient_facts: "(node_role ?candidate_state = Master_Eligible \<longrightarrow>
            (started_join_since_last_reboot ?candidate_state \<longrightarrow> 0 < current_term_of abstract_state candidate
                                                               \<and> election_won ?candidate_state = abstract_model.active_leader abstract_state candidate)
            \<and> (election_won ?candidate_state \<longrightarrow> started_join_since_last_reboot ?candidate_state
                                               \<and> abstract_model.effective_config
                                                     initial_configuration
                                                     (publications_committed abstract_state)
                                                     (abstract_model.current_published_history abstract_state candidate)
                                                     (last_committed_configuration_of abstract_state candidate)))
                                   \<and> (election_won ?candidate_state \<longrightarrow> node_role ?candidate_state = Master_Eligible)"
          using old_transient unfolding transient_link_def by blast
        have transient: "transient_link initial_configuration abstract_state candidate ?new_candidate_state"
          unfolding transient_link_def
        proof (intro conjI)
          show "node_role ?new_candidate_state = Master_Eligible \<longrightarrow>
            (started_join_since_last_reboot ?new_candidate_state \<longrightarrow> 0 < current_term_of abstract_state candidate
                                                                   \<and> election_won ?new_candidate_state = abstract_model.active_leader abstract_state candidate)
            \<and> (election_won ?new_candidate_state \<longrightarrow> started_join_since_last_reboot ?new_candidate_state
                                                   \<and> abstract_model.effective_config
                                                         initial_configuration
                                                         (publications_committed abstract_state)
                                                         (abstract_model.current_published_history abstract_state candidate)
                                                         (last_committed_configuration_of abstract_state candidate))"
            using old_transient_facts by simp
          show "abstract_model.fresh_votes
                    abstract_state
                    candidate
                    (current_term_of abstract_state candidate)
                    (publications_accepted abstract_state candidate)
                    (join_votes ?new_candidate_state)"
            using votes by simp
          show "election_won ?new_candidate_state \<longrightarrow> java_is_election_quorum
                                                         ?new_candidate_state
                                                         (join_votes ?new_candidate_state)
                                                    \<and> known_tip
                                                          initial_configuration
                                                          abstract_state
                                                          candidate ?new_candidate_state"
            using election_quorum known by simp
          show "election_won ?new_candidate_state \<longrightarrow> node_role ?new_candidate_state = Master_Eligible"
            using old_transient_facts by simp
          show "node_role ?new_candidate_state = Master_Eligible
                \<or> join_votes ?new_candidate_state = {} \<and> publish_votes ?new_candidate_state = {}"
            using role by simp
        qed
        show ?thesis using persisted transient unfolding node_link_def by blast
      qed
      have "linked
                initial_configuration
                (state\<lparr>
                  java_memory   := (java_memory state)(candidate := ?new_candidate_state),
                  java_disk     := (java_disk state)(candidate := disk_of ?new_candidate_state),
                  java_messages := java_messages state
                \<rparr>)
                abstract_state"
        by (rule master_node_update[OF grows_refl _ role new_candidate_link _ _ _ _ linkedD(4)[OF link]])
           (use role sent_response in \<open>auto\<close>)
      then show ?thesis using call_result by (intro exI[of _ abstract_state]) simp
    next
      case True
      then have not_yet_won: "\<not> election_won ?candidate_state" and won: "?won" by auto
      let ?next_abstract_state = "abstract_state\<lparr>
        elections_won := (elections_won abstract_state)((candidate, current_term_of abstract_state candidate) :=
            Some \<lparr>
              election_votes                   = ?new_votes,
              election_last_accepted_history   = publications_accepted abstract_state candidate,
              election_committed_configuration = last_committed_configuration_of abstract_state candidate
            \<rparr>)
      \<rparr>"
      let ?new_candidate_state = "?candidate_state\<lparr>
        join_votes             := ?new_votes,
        election_won           := True,
        last_published_version := position_version (last_accepted_position ?candidate_state)
      \<rparr>"
      have call_result: "java_call state (Java_Handle_Join
                                              voter
                                              voter_role
                                              candidate
                                              join_term
                                              voter_position)
                         =
          state\<lparr>
            java_memory   := (java_memory state)(candidate := ?new_candidate_state),
            java_disk     := (java_disk state)(candidate := disk_of ?new_candidate_state),
            java_messages := java_messages state
          \<rparr>"
        using guard role not_yet_won won by (simp add: Let_def java_put_def)
      have none: "elections_won abstract_state (candidate, current_term_of abstract_state candidate) = None"
        using node_linkD(15)[OF candidate_link role started_flag] not_yet_won
        unfolding abstract_model.active_leader_def by auto
      have quorums:
        "quorum (last_committed_configuration_of abstract_state candidate) ?new_votes"
        "quorum (config_of_tip_of initial_configuration (publications_accepted abstract_state candidate)) ?new_votes"
      proof -
        have won_quorums: "quorum (last_committed_configuration ?candidate_state) ?new_votes"
          "quorum (last_accepted_configuration ?candidate_state) ?new_votes"
          using won unfolding java_is_election_quorum_def has_quorum_eq by simp_all
        have accepted: "last_accepted_configuration ?candidate_state
            = config_of_tip_of initial_configuration (publications_accepted abstract_state candidate)"
          by (rule node_linkD(6)[OF candidate_link accepted_configuration_nonempty
                quorum_not_stale[OF won_quorums(2)]])
        have committed: "last_committed_configuration_of abstract_state candidate =
            (if last_committed_configuration ?candidate_state = {}
             then initial_configuration else last_committed_configuration ?candidate_state)"
          by (rule node_linkD(7)[OF candidate_link quorum_not_stale[OF won_quorums(1)]])
        show "quorum (last_committed_configuration_of abstract_state candidate) ?new_votes"
          "quorum (config_of_tip_of initial_configuration (publications_accepted abstract_state candidate)) ?new_votes"
          using won_quorums committed accepted by (auto dest: quorum_nonempty)
      qed
      have step: "abstract_model.transition initial_configuration abstract_state ?next_abstract_state"
        by (rule abstract_model.transition.win_election[OF started none quorums votes])
      have base: "term_of_tip_of (publications_accepted abstract_state candidate)
          < current_term_of abstract_state candidate"
      proof -
        have messages_invariant: "abstract_model.messages_ok initial_configuration abstract_state"
          and leadership_invariant: "abstract_model.leadership_ok initial_configuration abstract_state"
          using abstract_model.dynamic_invariants[OF reach] by auto
        show ?thesis
          by (rule abstract_model.new_election_base[OF messages_invariant leadership_invariant none started
                quorums(2) votes])
      qed
      have nothing_published:
        "abstract_model.published_by
             abstract_state
             candidate
             (current_term_of abstract_state candidate)
         =
          {}"
        using abstract_model.leadershipD(8)[OF abstract_model.dynamic_invariants[THEN conjunct2, THEN conjunct2, OF reach]]
          none
        unfolding abstract_model.published_by_def by fastforce
      have next_tip: "abstract_model.last_published_history_of
                          ?next_abstract_state
                          (candidate, current_term_of abstract_state candidate)
                      = publications_accepted abstract_state candidate"
        using abstract_model.last_published_history_win_new[OF nothing_published, of "\<lparr>
          election_votes                   = ?new_votes,
          election_last_accepted_history   = publications_accepted abstract_state candidate,
          election_committed_configuration = last_committed_configuration_of abstract_state candidate
        \<rparr>"] by simp
      have tips_other: "abstract_model.last_published_history_of
                            ?next_abstract_state
                            (other_node, current_term_of abstract_state other_node)
                        = abstract_model.last_published_history_of
                              abstract_state
                              (other_node, current_term_of abstract_state other_node)"
        if "other_node \<noteq> candidate" for other_node
        using abstract_model.last_published_history_win_other[of
            "(other_node, current_term_of abstract_state other_node)"
            candidate
            "current_term_of abstract_state candidate"
            abstract_state] that
        by simp
      have next_active: "abstract_model.active_leader ?next_abstract_state candidate"
        unfolding abstract_model.active_leader_def by simp
      have messages_invariant: "abstract_model.messages_ok initial_configuration abstract_state"
        using abstract_model.dynamic_invariants[OF reach] by auto
      have effective: "abstract_model.effective_config
                           initial_configuration
                           (publications_committed ?next_abstract_state)
                           (abstract_model.current_published_history ?next_abstract_state candidate)
                           (last_committed_configuration_of ?next_abstract_state candidate)"
        using abstract_model.messagesD(3)[OF messages_invariant, of candidate] next_tip by simp
      have new_candidate_link: "node_link initial_configuration ?next_abstract_state candidate ?new_candidate_state"
      proof -
        have persisted: "persisted_link initial_configuration ?next_abstract_state candidate ?new_candidate_state"
          using candidate_link[unfolded node_link_def, THEN conjunct1] unfolding persisted_link_def
          by (auto split: if_splits)
        have transient: "transient_link initial_configuration ?next_abstract_state candidate ?new_candidate_state"
        proof -
          have known: "known_tip initial_configuration ?next_abstract_state candidate ?new_candidate_state"
            using base next_tip node_linkD(1)[OF candidate_link] unfolding known_tip_def by simp
          have election_quorum: "java_is_election_quorum ?new_candidate_state (join_votes ?new_candidate_state)"
            using won unfolding java_is_election_quorum_def has_quorum_eq by simp
          have fresh_new_votes: "abstract_model.fresh_votes
                                     ?next_abstract_state
                                     candidate
                                         (current_term_of ?next_abstract_state candidate)
                                         (publications_accepted ?next_abstract_state candidate)
                                         (join_votes ?new_candidate_state)"
            using votes unfolding abstract_model.fresh_votes_def by simp
          show ?thesis
            using started started_flag next_active effective known election_quorum fresh_new_votes role
            unfolding transient_link_def by simp
        qed
        show ?thesis using persisted transient unfolding node_link_def by blast
      qed
      have frame: "other_node \<noteq> candidate \<Longrightarrow> node_frame abstract_state ?next_abstract_state other_node"
        for other_node
        unfolding node_frame_def abstract_model.active_leader_def using tips_other[of other_node] by auto
      have replies: "publish_votes ?candidate_state = {}"
      proof (rule ccontr)
        assume "publish_votes ?candidate_state \<noteq> {}"
        then obtain publish_voter where "publish_voter \<in> publish_votes ?candidate_state" by blast
        from linkedD(3)[OF link sent_response[OF this]]
        obtain history where
          history: "history \<in> publications_sent abstract_state" "owner_of_tip_of history = candidate"
            "position_of_tip_of history = last_published_position ?candidate_state"
          by auto
        have leadership_invariant: "abstract_model.leadership_ok initial_configuration abstract_state"
          using abstract_model.dynamic_invariants[OF reach] by auto
        from abstract_model.leadershipD(8)[OF leadership_invariant history(1)] history(2,3) none
          node_linkD(1)[OF candidate_link]
        show False by auto
      qed
      have "linked initial_configuration
          (state\<lparr>
            java_memory   := (java_memory state)(candidate := ?new_candidate_state),
            java_disk     := (java_disk state)(candidate := disk_of ?new_candidate_state),
            java_messages := java_messages state
          \<rparr>) ?next_abstract_state"
        by (rule master_node_update[OF transition_grows[OF step] _ role new_candidate_link frame _ _ _
              linkedD(4)[OF link]])
           (use role replies in \<open>auto\<close>)
      then show ?thesis using call_result step by (intro exI[of _ ?next_abstract_state]) simp
    qed
  qed
qed

end

end
