theory Client_Value
  imports "../Link"
begin

section \<open>Simulating \<open>handleClientValue\<close>\<close>

text \<open>
  A leader that publishes a client value makes the abstract \<open>publish\<close> transition. The helper lemmas
  describe what a leader that is active in the abstract model has published in its current term.
\<close>

context simulation
begin

(* TODO Move current_publication_prefix and older_tip_impossible into Link, so that Publish_Request
   and Publish_Response_Commit can use them without Publish_Request importing this theory. *)

text \<open>
  A publication history that was published in the current term of an active leader was published
  by that leader, and is a prefix of the history that the leader is currently extending.
\<close>

lemma current_publication_prefix:
  assumes active: "abstract_model.active_leader abstract_state node"
  assumes published: "history \<in> publications_sent abstract_state"
  assumes same_term: "term_of_tip_of history = current_term_of abstract_state node"
  shows "owner_of_tip_of history = node"
    "prefix history (abstract_model.current_published_history abstract_state node)"
proof -
  have leadership: "abstract_model.leadership_ok initial_configuration abstract_state"
    using abstract_model.dynamic_invariants[OF reach] by auto
  obtain owner_election leader_election where votes:
    "elections_won abstract_state (owner_of_tip_of history, current_term_of abstract_state node) = Some owner_election"
    "elections_won abstract_state (node, current_term_of abstract_state node) = Some leader_election"
    using abstract_model.leadershipD(8)[OF leadership published] active same_term
    unfolding abstract_model.active_leader_def by auto
  show "owner_of_tip_of history = node"
    by (rule abstract_model.dynamic_one_election_candidate_per_term[OF reach votes])
  with abstract_model.leadershipD(9)[OF leadership published] same_term
  show "prefix history (abstract_model.current_published_history abstract_state node)" by simp
qed

text \<open>
  A leader that is still extending the history that it accepted before it won its election, which
  ends in an earlier term, has published nothing in its current term.
\<close>

lemma older_tip_impossible:
  assumes active: "abstract_model.active_leader abstract_state node"
  assumes published: "history \<in> publications_sent abstract_state"
  assumes same_term: "term_of_tip_of history = current_term_of abstract_state node"
  assumes older: "term_of_tip_of (abstract_model.current_published_history abstract_state node)
                  < current_term_of abstract_state node"
  assumes base: "abstract_model.current_published_history abstract_state node
                 = publications_accepted abstract_state node"
  shows False
proof -
  have messages: "abstract_model.messages_ok initial_configuration abstract_state"
    and publications: "abstract_model.publications_ok initial_configuration abstract_state"
    using abstract_model.dynamic_invariants[OF reach] by auto
  have member: "abstract_model.current_published_history abstract_state node
                \<in> insert [] (publications_sent abstract_state)"
    using base abstract_model.messagesD(1)[OF messages, of node] by simp
  have "position_of_tip_of history
        \<le> position_of_tip_of (abstract_model.current_published_history abstract_state node)"
    using abstract_model.prefix_of_sent[OF publications member
        current_publication_prefix(2)[OF active published same_term]] by auto
  from position_term_mono[OF this] older same_term
  show False by simp
qed

lemma simulate_handle_client_value:
  assumes contract: "caller_contract
                         initial_configuration
                         initial_value
                         state
                         (Java_Handle_Client_Value
                              leader
                              new_term
                              version
                              new_value
                              new_config
                              previous_config)"
  shows "\<exists>next_abstract_state. (next_abstract_state = abstract_state
                                \<or> abstract_model.transition
                                      initial_configuration
                                      abstract_state
                                      next_abstract_state)
                               \<and> linked
                                     initial_configuration
                                     (java_call state (Java_Handle_Client_Value
                                                           leader
                                                           new_term
                                                           version
                                                           new_value
                                                           new_config
                                                           previous_config))
                                     next_abstract_state"
proof (cases "java_call state (Java_Handle_Client_Value
                                   leader
                                   new_term
                                   version
                                   new_value
                                   new_config
                                   previous_config)
              =
               state")
  case True
  with link show ?thesis by (intro exI[of _ abstract_state]) simp
next
  case changes: False
  note checks = java_put_changed[OF changes[unfolded java_call.simps Let_def], simplified]
  let ?leader_state = "java_memory state leader"
  from contract have master: "node_role ?leader_state = Master_Eligible"
    and previous: "previous_config = last_committed_configuration ?leader_state"
    by (simp_all add: Let_def)
  have leader_view: "disk_view state leader = ?leader_state" by (rule disk_view_master[OF master])
  have leader_link: "node_link initial_configuration abstract_state leader ?leader_state"
    using linkedD(1)[OF link, of leader] leader_view by simp
  let ?accepted_history = "publications_accepted abstract_state leader"
  let ?request = "\<lparr>
    publication_position        = \<lparr>position_term = new_term, position_version = version\<rparr>,
    publication_owner           = leader,
    publication_config          = new_config,
    publication_previous_config = last_committed_configuration ?leader_state
  \<rparr>"
  let ?new_history = "?accepted_history @ [?request]"
  let ?next_abstract_state = "abstract_state\<lparr>publications_sent := insert ?new_history (publications_sent abstract_state)\<rparr>"
  let ?next_leader_state = "?leader_state\<lparr>
    last_published_version       := version,
    last_published_configuration := new_config,
    publish_votes                := {}
  \<rparr>"
  let ?new_messages = "{Publish_Msg destination ?request new_value | destination. True}"
  let ?next_state = "state\<lparr>
    java_memory   := (java_memory state)(leader := ?next_leader_state),
    java_disk     := (java_disk state)(leader := disk_of ?next_leader_state),
    java_messages := java_messages state \<union> ?new_messages
  \<rparr>"
  from checks have won: "election_won ?leader_state"
    and published_version: "last_published_version ?leader_state = position_version (last_accepted_position ?leader_state)"
    and term_matches: "new_term = current_term ?leader_state"
    and version_increases: "last_published_version ?leader_state < version"
    and config_change_allowed: "new_config \<noteq> last_accepted_configuration ?leader_state \<Longrightarrow>
      last_committed_configuration ?leader_state = last_accepted_configuration ?leader_state"
    and proposed: "quorum new_config (join_votes ?leader_state)"
    by simp_all
  have abstract_term_matches: "new_term = current_term_of abstract_state leader"
    using term_matches node_linkD(1)[OF leader_link] by simp
  have result: "java_call state (Java_Handle_Client_Value
                                     leader
                                     new_term
                                     version
                                     new_value
                                     new_config
                                     previous_config)
                =
                 ?next_state"
    using checks previous master by (simp add: java_put_def Let_def)
  have active: "abstract_model.active_leader abstract_state leader"
    using won node_linkD(3)[OF leader_link master] by simp
  have current_history: "abstract_model.current_published_history abstract_state leader = ?accepted_history"
    by (rule linked_position_equal[OF leader_link won published_version])
  have committed_quorum: "quorum (last_committed_configuration ?leader_state) (join_votes ?leader_state)"
    and accepted_quorum: "quorum (last_accepted_configuration ?leader_state) (join_votes ?leader_state)"
    using node_linkD(9)[OF leader_link won] unfolding java_is_election_quorum_def has_quorum_eq by auto
  have accepted_config: "last_accepted_configuration ?leader_state = config_of_tip_of initial_configuration ?accepted_history"
    by (rule node_linkD(6)[OF leader_link quorum_nonempty[OF accepted_quorum]
          node_link_won_configurations(1)[OF leader_link won]])
  have committed_config: "last_committed_configuration_of abstract_state leader = last_committed_configuration ?leader_state"
    using node_linkD(7)[OF leader_link node_link_won_configurations(2)[OF leader_link won]]
      quorum_nonempty[OF committed_quorum] by simp
  have abstract_version_increases: "position_version (position_of_tip_of ?accepted_history) < version"
    by (rule linked_boot_versions[OF leader_link]) (simp add: published_version[symmetric] version_increases)
  have step: "abstract_model.transition initial_configuration abstract_state ?next_abstract_state"
    by (rule abstract_model.transition.publish[OF active current_history abstract_version_increases _ proposed
          node_linkD(8)[OF leader_link]])
       (use config_change_allowed accepted_config committed_config abstract_term_matches in \<open>auto\<close>)
  have after: "abstract_model.dynamic_reachable initial_configuration ?next_abstract_state"
    by (rule abstract_model.dynamic_reachable.advance[OF reach step])
  have leadership: "abstract_model.leadership_ok initial_configuration abstract_state"
    using abstract_model.dynamic_invariants[OF reach] by auto
  have new_position: "position_of_tip_of ?new_history = \<lparr>
    position_term    = new_term,
    position_version = version
  \<rparr>"
    and new_owner: "owner_of_tip_of ?new_history = leader"
    by (simp_all)
  have new: "?new_history \<notin> publications_sent abstract_state"
  proof
    assume "?new_history \<in> publications_sent abstract_state"
    from abstract_model.leadershipD(9)[OF leadership this] new_position new_owner abstract_term_matches current_history
    show False by simp
  qed
  have no_collision: "publication_position prior_request \<noteq> publication_position ?request"
    if prior: "Publish_Msg destination prior_request prior_value \<in> java_messages state"
    for destination prior_request prior_value
  proof
    assume positions: "publication_position prior_request = publication_position ?request"
    obtain parent where prior_history: "parent @ [prior_request] \<in> publications_sent abstract_state"
      using linkedD(3)[OF link prior] by auto
    have "parent @ [prior_request] = ?new_history"
      by (rule abstract_model.dynamic_unique_publication[OF after]) (simp_all add: prior_history positions)
    with prior_history new show False by simp
  qed
  have next_leadership: "abstract_model.leadership_ok initial_configuration ?next_abstract_state"
    using abstract_model.dynamic_invariants[OF after] by auto
  have current_history_of_term:
    "abstract_model.last_published_history_of abstract_state (leader, new_term) = ?accepted_history"
    using current_history abstract_term_matches by simp
  have next_history_of_term:
    "abstract_model.last_published_history_of ?next_abstract_state (leader, new_term) = ?new_history"
    by (rule abstract_model.last_published_history_publish_new[where candidate=leader and vote_term=new_term
          and parent="?accepted_history" and publication="?request",
          OF leadership next_leadership _ _ refl current_history_of_term])
       simp_all
  have next_history: "abstract_model.last_published_history_of ?next_abstract_state
                        (leader, current_term_of abstract_state leader) = ?new_history"
    using next_history_of_term abstract_term_matches by simp
  have histories_of_others: "abstract_model.last_published_history_of ?next_abstract_state
                               (other_node, current_term_of abstract_state other_node)
                             = abstract_model.last_published_history_of abstract_state
                                 (other_node, current_term_of abstract_state other_node)"
    if "other_node \<noteq> leader" for other_node
    using abstract_model.last_published_history_publish_other[of ?new_history leader new_term
          "(other_node, current_term_of abstract_state other_node)" abstract_state] that by simp
  have new_tip: "known_tip initial_configuration ?next_abstract_state leader ?next_leader_state"
    using won term_matches node_linkD(1)[OF leader_link] committed_quorum proposed version_increases published_version
    unfolding known_tip_def by (simp add: next_history_of_term abstract_term_matches[symmetric])
  have new_link: "node_link initial_configuration ?next_abstract_state leader ?next_leader_state"
  proof -
    have started: "started_join_since_last_reboot ?leader_state" by (rule node_linkD(16)[OF leader_link master won])
    have positive: "0 < current_term_of abstract_state leader" by (rule node_linkD(2)[OF leader_link master started])
    have next_active: "abstract_model.active_leader ?next_abstract_state leader"
      using active unfolding abstract_model.active_leader_def by simp
    have effective: "abstract_model.effective_config
                         initial_configuration
                         (publications_committed ?next_abstract_state)
                         (abstract_model.current_published_history ?next_abstract_state leader)
                         (last_committed_configuration_of ?next_abstract_state leader)"
      using next_history abstract_term_matches committed_config by (simp add: abstract_model.effective_config_def)
    have election_quorum: "java_is_election_quorum ?next_leader_state (join_votes ?next_leader_state)"
      using node_linkD(9)[OF leader_link won] unfolding java_is_election_quorum_def has_quorum_eq by simp
    have fresh: "abstract_model.fresh_votes ?next_abstract_state leader
                                                                     (current_term_of ?next_abstract_state leader)
                                                                     (publications_accepted ?next_abstract_state leader)
                                                                     (join_votes ?next_leader_state)"
      using node_linkD(8)[OF leader_link] unfolding abstract_model.fresh_votes_def by simp
    have persisted: "persisted_link initial_configuration ?next_abstract_state leader ?next_leader_state"
      using leader_link[unfolded node_link_def, THEN conjunct1] unfolding persisted_link_def
      by (auto split: if_splits)
    have transient: "transient_link initial_configuration ?next_abstract_state leader ?next_leader_state"
      using started positive next_active effective election_quorum fresh new_tip won master
      unfolding transient_link_def by simp
    show ?thesis using persisted transient unfolding node_link_def by blast
  qed
  have frame: "other_node \<noteq> leader \<Longrightarrow> node_frame abstract_state ?next_abstract_state other_node"
    for other_node
    unfolding node_frame_def abstract_model.active_leader_def using histories_of_others[of other_node] by auto
  have wires: "wire_link ?next_abstract_state message"
    if "message \<in> java_messages ?next_state" "message \<notin> java_messages state" for message
    using that quorum_nonempty[OF committed_quorum] quorum_nonempty[OF proposed]
    by auto
  have next_leader_master: "node_role ?next_leader_state = Master_Eligible" using master by simp
  have next_view: "disk_view ?next_state leader = ?next_leader_state" by (simp add: disk_view_def master)
  have "linked initial_configuration ?next_state ?next_abstract_state"
  proof (rule link_update[OF link transition_grows[OF step], where new_state = ?next_state and node = leader])
    show "\<And>other_node. other_node \<noteq> leader \<Longrightarrow>
      java_memory ?next_state other_node = java_memory state other_node
      \<and> java_disk ?next_state other_node = java_disk state other_node" by simp
    show "node_link initial_configuration ?next_abstract_state leader (disk_view ?next_state leader)"
      using next_view new_link by simp
    show "\<And>other_node. other_node \<noteq> leader \<Longrightarrow> node_frame abstract_state ?next_abstract_state other_node"
      by (rule frame)
    show "node_role (java_memory ?next_state leader) = Master_Eligible \<Longrightarrow>
      java_disk ?next_state leader = disk_of (java_memory ?next_state leader)" by simp
    show "\<forall>voter\<in>publish_votes (disk_view ?next_state leader).
        Response_Msg
            voter
            Master_Eligible
            leader
            (last_published_position (disk_view ?next_state leader))
          \<in> java_messages ?next_state"
      using next_view by simp
    show "node_role (java_memory ?next_state leader) = Data_Only \<Longrightarrow>
      memory_link ?next_abstract_state (disk_view ?next_state leader) (java_memory ?next_state leader)"
      using master by simp
    show "node_role (java_memory ?next_state leader) \<noteq> Master_Eligible \<Longrightarrow>
      \<not> election_won (java_memory ?next_state leader)"
      using master by simp
    show "java_messages state \<subseteq> java_messages ?next_state" by simp
    show "\<And>message. message \<in> java_messages ?next_state \<Longrightarrow> message \<notin> java_messages state \<Longrightarrow>
      wire_link ?next_abstract_state message" by (rule wires)
    show "wire_unique (java_messages ?next_state)"
      using no_wire_collision[OF linkedD(4)[OF link] no_collision] by simp
  qed
  with step result show ?thesis by (intro exI[of _ ?next_abstract_state]) simp
qed

end

end
