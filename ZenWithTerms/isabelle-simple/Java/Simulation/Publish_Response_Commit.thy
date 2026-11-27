theory Publish_Response_Commit
  imports "../Link"
begin


(* TODO java_put_rejected and java_put_accepted are not specific to these two calls. Move them into
   Link and use them in the other simulation theories, which unfold java_put by hand. *)

context simulation
begin

text \<open>
  Proof aids for the simulation of \<open>handlePublishResponse\<close> and \<open>handleCommit\<close>.

  \<^item> \<open>current_term_publication_prefix\<close>: a publication in the current term of an active leader was
    published by that leader, and is a prefix of the history that it is currently extending.
  \<^item> \<open>older_published_history_impossible\<close>: an active leader that has a publication in its
    current term cannot have an older-term accepted history as its current published history.
  \<^item> \<open>java_put_rejected\<close> and \<open>java_put_accepted\<close>: \<open>java_put\<close> unfolded for a condition that
    fails, and one that holds.
  \<^item> \<open>quorum_votes_nonempty\<close>: a quorum of a configuration is not empty.
\<close>

lemma current_term_publication_prefix:
  assumes active: "abstract_model.active_leader abstract_state node"
  assumes pub: "history \<in> publications_sent abstract_state"
  assumes term_matches: "term_of_tip_of history = current_term_of abstract_state node"
  shows "owner_of_tip_of history = node" "prefix history (abstract_model.current_published_history abstract_state node)"
proof -
  have leadership_ok_fact: "abstract_model.leadership_ok initial_configuration abstract_state" using abstract_model.dynamic_invariants[OF reach] by auto
  obtain election other_election where votes: "elections_won abstract_state (owner_of_tip_of history,current_term_of abstract_state node) = Some election" "elections_won abstract_state (node,current_term_of abstract_state node) = Some other_election"
    using abstract_model.leadershipD(8)[OF leadership_ok_fact pub] active term_matches unfolding abstract_model.active_leader_def by auto
  show "owner_of_tip_of history = node" by (rule abstract_model.dynamic_one_election_candidate_per_term[OF reach votes])
  with abstract_model.leadershipD(9)[OF leadership_ok_fact pub] term_matches
  show "prefix history (abstract_model.current_published_history abstract_state node)" by simp
qed

lemma older_published_history_impossible:
  assumes active: "abstract_model.active_leader abstract_state node"
  assumes pub: "history \<in> publications_sent abstract_state"
  assumes term_matches: "term_of_tip_of history = current_term_of abstract_state node"
  assumes old: "term_of_tip_of (abstract_model.current_published_history abstract_state node) < current_term_of abstract_state node"
  assumes base: "abstract_model.current_published_history abstract_state node = publications_accepted abstract_state node"
  shows False
proof -
  have messages_ok_fact: "abstract_model.messages_ok initial_configuration abstract_state" and publications_ok_fact: "abstract_model.publications_ok initial_configuration abstract_state" using abstract_model.dynamic_invariants[OF reach] by auto
  have mem: "abstract_model.current_published_history abstract_state node \<in> insert [] (publications_sent abstract_state)" using base abstract_model.messagesD(1)[OF messages_ok_fact, of node] by simp
  have "position_of_tip_of history \<le> position_of_tip_of (abstract_model.current_published_history abstract_state node)"
    using abstract_model.prefix_of_sent[OF publications_ok_fact mem current_term_publication_prefix(2)[OF active pub term_matches]] by auto
  from position_term_mono[OF this] old term_matches
  show False by simp
qed

lemma java_put_rejected: "\<not> condition \<Longrightarrow> java_put
                                            state
                                            node
                                            condition
                                            new_node_memory_state
                                            new_messages
                                        =
                                         state"
  by (simp add: java_put_def)

lemma java_put_accepted:
  "condition \<Longrightarrow> java_put state node condition new_node_memory_state new_messages = state\<lparr>
    java_memory   := (java_memory state)(node := new_node_memory_state),
    java_disk     := (if node_role new_node_memory_state = Master_Eligible then (java_disk state)(node := disk_of new_node_memory_state) else java_disk state),
    java_messages := java_messages state \<union> new_messages
  \<rparr>"
  by (simp add: java_put_def)

lemma quorum_votes_nonempty:
  assumes "quorum configuration votes"
  shows "votes \<noteq> {}"
  using assms unfolding quorum_def majority_def by auto

lemma simulate_handle_publish_response:
  assumes contract: "caller_contract
                         initial_configuration
                         initial_value
                         state
                         (Java_Handle_Publish_Response voter voter_role leader position)"
  shows "\<exists>next_abstract_state. (next_abstract_state = abstract_state
                                \<or> abstract_model.transition
                                      initial_configuration
                                      abstract_state
                                      next_abstract_state)
                               \<and> linked
                                     initial_configuration
                                     (java_call state (Java_Handle_Publish_Response
                                                           voter
                                                           voter_role
                                                           leader
                                                           position))
                                     next_abstract_state"
proof -
  let ?leader_state = "java_memory state leader"
  from contract have master: "node_role ?leader_state = Master_Eligible"
    and sent: "Response_Msg voter voter_role leader position \<in> java_messages state" by simp_all
  have dv: "disk_view state leader = ?leader_state" by (rule disk_view_master[OF master])
  have nl: "node_link initial_configuration abstract_state leader ?leader_state" using linkedD(1)[OF link, of leader] dv by simp
  have sr: "\<And>supporter. supporter \<in> publish_votes ?leader_state \<Longrightarrow>
      Response_Msg supporter Master_Eligible leader (last_published_position ?leader_state) \<in> java_messages state"
    using linkedD(2)[OF link, of _ leader] dv by simp
  let ?published_history = "abstract_model.current_published_history abstract_state leader"
  let ?new_votes = "if voter_role = Master_Eligible then insert voter (publish_votes ?leader_state) else publish_votes ?leader_state"
  let ?new_leader_state = "?leader_state\<lparr>publish_votes := ?new_votes\<rparr>"
  have master': "node_role ?new_leader_state = Master_Eligible" using master by simp
  show ?thesis
  proof (cases "election_won ?leader_state \<and> position = last_published_position ?leader_state")
    case False
    then have "java_call state (Java_Handle_Publish_Response voter voter_role leader position) = state"
      unfolding java_call.simps Let_def by (rule java_put_rejected)
    with link show ?thesis by (intro exI[of _ abstract_state]) simp
  next
    case True
    then have won: "election_won ?leader_state" and position: "position = last_published_position ?leader_state" by simp_all
    let ?new_messages = "if java_is_publish_quorum ?leader_state ?new_votes then {Commit_Msg
                                                                                      leader
                                                                                      destination
                                                                                      position | destination. True} else {}"
    let ?new_state = "state\<lparr>
      java_memory   := (java_memory state)(leader := ?new_leader_state),
      java_disk     := (java_disk state)(leader := disk_of ?new_leader_state),
      java_messages := java_messages state \<union> ?new_messages
    \<rparr>"
    have jc: "java_call state (Java_Handle_Publish_Response voter voter_role leader position) = ?new_state"
      using True master' by (simp add: Let_def java_put_def)
    have dv': "disk_view ?new_state leader = ?new_leader_state" using master' by (simp add: disk_view_def)
    have active: "abstract_model.active_leader abstract_state leader"
      using won node_linkD(3)[OF nl master] by simp
    have term_match: "position_term position = current_term_of abstract_state leader" using position node_linkD(1)[OF nl] by simp
    have replies: "\<forall>supporter\<in>?new_votes. Response_Msg supporter Master_Eligible leader position \<in> java_messages state"
      using sent position sr by (cases "voter_role = Master_Eligible") auto
    have local_replies: "\<forall>supporter\<in>publish_votes (disk_view ?new_state leader).
        Response_Msg
            supporter
            Master_Eligible
            leader
            (last_published_position (disk_view ?new_state leader)) \<in> java_messages ?new_state"
      using replies position dv' by auto
    have same: "\<And>other_node. other_node \<noteq> leader \<Longrightarrow> java_memory ?new_state other_node = java_memory state other_node
                                                   \<and> java_disk ?new_state other_node = java_disk state other_node" by simp
    have disk: "java_disk ?new_state leader = disk_of (java_memory ?new_state leader)" by simp
    show ?thesis
    proof (cases "java_is_publish_quorum ?leader_state ?new_votes")
      case False
      then have no_new_messages: "?new_messages = {}" by simp
      have nl': "node_link initial_configuration abstract_state leader (disk_view ?new_state leader)" using nl master dv' by simp
      have "linked initial_configuration ?new_state abstract_state"
        by (rule link_update[OF link grows_refl same nl' _ disk local_replies])
           (use linkedD(4)[OF link] False master' in \<open>auto simp: node_frame_def\<close>)
      with jc show ?thesis by (intro exI[of _ abstract_state]) simp
    next
      case True
      have no_new_messages: "?new_messages = {Commit_Msg leader destination position | destination. True}" using True by simp
      have "?new_votes \<noteq> {}" using True quorum_votes_nonempty unfolding java_is_publish_quorum_def has_quorum_eq by blast
      then obtain p0 where "p0 \<in> ?new_votes" by blast
      from linkedD(3)[OF link replies[rule_format, OF this]]
      obtain history where mem: "history \<in> publications_sent abstract_state" and tip_position: "position_of_tip_of history = position" by auto
      have ht: "term_of_tip_of history = current_term_of abstract_state leader" by (simp add: tip_position term_match)
      have tip: "?published_history \<in> publications_sent abstract_state" "position_of_tip_of ?published_history = position" "owner_of_tip_of ?published_history = leader"
        "last_published_configuration ?leader_state = config_of_tip_of initial_configuration ?published_history"
        using node_linkD(10)[OF nl won] position node_linkD(1)[OF nl] older_published_history_impossible[OF active mem ht]
        unfolding known_tip_def by auto
      have cur: "term_of_tip_of ?published_history = current_term_of abstract_state leader" using tip(2) term_match by simp
      have acks: "\<forall>supporter\<in>?new_votes. (supporter,?published_history) \<in> publish_responses_sent abstract_state"
      proof (intro ballI)
        fix supporter
        assume "supporter \<in> ?new_votes"
        from linkedD(3)[OF link replies[rule_format, OF this]]
        obtain acknowledged_history where acknowledged_history: "acknowledged_history \<in> publications_sent abstract_state" "(supporter,acknowledged_history) \<in> publish_responses_sent abstract_state" "position_of_tip_of acknowledged_history = position" by auto
        have "acknowledged_history = ?published_history" by (rule abstract_model.dynamic_unique_publication[OF reach acknowledged_history(1) tip(1)]) (simp add: acknowledged_history(3) tip(2))
        with acknowledged_history(2) show "(supporter,?published_history) \<in> publish_responses_sent abstract_state" by simp
      qed
      let ?next_abstract_state = "abstract_state\<lparr>publications_committed := insert ?published_history (publications_committed abstract_state)\<rparr>"
      have joint: "abstract_model.acknowledged_by_joint_quorum initial_configuration abstract_state ?published_history"
      proof (cases "?published_history \<in> publications_committed abstract_state")
        case True
        have "abstract_model.publications_ok initial_configuration abstract_state" using abstract_model.dynamic_invariants[OF reach] by auto
        from abstract_model.publicationsD(6)[OF this True]
        show ?thesis .
      next
        case False
        have "last_committed_configuration_of abstract_state leader = last_committed_configuration ?leader_state"
          using node_linkD(7)[OF nl node_link_won_configurations(2)[OF nl won]] \<open>java_is_publish_quorum ?leader_state ?new_votes\<close>
          unfolding java_is_publish_quorum_def has_quorum_eq by (auto dest: quorum_nonempty)
        with \<open>java_is_publish_quorum ?leader_state ?new_votes\<close> tip(4) acks
        have "\<exists>votes. quorum (last_committed_configuration_of abstract_state leader) votes
                      \<and> quorum (config_of_tip_of initial_configuration ?published_history) votes
                      \<and> (\<forall>supporter\<in>votes. (supporter,?published_history) \<in> publish_responses_sent abstract_state)"
          unfolding java_is_publish_quorum_def has_quorum_eq by (intro exI[of _ ?new_votes]) auto
        with abstract_model.first_commit_quorums_agree[OF reach node_linkD(14)[OF nl master won] False]
        show ?thesis by simp
      qed
      have step: "abstract_model.transition initial_configuration abstract_state ?next_abstract_state"
        by (rule abstract_model.transition.commit[OF active refl tip(1) cur tip(3) joint])
      have nl': "node_link initial_configuration ?next_abstract_state leader (disk_view ?new_state leader)"
        using node_link_quorum_commits[OF nl subset_insertI] master dv' by simp
      have frame: "other_node \<noteq> leader \<Longrightarrow> node_frame abstract_state ?next_abstract_state other_node" for other_node
        unfolding node_frame_def abstract_model.active_leader_def by simp
      have new: "wire_link ?next_abstract_state message" if "message \<in> java_messages ?new_state" "message \<notin> java_messages state" for message
      proof -
        have ex: "\<exists>destination. message = Commit_Msg leader destination position" using that True by auto
        then obtain destination where "message = Commit_Msg leader destination position" by blast
        then show ?thesis using tip by (auto intro!: bexI[of _ ?published_history])
      qed
      have unique: "wire_unique (java_messages ?new_state)"
        using wire_unique_control[OF linkedD(4)[OF link], of "?new_messages"] no_new_messages by auto
      have "linked initial_configuration ?new_state ?next_abstract_state"
        by (rule link_update[OF link transition_grows[OF step] same nl' frame disk local_replies _ _ _ new unique])
           (use master' in auto)
      with jc step show ?thesis by (intro exI[of _ ?next_abstract_state]) simp
    qed
  qed
qed

lemma simulate_handle_commit:
  assumes contract: "caller_contract
                         initial_configuration
                         initial_value
                         state
                         (Java_Handle_Commit node leader position)"
  shows "\<exists>next_abstract_state. (next_abstract_state = abstract_state
                                \<or> abstract_model.transition
                                      initial_configuration
                                      abstract_state
                                      next_abstract_state)
                               \<and> linked
                                     initial_configuration
                                     (java_call state (Java_Handle_Commit node leader position))
                                     next_abstract_state"
proof -
  let ?node_state = "java_memory state node"
  from contract have sent: "Commit_Msg leader node position \<in> java_messages state"
    and late: "election_won ?node_state
               \<and> position_version position \<noteq> last_published_version ?node_state \<longrightarrow>
        last_committed_configuration ?node_state = last_accepted_configuration ?node_state"
    by (simp_all add: Let_def)
  show ?thesis
  proof (cases "position_term position = current_term ?node_state
                \<and> position = last_accepted_position ?node_state")
    case False
    then have "java_call state (Java_Handle_Commit node leader position) = state"
      unfolding java_call.simps Let_def by (rule java_put_rejected)
    with link show ?thesis by (intro exI[of _ abstract_state]) simp
  next
    case True
    then have t0: "position_term position = current_term ?node_state" and position: "position = last_accepted_position ?node_state"
      by (rule conjunct1, rule conjunct2)
    let ?new_node_state = "queue_state (?node_state\<lparr>last_committed_configuration := last_accepted_configuration ?node_state\<rparr>)"
    show ?thesis
    proof (cases "node_role ?node_state = Master_Eligible")
      case master: True
      have dv: "disk_view state node = ?node_state" by (rule disk_view_master[OF master])
      have nl: "node_link initial_configuration abstract_state node ?node_state" using linkedD(1)[OF link, of node] dv by simp
      have sr: "\<And>supporter. supporter \<in> publish_votes ?node_state \<Longrightarrow>
          Response_Msg supporter Master_Eligible node (last_published_position ?node_state) \<in> java_messages state"
        using linkedD(2)[OF link, of _ node] dv by simp
      have ydef: "?new_node_state = ?node_state\<lparr>last_committed_configuration := last_accepted_configuration ?node_state\<rparr>"
        using master by (simp add: queue_state_def)
      have master': "node_role ?new_node_state = Master_Eligible" using master by (simp add: ydef)
      let ?new_state = "state\<lparr>
        java_memory := (java_memory state)(node := ?new_node_state),
        java_disk   := (java_disk state)(node := disk_of ?new_node_state)
      \<rparr>"
      have jc: "java_call state (Java_Handle_Commit node leader position) = ?new_state"
        unfolding java_call.simps Let_def by (subst java_put_accepted[OF True]) (simp add: master')
      have dv': "disk_view ?new_state node = ?new_node_state" using master' by (simp add: disk_view_def)
      have same: "\<And>other_node. other_node \<noteq> node \<Longrightarrow> java_memory ?new_state other_node = java_memory state other_node
                                                   \<and> java_disk ?new_state other_node = java_disk state other_node" by simp
      have disk: "java_disk ?new_state node = disk_of (java_memory ?new_state node)" by simp
      have replies: "\<forall>supporter\<in>publish_votes (disk_view ?new_state node).
          Response_Msg
              supporter
              Master_Eligible
              node
              (last_published_position (disk_view ?new_state node)) \<in> java_messages ?new_state"
        using sr dv' by (auto simp: ydef)
      show ?thesis
      proof (cases "election_won ?node_state
                    \<and> position_version position \<noteq> last_published_version ?node_state")
        case True
        from late[rule_format, OF True]
        have eq: "last_committed_configuration ?node_state = last_accepted_configuration ?node_state" .
        have "?node_state\<lparr>last_committed_configuration := last_accepted_configuration ?node_state\<rparr> = ?node_state"
          by (rule sym, cases ?node_state, use eq in simp)
        then have "?new_node_state = ?node_state" by (rule trans[OF ydef])
        then have "?new_state = state"
          using linkedD(5)[OF link master] by (cases state) (auto simp: fun_upd_idem_iff fun_upd_def fun_eq_iff)
        with jc link show ?thesis by (intro exI[of _ abstract_state]) simp
      next
        case nolate: False
        then have guard: "election_won ?node_state \<Longrightarrow> position_version position = last_published_version ?node_state" by simp
        let ?accepted_history = "publications_accepted abstract_state node"
        let ?next_abstract_state = "abstract_state\<lparr>last_committed_configuration_of := (last_committed_configuration_of abstract_state)(node := config_of_tip_of initial_configuration ?accepted_history)\<rparr>"
        show ?thesis
        proof (cases "last_accepted_configuration ?node_state \<noteq> stale_config")
          case real: True
          obtain committed_history where committed: "committed_history \<in> publications_committed abstract_state" and hk: "position_of_tip_of committed_history = position"
            using linkedD(3)[OF link sent] by auto
          have publications_ok_fact: "abstract_model.publications_ok initial_configuration abstract_state" and messages_ok_fact: "abstract_model.messages_ok initial_configuration abstract_state"
            using abstract_model.dynamic_invariants[OF reach] by auto
          have pub: "committed_history \<in> publications_sent abstract_state" by (rule abstract_model.publicationsD(5)[OF publications_ok_fact committed])
          have pos: "0 < position_term position" using publication_positive[OF publications_ok_fact pub] hk by simp
          have term_matches: "position_term position = current_term_of abstract_state node" using t0 node_linkD(1)[OF nl] by simp
          have match: "position_of_tip_of ?accepted_history = position"
            using node_linkD(4)[OF nl] position pos unfolding normalized_def by simp
          have mem: "?accepted_history \<in> publications_sent abstract_state" using abstract_model.messagesD(1)[OF messages_ok_fact, of node] match pos by auto
          have same_h: "?accepted_history = committed_history" by (rule abstract_model.dynamic_unique_publication[OF reach mem pub]) (simp add: hk match)
          have ack: "?accepted_history \<in> publications_committed abstract_state" using same_h committed by simp
          have cur: "term_of_tip_of ?accepted_history = current_term_of abstract_state node" using match term_matches by simp
          have own: "election_won ?node_state \<Longrightarrow> ?accepted_history = abstract_model.current_published_history abstract_state node"
            using guard position linked_position_equal[OF nl] by auto
          have step: "abstract_model.transition initial_configuration abstract_state ?next_abstract_state"
            by (rule abstract_model.transition.apply_commit[OF ack cur])
          have nonempty: "last_accepted_configuration ?node_state \<noteq> {}"
            using node_linkD(5)[OF nl] mem abstract_model.publicationsD(2)[OF publications_ok_fact] by auto
          have cfg: "last_accepted_configuration ?node_state = config_of_tip_of initial_configuration ?accepted_history"
            by (rule node_linkD(6)[OF nl nonempty real])
          have known: "election_won ?node_state \<Longrightarrow> known_tip initial_configuration ?next_abstract_state node (?node_state\<lparr>last_committed_configuration := last_accepted_configuration ?node_state\<rparr>)"
            using node_linkD(10)[OF nl] unfolding known_tip_def by simp
          have nl': "node_link initial_configuration ?next_abstract_state node ?new_node_state"
          proof -
            have pl: "persisted_link initial_configuration ?next_abstract_state node ?new_node_state"
              using nl[unfolded node_link_def, THEN conjunct1] nonempty cfg real
              unfolding ydef persisted_link_def by (auto split: if_splits)
            have act_b: "abstract_model.active_leader ?next_abstract_state node = abstract_model.active_leader abstract_state node"
              unfolding abstract_model.active_leader_def by simp
            have eff: "election_won ?node_state \<Longrightarrow> abstract_model.effective_config
                                                      initial_configuration
                                                      (publications_committed ?next_abstract_state)
                                                      (abstract_model.current_published_history ?next_abstract_state node)
                                                      (last_committed_configuration_of ?next_abstract_state node)"
              using own ack by (simp add: abstract_model.effective_config_def)
            have fv: "abstract_model.fresh_votes ?next_abstract_state node
                                                                          (current_term_of ?next_abstract_state node)
                                                                          (publications_accepted ?next_abstract_state node)
                                                                          (join_votes ?new_node_state)"
              using node_linkD(8)[OF nl] unfolding abstract_model.fresh_votes_def by (simp add: ydef)
            have iq: "election_won ?node_state \<Longrightarrow> java_is_election_quorum ?new_node_state (join_votes ?new_node_state)"
              using node_linkD(9)[OF nl] unfolding java_is_election_quorum_def has_quorum_eq by (simp add: ydef)
            have tl: "transient_link initial_configuration ?next_abstract_state node ?new_node_state"
              using node_linkD(2)[OF nl master] node_linkD(15)[OF nl master] node_linkD(16)[OF nl master]
                act_b eff fv iq known master
              unfolding transient_link_def by (simp add: ydef)
            show ?thesis using pl tl unfolding node_link_def by blast
          qed
          have frame: "other_node \<noteq> node \<Longrightarrow> node_frame abstract_state ?next_abstract_state other_node" for other_node
            unfolding node_frame_def abstract_model.active_leader_def by simp
          have nl'': "node_link initial_configuration ?next_abstract_state node (disk_view ?new_state node)" using nl' dv' by simp
          have "linked initial_configuration ?new_state ?next_abstract_state"
            by (rule link_update[OF link transition_grows[OF step] same nl'' frame disk replies])
               (use master' linkedD(4)[OF link] in simp_all)
          with jc step show ?thesis by (intro exI[of _ ?next_abstract_state]) simp
        next
          case False
          have stale: "last_accepted_configuration ?node_state = stale_config" using False by simp
          have not_won: "\<not> election_won ?node_state"
          proof
            assume won: "election_won ?node_state"
            from node_link_won_configurations(1)[OF nl won] stale
            show False by simp
          qed
          have nl': "node_link initial_configuration abstract_state node ?new_node_state" using nl not_won stale master
            unfolding node_link_defs known_tip_def java_is_election_quorum_def has_quorum_eq
              abstract_model.fresh_votes_def abstract_model.active_leader_def ydef
            by (auto split: if_splits)
          have nl'': "node_link
                          initial_configuration
                          abstract_state
                          node
                          (disk_view ?new_state node)" using nl' dv' by simp
          have "linked initial_configuration ?new_state abstract_state"
            by (rule link_update[OF link grows_refl same nl'' _ disk replies])
               (use master' linkedD(4)[OF link] in simp_all)
          with jc show ?thesis by (intro exI[of _ abstract_state]) simp
        qed
      qed
    next
      case other: False
      let ?new_state = "state\<lparr>java_memory := (java_memory state)(node := ?new_node_state)\<rparr>"
      have role': "node_role ?new_node_state = node_role ?node_state" by (simp add: queue_state_def)
      have jc: "java_call state (Java_Handle_Commit node leader position) = ?new_state"
        unfolding java_call.simps Let_def by (subst java_put_accepted[OF True]) (simp add: other role')
      have view: "disk_view ?new_state node = disk_view state node"
        using other role' by (simp add: disk_view_def)
      have same: "\<And>other_node. other_node \<noteq> node \<Longrightarrow> java_memory ?new_state other_node = java_memory state other_node
                                                   \<and> java_disk ?new_state other_node = java_disk state other_node" by simp
      have no_votes: "publish_votes (disk_view state node) = {}"
        using other by (simp add: disk_view_other memory_of_disk_def)
      have "linked initial_configuration ?new_state abstract_state"
        by (rule link_update[OF link grows_refl same])
           (use linkedD(4)[OF link] linkedD(1)[OF link, of node] linkedD(6)[OF link, of node] linkedD(7)[OF link, of node] other role' view no_votes
            in \<open>auto simp: node_frame_def queue_state_def memory_link_def\<close>)
      with jc show ?thesis by (intro exI[of _ abstract_state]) simp
    qed
  qed
qed

end

end
