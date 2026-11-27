theory Publish_Request
  imports Client_Value
begin


(* TODO Import the shared helper lemmas (current_publication_prefix, older_tip_impossible) from
   Link rather than from Client_Value, once they have moved there. *)

context simulation
begin

text \<open>
  The simulation of \<open>handlePublishRequest\<close>. A master-eligible node's acceptance of a publication
  is the abstract \<open>receive\<close> transition. On a node that is not master-eligible it only changes the
  in-memory state, which the abstract model does not track, so it is a stutter step.
\<close>

lemma publish_request_simulation:
  assumes contract: "caller_contract
                         initial_configuration
                         initial_value
                         state
                         (Java_Handle_Publish_Request node request new_value)"
  shows "\<exists>next_abstract_state. (next_abstract_state = abstract_state
                                \<or> abstract_model.transition
                                      initial_configuration
                                      abstract_state
                                      next_abstract_state)
                               \<and> linked
                                     initial_configuration
                                     (java_call state (Java_Handle_Publish_Request
                                                           node
                                                           request
                                                           new_value))
                                     next_abstract_state"
proof -
  let ?node_memory = "java_memory state node"
  let ?new_node_memory = "queue_state (?node_memory\<lparr>
    last_accepted_position       := publication_position request,
    last_accepted_value          := new_value,
    last_accepted_configuration  := publication_config request,
    last_committed_configuration := publication_previous_config request
  \<rparr>)"
  let ?msg = "Response_Msg
                  node
                  (node_role ?node_memory)
                  (publication_owner request)
                  (publication_position request)"
  let ?cond = "position_term (publication_position request) = current_term ?node_memory
               \<and> \<not> (position_term (publication_position request) = position_term (last_accepted_position ?node_memory)
                    \<and> position_version (publication_position request) \<le> position_version (last_accepted_position ?node_memory))"
  from contract have sent: "Publish_Msg node request new_value \<in> java_messages state" by simp
  show ?thesis
  proof (cases ?cond)
    case False
    note neg = this
    then have "java_call state (Java_Handle_Publish_Request node request new_value) = state"
      unfolding java_call.simps Let_def java_put_def by (simp only: neg if_False)
    then show ?thesis using link by (intro exI[of _ abstract_state]) simp
  next
    case True
    then have term_eq: "position_term (publication_position request) = current_term ?node_memory"
      and version_increases: "position_term (publication_position request) = position_term (last_accepted_position ?node_memory) \<Longrightarrow>
        position_version (last_accepted_position ?node_memory) < position_version (publication_position request)"
      by auto
    obtain base where history_sent: "base @ [request] \<in> publications_sent abstract_state" and nonempty_configs: "publication_config request \<noteq> {}" "publication_previous_config request \<noteq> {}"
      using linkedD(3)[OF link sent] by auto
    have role': "node_role ?new_node_memory = node_role ?node_memory" by (simp add: queue_state_def)
    have call_result: "java_call state (Java_Handle_Publish_Request node request new_value) =
        state\<lparr>
          java_memory   := (java_memory state)(node := ?new_node_memory),
          java_disk     := (if node_role ?new_node_memory = Master_Eligible then (java_disk state)(node := disk_of ?new_node_memory) else java_disk state),
          java_messages := java_messages state \<union> {?msg}
        \<rparr>"
      unfolding java_call.simps Let_def java_put_def by (rule if_P[OF True])
    have same_mem: "\<And>other_node. other_node \<noteq> node \<Longrightarrow> java_memory (java_call state (Java_Handle_Publish_Request
                                                                                       node
                                                                                       request
                                                                                       new_value)) other_node
                                                     =
                                 java_memory state other_node"
      unfolding call_result by simp
    have same_disk: "\<And>other_node. other_node \<noteq> node \<Longrightarrow> java_disk (java_call state (Java_Handle_Publish_Request
                                                                                      node
                                                                                      request
                                                                                      new_value)) other_node
                                                      =
                                  java_disk state other_node"
      unfolding call_result by simp
    have memory_after: "java_memory (java_call state (Java_Handle_Publish_Request
                                                          node
                                                          request
                                                          new_value)) node
                        =
                         ?new_node_memory" unfolding call_result by simp
    have messages_after: "java_messages (java_call state (Java_Handle_Publish_Request
                                                              node
                                                              request
                                                              new_value))
                          =
                           insert ?msg (java_messages state)"
      unfolding call_result by simp
    have unique: "wire_unique (insert ?msg (java_messages state))"
      using wire_unique_control[OF linkedD(4)[OF link], of "{?msg}"] by simp
    have frame: "other_node \<noteq> node \<Longrightarrow> node_frame abstract_state abstract_state other_node" for other_node by simp
    show ?thesis
    proof (cases "node_role ?node_memory = Master_Eligible")
      case master: True
      let ?old_memory = "java_memory state node"
      let ?updated_memory = "?old_memory\<lparr>
        last_accepted_position       := publication_position request,
        last_accepted_value          := new_value,
        last_accepted_configuration  := publication_config request,
        last_committed_configuration := publication_previous_config request
      \<rparr>"
      have new_memory_eq: "?new_node_memory = ?updated_memory" using master by (simp add: queue_state_def)
      have disk_view_before: "disk_view state node = ?old_memory" using master by (rule disk_view_master)
      have old_node_link: "node_link initial_configuration abstract_state node ?old_memory" using linkedD(1)[OF link, of node] disk_view_before by simp
      have disk_view_after: "disk_view (java_call state (Java_Handle_Publish_Request
                                                             node
                                                             request
                                                             new_value)) node
                             =
                              ?updated_memory"
        proof -
          have role_condition: "node_role ?new_node_memory = Master_Eligible" using master role' by simp
          show ?thesis unfolding disk_view_def memory_after if_P[OF role_condition] by (rule new_memory_eq)
        qed
      let ?msg' = "Response_Msg
                       node
                       Master_Eligible
                       (publication_owner request)
                       (publication_position request)"
      have msg_eq: "?msg = ?msg'" using master by simp
      have same_term: "position_term (publication_position request) = current_term_of abstract_state node"
        using term_eq node_linkD(1)[OF old_node_link] by simp
      let ?new_history = "base @ [request]"
      let ?next_abstract_state = "abstract_state\<lparr>
        publications_accepted           := (publications_accepted abstract_state)(node := ?new_history),
        last_committed_configuration_of := (last_committed_configuration_of abstract_state)(node := previous_config_of_tip_of initial_configuration ?new_history),
        publish_responses_sent          := insert (node,?new_history) (publish_responses_sent abstract_state)
      \<rparr>"
      have messages_invariant: "abstract_model.messages_ok initial_configuration abstract_state" and publications_invariant: "abstract_model.publications_ok initial_configuration abstract_state"
        using abstract_model.dynamic_invariants[OF reach] by auto
      have positive_term: "0 < position_term (publication_position request)" using publication_positive[OF publications_invariant history_sent] by simp
      have term_bound: "position_term (last_accepted_position ?old_memory) \<le> position_term (publication_position request)"
        using abstract_model.messagesD(2)[OF messages_invariant, of node] node_linkD(4)[OF old_node_link] same_term
        by (metis normalized_term)
      obtain accepted_term accepted_version where position: "last_accepted_position ?old_memory = \<lparr>
        position_term    = accepted_term,
        position_version = accepted_version
      \<rparr>"
        by (cases "last_accepted_position ?old_memory") auto
      have increase: "accepted_version < position_version (publication_position request)" if "accepted_term = position_term (publication_position request)"
        using that position version_increases by auto
      have "normalized (last_accepted_position ?old_memory) < publication_position request"
      proof (cases "accepted_term = 0")
        case True
        then show ?thesis using position positive_term by (simp add: normalized_def position_less_iff)
      next
        case False
        from term_bound position have "accepted_term \<le> position_term (publication_position request)" by simp
        then have "accepted_term < position_term (publication_position request)
                   \<or> accepted_term = position_term (publication_position request)" by (simp add: le_less)
        then show ?thesis using position False increase by (auto simp: normalized_def position_le_iff position_less_iff)
      qed
      then have position_increases: "position_of_tip_of (publications_accepted abstract_state node) < position_of_tip_of ?new_history"
        using node_linkD(4)[OF old_node_link] by simp
      have step: "abstract_model.transition initial_configuration abstract_state ?next_abstract_state"
        by (rule abstract_model.transition.receive[OF history_sent _ position_increases]) (simp add: same_term)
      have grow: "grows abstract_state ?next_abstract_state" by (rule transition_grows[OF step])
      have new_term_matches: "term_of_tip_of ?new_history = current_term_of abstract_state node" using same_term by simp
      have fresh_join_votes: "abstract_model.fresh_votes ?next_abstract_state node
                                                                                  (current_term_of ?next_abstract_state node)
                                                                                  (publications_accepted ?next_abstract_state node)
                                                                                  (join_votes ?updated_memory)"
        using fresh_frame[OF grow node_linkD(8)[OF old_node_link] less_imp_le[OF position_increases], of "join_votes ?old_memory"] by simp
      have active: "abstract_model.active_leader abstract_state node" if "election_won ?old_memory" using that node_linkD(3)[OF old_node_link master] by simp
      have at_tip: "abstract_model.current_published_history abstract_state node = ?new_history" if won: "election_won ?old_memory"
      proof -
        have "term_of_tip_of (abstract_model.current_published_history abstract_state node) = current_term_of abstract_state node"
          using node_linkD(10)[OF old_node_link won] node_linkD(1)[OF old_node_link] older_tip_impossible[OF active[OF won] history_sent new_term_matches]
          unfolding known_tip_def by auto
        then show ?thesis using abstract_model.receive_at_current_published_history[OF reach abstract_model.reachable_current_published_history_ok[OF reach]
            active[OF won] _ history_sent new_term_matches position_increases] by simp
      qed
      have leader: "java_is_election_quorum ?updated_memory (join_votes ?updated_memory)
                    \<and> known_tip initial_configuration ?next_abstract_state node ?updated_memory" if won: "election_won ?old_memory"
      proof -
        have old_tip: "known_tip initial_configuration abstract_state node ?old_memory" by (rule node_linkD(10)[OF old_node_link won])
        with at_tip[OF won] same_term node_linkD(1)[OF old_node_link] history_sent
        show ?thesis using node_linkD(9)[OF old_node_link won] unfolding known_tip_def java_is_election_quorum_def by auto
      qed
      have new_link: "node_link initial_configuration ?next_abstract_state node ?updated_memory"
      proof -
        have persisted: "persisted_link initial_configuration ?next_abstract_state node ?updated_memory"
          using old_node_link positive_term nonempty_configs unfolding node_link_def persisted_link_def by (auto simp: normalized_def split: if_splits)
        have active_leader_unchanged: "abstract_model.active_leader ?next_abstract_state node = abstract_model.active_leader abstract_state node"
          unfolding abstract_model.active_leader_def by simp
        have started_eq: "started_join_since_last_reboot ?old_memory \<Longrightarrow> election_won ?old_memory = abstract_model.active_leader abstract_state node"
          by (rule node_linkD(15)[OF old_node_link master])
        have effective: "election_won ?old_memory \<Longrightarrow> abstract_model.effective_config
                                                        initial_configuration
                                                        (publications_committed ?next_abstract_state)
                                                        (abstract_model.current_published_history ?next_abstract_state node)
                                                        (last_committed_configuration_of ?next_abstract_state node)"
        proof -
          assume won: "election_won ?old_memory"
          have "abstract_model.current_published_history ?next_abstract_state node = ?new_history"
            using at_tip[OF won] by (simp add: abstract_model.last_published_history_of_update_publications_accepted)
          then show ?thesis by (simp add: abstract_model.effective_config_def)
        qed
        have transient: "transient_link initial_configuration ?next_abstract_state node ?updated_memory"
          using node_linkD(2)[OF old_node_link master] node_linkD(16)[OF old_node_link master] started_eq active_leader_unchanged effective fresh_join_votes leader master
          unfolding transient_link_def by simp
        show ?thesis using persisted transient unfolding node_link_def by blast
      qed
      have response_wire_link: "wire_link ?next_abstract_state ?msg'" using history_sent by (auto intro!: bexI[of _ ?new_history])
      have publish_votes_eq: "publish_votes ?updated_memory = publish_votes ?old_memory" by simp
      have frame': "\<And>other_node. other_node \<noteq> node \<Longrightarrow> node_frame abstract_state ?next_abstract_state other_node"
        unfolding node_frame_def abstract_model.active_leader_def by auto
      have linked_after: "linked initial_configuration (java_call state (Java_Handle_Publish_Request
                                                                             node
                                                                             request
                                                                             new_value)) ?next_abstract_state"
      proof (rule link_update[OF link grow _ _ frame'])
        show "\<And>other_node. other_node \<noteq> node \<Longrightarrow> java_memory (java_call state (Java_Handle_Publish_Request
                                                                                 node
                                                                                 request
                                                                                 new_value)) other_node
                                               =
                                                java_memory state other_node
                                               \<and> java_disk (java_call state (Java_Handle_Publish_Request
                                                                                 node
                                                                                 request
                                                                                 new_value)) other_node
                                                 =
                                                  java_disk state other_node"
          using same_mem same_disk by blast
        show "node_link initial_configuration ?next_abstract_state node (disk_view (java_call state (Java_Handle_Publish_Request
                                                                                                         node
                                                                                                         request
                                                                                                         new_value)) node)"
          unfolding disk_view_after by (rule new_link)
        show "node_role (java_memory (java_call state (Java_Handle_Publish_Request
                                                           node
                                                           request
                                                           new_value)) node)
              =
               Master_Eligible \<Longrightarrow>
            java_disk (java_call state (Java_Handle_Publish_Request node request new_value)) node
            = disk_of (java_memory (java_call state (Java_Handle_Publish_Request
                                                         node
                                                         request
                                                         new_value)) node)"
          unfolding call_result using master role' by (simp)
        show "\<forall>voter\<in>publish_votes (disk_view (java_call state (Java_Handle_Publish_Request
                                                                    node
                                                                    request
                                                                    new_value)) node).
            Response_Msg
                voter
                Master_Eligible
                node
                (last_published_position (disk_view (java_call state (Java_Handle_Publish_Request
                                                                          node
                                                                          request
                                                                          new_value)) node))
            \<in> java_messages (java_call state (Java_Handle_Publish_Request node request new_value))"
          unfolding disk_view_after messages_after using linkedD(2)[OF link, of _ node] disk_view_before by simp
        show "node_role (java_memory (java_call state (Java_Handle_Publish_Request
                                                           node
                                                           request
                                                           new_value)) node)
              =
               Data_Only \<Longrightarrow>
            memory_link ?next_abstract_state (disk_view (java_call state (Java_Handle_Publish_Request
                                                                              node
                                                                              request
                                                                              new_value)) node)
              (java_memory (java_call state (Java_Handle_Publish_Request node request new_value)) node)"
          unfolding call_result using master role' by (simp)
        show "node_role (java_memory (java_call state (Java_Handle_Publish_Request
                                                           node
                                                           request
                                                           new_value)) node) \<noteq> Master_Eligible \<Longrightarrow>
            \<not> election_won (java_memory (java_call state (Java_Handle_Publish_Request
                                                              node
                                                              request
                                                              new_value)) node)"
          unfolding call_result using master role' by (simp)
        show "java_messages state \<subseteq> java_messages (java_call state (Java_Handle_Publish_Request
                                                                        node
                                                                        request
                                                                        new_value))"
          unfolding messages_after by blast
        show "\<And>message. message \<in> java_messages (java_call state (Java_Handle_Publish_Request
                                                                      node
                                                                      request
                                                                      new_value)) \<Longrightarrow>
            message \<notin> java_messages state \<Longrightarrow> wire_link ?next_abstract_state message"
          unfolding messages_after using response_wire_link msg_eq by auto
        show "wire_unique (java_messages (java_call state (Java_Handle_Publish_Request
                                                               node
                                                               request
                                                               new_value)))"
          unfolding messages_after by (rule unique)
      qed
      show ?thesis using step linked_after by (intro exI[of _ ?next_abstract_state]) simp
    next
      case nonmaster: False
      let ?node_disk_view = "disk_view state node"
      have disk_view_before: "?node_disk_view = memory_of_disk (node_role ?node_memory) (java_disk state node)" using nonmaster by (rule disk_view_other)
      have disk_view_after: "disk_view (java_call state (Java_Handle_Publish_Request
                                                             node
                                                             request
                                                             new_value)) node
                             =
                              ?node_disk_view"
      proof -
        have disk_n: "java_disk (java_call state (Java_Handle_Publish_Request node request new_value)) node = java_disk state node"
          unfolding call_result using nonmaster role' by simp
        have role_condition: "node_role ?new_node_memory \<noteq> Master_Eligible" using nonmaster role' by simp
        show ?thesis unfolding disk_view_def memory_after disk_n if_not_P[OF role_condition] using role' disk_view_before nonmaster by simp
      qed
      have mem_link: "node_role ?node_memory = Data_Only \<Longrightarrow> memory_link abstract_state ?node_disk_view ?new_node_memory"
      proof -
        assume data: "node_role ?node_memory = Data_Only"
        from linkedD(6)[OF link data]
        have known: "position_term (last_accepted_position ?node_memory) = 0
                     \<or> (\<exists>publication_history\<in>publications_sent abstract_state. position_of_tip_of publication_history = last_accepted_position ?node_memory)"
          and disk_not_behind: "normalized (last_accepted_position ?node_disk_view) \<le> normalized (last_accepted_position ?node_memory)"
          and term_bounded: "position_term (last_accepted_position ?node_memory) \<le> current_term ?node_memory"
          unfolding memory_link_def by auto
        have publications_invariant: "abstract_model.publications_ok initial_configuration abstract_state" using abstract_model.dynamic_invariants[OF reach] by auto
        have positive_term: "0 < position_term (publication_position request)" using publication_positive[OF publications_invariant history_sent] by simp
        have new_greater: "normalized (last_accepted_position ?node_memory) \<le> publication_position request"
        proof (cases "position_term (last_accepted_position ?node_memory) = 0")
          case True
          then show ?thesis using positive_term by (simp add: normalized_def position_le_iff)
        next
          case False
          then have "normalized (last_accepted_position ?node_memory) = last_accepted_position ?node_memory" by (simp add: normalized_def)
          moreover have "last_accepted_position ?node_memory \<le> publication_position request"
            using term_bounded term_eq version_increases by (cases "last_accepted_position ?node_memory") (auto simp: position_le_iff)
          ultimately show ?thesis by simp
        qed
        have published_position: "\<exists>publication_history\<in>publications_sent abstract_state. position_of_tip_of publication_history = publication_position request"
          using history_sent by (intro bexI[of _ "base @ [request]"]) simp_all
        then show "memory_link abstract_state ?node_disk_view ?new_node_memory"
          using disk_not_behind new_greater term_bounded term_eq positive_term
          unfolding memory_link_def queue_state_def by (auto simp: normalized_def split: if_splits)
      qed
      have linked_after: "linked
                              initial_configuration
                              (java_call state (Java_Handle_Publish_Request node request new_value))
                              abstract_state"
      proof (rule link_update[OF link grows_refl _ _ frame])
        show "\<And>other_node. other_node \<noteq> node \<Longrightarrow> java_memory (java_call state (Java_Handle_Publish_Request
                                                                                 node
                                                                                 request
                                                                                 new_value)) other_node
                                               =
                                                java_memory state other_node
                                               \<and> java_disk (java_call state (Java_Handle_Publish_Request
                                                                                 node
                                                                                 request
                                                                                 new_value)) other_node
                                                 =
                                                  java_disk state other_node"
          using same_mem same_disk by blast
        show "node_link
                  initial_configuration
                  abstract_state
                  node
                  (disk_view (java_call state (Java_Handle_Publish_Request node request new_value)) node)"
          unfolding disk_view_after by (rule linkedD(1)[OF link])
        show "node_role (java_memory (java_call state (Java_Handle_Publish_Request
                                                           node
                                                           request
                                                           new_value)) node)
              =
               Master_Eligible \<Longrightarrow>
            java_disk (java_call state (Java_Handle_Publish_Request node request new_value)) node
            = disk_of (java_memory (java_call state (Java_Handle_Publish_Request
                                                         node
                                                         request
                                                         new_value)) node)"
          unfolding call_result using nonmaster role' by (simp)
        show "\<forall>voter\<in>publish_votes (disk_view (java_call state (Java_Handle_Publish_Request
                                                                    node
                                                                    request
                                                                    new_value)) node).
            Response_Msg
                voter
                Master_Eligible
                node
                (last_published_position (disk_view (java_call state (Java_Handle_Publish_Request
                                                                          node
                                                                          request
                                                                          new_value)) node))
            \<in> java_messages (java_call state (Java_Handle_Publish_Request node request new_value))"
          unfolding disk_view_after messages_after using disk_view_before by (simp add: memory_of_disk_def)
        show "node_role (java_memory (java_call state (Java_Handle_Publish_Request
                                                           node
                                                           request
                                                           new_value)) node)
              =
               Data_Only \<Longrightarrow>
            memory_link
                abstract_state
                (disk_view (java_call state (Java_Handle_Publish_Request node request new_value)) node)
                (java_memory (java_call state (Java_Handle_Publish_Request node request new_value)) node)"
          unfolding disk_view_after memory_after using role' mem_link by simp
        show "node_role (java_memory (java_call state (Java_Handle_Publish_Request
                                                           node
                                                           request
                                                           new_value)) node) \<noteq> Master_Eligible \<Longrightarrow>
            \<not> election_won (java_memory (java_call state (Java_Handle_Publish_Request
                                                              node
                                                              request
                                                              new_value)) node)"
          unfolding call_result using linkedD(7)[OF link nonmaster] by (simp add: queue_state_def)
        show "java_messages state \<subseteq> java_messages (java_call state (Java_Handle_Publish_Request
                                                                        node
                                                                        request
                                                                        new_value))"
          unfolding messages_after by blast
        show "\<And>message. message \<in> java_messages (java_call state (Java_Handle_Publish_Request
                                                                      node
                                                                      request
                                                                      new_value)) \<Longrightarrow>
            message \<notin> java_messages state \<Longrightarrow> wire_link abstract_state message"
          unfolding messages_after using nonmaster history_sent by auto
        show "wire_unique (java_messages (java_call state (Java_Handle_Publish_Request
                                                               node
                                                               request
                                                               new_value)))"
          unfolding messages_after by (rule unique)
      qed
      show ?thesis using linked_after by (intro exI[of _ abstract_state]) simp
    qed
  qed
qed

lemma simulate_handle_publish_request:
  assumes "caller_contract
               initial_configuration
               initial_value
               state
               (Java_Handle_Publish_Request node request new_value)"
  shows "\<exists>next_abstract_state. (next_abstract_state = abstract_state
                                \<or> abstract_model.transition
                                      initial_configuration
                                      abstract_state
                                      next_abstract_state)
                               \<and> linked
                                     initial_configuration
                                     (java_call state (Java_Handle_Publish_Request
                                                           node
                                                           request
                                                           new_value))
                                     next_abstract_state"
  by (rule publish_request_simulation[OF assms])

end

end
