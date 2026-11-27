theory Safety
  imports Refinement
begin

section \<open>Correctness of the Java model\<close>

text \<open>
  The safety properties of the protocol hold of every state that the Java model can reach, that is,
  after any sequence of calls that respects the caller contract, with arbitrary restarts, delays,
  duplication and reordering of messages. The messages that a node can ever receive are those in
  the messages set.

  \<^item> The nodes never disagree about who leads (\<open>one_leader_per_term\<close>,
    \<open>one_publisher_per_term\<close>). Two nodes that have won an election in the same term are the same
    node, and any two publication requests in the same term come from the same leader.
  \<^item> The nodes never disagree about what was published (\<open>publications_agree\<close>). Two publication
    requests with the same position (term and version) are the same request, and carry the same
    value.
  \<^item> The committed history never diverges (\<open>committed_history_never_diverges\<close>). The positions of any
    two committed publications are the same, or one was published as a descendant of the other: they
    are related by the symmetric reflexive closure of \<open>descends\<close>. The Java state does not record
    ancestry, so \<open>descends\<close> is taken from the abstract state that the Java state is linked to.

  A publication is published when a \<open>Publish_Msg\<close> for it is in the messages (\<open>is_Published\<close>), and
  committed when a \<open>Commit_Msg\<close> for its position is in the messages (\<open>java_committed\<close>).

  The theorems are in the locale \<open>java_run\<close>, which fixes a reachable Java state \<open>state\<close>.
\<close>

definition java_committed :: "'v java_state \<Rightarrow> publication \<Rightarrow> bool" where
  "java_committed state request \<longleftrightarrow>
    (\<exists>leader destination.
      Commit_Msg leader destination (publication_position request) \<in> java_messages state)"

locale java_run =
  fixes initial_configuration :: config
  fixes initial_value :: 'v
  fixes versions :: "node \<Rightarrow> nat"
  fixes state :: "'v java_state"
  assumes reach: "java_reachable initial_configuration initial_value versions state"
begin

text \<open>
  A proof aid with no counterpart in Java: an abstract state that the reachable Java state is linked
  to (\<open>java_dynamic_refinement\<close>), chosen arbitrarily. The Java state does not record the
  publication histories or the election certificates of the abstract model, so the theorems below
  that need them are proved about this abstract state.
\<close>

definition linked_abstract_state :: abstract_state where
  "linked_abstract_state =
    (SOME abstract_state. abstract_model.dynamic_reachable initial_configuration abstract_state
     \<and> linked initial_configuration state abstract_state)"

lemma linked_abstract_state:
  shows "abstract_model.dynamic_reachable initial_configuration linked_abstract_state"
    and "linked initial_configuration state linked_abstract_state"
proof -
  have "\<exists>abstract_state. abstract_model.dynamic_reachable initial_configuration abstract_state
                         \<and> linked initial_configuration state abstract_state"
    using java_dynamic_refinement[OF reach] by blast
  then have "abstract_model.dynamic_reachable initial_configuration linked_abstract_state
             \<and> linked initial_configuration state linked_abstract_state"
    unfolding linked_abstract_state_def by (rule someI_ex)
  then show "abstract_model.dynamic_reachable initial_configuration linked_abstract_state"
    "linked initial_configuration state linked_abstract_state" by simp_all
qed

text \<open>
  A publication request is published, with a value, when it is in the messages in a message to
  some node.
\<close>

definition is_Published :: "publication \<Rightarrow> 'v \<Rightarrow> bool" where
  "is_Published request value \<longleftrightarrow>
    (\<exists>destination. Publish_Msg destination request value \<in> java_messages state)"

text \<open>
  A proof aid with no counterpart in Java: the positions of published states, related to the
  positions of the states that they were published on top of, and the positions of those states'
  ancestors. A pair is in the relation when the first position is that of a proper prefix of the
  history that ends at the second position, in the linked abstract state. It plays the part of the
  \<open>descendant\<close> history variable of the TLA+ specification.
\<close>

definition descends :: "(position \<times> position) set" where
  "descends =
    {(position_of_tip_of ancestor_history, position_of_tip_of descendant_history) |
      ancestor_history descendant_history.
      ancestor_history \<in> publications_sent linked_abstract_state
      \<and> descendant_history \<in> publications_sent linked_abstract_state
      \<and> prefix ancestor_history descendant_history
      \<and> ancestor_history \<noteq> descendant_history}"

theorem one_leader_per_term:
  fixes node_1 node_2 :: node
  defines node_state_1_def: "node_state_1 \<equiv> java_memory state node_1"
  defines node_state_2_def: "node_state_2 \<equiv> java_memory state node_2"
  assumes won_1: "election_won node_state_1"
  assumes won_2: "election_won node_state_2"
  assumes same_term: "current_term node_state_1 = current_term node_state_2"
  shows "node_1 = node_2"
proof -
  note linked = linked_abstract_state(2)
  have won_node: "node_role (java_memory state node) = Master_Eligible
                  \<and> elections_won linked_abstract_state (node, current_term (java_memory state node)) \<noteq> None"
    if "election_won (java_memory state node)" for node
  proof -
    have master: "node_role (java_memory state node) = Master_Eligible"
      using linkedD(7)[OF linked, of node] that by blast
    then have view: "disk_view state node = java_memory state node" by (rule disk_view_master)
    have "abstract_model.active_leader linked_abstract_state node"
      using node_linkD(3)[OF linkedD(1)[OF linked, of node]] that master view by simp
    moreover have "current_term (java_memory state node) = current_term_of linked_abstract_state node"
      using node_linkD(1)[OF linkedD(1)[OF linked, of node]] view by simp
    ultimately show ?thesis using master by (simp add: abstract_model.active_leader_def)
  qed
  have first: "elections_won linked_abstract_state (node_1, current_term node_state_1) \<noteq> None"
    using won_node[of node_1] won_1 unfolding node_state_1_def by blast
  have second: "elections_won linked_abstract_state (node_2, current_term node_state_1) \<noteq> None"
    using won_node[of node_2] won_2 same_term unfolding node_state_1_def node_state_2_def by metis
  obtain election_1 election_2 where
    "elections_won linked_abstract_state (node_1, current_term node_state_1) = Some election_1"
    "elections_won linked_abstract_state (node_2, current_term node_state_1) = Some election_2"
    using first second by blast
  then show ?thesis
    by (rule abstract_model.dynamic_one_election_candidate_per_term[OF linked_abstract_state(1)])
qed

theorem one_publisher_per_term:
  assumes published_1: "\<exists>value. is_Published publication_1 value"
  assumes published_2: "\<exists>value. is_Published publication_2 value"
  assumes same_term: "position_term (publication_position publication_1) = position_term (publication_position publication_2)"
  shows "publication_owner publication_1 = publication_owner publication_2"
proof -
  obtain destination_1 value_1 where message_1: "Publish_Msg destination_1 publication_1 value_1 \<in> java_messages state"
    using published_1 unfolding is_Published_def by blast
  obtain destination_2 value_2 where message_2: "Publish_Msg destination_2 publication_2 value_2 \<in> java_messages state"
    using published_2 unfolding is_Published_def by blast
  obtain parent_1 parent_2 where
    histories: "parent_1 @ [publication_1] \<in> publications_sent linked_abstract_state"
    "parent_2 @ [publication_2] \<in> publications_sent linked_abstract_state"
    using linkedD(3)[OF linked_abstract_state(2) message_1] linkedD(3)[OF linked_abstract_state(2) message_2] by auto
  have leadership: "abstract_model.leadership_ok initial_configuration linked_abstract_state"
    using abstract_model.dynamic_invariants[OF linked_abstract_state(1)] by auto
  obtain election_1 election_2 where
    "elections_won linked_abstract_state (publication_owner publication_1, position_term (publication_position publication_1)) = Some election_1"
    "elections_won linked_abstract_state (publication_owner publication_2, position_term (publication_position publication_1)) = Some election_2"
    using abstract_model.leadershipD(8)[OF leadership histories(1)]
      abstract_model.leadershipD(8)[OF leadership histories(2)] same_term by auto
  then show ?thesis
    by (rule abstract_model.dynamic_one_election_candidate_per_term[OF linked_abstract_state(1)])
qed

theorem publications_agree:
  assumes published_1: "is_Published publication_1 value_1"
  assumes published_2: "is_Published publication_2 value_2"
  assumes same_position: "publication_position publication_1 = publication_position publication_2"
  shows "publication_1 = publication_2 \<and> value_1 = value_2"
proof -
  obtain destination_1 where "Publish_Msg destination_1 publication_1 value_1 \<in> java_messages state"
    using published_1 unfolding is_Published_def by blast
  moreover obtain destination_2 where "Publish_Msg destination_2 publication_2 value_2 \<in> java_messages state"
    using published_2 unfolding is_Published_def by blast
  ultimately show ?thesis using linkedD(4)[OF linked_abstract_state(2)] same_position
    unfolding wire_unique_def by blast
qed

text \<open>
  The history of the abstract state that ends with a committed publication.
\<close>

lemma committed_request_link:
  assumes published: "is_Published request value"
  assumes committed: "java_committed state request"
  obtains history where "history \<in> publications_committed linked_abstract_state"
    "history \<in> publications_sent linked_abstract_state"
    "position_of_tip_of history = publication_position request"
proof -
  obtain destination where publish_message: "Publish_Msg destination request value \<in> java_messages state"
    using published unfolding is_Published_def by blast
  obtain parent where parent_history: "parent @ [request] \<in> publications_sent linked_abstract_state"
    using linkedD(3)[OF linked_abstract_state(2) publish_message] by auto
  obtain leader commit_destination where
    "Commit_Msg leader commit_destination (publication_position request) \<in> java_messages state"
    using committed unfolding java_committed_def by blast
  from linkedD(3)[OF linked_abstract_state(2) this]
  obtain committed_history where committed_history: "committed_history \<in> publications_committed linked_abstract_state"
    and committed_position: "position_of_tip_of committed_history = publication_position request" by auto
  have publications_ok: "abstract_model.publications_ok initial_configuration linked_abstract_state"
    using abstract_model.dynamic_invariants[OF linked_abstract_state(1)] by auto
  have sent: "committed_history \<in> publications_sent linked_abstract_state"
    by (rule abstract_model.publicationsD(5)[OF publications_ok committed_history])
  have "committed_history = parent @ [request]"
    by (rule abstract_model.dynamic_unique_publication[OF linked_abstract_state(1) sent parent_history])
       (simp add: committed_position)
  with committed_history have "parent @ [request] \<in> publications_committed linked_abstract_state" by simp
  from this parent_history show thesis by (rule that) simp
qed

theorem committed_history_never_diverges:
  assumes published_1: "\<exists>value. is_Published publication_1 value"
  assumes published_2: "\<exists>value. is_Published publication_2 value"
  assumes committed_1: "java_committed state publication_1"
  assumes committed_2: "java_committed state publication_2"
  shows "(publication_position publication_1, publication_position publication_2)
           \<in> (descends \<union> descends\<inverse>)\<^sup>="
proof (cases "publication_position publication_1 = publication_position publication_2")
  case True
  then show ?thesis by simp
next
  case False
  obtain history_1 where history_1: "history_1 \<in> publications_committed linked_abstract_state"
    "history_1 \<in> publications_sent linked_abstract_state"
    "position_of_tip_of history_1 = publication_position publication_1"
    using committed_request_link[of publication_1] published_1 committed_1 by blast
  obtain history_2 where history_2: "history_2 \<in> publications_committed linked_abstract_state"
    "history_2 \<in> publications_sent linked_abstract_state"
    "position_of_tip_of history_2 = publication_position publication_2"
    using committed_request_link[of publication_2] published_2 committed_2 by blast
  have prefixes: "prefix history_1 history_2 \<or> prefix history_2 history_1"
    by (rule abstract_model.dynamic_committed_states_form_chain
        [OF linked_abstract_state(1) history_1(1) history_2(1)])
  have different: "history_1 \<noteq> history_2" "history_2 \<noteq> history_1"
    using False history_1(3) history_2(3) by auto
  from prefixes show ?thesis
  proof
    assume "prefix history_1 history_2"
    then have "(publication_position publication_1, publication_position publication_2) \<in> descends"
      unfolding descends_def using history_1 history_2 different(1) \<open>prefix history_1 history_2\<close>
      by (intro CollectI exI[of _ history_1] exI[of _ history_2]) (simp add: history_1(3) history_2(3))
    then show ?thesis by blast
  next
    assume "prefix history_2 history_1"
    then have "(publication_position publication_2, publication_position publication_1) \<in> descends"
      unfolding descends_def using history_1 history_2 different(2) \<open>prefix history_2 history_1\<close>
      by (intro CollectI exI[of _ history_2] exI[of _ history_1]) (simp add: history_1(3) history_2(3))
    then show ?thesis by blast
  qed
qed

end

end
