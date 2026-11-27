theory Link
  imports Model "../Abstract_Model"
begin


(* TODO Base, Model, Abstract_Model and Basics/* predate the naming conventions in CLAUDE.md and
   still use single-character variables. Rename them, and check that the proofs in this theory and in
   Simulation/* that refer to variables by name (with `where`) still work. *)

section \<open>Relating the Java transcription to the abstract model\<close>

text \<open>
  The Java transcription of \<open>Model\<close> refines the dynamic model of \<open>Abstract_Model\<close>.
  The relation \<open>linked initial_configuration state abstract_state\<close> holds between a Java state
  \<open>state\<close> and an abstract state \<open>abstract_state\<close> when each node's state on disk (\<open>node_link\<close>), the
  in-memory state of each node that is not master-eligible (\<open>memory_link\<close>) and each message
  (\<open>wire_link\<close>) correspond to the abstract state. Every Java call is simulated by at most one abstract
  transition, so the safety properties of the dynamic model hold in the Java model.

  Everything in this theory is a proof aid with no counterpart in the Java code.
\<close>

text \<open>
  \<open>has_quorum\<close> of \<open>Model\<close>, which follows \<open>VotingConfiguration.hasQuorum\<close>, is the \<open>quorum\<close> of
  the abstract model.
\<close>

lemma has_quorum_eq[simp]: "has_quorum configuration votes = quorum configuration votes"
  unfolding has_quorum_def quorum_def majority_def by auto

text \<open>
  The abstract model gives a node with no history the position \<open>position_zero\<close>, whereas
  the position of a node at term zero carries the node's initial version.
  \<open>normalized\<close> maps every position at term zero to \<open>position_zero\<close>.
\<close>

definition normalized :: "position \<Rightarrow> position" where
  "normalized position = (if position_term position = 0 then position_zero else position)"

lemma normalized_mono:
  "position \<le> other_position \<Longrightarrow> normalized position \<le> normalized other_position"
  by (cases position; cases other_position) (auto simp: normalized_def position_le_iff)

lemma quorum_nonempty: "quorum initial_configuration votes \<Longrightarrow> initial_configuration \<noteq> {}"
  unfolding quorum_def majority_def voting_nodes_of_def by auto

text \<open>A superset of a quorum is a quorum.\<close>

lemma quorum_grow:
  assumes quorate: "quorum initial_configuration votes"
  assumes subset: "votes \<subseteq> more_votes"
  shows "quorum initial_configuration more_votes"
proof -
  have finite_voters: "finite (voting_nodes_of initial_configuration)"
    using quorate unfolding quorum_def majority_def by simp
  have "card (voting_nodes_of initial_configuration \<inter> votes) \<le> card (voting_nodes_of initial_configuration \<inter> more_votes)"
    by (rule card_mono) (use finite_voters subset in auto)
  with quorate finite_voters show ?thesis unfolding quorum_def majority_def by auto
qed

lemma is_election_quorum_insert:
  "java_is_election_quorum node_memory_state votes \<Longrightarrow>
    java_is_election_quorum node_memory_state (insert voter votes)"
  unfolding java_is_election_quorum_def by (auto intro: quorum_grow)

text \<open>
  The marker configuration \<open>stale_config\<close> has no real node in it, so no set of votes is a quorum of it.
  A node that has won an election therefore has real configurations: nobody votes as the stale
  marker.
\<close>

lemma quorum_stale: "\<not> quorum stale_config votes"
  unfolding quorum_def majority_def stale_config_def voting_nodes_of_def by simp

lemma quorum_not_stale:
  assumes "quorum configuration votes"
  shows "configuration \<noteq> stale_config"
  using assms quorum_stale by blast

text \<open>
  What a leader has published. Either it has won its election but not yet
  published, so the abstract tip is behind the term and equals its durable
  history, or it has published its tip, which is in \<open>publications_sent\<close> and matches
  its last published position and configuration.
\<close>

definition known_tip :: "config \<Rightarrow> abstract_state \<Rightarrow> node \<Rightarrow> 'v node_memory_state \<Rightarrow> bool" where
  "known_tip initial_configuration abstract_state node node_memory_state \<longleftrightarrow>
    (term_of_tip_of (abstract_model.current_published_history abstract_state node) < current_term node_memory_state
     \<and> abstract_model.current_published_history abstract_state node = publications_accepted abstract_state node
     \<and> last_published_version node_memory_state = position_version (last_accepted_position node_memory_state))
    \<or> (abstract_model.current_published_history abstract_state node \<in> publications_sent abstract_state
       \<and> position_of_tip_of (abstract_model.current_published_history abstract_state node) = last_published_position node_memory_state
       \<and> owner_of_tip_of (abstract_model.current_published_history abstract_state node) = node
       \<and> last_published_configuration node_memory_state = config_of_tip_of initial_configuration (abstract_model.current_published_history abstract_state node)
       \<and> quorum (previous_config_of_tip_of initial_configuration (abstract_model.current_published_history abstract_state node)) (join_votes node_memory_state)
       \<and> quorum (config_of_tip_of initial_configuration (abstract_model.current_published_history abstract_state node)) (join_votes node_memory_state)
       \<and> (last_published_version node_memory_state = position_version (last_accepted_position node_memory_state) \<longrightarrow>
           abstract_model.current_published_history abstract_state node = publications_accepted abstract_state node))"

text \<open>
  The correspondence for one node, between the abstract state and the node's state \<open>disk_view\<close>:
  what the node has on disk, together with, for a master-eligible node, its transient state. The
  abstract model describes the state on disk, since that is what the node votes from after a
  restart. The term is that of the abstract node. The last accepted position and configuration
  are those of the tip of its durable history, and an empty last accepted configuration means that
  there is no history. The last committed configuration is that of the abstract node, with the
  empty configuration standing for the initial one. The persisted configurations can instead both
  be the stale marker, in which case the abstract committed configuration is unconstrained: such a
  node cannot win an election, because the marker's node never votes (\<open>quorum_stale\<close>).

  For a master-eligible node that has started a join since its last restart, the term is positive and
  \<open>election_won\<close> holds exactly when the abstract node is an active leader. The abstract model does
  not record restarts, so after a restart \<open>election_won\<close> may be false for an active leader, and then
  the node cannot win again in its term. Whenever \<open>election_won\<close> holds, the node has started a join, its
  last committed configuration is effective for its current published history, and its election was won
  by a quorum of its join votes. A master-eligible node's join votes were cast for it in this term, with
  positions no later than its last accepted position. A node that has won an election is
  master-eligible, and a node that is not has no votes.\<close>

text \<open>
  The correspondence has two parts. \<open>persisted_link\<close> relates the node's state on disk to the
  abstract node, and depends only on the persisted fields of the node. \<open>transient_link\<close> relates the
  transient state of the node.
\<close>

definition persisted_link :: "config \<Rightarrow> abstract_state \<Rightarrow> node \<Rightarrow> 'v node_memory_state \<Rightarrow> bool" where
  "persisted_link initial_configuration abstract_state node node_memory_state \<longleftrightarrow>
    current_term node_memory_state = current_term_of abstract_state node
    \<and> normalized (last_accepted_position node_memory_state) = position_of_tip_of (publications_accepted abstract_state node)
    \<and> (if last_accepted_configuration node_memory_state = {}
       then publications_accepted abstract_state node = []
            \<and> last_committed_configuration node_memory_state = {}
       else last_accepted_configuration node_memory_state = config_of_tip_of initial_configuration (publications_accepted abstract_state node)
            \<or> last_accepted_configuration node_memory_state = stale_config
              \<and> last_committed_configuration node_memory_state = stale_config)
    \<and> (last_committed_configuration node_memory_state = stale_config
       \<or> last_committed_configuration_of abstract_state node =
           (if last_committed_configuration node_memory_state = {} then initial_configuration
            else last_committed_configuration node_memory_state))"

definition transient_link :: "config \<Rightarrow> abstract_state \<Rightarrow> node \<Rightarrow> 'v node_memory_state \<Rightarrow> bool" where
  "transient_link initial_configuration abstract_state node node_memory_state \<longleftrightarrow>
    (node_role node_memory_state = Master_Eligible \<longrightarrow>
      (started_join_since_last_reboot node_memory_state \<longrightarrow> 0 < current_term_of abstract_state node
                                                          \<and> election_won node_memory_state = abstract_model.active_leader abstract_state node)
      \<and> (election_won node_memory_state \<longrightarrow> started_join_since_last_reboot node_memory_state
                                          \<and> abstract_model.effective_config
                                                initial_configuration
                                                (publications_committed abstract_state)
                                                (abstract_model.current_published_history abstract_state node)
                                                (last_committed_configuration_of abstract_state node)))
    \<and> abstract_model.fresh_votes
          abstract_state
          node
          (current_term_of abstract_state node)
          (publications_accepted abstract_state node)
          (join_votes node_memory_state)
    \<and> (election_won node_memory_state \<longrightarrow>
        java_is_election_quorum node_memory_state (join_votes node_memory_state)
        \<and> known_tip initial_configuration abstract_state node node_memory_state)
    \<and> (election_won node_memory_state \<longrightarrow> node_role node_memory_state = Master_Eligible)
    \<and> (node_role node_memory_state = Master_Eligible
       \<or> join_votes node_memory_state = {} \<and> publish_votes node_memory_state = {})"

definition node_link :: "config \<Rightarrow> abstract_state \<Rightarrow> node \<Rightarrow> 'v node_memory_state \<Rightarrow> bool" where
  "node_link initial_configuration abstract_state node node_memory_state \<longleftrightarrow>
    persisted_link initial_configuration abstract_state node node_memory_state
    \<and> transient_link initial_configuration abstract_state node node_memory_state"

lemmas node_link_defs = node_link_def persisted_link_def transient_link_def

lemma node_linkD:
  assumes "node_link initial_configuration abstract_state node node_memory_state"
  shows "current_term node_memory_state = current_term_of abstract_state node"
    "node_role node_memory_state = Master_Eligible \<Longrightarrow> started_join_since_last_reboot node_memory_state \<Longrightarrow>
      0 < current_term_of abstract_state node"
    "node_role node_memory_state = Master_Eligible \<Longrightarrow> election_won node_memory_state \<Longrightarrow>
      abstract_model.active_leader abstract_state node"
    "normalized (last_accepted_position node_memory_state) =
      position_of_tip_of (publications_accepted abstract_state node)"
    "last_accepted_configuration node_memory_state = {} \<Longrightarrow> publications_accepted abstract_state node = []
                                                          \<and> last_committed_configuration node_memory_state = {}"
    "last_accepted_configuration node_memory_state \<noteq> {} \<Longrightarrow>
      last_accepted_configuration node_memory_state \<noteq> stale_config \<Longrightarrow>
      last_accepted_configuration node_memory_state =
        config_of_tip_of initial_configuration (publications_accepted abstract_state node)"
    "last_committed_configuration node_memory_state \<noteq> stale_config \<Longrightarrow>
      last_committed_configuration_of abstract_state node =
        (if last_committed_configuration node_memory_state = {} then initial_configuration
         else last_committed_configuration node_memory_state)"
    "abstract_model.fresh_votes
         abstract_state
         node
         (current_term_of abstract_state node)
         (publications_accepted abstract_state node)
         (join_votes node_memory_state)"
    "election_won node_memory_state \<Longrightarrow>
      java_is_election_quorum node_memory_state (join_votes node_memory_state)"
    "election_won node_memory_state \<Longrightarrow>
      known_tip initial_configuration abstract_state node node_memory_state"
    "election_won node_memory_state \<Longrightarrow> node_role node_memory_state = Master_Eligible"
    "node_role node_memory_state \<noteq> Master_Eligible \<Longrightarrow> join_votes node_memory_state = {}"
    "node_role node_memory_state \<noteq> Master_Eligible \<Longrightarrow> publish_votes node_memory_state = {}"
    "node_role node_memory_state = Master_Eligible \<Longrightarrow> election_won node_memory_state \<Longrightarrow>
      abstract_model.effective_config
          initial_configuration
          (publications_committed abstract_state)
          (abstract_model.current_published_history abstract_state node)
          (last_committed_configuration_of abstract_state node)"
    "node_role node_memory_state = Master_Eligible \<Longrightarrow> started_join_since_last_reboot node_memory_state \<Longrightarrow>
      election_won node_memory_state = abstract_model.active_leader abstract_state node"
    "node_role node_memory_state = Master_Eligible \<Longrightarrow> election_won node_memory_state \<Longrightarrow>
      started_join_since_last_reboot node_memory_state"
  using assms unfolding node_link_defs by (auto split: if_splits)

lemma node_link_won_configurations:
  assumes "node_link initial_configuration abstract_state node node_memory_state"
    "election_won node_memory_state"
  shows "last_accepted_configuration node_memory_state \<noteq> stale_config"
    "last_committed_configuration node_memory_state \<noteq> stale_config"
proof -
  have "quorum (last_committed_configuration node_memory_state) (join_votes node_memory_state)"
    "quorum (last_accepted_configuration node_memory_state) (join_votes node_memory_state)"
    using node_linkD(9)[OF assms(1) assms(2)] unfolding java_is_election_quorum_def has_quorum_eq by simp_all
  hence "last_committed_configuration node_memory_state \<noteq> stale_config
         \<and> last_accepted_configuration node_memory_state \<noteq> stale_config"
    using quorum_not_stale by blast
  then show "last_accepted_configuration node_memory_state \<noteq> stale_config"
    "last_committed_configuration node_memory_state \<noteq> stale_config"
    by simp_all
qed

text \<open>
  The publish votes of a master-eligible node are not part of the link to the abstract state. They
  are related to the messages by \<open>linked\<close>.
\<close>

lemma node_link_publish_votes[simp]:
  "node_role node_memory_state = Master_Eligible \<Longrightarrow>
    node_link initial_configuration abstract_state node (node_memory_state\<lparr>publish_votes := votes\<rparr>)
    \<longleftrightarrow> node_link initial_configuration abstract_state node node_memory_state"
  by (simp add: node_link_defs known_tip_def java_is_election_quorum_def has_quorum_eq)

lemma normalized_term[simp]: "position_term (normalized position) = position_term position"
  by (auto simp: normalized_def position_le_iff)

text \<open>A published history has a positive term: no publication is made at term zero.\<close>

lemma publication_positive:
  assumes "abstract_model.publications_ok initial_configuration abstract_state"
    "publication_history \<in> publications_sent abstract_state"
  shows "0 < term_of_tip_of publication_history"
  using abstract_model.publicationsD(2,4)[OF assms(1)] assms(2)
  by (cases publication_history rule: rev_cases) (auto simp: abstract_model.valid_edge_def)

text \<open>
  A node that has accepted a publication has the position of its tip, not the normalized position.
\<close>

lemma durable_position:
  assumes "node_link initial_configuration abstract_state node node_memory_state"
    "publications_accepted abstract_state node \<noteq> []"
    "abstract_model.dynamic_reachable initial_configuration abstract_state"
  shows "last_accepted_position node_memory_state = position_of_tip_of (publications_accepted abstract_state node)"
proof -
  have publications_ok: "abstract_model.publications_ok initial_configuration abstract_state"
    and messages_ok: "abstract_model.messages_ok initial_configuration abstract_state"
    using abstract_model.dynamic_invariants[OF assms(3)] by auto
  have sent: "publications_accepted abstract_state node \<in> publications_sent abstract_state"
    using abstract_model.messagesD(1)[OF messages_ok, of node] assms(2) by simp
  have positive: "0 < term_of_tip_of (publications_accepted abstract_state node)"
    by (rule publication_positive[OF publications_ok sent])
  with node_linkD(4)[OF assms(1)] show ?thesis by (auto simp: normalized_def split: if_splits)
qed

lemma linked_position_equal:
  assumes "node_link initial_configuration abstract_state node node_memory_state"
    "election_won node_memory_state"
    "last_published_version node_memory_state = position_version (last_accepted_position node_memory_state)"
  shows "abstract_model.current_published_history abstract_state node = publications_accepted abstract_state node"
proof -
  show ?thesis using node_linkD(10)[OF assms(1,2)] assms(3) unfolding known_tip_def by auto
qed

lemma linked_boot_versions:
  assumes "node_link initial_configuration abstract_state node node_memory_state"
    "position_version (last_accepted_position node_memory_state) < version"
  shows "position_version (position_of_tip_of (publications_accepted abstract_state node)) < version"
proof -
  have "position_version (normalized (last_accepted_position node_memory_state))
        \<le> position_version (last_accepted_position node_memory_state)"
    by (simp add: normalized_def)
  then show ?thesis using node_linkD(4)[OF assms(1)] assms(2) by (metis le_less_trans)
qed

text \<open>
  The correspondence for messages. A \<open>Join_Msg\<close> was sent, a \<open>Publish_Msg\<close> carries
  a publication that was made, a \<open>Response_Msg\<close> is an acknowledgement of one, and
  a \<open>Commit_Msg\<close> is for a quorum commit. A publish request is determined by its
  position (\<open>wire_unique\<close>).
\<close>

fun wire_link :: "abstract_state \<Rightarrow> 'v message \<Rightarrow> bool" where
  "wire_link abstract_state (Join_Msg voter voter_role candidate join_term voter_position) =
    (voter_role = Master_Eligible \<longrightarrow>
      (voter, candidate, join_term, normalized voter_position) \<in> joins_sent abstract_state)"
| "wire_link abstract_state (Publish_Msg destination request new_value) =
    (publication_config request \<noteq> {}
     \<and> publication_previous_config request \<noteq> {}
     \<and> (\<exists>parent. parent @ [request] \<in> publications_sent abstract_state))"
| "wire_link abstract_state (Response_Msg voter voter_role leader position) =
    (voter_role = Master_Eligible \<longrightarrow>
      (\<exists>publication_history\<in>publications_sent abstract_state. (voter, publication_history) \<in> publish_responses_sent abstract_state
                                                              \<and> owner_of_tip_of publication_history = leader
                                                              \<and> position_of_tip_of publication_history = position))"
| "wire_link abstract_state (Commit_Msg leader destination position) =
    (\<exists>publication_history\<in>publications_committed abstract_state. owner_of_tip_of publication_history = leader
                                                                 \<and> position_of_tip_of publication_history = position)"

text \<open>
  Two publish requests in the messages with the same position are the same request, with the same
  value.
\<close>

definition wire_unique :: "'v message set \<Rightarrow> bool" where
  "wire_unique msgs \<longleftrightarrow>
    (\<forall>destination destination'
                      request
                      request'
                      new_value
                      new_value'.
                      Publish_Msg destination request new_value \<in> msgs \<longrightarrow> Publish_Msg
                                                                             destination'
                                                                             request'
                                                                             new_value' \<in> msgs \<longrightarrow>
      publication_position request = publication_position request' \<longrightarrow> request = request'
                                                                     \<and> new_value = new_value')"

text \<open>
  What the abstract model needs to know about the in-memory state of a data node that is not
  master-eligible, because its worker will write that state to disk: the position that it has
  accepted is that of a publication, is not behind the position on disk, and is no later than
  its current term.
\<close>

definition memory_link :: "abstract_state \<Rightarrow> 'v node_memory_state \<Rightarrow> 'v node_memory_state \<Rightarrow> bool" where
  "memory_link abstract_state disk_node memory_node \<longleftrightarrow>
    (position_term (last_accepted_position memory_node) = 0
     \<or> (\<exists>publication_history\<in>publications_sent abstract_state. position_of_tip_of publication_history = last_accepted_position memory_node))
    \<and> normalized (last_accepted_position disk_node) \<le> normalized (last_accepted_position memory_node)
    \<and> position_term (last_accepted_position memory_node) \<le> current_term memory_node"

text \<open>
  The state of a node that the abstract model describes is what the node would vote from after a
  restart, that is, what is on disk. \<open>disk_view state node\<close> is that state in the form of an in-memory
  state. For a master-eligible node it is the in-memory state, which is written through to the disk.
  For any other node it is the state that is read back from the disk (\<open>memory_of_disk\<close>), with no
  transient state.
\<close>

definition disk_view :: "'v java_state \<Rightarrow> node \<Rightarrow> 'v node_memory_state" where
  "disk_view state node =
    (if node_role (java_memory state node) = Master_Eligible
     then java_memory state node
     else memory_of_disk (node_role (java_memory state node)) (java_disk state node))"

lemma disk_view_master:
  "node_role (java_memory state node) = Master_Eligible \<Longrightarrow> disk_view state node = java_memory state node"
  by (simp add: disk_view_def)

lemma disk_view_other:
  "node_role (java_memory state node) \<noteq> Master_Eligible \<Longrightarrow>
    disk_view state node = memory_of_disk (node_role (java_memory state node)) (java_disk state node)"
  by (simp add: disk_view_def)

lemma disk_view_role[simp]: "node_role (disk_view state node) = node_role (java_memory state node)"
  by (simp add: disk_view_def memory_of_disk_def)

lemma disk_of_memory_of_disk[simp]: "disk_of (memory_of_disk role node_disk_state) = node_disk_state"
  by (cases node_disk_state) (simp add: disk_of_def memory_of_disk_def)

lemma disk_view_same:
  "java_memory new_state node = java_memory state node \<Longrightarrow> java_disk new_state node = java_disk state node \<Longrightarrow>
    disk_view new_state node = disk_view state node"
  by (simp add: disk_view_def)

text \<open>
  The relation between a Java state and an abstract state. The conjuncts are, in order:
  \<^item> Every node's \<open>disk_view\<close> is linked to the abstract node (\<open>node_link\<close>).
  \<^item> A master-eligible node's publish votes were responses, which are in the messages.
  \<^item> A master-eligible node's disk is what its in-memory state writes through to it.
  \<^item> A data node's in-memory state is linked to its disk (\<open>memory_link\<close>).
  \<^item> A node that is not master-eligible has not won an election.
  \<^item> Every message is linked to the abstract state (\<open>wire_link\<close>), and publish requests are unique
    by position (\<open>wire_unique\<close>).
\<close>

definition linked :: "config \<Rightarrow> 'v java_state \<Rightarrow> abstract_state \<Rightarrow> bool" where
  "linked initial_configuration state abstract_state \<longleftrightarrow>
    (\<forall>node. node_link initial_configuration abstract_state node (disk_view state node))
    \<and> (\<forall>leader voter. voter \<in> publish_votes (disk_view state leader) \<longrightarrow>
        Response_Msg voter Master_Eligible leader (last_published_position (disk_view state leader))
          \<in> java_messages state)
    \<and> (\<forall>node. node_role (java_memory state node) = Master_Eligible \<longrightarrow>
        java_disk state node = disk_of (java_memory state node))
    \<and> (\<forall>node. node_role (java_memory state node) = Data_Only \<longrightarrow>
        memory_link abstract_state (disk_view state node) (java_memory state node))
    \<and> (\<forall>node. node_role (java_memory state node) \<noteq> Master_Eligible \<longrightarrow>
        \<not> election_won (java_memory state node))
    \<and> (\<forall>message\<in>java_messages state. wire_link abstract_state message)
    \<and> wire_unique (java_messages state)"

lemma linkedD:
  assumes "linked initial_configuration state abstract_state"
  shows "node_link initial_configuration abstract_state node (disk_view state node)"
    "voter \<in> publish_votes (disk_view state node) \<Longrightarrow>
      Response_Msg voter Master_Eligible node (last_published_position (disk_view state node))
        \<in> java_messages state"
    "message \<in> java_messages state \<Longrightarrow> wire_link abstract_state message"
    "wire_unique (java_messages state)"
    "node_role (java_memory state node) = Master_Eligible \<Longrightarrow>
      java_disk state node = disk_of (java_memory state node)"
    "node_role (java_memory state node) = Data_Only \<Longrightarrow>
      memory_link abstract_state (disk_view state node) (java_memory state node)"
    "node_role (java_memory state node) \<noteq> Master_Eligible \<Longrightarrow>
      \<not> election_won (java_memory state node)"
  using assms unfolding linked_def by auto

lemma linked_disk_view_disk:
  assumes "linked initial_configuration state abstract_state"
  shows "disk_of (disk_view state node) = java_disk state node"
  using linkedD(5)[OF assms, of node] by (cases "node_role (java_memory state node) = Master_Eligible")
    (simp_all add: disk_view_master disk_view_other)

text \<open>
  \<open>grows before after\<close>: the sets of messages that the abstract model records only gain elements. A
  link to \<open>before\<close> that only mentions these sets in the positive direction carries over to \<open>after\<close>.
\<close>

definition grows :: "abstract_state \<Rightarrow> abstract_state \<Rightarrow> bool" where
  "grows before after \<longleftrightarrow>
    joins_sent before \<subseteq> joins_sent after
    \<and> publications_sent before \<subseteq> publications_sent after
    \<and> publish_responses_sent before \<subseteq> publish_responses_sent after
    \<and> publications_committed before \<subseteq> publications_committed after"

lemma memory_link_frame:
  "memory_link abstract_state disk_node memory_node \<Longrightarrow> grows abstract_state next_abstract_state \<Longrightarrow>
    memory_link next_abstract_state disk_node memory_node"
  unfolding memory_link_def grows_def by blast

lemma wire_frame:
  "grows abstract_state next_abstract_state \<Longrightarrow> wire_link abstract_state message \<Longrightarrow>
    wire_link next_abstract_state message"
  by (cases message) (auto simp: grows_def)

lemma fresh_frame:
  assumes "grows abstract_state next_abstract_state"
    "abstract_model.fresh_votes abstract_state node vote_term publication_history votes"
    "position_of_tip_of publication_history \<le> position_of_tip_of later_history"
    "fewer_votes \<subseteq> votes"
  shows "abstract_model.fresh_votes next_abstract_state node vote_term later_history fewer_votes"
proof (unfold abstract_model.fresh_votes_def, intro ballI)
  fix voter
  assume "voter \<in> fewer_votes"
  then have "voter \<in> votes" using assms(4) by blast
  then obtain position where "position \<le> position_of_tip_of publication_history"
    "(voter, node, vote_term, position) \<in> joins_sent abstract_state"
    using assms(2) unfolding abstract_model.fresh_votes_def by blast
  then have "position \<le> position_of_tip_of later_history" using assms(3) by order
  moreover have "(voter, node, vote_term, position) \<in> joins_sent next_abstract_state"
    using \<open>(voter, node, vote_term, position) \<in> joins_sent abstract_state\<close> assms(1) unfolding grows_def by blast
  ultimately show "\<exists>position\<le>position_of_tip_of later_history.
      (voter, node, vote_term, position) \<in> joins_sent next_abstract_state" by blast
qed

text \<open>
  \<open>node_frame before after node\<close>: the abstract node is the same in both abstract states, as far as
  the link to its \<open>disk_view\<close> is concerned.
\<close>

definition node_frame :: "abstract_state \<Rightarrow> abstract_state \<Rightarrow> node \<Rightarrow> bool" where
  "node_frame before after node \<longleftrightarrow>
    current_term_of before node = current_term_of after node
    \<and> publications_accepted before node = publications_accepted after node
    \<and> last_committed_configuration_of before node = last_committed_configuration_of after node
    \<and> abstract_model.active_leader before node = abstract_model.active_leader after node
    \<and> abstract_model.current_published_history before node = abstract_model.current_published_history after node"

lemma known_tip_frame:
  assumes "known_tip initial_configuration abstract_state node node_memory_state"
    "grows abstract_state next_abstract_state" "node_frame abstract_state next_abstract_state node"
  shows "known_tip initial_configuration next_abstract_state node node_memory_state"
proof -
  have published_same: "abstract_model.current_published_history next_abstract_state node
      = abstract_model.current_published_history abstract_state node"
    using assms(3) unfolding node_frame_def by metis
  have accepted_same: "publications_accepted next_abstract_state node = publications_accepted abstract_state node"
    using assms(3) unfolding node_frame_def by metis
  have sent_grows: "publications_sent abstract_state \<subseteq> publications_sent next_abstract_state"
    using assms(2) unfolding grows_def by blast
  show ?thesis using assms(1) sent_grows unfolding known_tip_def published_same accepted_same by blast
qed

lemma node_link_frame:
  assumes linked_node: "node_link initial_configuration abstract_state node node_memory_state"
  assumes grown: "grows abstract_state next_abstract_state"
  assumes framed: "node_frame abstract_state next_abstract_state node"
  shows "node_link initial_configuration next_abstract_state node node_memory_state"
proof -
  from framed have eqs: "current_term_of next_abstract_state node = current_term_of abstract_state node"
    "publications_accepted next_abstract_state node = publications_accepted abstract_state node"
    "last_committed_configuration_of next_abstract_state node = last_committed_configuration_of abstract_state node"
    "abstract_model.active_leader next_abstract_state node = abstract_model.active_leader abstract_state node"
    "abstract_model.current_published_history next_abstract_state node
      = abstract_model.current_published_history abstract_state node"
    unfolding node_frame_def by metis+
  have committed: "publications_committed abstract_state \<subseteq> publications_committed next_abstract_state"
    using grown unfolding grows_def by blast
  have effective: "election_won node_memory_state \<Longrightarrow> node_role node_memory_state = Master_Eligible \<Longrightarrow>
      abstract_model.effective_config
          initial_configuration
          (publications_committed next_abstract_state)
          (abstract_model.current_published_history next_abstract_state node)
          (last_committed_configuration_of next_abstract_state node)"
    using abstract_model.effective_config_mono[OF node_linkD(14)[OF linked_node] committed] eqs by auto
  have fresh: "abstract_model.fresh_votes
                   next_abstract_state
                   node
                   (current_term_of next_abstract_state node)
                   (publications_accepted next_abstract_state node)
                   (join_votes node_memory_state)"
    using fresh_frame[OF grown node_linkD(8)[OF linked_node], of
        "publications_accepted abstract_state node" "join_votes node_memory_state"] framed
    unfolding node_frame_def by simp
  have known: "election_won node_memory_state \<Longrightarrow>
      known_tip initial_configuration next_abstract_state node node_memory_state"
    using known_tip_frame[OF node_linkD(10)[OF linked_node] grown framed] by blast
  show ?thesis using linked_node known fresh effective unfolding node_link_defs by (simp add: eqs)
qed

lemma node_link_quorum_commits:
  assumes "node_link initial_configuration abstract_state node node_memory_state"
    "publications_committed abstract_state \<subseteq> commits"
  shows "node_link
             initial_configuration
             (abstract_state\<lparr>publications_committed := commits\<rparr>)
             node
             node_memory_state"
proof (rule node_link_frame[OF assms(1)])
  show "grows abstract_state (abstract_state\<lparr>publications_committed := commits\<rparr>)"
    using assms(2) unfolding grows_def by simp
  show "node_frame abstract_state (abstract_state\<lparr>publications_committed := commits\<rparr>) node"
    unfolding node_frame_def abstract_model.active_leader_def by simp
qed

lemma transition_grows:
  "abstract_model.transition initial_configuration abstract_state next_abstract_state \<Longrightarrow>
    grows abstract_state next_abstract_state"
  by (erule abstract_model.transition.cases) (auto simp: grows_def)

lemma grows_refl[simp]: "grows abstract_state abstract_state"
  by (simp add: grows_def)

lemma node_frame_refl[simp]: "node_frame abstract_state abstract_state node"
  by (simp add: node_frame_def)

lemma wire_unique_control:
  assumes "wire_unique messages" "\<And>destination publication payload_value. Publish_Msg
                                                                              destination
                                                                              publication
                                                                              payload_value \<notin> new_messages"
  shows "wire_unique (messages \<union> new_messages)"
  using assms unfolding wire_unique_def by blast

lemma fresh_vote_insert:
  assumes fresh: "abstract_model.fresh_votes
                      abstract_state
                      candidate
                      vote_term
                      publication_history
                      votes"
  assumes message: "(voter, candidate, vote_term, position) \<in> joins_sent abstract_state"
    "position \<le> position_of_tip_of publication_history"
  shows "abstract_model.fresh_votes
             abstract_state
             candidate
             vote_term
             publication_history
             (insert voter votes)"
proof (unfold abstract_model.fresh_votes_def, intro ballI)
  fix other_voter
  assume "other_voter \<in> insert voter votes"
  then show "\<exists>position\<le>position_of_tip_of publication_history.
      (other_voter, candidate, vote_term, position) \<in> joins_sent abstract_state"
    using fresh message unfolding abstract_model.fresh_votes_def by blast
qed

text \<open>No election has been won in a term that a node has not reached.\<close>

lemma certificate_future:
  assumes reaches: "abstract_model.dynamic_reachable initial_configuration abstract_state"
  assumes newer: "current_term_of abstract_state node < vote_term"
  shows "elections_won abstract_state (node, vote_term) = None"
proof (rule ccontr)
  assume "elections_won abstract_state (node, vote_term) \<noteq> None"
  then have "vote_term \<le> current_term_of abstract_state node"
    using abstract_model.reachable_current_published_history_ok[OF reaches]
    unfolding abstract_model.current_published_history_ok_def by blast
  with newer show False by simp
qed

lemma known_tip_insert_join:
  assumes "known_tip initial_configuration abstract_state node node_memory_state"
  shows "known_tip
             initial_configuration
             abstract_state
             node
             (node_memory_state\<lparr>join_votes := insert voter (join_votes node_memory_state)\<rparr>)"
  using assms unfolding known_tip_def by (auto simp: Let_def intro: quorum_grow)

lemma no_wire_collision:
  assumes unique: "wire_unique messages"
  assumes fresh: "\<And>destination publication payload_value.
    Publish_Msg destination publication payload_value \<in> messages \<Longrightarrow>
    publication_position publication \<noteq> publication_position new_publication"
  shows "wire_unique (messages \<union> {Publish_Msg destination new_publication new_value | destination. True})"
  unfolding wire_unique_def
proof (intro allI impI)
  fix destination other_destination publication other_publication payload_value other_payload_value
  let ?messages = "messages \<union> {Publish_Msg destination new_publication new_value | destination. True}"
  assume first: "Publish_Msg destination publication payload_value \<in> ?messages"
    and second: "Publish_Msg other_destination other_publication other_payload_value \<in> ?messages"
    and position: "publication_position publication = publication_position other_publication"
  from first have first': "Publish_Msg destination publication payload_value \<in> messages
                           \<or> publication = new_publication \<and> payload_value = new_value" by auto
  from second have second': "Publish_Msg other_destination other_publication other_payload_value \<in> messages
                             \<or> other_publication = new_publication \<and> other_payload_value = new_value" by auto
  from first' second' position unique fresh[of destination publication payload_value]
    fresh[of other_destination other_publication other_payload_value]
  show "publication = other_publication \<and> payload_value = other_payload_value" unfolding wire_unique_def by auto
qed

text \<open>
  The update of one node. \<open>new_state\<close> is a state that differs from \<open>state\<close> in the memory and the
  disk of node \<open>node\<close>, and in having more messages. The abstract state \<open>next_abstract_state\<close> follows
  \<open>abstract_state\<close>.
\<close>

lemma link_update:
  assumes old: "linked initial_configuration state abstract_state"
  assumes grown: "grows abstract_state next_abstract_state"
  assumes same: "\<And>other_node. other_node \<noteq> node \<Longrightarrow>
    java_memory new_state other_node = java_memory state other_node
    \<and> java_disk new_state other_node = java_disk state other_node"
  assumes linked_node: "node_link
                            initial_configuration
                            next_abstract_state
                            node
                            (disk_view new_state node)"
  assumes frame: "\<And>other_node. other_node \<noteq> node \<Longrightarrow> node_frame
                                                       abstract_state
                                                       next_abstract_state
                                                       other_node"
  assumes disk: "node_role (java_memory new_state node) = Master_Eligible \<Longrightarrow>
    java_disk new_state node = disk_of (java_memory new_state node)"
  assumes replies: "\<forall>voter\<in>publish_votes (disk_view new_state node).
    Response_Msg voter Master_Eligible node (last_published_position (disk_view new_state node))
      \<in> java_messages new_state"
  assumes mem_link: "node_role (java_memory new_state node) = Data_Only \<Longrightarrow>
    memory_link next_abstract_state (disk_view new_state node) (java_memory new_state node)"
  assumes no_won: "node_role (java_memory new_state node) \<noteq> Master_Eligible \<Longrightarrow>
    \<not> election_won (java_memory new_state node)"
  assumes messages: "java_messages state \<subseteq> java_messages new_state"
  assumes news: "\<And>message. message \<in> java_messages new_state \<Longrightarrow> message \<notin> java_messages state \<Longrightarrow>
    wire_link next_abstract_state message"
  assumes unique: "wire_unique (java_messages new_state)"
  shows "linked initial_configuration new_state next_abstract_state"
proof -
  have view: "other_node \<noteq> node \<Longrightarrow> disk_view new_state other_node = disk_view state other_node"
    for other_node
    using same[of other_node] by (blast intro: disk_view_same)
  have "node_link
            initial_configuration
            next_abstract_state
            other_node
            (disk_view new_state other_node)"
    for other_node
    using linked_node node_link_frame[OF linkedD(1)[OF old, of other_node] grown]
      frame[of other_node] view[of other_node] by (cases "other_node = node") auto
  moreover have "voter \<in> publish_votes (disk_view new_state leader) \<Longrightarrow>
      Response_Msg
          voter
          Master_Eligible
          leader
          (last_published_position (disk_view new_state leader))
        \<in> java_messages new_state" for voter leader
    using replies linkedD(2)[OF old, of voter leader] messages view[of leader]
    by (cases "leader = node") auto
  moreover have "node_role (java_memory new_state other_node) = Master_Eligible \<Longrightarrow>
      java_disk new_state other_node = disk_of (java_memory new_state other_node)" for other_node
    using disk linkedD(5)[OF old, of other_node] same[of other_node] by (cases "other_node = node") auto
  moreover have "node_role (java_memory new_state other_node) = Data_Only \<Longrightarrow>
      memory_link
          next_abstract_state
          (disk_view new_state other_node)
          (java_memory new_state other_node)"
    for other_node
    using mem_link linkedD(6)[OF old, of other_node]
      memory_link_frame[OF _ grown, of "disk_view state other_node" "java_memory state other_node"]
      same[of other_node] view[of other_node] by (cases "other_node = node") auto
  moreover have "node_role (java_memory new_state other_node) \<noteq> Master_Eligible \<Longrightarrow>
      \<not> election_won (java_memory new_state other_node)" for other_node
    using no_won linkedD(7)[OF old, of other_node] same[of other_node] by (cases "other_node = node") auto
  moreover have "wire_link next_abstract_state message" if "message \<in> java_messages new_state" for message
    using that news[of message] wire_frame[OF grown linkedD(3)[OF old, of message]] by blast
  ultimately show ?thesis using unique unfolding linked_def by blast
qed

lemma linked_initial:
  "linked
       initial_configuration
       (java_initial initial_value versions)
       (abstract_model.bootstrapped initial_configuration)"
  unfolding linked_def node_link_defs wire_unique_def abstract_model.fresh_votes_def abstract_model.active_leader_def
  by (simp add: java_initial_def disk_view_def disk_of_def abstract_model.bootstrapped_def normalized_def memory_link_def)

section \<open>Simulation of each call\<close>

text \<open>
  Each simulation lemma, in the theories that import this one, shows that, from linked states, a call
  that respects the caller contract gives a Java state that is linked to the same abstract state or
  to one that follows it by one transition. A call that the class rejects changes nothing, and
  stutters.
\<close>

locale simulation =
  fixes initial_configuration :: config and state :: "'v java_state" and abstract_state :: abstract_state
  assumes boot: "initial_configuration \<noteq> {}"
  assumes reach: "abstract_model.dynamic_reachable initial_configuration abstract_state"
  assumes link: "linked initial_configuration state abstract_state"

end
