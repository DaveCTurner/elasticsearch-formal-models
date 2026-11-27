theory Zen_With_Terms_Refinement
  imports Zen_With_Terms_Translation Abstract_Model
begin

section \<open>Relating messages and local state to the dynamic model\<close>

text \<open>
  The TLA+ translation refines the dynamic model of \<open>Abstract_Model\<close>.
  The relation \<open>linked initial_configuration s a\<close> holds between a TLA+ state \<open>s\<close> and an abstract
  state \<open>a\<close> when each node's state on disk (\<open>node_link\<close>), the in-memory state of each node
  that is not master-eligible (\<open>memory_link\<close>), each message
  (\<open>wire_link\<close>) and the \<open>descendant\<close> relation (\<open>ancestry_link\<close>) correspond to
  the abstract state. Every TLA+ action is simulated by at most one abstract
  transition, so the safety properties of the dynamic model hold in the TLA+
  translation.
\<close>

text \<open>
  The abstract model gives a node with no history the position \<open>position_zero\<close>, whereas
  the TLA+ position at term zero carries the node's initial version.
  \<open>normalized\<close> maps every position at term zero to \<open>position_zero\<close>.
\<close>

definition normalized :: "position \<Rightarrow> position" where
  "normalized position = (if position_term position = 0 then position_zero else position)"

lemma normalized_mono:
  "k \<le> r \<Longrightarrow> normalized k \<le> normalized r"
  by (cases k; cases r) (auto simp: normalized_def position_le_iff)

lemma quorum_nonempty: "quorum initial_configuration Q \<Longrightarrow> initial_configuration \<noteq> {}"
  unfolding quorum_def majority_def voting_nodes_of_def by auto

lemma quorum_grow:
  assumes q: "quorum initial_configuration Q"
  assumes sub: "Q \<subseteq> R"
  shows "quorum initial_configuration R"
proof -
  have fin: "finite (voting_nodes_of initial_configuration)" using q unfolding quorum_def majority_def by simp
  have "card (voting_nodes_of initial_configuration \<inter> Q) \<le> card (voting_nodes_of initial_configuration \<inter> R)"
    by (rule card_mono) (use fin sub in auto)
  with q fin show ?thesis unfolding quorum_def majority_def by auto
qed

lemma is_election_quorum_insert: "is_election_quorum x Q \<Longrightarrow> is_election_quorum x (insert n Q)"
  unfolding is_election_quorum_def by (auto intro: quorum_grow)

text \<open>
  What a leader has published. Either it has won its election but not yet
  published, so the abstract tip is behind the term and equals its durable
  history, or it has published its tip, which is in \<open>publications_sent\<close> and matches
  its last published position and configuration.
\<close>

lemma quorum_stale: "\<not> quorum stale_config Q"
  unfolding quorum_def majority_def stale_config_def voting_nodes_of_def by simp

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
  The correspondence for one node, between the abstract state and the node's state \<open>nodes_at\<close>:
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
        is_election_quorum node_memory_state (join_votes node_memory_state)
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
  assumes "node_link initial_configuration a n x"
  shows "current_term x = current_term_of a n"
    "node_role x = Master_Eligible \<Longrightarrow> started_join_since_last_reboot x \<Longrightarrow> 0 < current_term_of a n"
    "node_role x = Master_Eligible \<Longrightarrow> election_won x \<Longrightarrow> abstract_model.active_leader a n"
    "normalized (last_accepted_position x) = position_of_tip_of (publications_accepted a n)"
    "last_accepted_configuration x = {} \<Longrightarrow> publications_accepted a n = []
                                          \<and> last_committed_configuration x = {}"
    "last_accepted_configuration x \<noteq> {} \<Longrightarrow> last_accepted_configuration x \<noteq> stale_config \<Longrightarrow>
      last_accepted_configuration x = config_of_tip_of initial_configuration (publications_accepted a n)"
    "last_committed_configuration x \<noteq> stale_config \<Longrightarrow>
      last_committed_configuration_of a n = (if last_committed_configuration x = {} then initial_configuration else last_committed_configuration x)"
    "abstract_model.fresh_votes a n (current_term_of a n) (publications_accepted a n) (join_votes x)"
    "election_won x \<Longrightarrow> is_election_quorum x (join_votes x)"
    "election_won x \<Longrightarrow> known_tip initial_configuration a n x"
    "election_won x \<Longrightarrow> node_role x = Master_Eligible"
    "node_role x \<noteq> Master_Eligible \<Longrightarrow> join_votes x = {}"
    "node_role x \<noteq> Master_Eligible \<Longrightarrow> publish_votes x = {}"
    "node_role x = Master_Eligible \<Longrightarrow> election_won x \<Longrightarrow> abstract_model.effective_config
                                                          initial_configuration
                                                          (publications_committed a)
                                                          (abstract_model.current_published_history a n)
                                                          (last_committed_configuration_of a n)"
    "node_role x = Master_Eligible \<Longrightarrow> started_join_since_last_reboot x \<Longrightarrow> election_won x = abstract_model.active_leader a n"
    "node_role x = Master_Eligible \<Longrightarrow> election_won x \<Longrightarrow> started_join_since_last_reboot x"
  using assms unfolding node_link_defs by (auto split: if_splits)

text \<open>A node that has won an election has real configurations: nobody votes as the stale marker.\<close>

lemma quorum_not_stale:
  assumes "quorum D Q"
  shows "D \<noteq> stale_config"
  using assms quorum_stale by blast

lemma node_link_won_configurations:
  assumes "node_link initial_configuration a n x" "election_won x"
  shows "last_accepted_configuration x \<noteq> stale_config" "last_committed_configuration x \<noteq> stale_config"
proof -
  have "quorum (last_committed_configuration x) (join_votes x)"
    "quorum (last_accepted_configuration x) (join_votes x)"
    using node_linkD(9)[OF assms(1) assms(2)] unfolding is_election_quorum_def by simp_all
  hence "last_committed_configuration x \<noteq> stale_config
         \<and> last_accepted_configuration x \<noteq> stale_config"
    using quorum_not_stale by blast
  then show "last_accepted_configuration x \<noteq> stale_config" "last_committed_configuration x \<noteq> stale_config"
    by simp_all
qed

lemma node_link_publish_votes[simp]:
  "node_role x = Master_Eligible \<Longrightarrow> node_link initial_configuration a n (x\<lparr>publish_votes := Q\<rparr>) \<longleftrightarrow> node_link
                                                                                                     initial_configuration
                                                                                                     a
                                                                                                     n
                                                                                                     x"
  by (simp add: node_link_defs known_tip_def is_election_quorum_def)

lemma normalized_term[simp]: "position_term (normalized k) = position_term k"
  by (auto simp: normalized_def position_le_iff)

lemma publication_positive:
  assumes "abstract_model.publications_ok initial_configuration a" "h \<in> publications_sent a"
  shows "0 < term_of_tip_of h"
  using abstract_model.publicationsD(2,4)[OF assms(1)] assms(2)
  by (cases h rule: rev_cases) (auto simp: abstract_model.valid_edge_def)

lemma durable_position:
  assumes "node_link initial_configuration a n x" "publications_accepted a n \<noteq> []"
    "abstract_model.dynamic_reachable initial_configuration a"
  shows "last_accepted_position x = position_of_tip_of (publications_accepted a n)"
proof -
  have ok: "abstract_model.publications_ok initial_configuration a" and j: "abstract_model.messages_ok initial_configuration a" using abstract_model.dynamic_invariants[OF assms(3)] by auto
  have h: "publications_accepted a n \<in> publications_sent a" using abstract_model.messagesD(1)[OF j, of n] assms(2) by simp
  have positive: "0 < term_of_tip_of (publications_accepted a n)" by (rule publication_positive[OF ok h])
  with node_linkD(4)[OF assms(1)] show ?thesis by (auto simp: normalized_def split: if_splits)
qed

lemma linked_position_equal:
  assumes "node_link initial_configuration a n x" "election_won x"
    "last_published_version x = position_version (last_accepted_position x)"
  shows "abstract_model.current_published_history a n = publications_accepted a n"
proof -
  show ?thesis using node_linkD(10)[OF assms(1,2)] assms(3) unfolding known_tip_def by auto
qed

lemma linked_boot_versions:
  assumes "node_link initial_configuration a n x" "position_version (last_accepted_position x) < v"
  shows "position_version (position_of_tip_of (publications_accepted a n)) < v"
proof -
  have "position_version (normalized (last_accepted_position x)) \<le> position_version (last_accepted_position x)" by (simp add: normalized_def)
  then show ?thesis using node_linkD(4)[OF assms(1)] assms(2) by (metis le_less_trans)
qed

text \<open>
  The correspondence for messages. A \<open>Join_Msg\<close> was sent, a \<open>Publish_Msg\<close> carries
  a publication that was made, a \<open>Response_Msg\<close> is an acknowledgement of one, and
  a \<open>Commit_Msg\<close> is for a quorum commit. A publish request is determined by its
  position.
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

definition ancestry_link :: "'v tla_state \<Rightarrow> abstract_state \<Rightarrow> bool" where
  "ancestry_link state abstract_state \<longleftrightarrow>
    (\<forall>publication_history\<in>publications_sent abstract_state. \<forall>ancestor\<in>publications_sent abstract_state.
      prefix ancestor publication_history \<and> ancestor \<noteq> publication_history \<longrightarrow>
      (position_of_tip_of ancestor, position_of_tip_of publication_history) \<in> descendant state)"

lemma ancestry_edge:
  assumes "ancestry_link s a" "p \<in> publications_sent a" "h \<in> publications_sent a" "prefix p h" "p \<noteq> h"
  shows "(position_of_tip_of p,position_of_tip_of h) \<in> descendant s"
  using assms unfolding ancestry_link_def by auto

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

definition linked :: "config \<Rightarrow> 'v tla_state \<Rightarrow> abstract_state \<Rightarrow> bool" where
  "linked initial_configuration state abstract_state \<longleftrightarrow>
    (\<forall>node. node_link initial_configuration abstract_state node (nodes_at state node))
    \<and> (\<forall>leader voter. voter \<in> publish_votes (nodes_at state leader) \<longrightarrow>
        Response_Msg voter Master_Eligible leader (last_published_position (nodes_at state leader))
          \<in> messages state)
    \<and> (\<forall>node. node_role (memory_at state node) = node_role (nodes_at state node))
    \<and> (\<forall>node. node_role (nodes_at state node) = Data_Only \<longrightarrow>
        memory_link abstract_state (nodes_at state node) (memory_at state node))
    \<and> (\<forall>node. node_role (nodes_at state node) \<noteq> Master_Eligible \<longrightarrow> \<not> election_won (memory_at state node))
    \<and> (\<forall>message\<in>messages state. wire_link abstract_state message)
    \<and> wire_unique (messages state)
    \<and> ancestry_link state abstract_state"

lemma linkedD:
  assumes "linked initial_configuration s a"
  shows "node_link initial_configuration a n (nodes_at s n)"
    "p \<in> publish_votes (nodes_at s n) \<Longrightarrow>
      Response_Msg p Master_Eligible n (last_published_position (nodes_at s n)) \<in> messages s"
    "m \<in> messages s \<Longrightarrow> wire_link a m"
    "wire_unique (messages s)"
    "ancestry_link s a"
    "node_role (memory_at s n) = node_role (nodes_at s n)"
    "node_role (nodes_at s n) = Data_Only \<Longrightarrow> memory_link a (nodes_at s n) (memory_at s n)"
    "node_role (nodes_at s n) \<noteq> Master_Eligible \<Longrightarrow> \<not> election_won (memory_at s n)"
  using assms unfolding linked_def by auto

definition grows :: "abstract_state \<Rightarrow> abstract_state \<Rightarrow> bool" where
  "grows before after \<longleftrightarrow>
    joins_sent before \<subseteq> joins_sent after
    \<and> publications_sent before \<subseteq> publications_sent after
    \<and> publish_responses_sent before \<subseteq> publish_responses_sent after
    \<and> publications_committed before \<subseteq> publications_committed after"

lemma memory_link_frame:
  "memory_link a x m \<Longrightarrow> grows a b \<Longrightarrow> memory_link b x m"
  unfolding memory_link_def grows_def by blast

lemma wire_frame:
  "grows a b \<Longrightarrow> wire_link a m \<Longrightarrow> wire_link b m"
  by (cases m) (auto simp: grows_def)

lemma fresh_frame:
  assumes "grows a b" "abstract_model.fresh_votes a n t h Q" "position_of_tip_of h \<le> position_of_tip_of k" "Q' \<subseteq> Q"
  shows "abstract_model.fresh_votes b n t k Q'"
proof (unfold abstract_model.fresh_votes_def, intro ballI)
  fix q
  assume "q \<in> Q'"
  then have "q \<in> Q" using assms(4) by blast
  then obtain r where "r \<le> position_of_tip_of h" "(q,n,t,r) \<in> joins_sent a"
    using assms(2) unfolding abstract_model.fresh_votes_def by blast
  then have "r \<le> position_of_tip_of k" using assms(3) by order
  moreover have "(q,n,t,r) \<in> joins_sent b"
    using \<open>(q,n,t,r) \<in> joins_sent a\<close> assms(1) unfolding grows_def by blast
  ultimately show "\<exists>r\<le>position_of_tip_of k. (q,n,t,r) \<in> joins_sent b" by blast
qed

definition node_frame :: "abstract_state \<Rightarrow> abstract_state \<Rightarrow> node \<Rightarrow> bool" where
  "node_frame before after node \<longleftrightarrow>
    current_term_of before node = current_term_of after node
    \<and> publications_accepted before node = publications_accepted after node
    \<and> last_committed_configuration_of before node = last_committed_configuration_of after node
    \<and> abstract_model.active_leader before node = abstract_model.active_leader after node
    \<and> abstract_model.current_published_history before node = abstract_model.current_published_history after node"

lemma known_tip_frame:
  assumes "known_tip initial_configuration a n x" "grows a b" "node_frame a b n"
  shows "known_tip initial_configuration b n x"
proof -
  have ct: "abstract_model.current_published_history b n = abstract_model.current_published_history a n"
    using assms(3) unfolding node_frame_def by metis
  have dh: "publications_accepted b n = publications_accepted a n" using assms(3) unfolding node_frame_def by metis
  have pubs: "publications_sent a \<subseteq> publications_sent b" using assms(2) unfolding grows_def by blast
  show ?thesis using assms(1) pubs unfolding known_tip_def ct dh by blast
qed

lemma node_link_frame:
  assumes node: "node_link initial_configuration a n x"
  assumes g: "grows a b"
  assumes f: "node_frame a b n"
  shows "node_link initial_configuration b n x"
proof -
  from f have eqs: "current_term_of b n = current_term_of a n" "publications_accepted b n = publications_accepted a n"
    "last_committed_configuration_of b n = last_committed_configuration_of a n"
    "abstract_model.active_leader b n = abstract_model.active_leader a n"
    "abstract_model.current_published_history b n = abstract_model.current_published_history a n"
    unfolding node_frame_def by metis+
  have committed: "publications_committed a \<subseteq> publications_committed b" using g unfolding grows_def by blast
  have effective: "election_won x \<Longrightarrow> node_role x = Master_Eligible \<Longrightarrow> abstract_model.effective_config
                                                                        initial_configuration
                                                                        (publications_committed b)
                                                                        (abstract_model.current_published_history b n)
                                                                        (last_committed_configuration_of b n)"
    using abstract_model.effective_config_mono[OF node_linkD(14)[OF node] committed] eqs by auto
  have fresh: "abstract_model.fresh_votes
                   b
                   n
                   (current_term_of b n)
                   (publications_accepted b n)
                   (join_votes x)"
    using fresh_frame[OF g node_linkD(8)[OF node], of "publications_accepted a n" "join_votes x"] f
    unfolding node_frame_def by simp
  have known: "election_won x \<Longrightarrow> known_tip initial_configuration b n x"
    using known_tip_frame[OF node_linkD(10)[OF node] g f] by blast
  show ?thesis using node known fresh effective unfolding node_link_defs by (simp add: eqs)
qed

lemma node_link_quorum_commits:
  assumes "node_link initial_configuration a n x" "publications_committed a \<subseteq> K"
  shows "node_link initial_configuration (a\<lparr>publications_committed := K\<rparr>) n x"
proof (rule node_link_frame[OF assms(1)])
  show "grows a (a\<lparr>publications_committed := K\<rparr>)" using assms(2) unfolding grows_def by simp
  show "node_frame a (a\<lparr>publications_committed := K\<rparr>) n"
    unfolding node_frame_def abstract_model.active_leader_def by simp
qed

lemma link_update:
  assumes old: "linked initial_configuration s a"
  assumes g: "grows a b"
  assumes node: "node_link initial_configuration b n x"
  assumes frame: "\<And>i. i \<noteq> n \<Longrightarrow> node_frame a b i"
  assumes master: "node_role (nodes_at s n) = Master_Eligible" "node_role x = Master_Eligible"
  assumes replies: "\<forall>p\<in>publish_votes x. Response_Msg p Master_Eligible n (last_published_position x) \<in> M"
  assumes messages: "messages s \<subseteq> M"
  assumes news: "\<And>m. m \<in> M \<Longrightarrow> m \<notin> messages s \<Longrightarrow> wire_link b m"
  assumes unique: "wire_unique M"
  assumes ancestry: "ancestry_link ((put_node s n x)\<lparr>messages := M, descendant := G\<rparr>) b"
  shows "linked initial_configuration ((put_node s n x)\<lparr>messages := M, descendant := G\<rparr>) b"
proof -
  have "node_link initial_configuration b i (((nodes_at s)(n := x)) i)" for i
    using node node_link_frame[OF linkedD(1)[OF old, of i] g] frame[of i] by auto
  moreover have "wire_link b m" if "m \<in> M" for m
    using that news[of m] wire_frame[OF g linkedD(3)[OF old, of m]] by blast
  moreover have "node_role (memory_at s i) = node_role (((nodes_at s)(n := x)) i)" for i
    using linkedD(6)[OF old, of i] linkedD(6)[OF old, of n] master by (cases "i = n") auto
  moreover have "node_role (((nodes_at s)(n := x)) i) = Data_Only \<longrightarrow>
      memory_link b (((nodes_at s)(n := x)) i) (memory_at s i)" for i
    using linkedD(7)[OF old, of i] memory_link_frame[OF _ g, of "nodes_at s i" "memory_at s i"] master
    by (cases "i = n") auto
  moreover have "node_role (((nodes_at s)(n := x)) i) \<noteq> Master_Eligible \<longrightarrow> \<not> election_won (memory_at s i)" for i
    using linkedD(8)[OF old, of i] master by (cases "i = n") auto
  ultimately show ?thesis using replies messages linkedD(2)[OF old] unique ancestry
    unfolding linked_def put_node_def by auto
qed

lemma ancestry_unchanged:
  assumes "linked initial_configuration s a" "publications_sent b = publications_sent a" "descendant s \<subseteq> descendant s'"
  shows "ancestry_link s' b"
  using linkedD(5)[OF assms(1)] assms(2,3) unfolding ancestry_link_def by blast

lemma linked_initial:
  "linked
       initial_configuration
       (tla_initial initial_value versions)
       (abstract_model.bootstrapped initial_configuration)"
  unfolding linked_def node_link_defs wire_unique_def ancestry_link_def abstract_model.fresh_votes_def abstract_model.active_leader_def
  by (simp add: tla_initial_def initial_node_def abstract_model.bootstrapped_def normalized_def memory_link_def)

lemma transition_grows:
  "abstract_model.transition initial_configuration a b \<Longrightarrow> grows a b"
  by (erule abstract_model.transition.cases) (auto simp: grows_def)

lemma grows_refl[simp]: "grows a a"
  by (simp add: grows_def)

lemma node_frame_refl[simp]: "node_frame a a n"
  by (simp add: node_frame_def)

lemma link_node_update:
  assumes old: "linked initial_configuration s a"
  assumes g: "grows a b"
  assumes node: "node_link initial_configuration b n x"
  assumes frame: "\<And>i. i \<noteq> n \<Longrightarrow> node_frame a b i"
  assumes master: "node_role (nodes_at s n) = Master_Eligible" "node_role x = Master_Eligible"
  assumes replies: "\<forall>p\<in>publish_votes x. Response_Msg p Master_Eligible n (last_published_position x) \<in> messages s"
  assumes pubs: "publications_sent b = publications_sent a"
  shows "linked initial_configuration (put_node s n x) b"
proof -
  have "ancestry_link ((put_node s n x)\<lparr>messages := messages s, descendant := descendant s\<rparr>) b"
    by (rule ancestry_unchanged[OF old pubs]) (simp add: put_node_def)
  from link_update[OF old g node frame master replies _ _ linkedD(4)[OF old] this]
  show ?thesis
    by (simp add: put_node_def)
qed

text \<open>
  The update of a node that need not be master-eligible, which also changes its in-memory state.
\<close>

lemma link_update_memory:
  assumes old: "linked initial_configuration s a"
  assumes g: "grows a b"
  assumes node: "node_link initial_configuration b n x"
  assumes frame: "\<And>i. i \<noteq> n \<Longrightarrow> node_frame a b i"
  assumes role: "node_role m = node_role x"
  assumes mem_link: "node_role x = Data_Only \<Longrightarrow> memory_link b x m"
  assumes no_won: "node_role x \<noteq> Master_Eligible \<Longrightarrow> \<not> election_won m"
  assumes replies: "\<forall>p\<in>publish_votes x. Response_Msg p Master_Eligible n (last_published_position x) \<in> M"
  assumes messages: "messages s \<subseteq> M"
  assumes news: "\<And>msg. msg \<in> M \<Longrightarrow> msg \<notin> messages s \<Longrightarrow> wire_link b msg"
  assumes unique: "wire_unique M"
  assumes ancestry: "ancestry_link ((put_node s n x)\<lparr>
    memory_at  := (memory_at s)(n := m),
    messages   := M,
    descendant := G
  \<rparr>) b"
  shows "linked
             initial_configuration
             ((put_node s n x)\<lparr>
               memory_at  := (memory_at s)(n := m),
               messages   := M,
               descendant := G
             \<rparr>)
             b"
proof -
  have "node_link initial_configuration b i (((nodes_at s)(n := x)) i)" for i
    using node node_link_frame[OF linkedD(1)[OF old, of i] g] frame[of i] by auto
  moreover have "wire_link b msg" if "msg \<in> M" for msg
    using that news[of msg] wire_frame[OF g linkedD(3)[OF old, of msg]] by blast
  moreover have "node_role (((memory_at s)(n := m)) i) = node_role (((nodes_at s)(n := x)) i)" for i
    using linkedD(6)[OF old, of i] role by (cases "i = n") auto
  moreover have "node_role (((nodes_at s)(n := x)) i) = Data_Only \<longrightarrow>
      memory_link b (((nodes_at s)(n := x)) i) (((memory_at s)(n := m)) i)" for i
    using linkedD(7)[OF old, of i] memory_link_frame[OF _ g, of "nodes_at s i" "memory_at s i"] mem_link
    by (cases "i = n") auto
  moreover have "node_role (((nodes_at s)(n := x)) i) \<noteq> Master_Eligible \<longrightarrow>
      \<not> election_won (((memory_at s)(n := m)) i)" for i
    using linkedD(8)[OF old, of i] no_won by (cases "i = n") auto
  ultimately show ?thesis using replies messages linkedD(2)[OF old] unique ancestry
    unfolding linked_def put_node_def by auto
qed

lemma wire_unique_control:
  assumes "wire_unique M" "\<And>d p v. Publish_Msg d p v \<notin> K"
  shows "wire_unique (M \<union> K)"
  using assms unfolding wire_unique_def by blast

lemma fresh_vote_insert:
  assumes fresh: "abstract_model.fresh_votes a c t h Q"
  assumes msg: "(n,c,t,r) \<in> joins_sent a" "r \<le> position_of_tip_of h"
  shows "abstract_model.fresh_votes a c t h (insert n Q)"
proof (unfold abstract_model.fresh_votes_def, intro ballI)
  fix i
  assume "i \<in> insert n Q"
  then show "\<exists>r\<le>position_of_tip_of h. (i,c,t,r) \<in> joins_sent a"
    using fresh msg unfolding abstract_model.fresh_votes_def by blast
qed

lemma certificate_future:
  assumes reaches: "abstract_model.dynamic_reachable initial_configuration a"
  assumes newer: "current_term_of a n < t"
  shows "elections_won a (n,t) = None"
proof (rule ccontr)
  assume "elections_won a (n,t) \<noteq> None"
  then have "t \<le> current_term_of a n" using abstract_model.reachable_current_published_history_ok[OF reaches]
    unfolding abstract_model.current_published_history_ok_def by blast
  with newer show False by simp
qed

lemma known_tip_insert_join:
  assumes "known_tip initial_configuration a n x"
  shows "known_tip initial_configuration a n (x\<lparr>join_votes := insert i (join_votes x)\<rparr>)"
  using assms unfolding known_tip_def by (auto simp: Let_def intro: quorum_grow)

lemma ancestry_extend:
  assumes old: "ancestry_link s a"
  assumes ok: "abstract_model.publications_ok initial_configuration a"
  assumes parent: "p \<in> insert [] (publications_sent a)"
  assumes position: "p \<noteq> [] \<Longrightarrow> k = position_of_tip_of p"
  assumes new: "h = p @ [x]" "h \<notin> publications_sent a"
  assumes pubs: "publications_sent b = insert h (publications_sent a)"
  assumes graph: "descendant s' = extend_descendant (descendant s) k (position_of_tip_of h)"
  shows "ancestry_link s' b"
  unfolding ancestry_link_def
proof (intro ballI impI)
  fix e d
  assume e: "e \<in> publications_sent b" and d: "d \<in> publications_sent b" and pref: "prefix d e \<and> d \<noteq> e"
  have "e \<in> publications_sent a \<or> e = h" using e pubs by auto
  then show "(position_of_tip_of d,position_of_tip_of e) \<in> descendant s'"
  proof
    assume ep: "e \<in> publications_sent a"
    have dp: "d \<in> publications_sent a"
      using abstract_model.prefix_of_sent[OF ok, of e d] ep pref d pubs new by auto
    from old ep dp pref show ?thesis unfolding ancestry_link_def graph extend_descendant_def by blast
  next
    assume eh: "e = h"
    then have dp: "d \<in> publications_sent a" using d pref pubs by simp
    have pre: "prefix d p" using pref eh new(1) by auto
    then have nonempty: "p \<noteq> []" using dp abstract_model.publicationsD(2)[OF ok] by auto
    have pp: "p \<in> publications_sent a" using parent nonempty by simp
    show ?thesis
    proof (cases "d = p")
      case True
      with position[OF nonempty] eh show ?thesis unfolding graph extend_descendant_def by simp
    next
      case False
      have edge: "(position_of_tip_of d,position_of_tip_of p) \<in> descendant s" by (rule ancestry_edge[OF old dp pp pre False])
      have "(position_of_tip_of d,position_of_tip_of h) \<in> {(a,position_of_tip_of h) | a. (a,k) \<in> descendant s}"
        by (rule CollectI, rule exI[of _ "position_of_tip_of d"]) (simp add: edge position[OF nonempty])
      with eh show ?thesis unfolding graph extend_descendant_def by blast
    qed
  qed
qed

lemma no_wire_collision:
  assumes unique: "wire_unique M"
  assumes fresh: "\<And>d p v. Publish_Msg d p v \<in> M \<Longrightarrow> publication_position p \<noteq> publication_position q"
  shows "wire_unique (M \<union> {Publish_Msg d q w | d. True})"
  unfolding wire_unique_def
proof (intro allI impI)
  fix d e p r v x
  let ?M = "M \<union> {Publish_Msg d q w | d. True}"
  assume p: "Publish_Msg d p v \<in> ?M" and r: "Publish_Msg e r x \<in> ?M" and position: "publication_position p = publication_position r"
  from p have p': "Publish_Msg d p v \<in> M \<or> p = q \<and> v = w" by auto
  from r have r': "Publish_Msg e r x \<in> M \<or> r = q \<and> x = w" by auto
  from p' r' position unique fresh[of d p v] fresh[of e r x]
  show "p = r \<and> v = x" unfolding wire_unique_def by auto
qed

section \<open>Simulation of each TLA+ action\<close>

text \<open>
  Each lemma shows that, from linked states, performing the action on the TLA+
  state gives a state that is linked to the same abstract state or to one that
  follows it by one transition.
\<close>

locale simulation =
  fixes initial_configuration :: config and s :: "'v tla_state" and a :: abstract_state
  assumes boot: "initial_configuration \<noteq> {}"
  assumes reach: "abstract_model.dynamic_reachable initial_configuration a"
  assumes link: "linked initial_configuration s a"
begin

lemmas node = linkedD(1)[OF link]
lemmas wire = linkedD(3)[OF link]
lemmas sent_response = linkedD(2)[OF link]

lemma simulate_set_initial_state:
  assumes "enabled s (Set_Initial_State n)"
  shows "linked
             initial_configuration
             (execute initial_configuration initial_value s (Set_Initial_State n))
             a"
proof -
  let ?x = "nodes_at s n"
  let ?x' = "?x\<lparr>
    last_accepted_configuration  := initial_configuration,
    last_committed_configuration := initial_configuration,
    last_accepted_value          := initial_value
  \<rparr>"
  from assms have cfg: "last_accepted_configuration ?x = {}" and votes: "publish_votes ?x = {}" and off: "\<not> election_won ?x"
    and master: "node_role ?x = Master_Eligible"
    by (simp_all add: Let_def)
  have empty: "publications_accepted a n = []" "last_committed_configuration ?x = {}"
    using node_linkD(5)[OF node[of n] cfg] by auto
  have "node_link initial_configuration a n ?x'"
  proof -
    have n: "node_link initial_configuration a n ?x" by (rule node)
    have "transient_link initial_configuration a n ?x'"
      using n off unfolding node_link_def transient_link_def by simp
    moreover have "persisted_link initial_configuration a n ?x'"
      using n boot cfg empty unfolding node_link_def persisted_link_def by (simp add: stale_config_def)
    ultimately show ?thesis unfolding node_link_def by blast
  qed
  from link_node_update[OF link grows_refl this _ master _ _ _] master votes
  show ?thesis by simp
qed

text \<open>
  A restart reloads the in-memory state, or empties it for a coordinating-only node, and keeps the
  state on disk, except that where the persisted term of a coordinating-only node is zero the node
  has no durable history and its state is replaced by an empty one. None of this changes the
  abstract state: the node's transient state is dropped, and with it any election it has won, but the
  abstract model never needed to record that, so a restart is a stutter step.
\<close>

lemma simulate_restart_node:
  "\<exists>b. (b = a \<or> abstract_model.transition initial_configuration a b)
       \<and> linked
             initial_configuration
             (execute initial_configuration initial_value s (Restart_Node n r))
             b"
proof -
  let ?x = "nodes_at s n"
  let ?b = a
  let ?d = "restarted_disk initial_value r ?x"
  let ?m = "restarted_memory initial_value r ?x"
  have grow: "grows a ?b" by (rule grows_refl)
  have nl: "node_link initial_configuration a n ?x" by (rule node)
  have p: "abstract_model.publications_ok initial_configuration a" and j: "abstract_model.messages_ok initial_configuration a" using abstract_model.dynamic_invariants[OF reach] by auto
  have disk: "node_link initial_configuration ?b n ?d"
  proof (cases "current_term ?x = 0 \<and> r = Coordinating_Only")
    case True
    have term0: "current_term_of a n = 0" using node_linkD(1)[OF nl] True by simp
    have empty: "publications_accepted a n = []"
    proof (rule ccontr)
      assume "publications_accepted a n \<noteq> []"
      then have "publications_accepted a n \<in> publications_sent a" using abstract_model.messagesD(1)[OF j, of n] by simp
      from publication_positive[OF p this] abstract_model.messagesD(2)[OF j, of n] term0
      show False by simp
    qed
    have committed: "last_committed_configuration_of a n = initial_configuration"
      using abstract_model.messagesD(3)[OF j, of n] empty by (auto simp: abstract_model.effective_config_def)
    have d: "?d = empty_node initial_value r ?x" using True unfolding restarted_disk_def by simp
    show ?thesis
      using nl True empty committed d
      unfolding node_link_defs empty_node_def reset_transient_def abstract_model.active_leader_def abstract_model.fresh_votes_def
      by (auto simp: normalized_def split: if_splits)
  next
    case False
    then have d: "?d = loaded_node r ?x"
      unfolding restarted_disk_def by (cases "current_term ?x = 0"; cases r) simp_all
    have p0: "persisted_link initial_configuration a n ?x" using nl unfolding node_link_def by blast
    have same: "persisted_link initial_configuration ?b n (loaded_node r ?x)
                = persisted_link initial_configuration a n ?x"
      by (simp add: persisted_link_def loaded_node_def reset_transient_def)
    have persisted: "persisted_link initial_configuration ?b n ?d" using p0 same d by simp
    have transient: "transient_link initial_configuration ?b n ?d"
      unfolding d by (cases r) (simp_all add: transient_link_def loaded_node_def reset_transient_def
          abstract_model.active_leader_def abstract_model.fresh_votes_def)
    show ?thesis using persisted transient unfolding node_link_def by simp
  qed
  have role_d: "node_role ?d = r"
    unfolding restarted_disk_def empty_node_def loaded_node_def by simp
  have role_m: "node_role ?m = r"
    unfolding restarted_memory_def restarted_disk_def empty_node_def loaded_node_def by simp
  have mem_link: "node_role ?d = Data_Only \<Longrightarrow> memory_link ?b ?d ?m"
  proof -
    assume "node_role ?d = Data_Only"
    with role_d have r: "r = Data_Only" by simp
    then have md: "?m = ?d" unfolding restarted_memory_def by simp
    have key: "normalized (last_accepted_position ?d) = position_of_tip_of (publications_accepted ?b n)"
      using node_linkD(4)[OF disk] by simp
    have "position_term (last_accepted_position ?d) = 0
          \<or> (\<exists>publication_history\<in>publications_sent ?b. position_of_tip_of publication_history = last_accepted_position ?d)"
    proof (cases "position_term (last_accepted_position ?d) = 0")
      case True
      then show ?thesis by simp
    next
      case False
      then have "normalized (last_accepted_position ?d) = last_accepted_position ?d"
        by (simp add: normalized_def)
      with key have "position_of_tip_of (publications_accepted a n) = last_accepted_position ?d" by simp
      moreover have "publications_accepted a n \<noteq> []"
        using False key by (auto simp: normalized_def split: if_splits)
      ultimately show ?thesis using abstract_model.messagesD(1)[OF j, of n] by auto
    qed
    moreover have "position_term (last_accepted_position ?d) \<le> current_term ?d"
    proof -
      have "position_term (last_accepted_position ?d) = term_of_tip_of (publications_accepted a n)"
        using arg_cong[where f = position_term, OF key] by simp
      then show ?thesis
        using abstract_model.messagesD(2)[OF j, of n] node_linkD(1)[OF disk] by auto
    qed
    ultimately show "memory_link ?b ?d ?m" using md unfolding memory_link_def by simp
  qed
  have frame: "i \<noteq> n \<Longrightarrow> node_frame a ?b i" for i
    unfolding node_frame_def abstract_model.active_leader_def by auto
  have anc: "ancestry_link ((put_node s n ?d)\<lparr>
    memory_at  := (memory_at s)(n := ?m),
    messages   := messages s,
    descendant := descendant s
  \<rparr>) ?b"
    by (rule ancestry_unchanged[OF link]) (simp_all add: put_node_def)
  have replies: "publish_votes ?d = {}"
    unfolding restarted_disk_def empty_node_def loaded_node_def reset_transient_def by simp
  have "linked initial_configuration ((put_node s n ?d)\<lparr>
    memory_at  := (memory_at s)(n := ?m),
    messages   := messages s,
    descendant := descendant s
  \<rparr>) ?b"
    by (rule link_update_memory[OF link grow disk frame _ mem_link _ _ _ _ linkedD(4)[OF link] anc])
       (use role_d role_m replies in \<open>auto simp: restarted_memory_def restarted_disk_def empty_node_def
         loaded_node_def reset_transient_def\<close>)
  then show ?thesis by (intro exI[of _ ?b]) (simp add: put_node_def)
qed

text \<open>
  Moving to a new term on a master-eligible node is the abstract \<open>start_join\<close> transition. On a
  node that is not master-eligible it only changes the node's in-memory state, which the abstract
  model does not track, and sends a vote that nobody counts.
\<close>

lemma simulate_handle_start_join:
  assumes enable: "enabled s (Handle_Start_Join n c t)"
  shows "\<exists>b. (b = a \<or> abstract_model.transition initial_configuration a b)
             \<and> linked
                   initial_configuration
                   (execute initial_configuration initial_value s (Handle_Start_Join n c t))
                   b"
proof (cases "node_role (nodes_at s n) = Master_Eligible")
  case True
  let ?b = "a\<lparr>
    current_term_of := (current_term_of a)(n := t),
    joins_sent      := insert (n,c,t,position_of_tip_of (publications_accepted a n)) (joins_sent a)
  \<rparr>"
  let ?x = "nodes_at s n"
  let ?y = "(reset_transient ?x)\<lparr>current_term := t, started_join_since_last_reboot := True\<rparr>"
  let ?msg = "Join_Msg n Master_Eligible c t (last_accepted_position ?x)"
  let ?M = "insert ?msg (messages s)"
  have master: "node_role ?x = Master_Eligible" using True .
  have master': "node_role ?y = Master_Eligible" using True by (simp add: reset_transient_def)
  have inc: "current_term_of a n < t"
    using enable node_linkD(1)[OF node[of n]] True by (simp add: memory_state_def)
  have step: "abstract_model.transition initial_configuration a ?b" by (rule abstract_model.transition.start_join[OF inc])
  have nl: "node_link initial_configuration ?b n ?y"
  proof -
    have n: "node_link initial_configuration a n ?x" by (rule node)
    have pos: "0 < t" using inc by simp
    have "persisted_link initial_configuration ?b n ?y"
      using n unfolding node_link_def persisted_link_def reset_transient_def by (auto split: if_splits)
    moreover have "transient_link initial_configuration ?b n ?y"
    proof -
      have inactive: "\<not> abstract_model.active_leader ?b n"
        using certificate_future[OF reach inc] unfolding abstract_model.active_leader_def by simp
      show ?thesis
        using inactive pos True
        unfolding transient_link_def reset_transient_def abstract_model.fresh_votes_def by simp
    qed
    ultimately show ?thesis unfolding node_link_def by blast
  qed
  have frame: "i \<noteq> n \<Longrightarrow> node_frame a ?b i" for i
    unfolding node_frame_def abstract_model.active_leader_def by auto
  have add: "wire_link ?b ?msg" using node_linkD(4)[OF node[of n]] by simp
  have news: "\<And>m. m \<in> ?M \<Longrightarrow> m \<notin> messages s \<Longrightarrow> wire_link ?b m"
    using add by auto
  have replies: "\<forall>p\<in>publish_votes ?y. Response_Msg p Master_Eligible n (last_published_position ?y) \<in> ?M"
    by (simp add: reset_transient_def)
  have unique: "wire_unique ?M"
    using wire_unique_control[OF linkedD(4)[OF link], of "{?msg}"] by simp
  have anc: "ancestry_link ((put_node s n ?y)\<lparr>messages := ?M, descendant := descendant s\<rparr>) ?b"
    by (rule ancestry_unchanged[OF link]) (simp_all add: put_node_def)
  from link_update[OF link transition_grows[OF step] nl frame master master' replies _ news unique anc]
  have "linked initial_configuration (execute
                                          initial_configuration
                                          initial_value
                                          s
                                          (Handle_Start_Join n c t)) ?b"
    using True by (auto simp: reset_transient_def put_node_def Let_def memory_state_def put_memory_state_def
        queue_term_def)
  with step show ?thesis by (intro exI[of _ ?b]) simp
next
  case False
  let ?x = "nodes_at s n"
  let ?m = "memory_at s n"
  let ?m' = "queue_term ((reset_transient ?m)\<lparr>
    current_term                   := t,
    started_join_since_last_reboot := True
  \<rparr>)"
  let ?msg = "Join_Msg n (node_role ?m) c t (last_accepted_position ?m)"
  let ?M = "insert ?msg (messages s)"
  have role: "node_role ?m = node_role ?x" by (rule linkedD(6)[OF link])
  have role': "node_role ?m' = node_role ?x"
    using role by (simp add: queue_term_def reset_transient_def)
  have inc: "current_term ?m < t" using enable False by (simp add: Let_def memory_state_def)
  have news: "\<And>msg. msg \<in> ?M \<Longrightarrow> msg \<notin> messages s \<Longrightarrow> wire_link a msg"
    using role False by auto
  have mem_link: "node_role ?x = Data_Only \<Longrightarrow> memory_link a ?x ?m'"
    using linkedD(7)[OF link, of n] inc
    by (auto simp: memory_link_def queue_term_def reset_transient_def)
  have unique: "wire_unique ?M"
    using wire_unique_control[OF linkedD(4)[OF link], of "{?msg}"] by simp
  have anc: "ancestry_link ((put_node s n ?x)\<lparr>
    memory_at  := (memory_at s)(n := ?m'),
    messages   := ?M,
    descendant := descendant s
  \<rparr>) a"
    by (rule ancestry_unchanged[OF link]) (simp_all add: put_node_def)
  have "linked
            initial_configuration
            ((put_node s n ?x)\<lparr>
              memory_at  := (memory_at s)(n := ?m'),
              messages   := ?M,
              descendant := descendant s
            \<rparr>)
            a"
    by (rule link_update_memory[OF link grows_refl node[of n] _ role' mem_link _ _ _ news unique anc])
       (use sent_response linkedD(8)[OF link, of n] in \<open>auto simp: queue_term_def reset_transient_def\<close>)
  then show ?thesis using False
    by (intro exI[of _ a]) (simp add: Let_def put_node_def put_memory_state_def put_memory_def memory_state_def)
qed

lemma simulate_handle_join:
  assumes enable: "enabled s (Handle_Join n nr c t r)"
  shows "\<exists>b. (b = a \<or> abstract_model.transition initial_configuration a b)
             \<and> linked
                   initial_configuration
                   (execute initial_configuration initial_value s (Handle_Join n nr c t r))
                   b"
proof -
  let ?x = "nodes_at s c"
  let ?Q = "if nr = Master_Eligible then insert n (join_votes ?x) else join_votes ?x"
  let ?won = "is_election_quorum ?x ?Q"
  have c: "node_link initial_configuration a c ?x" by (rule node)
  from enable have role: "node_role ?x = Master_Eligible" by (simp add: Let_def)
  from enable have sent: "Join_Msg n nr c t r \<in> messages s" and term_match: "t = current_term_of a c"
    and fresh: "r \<le> last_accepted_position ?x" and started_flag: "started_join_since_last_reboot ?x"
    and started: "0 < current_term_of a c"
    and acfg: "last_accepted_configuration ?x \<noteq> {}"
    using node_linkD(1)[OF c] node_linkD(2)[OF c role] by (auto simp: Let_def)
  have r: "normalized r \<le> position_of_tip_of (publications_accepted a c)"
    using normalized_mono[OF fresh] node_linkD(4)[OF c] by simp
  have votes: "abstract_model.fresh_votes a c (current_term_of a c) (publications_accepted a c) ?Q"
  proof (cases "nr = Master_Eligible")
    case True
    then have msg: "(n,c,current_term_of a c,normalized r) \<in> joins_sent a"
      using wire[OF sent] term_match by simp
    show ?thesis using True fresh_vote_insert[OF node_linkD(8)[OF c] msg r] by simp
  next
    case False
    then show ?thesis using node_linkD(8)[OF c] by simp
  qed
  have retained: "election_won ?x \<Longrightarrow> ?won"
  proof (cases "nr = Master_Eligible")
    case True
    then show "election_won ?x \<Longrightarrow> ?won"
      using is_election_quorum_insert[OF node_linkD(9)[OF c]] by simp
  next
    case False
    then show "election_won ?x \<Longrightarrow> ?won" using node_linkD(9)[OF c] by simp
  qed
  show ?thesis
  proof (cases "\<not> election_won ?x \<and> ?won")
    case False
    then have won: "?won = election_won ?x" using retained by blast
    let ?y = "?x\<lparr>join_votes := ?Q\<rparr>"
    have known: "election_won ?x \<Longrightarrow> known_tip initial_configuration a c ?y"
    proof (cases "nr = Master_Eligible")
      case True
      then show "election_won ?x \<Longrightarrow> known_tip initial_configuration a c ?y"
        using known_tip_insert_join[OF node_linkD(10)[OF c], of n] by simp
      next
      case False
      then show "election_won ?x \<Longrightarrow> known_tip initial_configuration a c ?y"
        using node_linkD(10)[OF c] unfolding known_tip_def by simp
    qed
    have nl: "node_link initial_configuration a c ?y"
      using c votes won known role
      unfolding node_link_defs is_election_quorum_def by (auto split: if_splits)
    have "linked initial_configuration (put_node s c ?y) a"
      by (rule link_node_update[OF link grows_refl nl _ role _ _ _]) (use role in \<open>simp_all add: sent_response\<close>)
    with False won show ?thesis by (intro exI[of _ a]) (simp add: Let_def)
  next
    case True
    then have off: "\<not> election_won ?x" and won: "?won" by auto
    let ?b = "a\<lparr>
      elections_won             := (elections_won a)((c,current_term_of a c) :=
          Some \<lparr>
            election_votes                   = ?Q,
            election_last_accepted_history   = publications_accepted a c,
            election_committed_configuration = last_committed_configuration_of a c
          \<rparr>)
    \<rparr>"
    let ?y = "?x\<lparr>
      join_votes             := ?Q,
      election_won           := True,
      last_published_version := position_version (last_accepted_position ?x)
    \<rparr>"
    have none: "elections_won a (c,current_term_of a c) = None"
      using node_linkD(15)[OF c role started_flag] off unfolding abstract_model.active_leader_def by auto
    have q: "quorum (last_committed_configuration_of a c) ?Q" "quorum (config_of_tip_of initial_configuration (publications_accepted a c)) ?Q"
    proof -
      have won': "quorum (last_committed_configuration ?x) ?Q" "quorum (last_accepted_configuration ?x) ?Q"
        using won unfolding is_election_quorum_def by simp_all
      have accepted: "last_accepted_configuration ?x = config_of_tip_of initial_configuration (publications_accepted a c)"
        by (rule node_linkD(6)[OF c acfg quorum_not_stale[OF won'(2)]])
      have committed: "last_committed_configuration_of a c =
          (if last_committed_configuration ?x = {} then initial_configuration else last_committed_configuration ?x)"
        by (rule node_linkD(7)[OF c quorum_not_stale[OF won'(1)]])
      show "quorum (last_committed_configuration_of a c) ?Q" "quorum (config_of_tip_of initial_configuration (publications_accepted a c)) ?Q"
        using won' committed accepted by (auto dest: quorum_nonempty)
    qed
    have step: "abstract_model.transition initial_configuration a ?b" by (rule abstract_model.transition.win_election[OF started none q votes])
    have base: "term_of_tip_of (publications_accepted a c) < current_term_of a c"
    proof -
      have j: "abstract_model.messages_ok initial_configuration a" and l: "abstract_model.leadership_ok initial_configuration a" using abstract_model.dynamic_invariants[OF reach] by auto
      show ?thesis by (rule abstract_model.new_election_base[OF j l none started q(2) votes])
    qed
    have empty: "abstract_model.published_by a c (current_term_of a c) = {}"
      using abstract_model.leadershipD(8)[OF abstract_model.dynamic_invariants[THEN conjunct2, THEN conjunct2, OF reach]] none
      unfolding abstract_model.published_by_def by fastforce
    have tip_b: "abstract_model.last_published_history_of ?b (c, current_term_of a c) = publications_accepted a c"
      using abstract_model.last_published_history_win_new[OF empty, of "\<lparr>
        election_votes                   = ?Q,
        election_last_accepted_history   = publications_accepted a c,
        election_committed_configuration = last_committed_configuration_of a c
      \<rparr>"] by simp
    have tips_other: "abstract_model.last_published_history_of ?b (i, current_term_of a i) = abstract_model.last_published_history_of a (i, current_term_of a i)" if "i \<noteq> c" for i
      using abstract_model.last_published_history_win_other[of "(i, current_term_of a i)" c "current_term_of a c" a] that by simp
    have active_b: "abstract_model.active_leader ?b c" unfolding abstract_model.active_leader_def by simp
    have j: "abstract_model.messages_ok initial_configuration a" using abstract_model.dynamic_invariants[OF reach] by auto
    have eff: "abstract_model.effective_config
                   initial_configuration
                   (publications_committed ?b)
                   (abstract_model.current_published_history ?b c)
                   (last_committed_configuration_of ?b c)"
      using abstract_model.messagesD(3)[OF j, of c] tip_b by simp
    have nl: "node_link initial_configuration ?b c ?y"
    proof -
      have pl: "persisted_link initial_configuration ?b c ?y"
        using c[unfolded node_link_def, THEN conjunct1] unfolding persisted_link_def by (auto split: if_splits)
      have tl: "transient_link initial_configuration ?b c ?y"
      proof -
        have kt: "known_tip initial_configuration ?b c ?y"
          using base tip_b node_linkD(1)[OF c] unfolding known_tip_def by simp
        have iq: "is_election_quorum ?y (join_votes ?y)"
          using won unfolding is_election_quorum_def by simp
        have fv: "abstract_model.fresh_votes ?b c
                                                    (current_term_of ?b c)
                                                    (publications_accepted ?b c)
                                                    (join_votes ?y)"
          using votes unfolding abstract_model.fresh_votes_def by simp
        show ?thesis
          using started started_flag active_b eff kt iq fv role
          unfolding transient_link_def by simp
      qed
      show ?thesis using pl tl unfolding node_link_def by blast
    qed
    have frame: "i \<noteq> c \<Longrightarrow> node_frame a ?b i" for i
      unfolding node_frame_def abstract_model.active_leader_def using tips_other[of i] by auto
    have replies: "publish_votes ?x = {}"
    proof (rule ccontr)
      assume "publish_votes ?x \<noteq> {}"
      then obtain p where "p \<in> publish_votes ?x" by blast
      from wire[OF sent_response[OF this]] obtain h where
        h: "h \<in> publications_sent a" "owner_of_tip_of h = c" "position_of_tip_of h = last_published_position ?x" by auto
      have l: "abstract_model.leadership_ok initial_configuration a" using abstract_model.dynamic_invariants[OF reach] by auto
      from abstract_model.leadershipD(8)[OF l h(1)] h(2,3) none node_linkD(1)[OF c]
      show False by auto
    qed
    have "linked initial_configuration (put_node s c ?y) ?b"
      by (rule link_node_update[OF link transition_grows[OF step] nl frame role _ _ _])
         (use role in \<open>simp_all add: replies\<close>)
    with step True show ?thesis by (intro exI[of _ ?b]) (simp add: Let_def)
  qed
qed

lemma current_publication_prefix:
  assumes active: "abstract_model.active_leader a n"
  assumes pub: "h \<in> publications_sent a"
  assumes t: "term_of_tip_of h = current_term_of a n"
  shows "owner_of_tip_of h = n" "prefix h (abstract_model.current_published_history a n)"
proof -
  have l: "abstract_model.leadership_ok initial_configuration a" using abstract_model.dynamic_invariants[OF reach] by auto
  obtain e f where votes: "elections_won a (owner_of_tip_of h,current_term_of a n) = Some e" "elections_won a (n,current_term_of a n) = Some f"
    using abstract_model.leadershipD(8)[OF l pub] active t unfolding abstract_model.active_leader_def by auto
  show "owner_of_tip_of h = n" by (rule abstract_model.dynamic_one_election_candidate_per_term[OF reach votes])
  with abstract_model.leadershipD(9)[OF l pub] t show "prefix h (abstract_model.current_published_history a n)" by simp
qed

lemma older_tip_impossible:
  assumes active: "abstract_model.active_leader a n"
  assumes pub: "h \<in> publications_sent a"
  assumes t: "term_of_tip_of h = current_term_of a n"
  assumes old: "term_of_tip_of (abstract_model.current_published_history a n) < current_term_of a n"
  assumes base: "abstract_model.current_published_history a n = publications_accepted a n"
  shows False
proof -
  have j: "abstract_model.messages_ok initial_configuration a" and p: "abstract_model.publications_ok initial_configuration a" using abstract_model.dynamic_invariants[OF reach] by auto
  have mem: "abstract_model.current_published_history a n \<in> insert [] (publications_sent a)" using base abstract_model.messagesD(1)[OF j, of n] by simp
  have "position_of_tip_of h \<le> position_of_tip_of (abstract_model.current_published_history a n)"
    using abstract_model.prefix_of_sent[OF p mem current_publication_prefix(2)[OF active pub t]] by auto
  from position_term_mono[OF this] old t show False by simp
qed

lemma simulate_handle_client_value:
  assumes enabled: "enabled s (Handle_Client_Value n t v payload_value D)"
  shows "\<exists>b. abstract_model.transition initial_configuration a b
             \<and> linked
                   initial_configuration
                   (execute
                        initial_configuration
                        initial_value
                        s
                        (Handle_Client_Value n t v payload_value D))
                   b"
proof -
  let ?x = "nodes_at s n"
  let ?hist = "publications_accepted a n"
  let ?p = "\<lparr>
    publication_position        = \<lparr>position_term = t, position_version = v\<rparr>,
    publication_owner           = n,
    publication_config          = D,
    publication_previous_config = last_committed_configuration ?x
  \<rparr>"
  let ?h = "?hist @ [?p]"
  let ?b = "a\<lparr>
    publications_sent := insert ?h (publications_sent a)
  \<rparr>"
  let ?x' = "?x\<lparr>
    last_published_version       := v,
    last_published_configuration := D,
    publish_votes                := {}
  \<rparr>"
  let ?M = "messages s \<union> {Publish_Msg d ?p payload_value | d. True}"
  let ?G = "extend_descendant
                (descendant s)
                (last_accepted_position ?x)
                \<lparr>position_term = t, position_version = v\<rparr>"
  have nl: "node_link initial_configuration a n ?x" by (rule node)
  from enabled have won: "election_won ?x" and ver: "last_published_version ?x = position_version (last_accepted_position ?x)"
    and t: "t = current_term_of a n" and inc: "last_published_version ?x < v" and proposed: "quorum D (join_votes ?x)"
    and guard: "D \<noteq> last_accepted_configuration ?x \<Longrightarrow> last_committed_configuration ?x = last_accepted_configuration ?x"
    using node_linkD(1)[OF nl] by (simp_all add: Let_def)
  have master: "node_role ?x = Master_Eligible" by (rule node_linkD(11)[OF nl won])
  have active: "abstract_model.active_leader a n" using won node_linkD(3)[OF nl master] by simp
  have tip: "abstract_model.current_published_history a n = ?hist" by (rule linked_position_equal[OF nl won ver])
  have E: "quorum (last_committed_configuration ?x) (join_votes ?x)" and A: "quorum (last_accepted_configuration ?x) (join_votes ?x)"
    using node_linkD(9)[OF nl won] unfolding is_election_quorum_def by auto
  have ac: "last_accepted_configuration ?x = config_of_tip_of initial_configuration ?hist"
    by (rule node_linkD(6)[OF nl quorum_nonempty[OF A] node_link_won_configurations(1)[OF nl won]])
  have cc: "last_committed_configuration_of a n = last_committed_configuration ?x"
    using node_linkD(7)[OF nl node_link_won_configurations(2)[OF nl won]] quorum_nonempty[OF E] by simp
  have inc': "position_version (position_of_tip_of ?hist) < v" by (rule linked_boot_versions[OF nl]) (simp add: ver[symmetric] inc)
  have step: "abstract_model.transition initial_configuration a ?b"
    by (rule abstract_model.transition.publish[OF active tip inc' _ proposed node_linkD(8)[OF nl]])
       (use guard ac cc t in \<open>auto\<close>)
  have after: "abstract_model.dynamic_reachable initial_configuration ?b" by (rule abstract_model.dynamic_reachable.advance[OF reach step])
  have p: "abstract_model.publications_ok initial_configuration a" and j: "abstract_model.messages_ok initial_configuration a" and l: "abstract_model.leadership_ok initial_configuration a"
    using abstract_model.dynamic_invariants[OF reach] by auto
  have hk: "position_of_tip_of ?h = \<lparr>position_term = t, position_version = v\<rparr>" and own: "owner_of_tip_of ?h = n" by (simp_all)
  have new: "?h \<notin> publications_sent a"
  proof
    assume "?h \<in> publications_sent a"
    from abstract_model.leadershipD(9)[OF l this] hk own t tip
    show False by simp
  qed
  have no_collision: "publication_position q \<noteq> publication_position ?p"
    if prior: "Publish_Msg d q w \<in> messages s" for d q w
  proof
    assume positions: "publication_position q = publication_position ?p"
    obtain b where old_pub: "b @ [q] \<in> publications_sent a" using wire[OF prior] by auto
    have "b @ [q] = ?h"
      by (rule abstract_model.dynamic_unique_publication[OF after]) (simp_all add: old_pub positions)
    with old_pub new show False by simp
  qed
  have lb: "abstract_model.leadership_ok initial_configuration ?b" using abstract_model.dynamic_invariants[OF after] by auto
  have tip': "abstract_model.last_published_history_of a (n, t) = ?hist" using tip t by simp
  have tip_b0: "abstract_model.last_published_history_of ?b (n, t) = ?h"
    by (rule abstract_model.last_published_history_publish_new[where candidate=n and vote_term=t and parent="?hist" and publication="?p", OF l lb _ _ refl tip'])
       simp_all
  have tip_b: "abstract_model.last_published_history_of ?b (n, current_term_of a n) = ?h" using tip_b0 t by simp
  note tip_bn = tip_b[simplified t]
  have tips_other: "abstract_model.last_published_history_of ?b (i, current_term_of a i) = abstract_model.last_published_history_of a (i, current_term_of a i)" if "i \<noteq> n" for i
    using abstract_model.last_published_history_publish_other[of ?h n t "(i, current_term_of a i)" a] that by simp
  have new_tip: "known_tip initial_configuration ?b n ?x'"
    using won t node_linkD(1)[OF nl] E proposed inc ver
    unfolding known_tip_def by (simp add: tip_b tip_bn)
  have new_link: "node_link initial_configuration ?b n ?x'"
  proof -
    have started: "started_join_since_last_reboot ?x" by (rule node_linkD(16)[OF nl master won])
    have pos: "0 < current_term_of a n" by (rule node_linkD(2)[OF nl master started])
    have active_b: "abstract_model.active_leader ?b n" using active unfolding abstract_model.active_leader_def by simp
    have eff: "abstract_model.effective_config
                   initial_configuration
                   (publications_committed ?b)
                   (abstract_model.current_published_history ?b n)
                   (last_committed_configuration_of ?b n)"
      using tip_bn t cc by (simp add: abstract_model.effective_config_def)
    have iq: "is_election_quorum ?x' (join_votes ?x')"
      using node_linkD(9)[OF nl won] unfolding is_election_quorum_def by simp
    have fv: "abstract_model.fresh_votes ?b n
                                                (current_term_of ?b n)
                                                (publications_accepted ?b n)
                                                (join_votes ?x')"
      using node_linkD(8)[OF nl] unfolding abstract_model.fresh_votes_def by simp
    have pl: "persisted_link initial_configuration ?b n ?x'"
      using nl[unfolded node_link_def, THEN conjunct1] unfolding persisted_link_def by (auto split: if_splits)
    have tl: "transient_link initial_configuration ?b n ?x'"
      using started pos active_b eff iq fv new_tip won master
      unfolding transient_link_def by simp
    show ?thesis using pl tl unfolding node_link_def by blast
  qed
  have frame: "i \<noteq> n \<Longrightarrow> node_frame a ?b i" for i
    unfolding node_frame_def abstract_model.active_leader_def using tips_other[of i] by auto
  have wires: "wire_link ?b m" if "m \<in> ?M" "m \<notin> messages s" for m
    using that quorum_nonempty[OF E] quorum_nonempty[OF proposed]
    by auto
  have graph: "ancestry_link ((put_node s n ?x')\<lparr>messages := ?M, descendant := ?G\<rparr>) ?b"
    by (rule ancestry_extend[OF linkedD(5)[OF link] p abstract_model.messagesD(1)[OF j] durable_position[OF nl _ reach] refl new])
       (simp_all)
  have master': "node_role ?x' = Master_Eligible" using master by simp
  from link_update[OF link transition_grows[OF step] new_link frame master master' _ _ wires
      no_wire_collision[OF linkedD(4)[OF link] no_collision] graph] step
  show ?thesis by (intro exI[of _ ?b]) (simp add: Let_def)
qed

lemma simulate_handle_publish_request:
  assumes enabled: "enabled s (Handle_Publish_Request n p payload_value)"
  shows "\<exists>b. (b = a \<or> abstract_model.transition initial_configuration a b)
             \<and> linked
                   initial_configuration
                   (execute
                        initial_configuration
                        initial_value
                        s
                        (Handle_Publish_Request n p payload_value))
                   b"
proof (cases "node_role (nodes_at s n) = Master_Eligible")
  case True
  let ?x = "nodes_at s n"
  have master: "node_role ?x = Master_Eligible" using True .
  have nl: "node_link initial_configuration a n ?x" by (rule node)
  from enabled have sent: "Publish_Msg n p payload_value \<in> messages s" and term_match: "position_term (publication_position p) = current_term_of a n"
    and ver: "position_term (publication_position p) = position_term (last_accepted_position ?x) \<Longrightarrow> position_version (last_accepted_position ?x) < position_version (publication_position p)"
    using node_linkD(1)[OF nl] True by (simp_all add: Let_def memory_state_def)
  obtain base where pub: "base @ [p] \<in> publications_sent a" and cfg: "publication_config p \<noteq> {}" "publication_previous_config p \<noteq> {}"
    using wire[OF sent] by auto
  let ?h = "base @ [p]"
  let ?b = "a\<lparr>
    publications_accepted           := (publications_accepted a)(n := ?h),
    last_committed_configuration_of := (last_committed_configuration_of a)(n := previous_config_of_tip_of initial_configuration ?h),
    publish_responses_sent          := insert (n,?h) (publish_responses_sent a)
  \<rparr>"
  let ?x' = "?x\<lparr>
    last_accepted_position       := publication_position p,
    last_accepted_value          := payload_value,
    last_accepted_configuration  := publication_config p,
    last_committed_configuration := publication_previous_config p
  \<rparr>"
  let ?msg = "Response_Msg n Master_Eligible (publication_owner p) (publication_position p)"
  let ?M = "insert ?msg (messages s)"
  have master': "node_role ?x' = Master_Eligible" using master by simp
  have j: "abstract_model.messages_ok initial_configuration a" and p_ok: "abstract_model.publications_ok initial_configuration a" using abstract_model.dynamic_invariants[OF reach] by auto
  have pos: "0 < position_term (publication_position p)" using publication_positive[OF p_ok pub] by simp
  have bound: "position_term (last_accepted_position ?x) \<le> position_term (publication_position p)"
    using abstract_model.messagesD(2)[OF j, of n] node_linkD(4)[OF nl] term_match
    by (metis normalized_term)
  obtain u v where position: "last_accepted_position ?x = \<lparr>position_term = u, position_version = v\<rparr>" by (cases "last_accepted_position ?x") auto
  have increase: "v < position_version (publication_position p)" if "u = position_term (publication_position p)"
    using that position ver by auto
  have "normalized (last_accepted_position ?x) < publication_position p"
  proof (cases "u = 0")
    case True
    then show ?thesis using position pos by (simp add: normalized_def position_less_iff)
  next
    case False
    from bound position have "u \<le> position_term (publication_position p)" by simp
    then have "u < position_term (publication_position p)
               \<or> u = position_term (publication_position p)" by (simp add: le_less)
    then show ?thesis using position False increase by (auto simp: normalized_def position_le_iff position_less_iff)
  qed
  then have inc: "position_of_tip_of (publications_accepted a n) < position_of_tip_of ?h"
    using node_linkD(4)[OF nl] by simp
  have step: "abstract_model.transition initial_configuration a ?b" by (rule abstract_model.transition.receive[OF pub _ inc]) (simp add: term_match)
  have grow: "grows a ?b" by (rule transition_grows[OF step])
  have nterm: "term_of_tip_of ?h = current_term_of a n" using term_match by simp
  have voted: "abstract_model.fresh_votes ?b n
                                                 (current_term_of ?b n)
                                                 (publications_accepted ?b n)
                                                 (join_votes ?x')"
    using fresh_frame[OF grow node_linkD(8)[OF nl] less_imp_le[OF inc], of "join_votes ?x"] by simp
  have active: "abstract_model.active_leader a n" if "election_won ?x" using that node_linkD(3)[OF nl master] by simp
  have at_tip: "abstract_model.current_published_history a n = ?h" if won: "election_won ?x"
  proof -
    have "term_of_tip_of (abstract_model.current_published_history a n) = current_term_of a n"
      using node_linkD(10)[OF nl won] node_linkD(1)[OF nl] older_tip_impossible[OF active[OF won] pub nterm]
      unfolding known_tip_def by auto
    then show ?thesis using abstract_model.receive_at_current_published_history[OF reach abstract_model.reachable_current_published_history_ok[OF reach]
        active[OF won] _ pub nterm inc] by simp
  qed
  have leader: "is_election_quorum ?x' (join_votes ?x') \<and> known_tip initial_configuration ?b n ?x'" if won: "election_won ?x"
  proof -
    have old_tip: "known_tip initial_configuration a n ?x" by (rule node_linkD(10)[OF nl won])
    with at_tip[OF won] term_match node_linkD(1)[OF nl] pub
    show ?thesis unfolding known_tip_def is_election_quorum_def by auto
  qed
  have new_link: "node_link initial_configuration ?b n ?x'"
  proof -
    have pl: "persisted_link initial_configuration ?b n ?x'"
      using nl pos cfg unfolding node_link_def persisted_link_def by (auto simp: normalized_def split: if_splits)
    have act_b: "abstract_model.active_leader ?b n = abstract_model.active_leader a n"
      unfolding abstract_model.active_leader_def by simp
    have started_eq: "started_join_since_last_reboot ?x \<Longrightarrow> election_won ?x = abstract_model.active_leader a n"
      by (rule node_linkD(15)[OF nl master])
    have eff: "election_won ?x \<Longrightarrow> abstract_model.effective_config
                                     initial_configuration
                                     (publications_committed ?b)
                                     (abstract_model.current_published_history ?b n)
                                     (last_committed_configuration_of ?b n)"
    proof -
      assume won: "election_won ?x"
      have "abstract_model.current_published_history ?b n = ?h"
        using at_tip[OF won] by (simp add: abstract_model.last_published_history_of_update_publications_accepted)
      then show ?thesis by (simp add: abstract_model.effective_config_def)
    qed
    have tl: "transient_link initial_configuration ?b n ?x'"
      using node_linkD(2)[OF nl master] node_linkD(16)[OF nl master] started_eq act_b eff voted leader master
      unfolding transient_link_def by simp
    show ?thesis using pl tl unfolding node_link_def by blast
  qed
  have frame: "i \<noteq> n \<Longrightarrow> node_frame a ?b i" for i
    unfolding node_frame_def abstract_model.active_leader_def by auto
  have fresh: "wire_link ?b ?msg" using pub by (auto intro!: bexI[of _ ?h])
  have news: "\<And>m. m \<in> ?M \<Longrightarrow> m \<notin> messages s \<Longrightarrow> wire_link ?b m"
    using fresh by auto
  have replies: "\<forall>q\<in>publish_votes ?x'. Response_Msg
                                           q
                                           Master_Eligible
                                           n
                                           (last_published_position ?x') \<in> ?M"
    using sent_response by auto
  have unique: "wire_unique ?M"
    using wire_unique_control[OF linkedD(4)[OF link], of "{?msg}"] by simp
  have graph: "ancestry_link ((put_node s n ?x')\<lparr>messages := ?M, descendant := descendant s\<rparr>) ?b"
    by (rule ancestry_unchanged[OF link]) (simp_all add: put_node_def)
  have updated: "linked initial_configuration ((put_node s n ?x')\<lparr>
    messages   := ?M,
    descendant := descendant s
  \<rparr>) ?b"
    by (rule link_update[OF link grow new_link frame master master' replies subset_insertI news unique graph])
  from step updated show ?thesis using True
    by (intro exI[of _ ?b]) (simp add: put_node_def Let_def memory_state_def put_memory_state_def queue_state_def)
next
  case False
  let ?x = "nodes_at s n"
  let ?m = "memory_at s n"
  let ?m' = "queue_state (?m\<lparr>
    last_accepted_position       := publication_position p,
    last_accepted_value          := payload_value,
    last_accepted_configuration  := publication_config p,
    last_committed_configuration := publication_previous_config p
  \<rparr>)"
  let ?msg = "Response_Msg n (node_role ?m) (publication_owner p) (publication_position p)"
  let ?M = "insert ?msg (messages s)"
  have role: "node_role ?m = node_role ?x" by (rule linkedD(6)[OF link])
  have role': "node_role ?m' = node_role ?x" using role by (simp add: queue_state_def)
  from enabled False have sent: "Publish_Msg n p payload_value \<in> messages s"
    and term_eq: "position_term (publication_position p) = current_term ?m"
    and ver: "position_term (publication_position p) = position_term (last_accepted_position ?m) \<Longrightarrow>
      position_version (last_accepted_position ?m) < position_version (publication_position p)"
    by (simp_all add: Let_def memory_state_def)
  obtain base where pub: "base @ [p] \<in> publications_sent a" using wire[OF sent] by auto
  have news: "\<And>msg. msg \<in> ?M \<Longrightarrow> msg \<notin> messages s \<Longrightarrow> wire_link a msg"
    using role False by auto
  have mem_link: "node_role ?x = Data_Only \<Longrightarrow> memory_link a ?x ?m'"
  proof -
    assume data: "node_role ?x = Data_Only"
    from linkedD(7)[OF link data]
    have known: "position_term (last_accepted_position ?m) = 0
                 \<or> (\<exists>publication_history\<in>publications_sent a. position_of_tip_of publication_history = last_accepted_position ?m)"
      and ge: "normalized (last_accepted_position ?x) \<le> normalized (last_accepted_position ?m)"
      and le: "position_term (last_accepted_position ?m) \<le> current_term ?m"
      unfolding memory_link_def by auto
    have p_ok: "abstract_model.publications_ok initial_configuration a" using abstract_model.dynamic_invariants[OF reach] by auto
    have pos: "0 < position_term (publication_position p)" using publication_positive[OF p_ok pub] by simp
    have new_greater: "normalized (last_accepted_position ?m) \<le> publication_position p"
    proof (cases "position_term (last_accepted_position ?m) = 0")
      case True
      then show ?thesis using pos by (simp add: normalized_def position_le_iff)
    next
      case False
      then have "normalized (last_accepted_position ?m) = last_accepted_position ?m" by (simp add: normalized_def)
      moreover have "last_accepted_position ?m \<le> publication_position p"
        using le term_eq ver by (cases "last_accepted_position ?m") (auto simp: position_le_iff)
      ultimately show ?thesis by simp
    qed
    have wit: "\<exists>publication_history\<in>publications_sent a. position_of_tip_of publication_history = publication_position p"
      using pub by (intro bexI[of _ "base @ [p]"]) simp_all
    then show "memory_link a ?x ?m'"
      using ge new_greater le term_eq pos
      unfolding memory_link_def queue_state_def by (auto simp: normalized_def split: if_splits)
  qed
  have unique: "wire_unique ?M"
    using wire_unique_control[OF linkedD(4)[OF link], of "{?msg}"] by simp
  have anc: "ancestry_link ((put_node s n ?x)\<lparr>
    memory_at  := (memory_at s)(n := ?m'),
    messages   := ?M,
    descendant := descendant s
  \<rparr>) a"
    by (rule ancestry_unchanged[OF link]) (simp_all add: put_node_def)
  have "linked
            initial_configuration
            ((put_node s n ?x)\<lparr>
              memory_at  := (memory_at s)(n := ?m'),
              messages   := ?M,
              descendant := descendant s
            \<rparr>)
            a"
    by (rule link_update_memory[OF link grows_refl node[of n] _ role' mem_link _ _ _ news unique anc])
       (use sent_response linkedD(8)[OF link, of n] in \<open>auto simp: queue_state_def\<close>)
  then show ?thesis using False
    by (intro exI[of _ a]) (simp add: Let_def put_node_def put_memory_state_def put_memory_def memory_state_def)
qed

lemma quorum_votes_nonempty:
  assumes "quorum D Q"
  shows "Q \<noteq> {}"
  using assms unfolding quorum_def majority_def by auto

lemma simulate_handle_publish_response:
  assumes enabled: "enabled s (Handle_Publish_Response n nr c k)"
  shows "\<exists>b. (b = a \<or> abstract_model.transition initial_configuration a b)
             \<and> linked
                   initial_configuration
                   (execute initial_configuration initial_value s (Handle_Publish_Response n nr c k))
                   b"
proof -
  let ?x = "nodes_at s c"
  let ?h = "abstract_model.current_published_history a c"
  let ?Q = "if nr = Master_Eligible then insert n (publish_votes ?x) else publish_votes ?x"
  let ?y = "?x\<lparr>publish_votes := ?Q\<rparr>"
  have nl: "node_link initial_configuration a c ?x" by (rule node)
  from enabled have sent: "Response_Msg n nr c k \<in> messages s"
    and won: "election_won ?x" and k: "k = last_published_position ?x" by (auto simp: Let_def)
  have master: "node_role ?x = Master_Eligible" by (rule node_linkD(11)[OF nl won])
  have master': "node_role ?y = Master_Eligible" using master by simp
  have active: "abstract_model.active_leader a c" using won node_linkD(3)[OF nl master] by simp
  have term_match: "position_term k = current_term_of a c" using k node_linkD(1)[OF nl] by simp
  have replies: "\<forall>p\<in>?Q. Response_Msg p Master_Eligible c k \<in> messages s"
    using sent k sent_response[of _ c] by (cases "nr = Master_Eligible") auto
  have local_replies: "\<forall>p\<in>publish_votes ?y. Response_Msg
                                                p
                                                Master_Eligible
                                                c
                                                (last_published_position ?y) \<in> messages s"
    using replies k by simp
  show ?thesis
  proof (cases "is_publish_quorum ?x ?Q")
    case False
    have "node_link initial_configuration a c ?y" using nl master by simp
    from link_node_update[OF link grows_refl this _ master master' local_replies] False
    show ?thesis by (intro exI[of _ a]) (simp add: Let_def put_node_def)
  next
    case True
    have "?Q \<noteq> {}" using True quorum_votes_nonempty unfolding is_publish_quorum_def by blast
    then obtain p0 where "p0 \<in> ?Q" by blast
    from wire[OF replies[rule_format, OF this]]
    obtain h where mem: "h \<in> publications_sent a" and tip_position: "position_of_tip_of h = k" by auto
    have ht: "term_of_tip_of h = current_term_of a c" by (simp add: tip_position term_match)
    have tip: "?h \<in> publications_sent a" "position_of_tip_of ?h = k" "owner_of_tip_of ?h = c"
      "last_published_configuration ?x = config_of_tip_of initial_configuration ?h"
      using node_linkD(10)[OF nl won] k node_linkD(1)[OF nl] older_tip_impossible[OF active mem ht]
      unfolding known_tip_def by auto
    have cur: "term_of_tip_of ?h = current_term_of a c" using tip(2) term_match by simp
    have acks: "\<forall>p\<in>?Q. (p,?h) \<in> publish_responses_sent a"
    proof (intro ballI)
      fix p
      assume "p \<in> ?Q"
      from wire[OF replies[rule_format, OF this]]
      obtain u where u: "u \<in> publications_sent a" "(p,u) \<in> publish_responses_sent a" "position_of_tip_of u = k" by auto
      have "u = ?h" by (rule abstract_model.dynamic_unique_publication[OF reach u(1) tip(1)]) (simp add: u(3) tip(2))
      with u(2) show "(p,?h) \<in> publish_responses_sent a" by simp
    qed
    let ?b = "a\<lparr>publications_committed := insert ?h (publications_committed a)\<rparr>"
    let ?M = "messages s \<union> {Commit_Msg c d k | d. True}"
    have joint: "abstract_model.acknowledged_by_joint_quorum initial_configuration a ?h"
    proof (cases "?h \<in> publications_committed a")
      case True
      have "abstract_model.publications_ok initial_configuration a" using abstract_model.dynamic_invariants[OF reach] by auto
      from abstract_model.publicationsD(6)[OF this True]
      show ?thesis .
    next
      case False
      have "last_committed_configuration_of a c = last_committed_configuration ?x"
        using node_linkD(7)[OF nl node_link_won_configurations(2)[OF nl won]] True
        unfolding is_publish_quorum_def by (auto dest: quorum_nonempty)
      with True tip(4) acks have "\<exists>Q. quorum (last_committed_configuration_of a c) Q
                                      \<and> quorum (config_of_tip_of initial_configuration ?h) Q
                                      \<and> (\<forall>p\<in>Q. (p,?h) \<in> publish_responses_sent a)"
        unfolding is_publish_quorum_def by (intro exI[of _ ?Q]) auto
      with abstract_model.first_commit_quorums_agree[OF reach node_linkD(14)[OF nl master won] False]
      show ?thesis by simp
    qed
    have step: "abstract_model.transition initial_configuration a ?b" by (rule abstract_model.transition.commit[OF active refl tip(1) cur tip(3) joint])
    have nl': "node_link initial_configuration ?b c ?y"
      using node_link_quorum_commits[OF nl subset_insertI] master by simp
    have frame: "i \<noteq> c \<Longrightarrow> node_frame a ?b i" for i
      unfolding node_frame_def abstract_model.active_leader_def by simp
    have new: "wire_link ?b m" if "m \<in> ?M" "m \<notin> messages s" for m
      using that tip by (auto intro!: bexI[of _ ?h])
    have unique: "wire_unique ?M" by (rule wire_unique_control[OF linkedD(4)[OF link]]) auto
    have graph: "ancestry_link ((put_node s c ?y)\<lparr>messages := ?M, descendant := descendant s\<rparr>) ?b"
      by (rule ancestry_unchanged[OF link]) (simp_all add: put_node_def)
    have "linked initial_configuration ((put_node s c ?y)\<lparr>
      messages   := ?M,
      descendant := descendant s
    \<rparr>) ?b"
      by (rule link_update[OF link transition_grows[OF step] nl' frame master master' _ _ new unique graph])
         (use local_replies in auto)
    with step True show ?thesis by (intro exI[of _ ?b]) (simp add: Let_def put_node_def)
  qed
qed

lemma simulate_handle_commit:
  assumes enabled: "enabled s (Handle_Commit c n k)"
  shows "\<exists>b. (b = a \<or> abstract_model.transition initial_configuration a b)
             \<and> linked
                   initial_configuration
                   (execute initial_configuration initial_value s (Handle_Commit c n k))
                   b"
proof (cases "node_role (nodes_at s n) = Master_Eligible")
  case True
  let ?x = "nodes_at s n"
  let ?h = "publications_accepted a n"
  let ?b = "a\<lparr>last_committed_configuration_of := (last_committed_configuration_of a)(n := config_of_tip_of initial_configuration ?h)\<rparr>"
  let ?y = "?x\<lparr>last_committed_configuration := last_accepted_configuration ?x\<rparr>"
  have master: "node_role ?x = Master_Eligible" using True .
  have master': "node_role ?y = Master_Eligible" using master by simp
  have nl: "node_link initial_configuration a n ?x" by (rule node)
  from enabled have sent: "Commit_Msg c n k \<in> messages s" and t: "position_term k = current_term_of a n"
    and k: "k = last_accepted_position ?x" and guard: "election_won ?x \<Longrightarrow> position_version k = last_published_version ?x"
    using node_linkD(1)[OF nl] True by (auto simp: Let_def memory_state_def)
  have run: "execute initial_configuration initial_value s (Handle_Commit c n k) = put_node s n ?y"
    using True by (simp add: Let_def memory_state_def put_memory_state_def queue_state_def)
  show ?thesis
  proof (cases "last_accepted_configuration ?x \<noteq> stale_config")
    case True
    then have real: "last_accepted_configuration ?x \<noteq> stale_config" .
    obtain h where committed: "h \<in> publications_committed a" and hk: "position_of_tip_of h = k"
      using wire[OF sent] by auto
    have p: "abstract_model.publications_ok initial_configuration a" and j: "abstract_model.messages_ok initial_configuration a" using abstract_model.dynamic_invariants[OF reach] by auto
    have pub: "h \<in> publications_sent a" by (rule abstract_model.publicationsD(5)[OF p committed])
    have pos: "0 < position_term k" using publication_positive[OF p pub] hk by simp
    have match: "position_of_tip_of ?h = k"
      using node_linkD(4)[OF nl] k pos unfolding normalized_def by simp
    have mem: "?h \<in> publications_sent a" using abstract_model.messagesD(1)[OF j, of n] match pos by auto
    have same: "?h = h" by (rule abstract_model.dynamic_unique_publication[OF reach mem pub]) (simp add: hk match)
    have ack: "?h \<in> publications_committed a" using same committed by simp
    have cur: "term_of_tip_of ?h = current_term_of a n" using match t by simp
    have own: "election_won ?x \<Longrightarrow> ?h = abstract_model.current_published_history a n"
      using guard k linked_position_equal[OF nl] by auto
    have step: "abstract_model.transition initial_configuration a ?b" by (rule abstract_model.transition.apply_commit[OF ack cur])
    have nonempty: "last_accepted_configuration ?x \<noteq> {}"
      using node_linkD(5)[OF nl] mem abstract_model.publicationsD(2)[OF p] by auto
    have cfg: "last_accepted_configuration ?x = config_of_tip_of initial_configuration ?h" by (rule node_linkD(6)[OF nl nonempty real])
    have known: "election_won ?x \<Longrightarrow> known_tip initial_configuration ?b n ?y"
      using node_linkD(10)[OF nl] unfolding known_tip_def by simp
    have nl': "node_link initial_configuration ?b n ?y"
    proof -
      have pl: "persisted_link initial_configuration ?b n ?y"
        using nl[unfolded node_link_def, THEN conjunct1] nonempty cfg real
        unfolding persisted_link_def by (auto split: if_splits)
      have act_b: "abstract_model.active_leader ?b n = abstract_model.active_leader a n"
        unfolding abstract_model.active_leader_def by simp
      have cp: "abstract_model.current_published_history ?b n = abstract_model.current_published_history a n" by simp
      have eff: "election_won ?x \<Longrightarrow> abstract_model.effective_config
                                       initial_configuration
                                       (publications_committed ?b)
                                       (abstract_model.current_published_history ?b n)
                                       (last_committed_configuration_of ?b n)"
        using own ack by (simp add: abstract_model.effective_config_def)
      have fv: "abstract_model.fresh_votes ?b n
                                                  (current_term_of ?b n)
                                                  (publications_accepted ?b n)
                                                  (join_votes ?y)"
        using node_linkD(8)[OF nl] unfolding abstract_model.fresh_votes_def by simp
      have iq: "election_won ?x \<Longrightarrow> is_election_quorum ?y (join_votes ?y)"
        using node_linkD(9)[OF nl] unfolding is_election_quorum_def by simp
      have tl: "transient_link initial_configuration ?b n ?y"
        using node_linkD(2)[OF nl master] node_linkD(15)[OF nl master] node_linkD(16)[OF nl master]
          act_b eff fv iq known master
        unfolding transient_link_def by simp
      show ?thesis using pl tl unfolding node_link_def by blast
    qed
    have frame: "i \<noteq> n \<Longrightarrow> node_frame a ?b i" for i
      unfolding node_frame_def abstract_model.active_leader_def by simp
    have "linked initial_configuration (put_node s n ?y) ?b"
      by (rule link_node_update[OF link transition_grows[OF step] nl' frame master master'])
         (auto intro: sent_response)
    with step run show ?thesis by (intro exI[of _ ?b]) simp
  next
    case False
    text \<open>
      The persisted configurations are the stale marker, and the node cannot lead. The abstract state
      is unchanged.
    \<close>
    have stale: "last_accepted_configuration ?x = stale_config" using False by simp
    have not_won: "\<not> election_won ?x"
    proof
      assume won: "election_won ?x"
      from node_link_won_configurations(1)[OF nl won] stale
      show False by simp
    qed
    have nl': "node_link initial_configuration a n ?y" using nl not_won stale master
      unfolding node_link_defs known_tip_def is_election_quorum_def abstract_model.fresh_votes_def abstract_model.active_leader_def
      by (auto split: if_splits)
    have "linked initial_configuration (put_node s n ?y) a"
      by (rule link_node_update[OF link grows_refl nl' _ master master']) (auto intro: sent_response)
    with run show ?thesis by (intro exI[of _ a]) simp
  qed
next
  case False
  let ?x = "nodes_at s n"
  let ?m = "memory_at s n"
  let ?m' = "queue_state (?m\<lparr>last_committed_configuration := last_accepted_configuration ?m\<rparr>)"
  have role: "node_role ?m = node_role ?x" by (rule linkedD(6)[OF link])
  have role': "node_role ?m' = node_role ?x" using role by (simp add: queue_state_def)
  from enabled False have sent: "Commit_Msg c n k \<in> messages s"
    by (auto simp: Let_def memory_state_def)
  have mem_link: "node_role ?x = Data_Only \<Longrightarrow> memory_link a ?x ?m'"
    using linkedD(7)[OF link, of n] unfolding memory_link_def queue_state_def by auto
  have anc: "ancestry_link ((put_node s n ?x)\<lparr>
    memory_at  := (memory_at s)(n := ?m'),
    messages   := messages s,
    descendant := descendant s
  \<rparr>) a"
    by (rule ancestry_unchanged[OF link]) (simp_all add: put_node_def)
  have "linked
            initial_configuration
            ((put_node s n ?x)\<lparr>
              memory_at  := (memory_at s)(n := ?m'),
              messages   := messages s,
              descendant := descendant s
            \<rparr>)
            a"
    by (rule link_update_memory[OF link grows_refl node[of n] _ role' mem_link _ _ _ _ linkedD(4)[OF link] anc])
       (use sent_response linkedD(8)[OF link, of n] in \<open>auto simp: queue_state_def\<close>)
  then show ?thesis using False
    by (intro exI[of _ a]) (simp add: Let_def put_node_def put_memory_state_def put_memory_def memory_state_def)
qed

text \<open>
  The writes of the worker of a data node that is not master-eligible. The state that it writes is
  the disk state that the abstract model describes. A write of the term is a vote in a term, as
  far as the abstract model is concerned, though nobody counts it, and a write of the last
  accepted state is the acceptance of a publication.
\<close>

lemma simulate_persist_term:
  assumes enabled: "enabled s (Persist_Term n)"
  shows "\<exists>b. (b = a \<or> abstract_model.transition initial_configuration a b)
             \<and> linked
                   initial_configuration
                   (execute initial_configuration initial_value s (Persist_Term n))
                   b"
proof -
  let ?x = "nodes_at s n"
  let ?m = "memory_at s n"
  let ?t = "current_term ?m"
  let ?x' = "?x\<lparr>current_term := ?t\<rparr>"
  let ?m' = "?m\<lparr>term_queued := False\<rparr>"
  let ?b = "a\<lparr>
    current_term_of := (current_term_of a)(n := ?t),
    joins_sent      := insert (n,n,?t,position_of_tip_of (publications_accepted a n)) (joins_sent a)
  \<rparr>"
  from enabled have data: "node_role ?x = Data_Only" and lt: "current_term ?x < ?t"
    by (simp_all add: Let_def)
  have nl: "node_link initial_configuration a n ?x" by (rule node)
  have role: "node_role ?m = node_role ?x" by (rule linkedD(6)[OF link])
  have not_master: "node_role ?x \<noteq> Master_Eligible" using data by simp
  have not_won: "\<not> election_won ?x" using node_linkD(11)[OF nl] not_master by blast
  have no_votes: "join_votes ?x = {}" by (rule node_linkD(12)[OF nl not_master])
  have no_publish_votes: "publish_votes ?x = {}" by (rule node_linkD(13)[OF nl not_master])
  have inc: "current_term_of a n < ?t" using lt node_linkD(1)[OF nl] by simp
  have step: "abstract_model.transition initial_configuration a ?b" by (rule abstract_model.transition.start_join[OF inc])
  have grow: "grows a ?b" by (rule transition_grows[OF step])
  have new_link: "node_link initial_configuration ?b n ?x'"
  proof -
    have pl: "persisted_link initial_configuration ?b n ?x'"
      using nl[unfolded node_link_def, THEN conjunct1] unfolding persisted_link_def by (auto split: if_splits)
    have tl: "transient_link initial_configuration ?b n ?x'"
      using not_won no_votes no_publish_votes data
      unfolding transient_link_def abstract_model.fresh_votes_def by simp
    show ?thesis using pl tl unfolding node_link_def by blast
  qed
  have frame: "i \<noteq> n \<Longrightarrow> node_frame a ?b i" for i
    unfolding node_frame_def abstract_model.active_leader_def by auto
  have role': "node_role ?m' = node_role ?x'" using role by simp
  have mem_link: "node_role ?x' = Data_Only \<Longrightarrow> memory_link ?b ?x' ?m'"
    using linkedD(7)[OF link] data memory_link_frame[OF _ grow] by (auto simp: memory_link_def grows_def)
  have anc: "ancestry_link ((put_node s n ?x')\<lparr>
    memory_at  := (memory_at s)(n := ?m'),
    messages   := messages s,
    descendant := descendant s
  \<rparr>) ?b"
    by (rule ancestry_unchanged[OF link]) (simp_all add: put_node_def)
  have "linked initial_configuration ((put_node s n ?x')\<lparr>
    memory_at  := (memory_at s)(n := ?m'),
    messages   := messages s,
    descendant := descendant s
  \<rparr>) ?b"
    by (rule link_update_memory[OF link grow new_link frame role' mem_link _ _ _ _ linkedD(4)[OF link] anc])
       (use no_publish_votes linkedD(8)[OF link, of n] in auto)
  with step show ?thesis by (intro exI[of _ ?b]) (simp add: put_node_def)
qed

lemma normalized_zero_least:
  assumes "normalized k \<le> position_zero"
  shows "normalized k = position_zero"
  using assms by (cases k) (auto simp: normalized_def position_le_iff)

lemma simulate_persist_state:
  assumes enabled: "enabled s (Persist_State n)"
  shows "\<exists>b. (b = a \<or> abstract_model.transition initial_configuration a b)
             \<and> linked
                   initial_configuration
                   (execute initial_configuration initial_value s (Persist_State n))
                   b"
proof -
  let ?x = "nodes_at s n"
  let ?m = "memory_at s n"
  let ?x' = "?x\<lparr>
    last_accepted_position       := last_accepted_position ?m,
    last_accepted_value          := last_accepted_value ?m,
    last_accepted_configuration  := stale_config,
    last_committed_configuration := stale_config
  \<rparr>"
  let ?m' = "?m\<lparr>state_queued := False\<rparr>"
  from enabled have data: "node_role ?x = Data_Only"
    and term_eq: "current_term ?x = position_term (last_accepted_position ?m)"
    by (simp_all add: Let_def)
  have nl: "node_link initial_configuration a n ?x" by (rule node)
  have role: "node_role ?m = node_role ?x" by (rule linkedD(6)[OF link])
  have role': "node_role ?m' = node_role ?x'" using role by simp
  have not_master: "node_role ?x \<noteq> Master_Eligible" using data by simp
  have not_won: "\<not> election_won ?x" using node_linkD(11)[OF nl] not_master by blast
  have no_votes: "join_votes ?x = {}" by (rule node_linkD(12)[OF nl not_master])
  have no_publish_votes: "publish_votes ?x = {}" by (rule node_linkD(13)[OF nl not_master])
  from linkedD(7)[OF link data]
  have known: "position_term (last_accepted_position ?m) = 0
               \<or> (\<exists>publication_history\<in>publications_sent a. position_of_tip_of publication_history = last_accepted_position ?m)"
    and ge: "normalized (last_accepted_position ?x) \<le> normalized (last_accepted_position ?m)"
    and le: "position_term (last_accepted_position ?m) \<le> current_term ?m"
    unfolding memory_link_def by auto
  show ?thesis
  proof (cases "normalized (last_accepted_position ?x) = normalized (last_accepted_position ?m)")
    case True
    have new_link: "node_link initial_configuration a n ?x'"
      using nl not_won no_votes data True
      unfolding node_link_defs abstract_model.active_leader_def abstract_model.fresh_votes_def by (auto simp: stale_config_def split: if_splits)
    have mem_link: "node_role ?x' = Data_Only \<Longrightarrow> memory_link a ?x' ?m'"
      using known le True data unfolding memory_link_def by auto
    have anc: "ancestry_link ((put_node s n ?x')\<lparr>
      memory_at  := (memory_at s)(n := ?m'),
      messages   := messages s,
      descendant := descendant s
    \<rparr>) a"
      by (rule ancestry_unchanged[OF link]) (simp_all add: put_node_def)
    have "linked
              initial_configuration
              ((put_node s n ?x')\<lparr>
                memory_at  := (memory_at s)(n := ?m'),
                messages   := messages s,
                descendant := descendant s
              \<rparr>)
              a"
      by (rule link_update_memory[OF link grows_refl new_link _ role' mem_link _ _ _ _ linkedD(4)[OF link] anc])
         (use no_publish_votes linkedD(8)[OF link, of n] in auto)
    then show ?thesis by (intro exI[of _ a]) (simp add: put_node_def)
  next
    case False
    with ge have lt: "normalized (last_accepted_position ?x) < normalized (last_accepted_position ?m)" by simp
    have term_pos: "position_term (last_accepted_position ?m) \<noteq> 0"
    proof
      assume "position_term (last_accepted_position ?m) = 0"
      then have "normalized (last_accepted_position ?m) = position_zero" by (simp add: normalized_def)
      with ge have "normalized (last_accepted_position ?x) \<le> position_zero" by simp
      from normalized_zero_least[OF this] False \<open>normalized (last_accepted_position ?m) = position_zero\<close>
      show False by simp
    qed
    from known term_pos obtain h where pub: "h \<in> publications_sent a"
      and hpos: "position_of_tip_of h = last_accepted_position ?m" by auto
    have norm_m: "normalized (last_accepted_position ?m) = last_accepted_position ?m"
      using term_pos by (simp add: normalized_def)
    have inc: "position_of_tip_of (publications_accepted a n) < position_of_tip_of h"
      using lt norm_m hpos node_linkD(4)[OF nl] by simp
    have term_h: "term_of_tip_of h = current_term_of a n"
      using hpos term_eq node_linkD(1)[OF nl] by simp
    let ?b = "a\<lparr>
      publications_accepted           := (publications_accepted a)(n := h),
      last_committed_configuration_of := (last_committed_configuration_of a)(n := previous_config_of_tip_of initial_configuration h),
      publish_responses_sent          := insert (n,h) (publish_responses_sent a)
    \<rparr>"
    have step: "abstract_model.transition initial_configuration a ?b" by (rule abstract_model.transition.receive[OF pub term_h inc])
    have grow: "grows a ?b" by (rule transition_grows[OF step])
    have new_link: "node_link initial_configuration ?b n ?x'"
      using nl not_won no_votes data norm_m hpos
      unfolding node_link_defs abstract_model.active_leader_def abstract_model.fresh_votes_def by (auto simp: stale_config_def split: if_splits)
    have frame: "i \<noteq> n \<Longrightarrow> node_frame a ?b i" for i
      unfolding node_frame_def abstract_model.active_leader_def by auto
    have mem_link: "node_role ?x' = Data_Only \<Longrightarrow> memory_link ?b ?x' ?m'"
      using known le pub hpos data unfolding memory_link_def by (auto simp: normalized_def split: if_splits)
    have anc: "ancestry_link ((put_node s n ?x')\<lparr>
      memory_at  := (memory_at s)(n := ?m'),
      messages   := messages s,
      descendant := descendant s
    \<rparr>) ?b"
      by (rule ancestry_unchanged[OF link]) (simp_all add: put_node_def)
    have "linked initial_configuration ((put_node s n ?x')\<lparr>
      memory_at  := (memory_at s)(n := ?m'),
      messages   := messages s,
      descendant := descendant s
    \<rparr>) ?b"
      by (rule link_update_memory[OF link grow new_link frame role' mem_link _ _ _ _ linkedD(4)[OF link] anc])
         (use no_publish_votes linkedD(8)[OF link, of n] in auto)
    with step show ?thesis by (intro exI[of _ ?b]) (simp add: put_node_def)
  qed
qed

text \<open>Combining the cases: every enabled TLA+ action is simulated.\<close>

theorem simulate_action:
  assumes "enabled s action"
  shows "\<exists>b. (b = a \<or> abstract_model.transition initial_configuration a b)
             \<and> linked initial_configuration (execute initial_configuration initial_value s action) b"
  using assms(1)
proof (cases action)
  case (Set_Initial_State n)
  then show ?thesis using simulate_set_initial_state[of n initial_value] assms by blast
next
  case (Handle_Start_Join n c t)
  then have "enabled s (Handle_Start_Join n c t)" using assms(1) by simp
  from simulate_handle_start_join[OF this, of initial_value] Handle_Start_Join
  show ?thesis by blast
next
  case (Handle_Join n nr c t r)
  then show ?thesis using simulate_handle_join[of n nr c t r initial_value] assms by simp
next
  case (Handle_Client_Value n t v payload_value D)
  then show ?thesis using simulate_handle_client_value[of n t v payload_value D initial_value] assms by blast
next
  case (Handle_Publish_Request n p payload_value)
  then show ?thesis using simulate_handle_publish_request[of n p payload_value initial_value] assms by blast
next
  case (Handle_Publish_Response n nr c k)
  then show ?thesis using simulate_handle_publish_response[of n nr c k initial_value] assms by simp
next
  case (Handle_Commit c n k)
  then show ?thesis using simulate_handle_commit[of c n k initial_value] assms by blast
next
  case (Restart_Node n r)
  then show ?thesis using simulate_restart_node[of initial_value n r] by blast
next
  case (Persist_Term n)
  then show ?thesis using simulate_persist_term[of n initial_value] assms by simp
next
  case (Persist_State n)
  then show ?thesis using simulate_persist_state[of n initial_value] assms by simp
qed

end

theorem tla_dynamic_refinement:
  assumes "tla_reachable initial_configuration initial_value versions s"
  shows "\<exists>a. abstract_model.dynamic_reachable initial_configuration a
             \<and> linked initial_configuration s a"
  using assms
proof (induction rule: tla_reachable.induct)
  case init
  show ?case by (intro exI[of _ "abstract_model.bootstrapped initial_configuration"] conjI)
      (rule abstract_model.dynamic_reachable.boot[OF init.hyps(2)], rule linked_initial)
next
  case (advance s action)
  then obtain a where a: "abstract_model.dynamic_reachable initial_configuration a" "linked
                                                                                         initial_configuration
                                                                                         s
                                                                                         a" by blast
  have nonempty: "initial_configuration \<noteq> {}" using a(1) using a(1) abstract_model.dynamic_reachable_nonempty by blast
  interpret simulation initial_configuration s a by (unfold_locales; fact)
  obtain b where step: "b = a \<or> abstract_model.transition initial_configuration a b" and link: "linked
                                                                                                    initial_configuration
                                                                                                    (execute
                                                                                                         initial_configuration
                                                                                                         initial_value
                                                                                                         s
                                                                                                         action)
                                                                                                    b"
    using simulate_action[OF advance.hyps(2), of initial_value]
    by blast
  have "abstract_model.dynamic_reachable initial_configuration b" using a(1) step by (auto intro: abstract_model.dynamic_reachable.advance)
  with link show ?case by blast
qed

section \<open>Transfer to TLA+ messages and descendant edges\<close>

lemma followed_by_simulation:
  assumes run: "rtranclp (tla_next initial_configuration initial_value) s s'"
  assumes reach: "abstract_model.dynamic_reachable initial_configuration a"
  assumes link: "linked initial_configuration s a"
  shows "\<exists>b. rtranclp (abstract_model.transition initial_configuration) a b
             \<and> abstract_model.dynamic_reachable initial_configuration b
             \<and> linked initial_configuration s' b"
  using run
proof (induction rule: rtranclp_induct)
  case base
  show ?case using reach link by blast
next
  case (step u v)
  then obtain b where trail: "rtranclp (abstract_model.transition initial_configuration) a b" and b: "abstract_model.dynamic_reachable initial_configuration b" "linked
                                                                                                                                                                     initial_configuration
                                                                                                                                                                     u
                                                                                                                                                                     b" by blast
  have nonempty: "initial_configuration \<noteq> {}" using b(1) using b(1) abstract_model.dynamic_reachable_nonempty by blast
  interpret simulation initial_configuration u b by (unfold_locales; fact)
  obtain action where enabled: "enabled u action" and v: "v = execute
                                                                  initial_configuration
                                                                  initial_value
                                                                  u
                                                                  action"
    using step.hyps(2) unfolding tla_next_def by blast
  obtain c where move: "c = b \<or> abstract_model.transition initial_configuration b c" and c: "linked
                                                                                                 initial_configuration
                                                                                                 v
                                                                                                 c"
    using simulate_action[OF enabled, of initial_value] v by blast
  have "rtranclp (abstract_model.transition initial_configuration) a c" using trail move by (auto intro: rtranclp.rtrancl_into_rtrancl)
  moreover have "abstract_model.dynamic_reachable initial_configuration c" using b(1) move by (auto intro: abstract_model.dynamic_reachable.advance)
  ultimately show ?case using c by blast
qed

lemma certificate_persists:
  assumes "rtranclp (abstract_model.transition initial_configuration) a b" "elections_won a k = Some e"
  shows "elections_won b k = Some e"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step u v)
  from step.hyps(2) show ?case using step.IH[OF step.prems]
    by (cases rule: abstract_model.transition.cases) auto
qed

theorem tla_one_election_candidate_per_term:
  assumes reach: "tla_reachable initial_configuration initial_value versions s"
  assumes run: "rtranclp (tla_next initial_configuration initial_value) s s'"
  assumes won: "election_won (nodes_at s c)" "election_won (nodes_at s' d)"
  assumes same: "current_term (nodes_at s c) = current_term (nodes_at s' d)"
  shows "c = d"
proof -
  obtain a where a: "abstract_model.dynamic_reachable initial_configuration a" "linked
                                                                                    initial_configuration
                                                                                    s
                                                                                    a"
    using tla_dynamic_refinement[OF reach] by blast
  obtain b where trail: "rtranclp (abstract_model.transition initial_configuration) a b" and b: "abstract_model.dynamic_reachable initial_configuration b" "linked
                                                                                                                                                                initial_configuration
                                                                                                                                                                s'
                                                                                                                                                                b"
    using followed_by_simulation[OF run a(1) a(2)] by blast
  let ?t = "current_term (nodes_at s c)"
  have u: "node_link initial_configuration a c (nodes_at s c)" and v: "node_link
                                                                           initial_configuration
                                                                           b
                                                                           d
                                                                           (nodes_at s' d)"
    by (rule linkedD(1)[OF a(2)], rule linkedD(1)[OF b(2)])
  obtain e f where e: "elections_won a (c,?t) = Some e" and f: "elections_won b (d,?t) = Some f"
    using node_linkD(1)[OF u] node_linkD(3)[OF u node_linkD(11)[OF u won(1)]]
      node_linkD(1)[OF v] node_linkD(3)[OF v node_linkD(11)[OF v won(2)]] won same
    unfolding abstract_model.active_leader_def by auto
  show ?thesis by (rule abstract_model.dynamic_one_election_candidate_per_term[OF b(1) certificate_persists[OF trail e] f])
qed

theorem tla_one_publisher_per_term:
  assumes reach: "tla_reachable initial_configuration initial_value versions s"
  assumes m: "Publish_Msg d p v \<in> messages s" "Publish_Msg e q w \<in> messages s"
  assumes t: "position_term (publication_position p) = position_term (publication_position q)"
  shows "publication_owner p = publication_owner q"
proof -
  obtain a where a: "abstract_model.dynamic_reachable initial_configuration a" "linked
                                                                                    initial_configuration
                                                                                    s
                                                                                    a"
    using tla_dynamic_refinement[OF reach] by blast
  obtain h k where pubs: "h @ [p] \<in> publications_sent a" "k @ [q] \<in> publications_sent a"
    using linkedD(3)[OF a(2) m(1)] linkedD(3)[OF a(2) m(2)] by auto
  have l: "abstract_model.leadership_ok initial_configuration a" using abstract_model.dynamic_invariants[OF a(1)] by auto
  obtain ep eq where "elections_won a (publication_owner p,position_term (publication_position p)) = Some ep"
    "elections_won a (publication_owner q,position_term (publication_position p)) = Some eq"
    using abstract_model.leadershipD(8)[OF l pubs(1)] abstract_model.leadershipD(8)[OF l pubs(2)] t by auto
  then show ?thesis by (rule abstract_model.dynamic_one_election_candidate_per_term[OF a(1)])
qed

theorem tla_log_matching:
  assumes "tla_reachable initial_configuration initial_value versions s"
    "Publish_Msg d p v \<in> messages s" "Publish_Msg e q w \<in> messages s"
    "publication_position p = publication_position q"
  shows "p = q \<and> v = w"
proof -
  obtain a where "linked initial_configuration s a" using tla_dynamic_refinement[OF assms(1)] by blast
  from linkedD(4)[OF this] assms(2-4) show ?thesis unfolding wire_unique_def by blast
qed

definition commit_for :: "'v tla_state \<Rightarrow> publication \<Rightarrow> bool" where
  "commit_for state request \<longleftrightarrow>
    (\<exists>leader destination. Commit_Msg leader destination (publication_position request) \<in> messages state)"

lemma committed_request_link:
  assumes a: "abstract_model.dynamic_reachable initial_configuration a" "linked
                                                                             initial_configuration
                                                                             s
                                                                             a"
  assumes pub: "Publish_Msg d p v \<in> messages s"
  assumes commit: "commit_for s p"
  obtains h where "h \<in> publications_committed a" "h \<in> publications_sent a" "position_of_tip_of h = publication_position p"
proof -
  obtain h where hp: "h @ [p] \<in> publications_sent a" using linkedD(3)[OF a(2) pub] by auto
  obtain c d where "Commit_Msg c d (publication_position p) \<in> messages s" using commit unfolding commit_for_def by blast
  from linkedD(3)[OF a(2) this] obtain k where kc: "k \<in> publications_committed a" and kp: "position_of_tip_of k = publication_position p" by auto
  have pub_ok: "abstract_model.publications_ok initial_configuration a" using abstract_model.dynamic_invariants[OF a(1)] by auto
  have kpub: "k \<in> publications_sent a" by (rule abstract_model.publicationsD(5)[OF pub_ok kc])
  have "k = h @ [p]" by (rule abstract_model.dynamic_unique_publication[OF a(1) kpub hp]) (simp add: kp)
  with kc have "h @ [p] \<in> publications_committed a" by simp
  from this hp show thesis by (rule that) simp
qed

theorem tla_committed_values_form_chain:
  assumes reach: "tla_reachable initial_configuration initial_value versions s"
  assumes m: "Publish_Msg d p v \<in> messages s" "Publish_Msg e q w \<in> messages s"
  assumes commits: "commit_for s p" "commit_for s q"
  assumes distinct: "publication_position p \<noteq> publication_position q"
  shows "(publication_position p,publication_position q) \<in> descendant s
         \<or> (publication_position q,publication_position p) \<in> descendant s"
proof -
  obtain a where a: "abstract_model.dynamic_reachable initial_configuration a" "linked
                                                                                    initial_configuration
                                                                                    s
                                                                                    a"
    using tla_dynamic_refinement[OF reach] by blast
  obtain h where h: "h \<in> publications_committed a" "h \<in> publications_sent a" "position_of_tip_of h = publication_position p"
    by (rule committed_request_link[OF a m(1) commits(1)])
  obtain k where k: "k \<in> publications_committed a" "k \<in> publications_sent a" "position_of_tip_of k = publication_position q"
    by (rule committed_request_link[OF a m(2) commits(2)])
  have prefixes: "prefix h k \<or> prefix k h" by (rule abstract_model.dynamic_committed_states_form_chain[OF a(1) h(1) k(1)])
  have different: "h \<noteq> k" "k \<noteq> h" using distinct h(3) k(3) by auto
  from prefixes show ?thesis
  proof
    assume "prefix h k"
    from ancestry_edge[OF linkedD(5)[OF a(2)] h(2) k(2) this different(1)] h(3) k(3)
    show ?thesis by simp
  next
    assume "prefix k h"
    from ancestry_edge[OF linkedD(5)[OF a(2)] k(2) h(2) this different(2)] h(3) k(3)
    show ?thesis by simp
  qed
qed

end
