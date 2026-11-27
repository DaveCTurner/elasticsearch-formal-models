theory Base
  imports "../Basics/Publication" "../Basics/Quorum"
begin

section \<open>Definitions for the Java transcription\<close>

text \<open>
  The role with which a node is running. A master-eligible node can vote and lead, whether or not
  it is also a data node, and persists its state synchronously. A data node that is not
  master-eligible persists its state asynchronously. A coordinating-only node does not persist
  its state. Every role runs \<open>handleStartJoin\<close>, \<open>handlePublishRequest\<close> and \<open>handleCommit\<close> on its
  own in-memory state, but only a master-eligible node can lead.
\<close>

datatype role = Master_Eligible | Data_Only | Coordinating_Only

text \<open>
  The messages that nodes exchange. Each corresponds to a Java object:
  \<open>Join_Msg\<close> to \<open>Join\<close>, \<open>Publish_Msg\<close> to \<open>PublishRequest\<close>,
  \<open>Response_Msg\<close> to \<open>PublishResponse\<close> and \<open>Commit_Msg\<close> to
  \<open>ApplyCommitRequest\<close>. The Java objects do not carry their destination, so it
  is added here. A \<open>Join\<close> and a \<open>PublishResponse\<close> are votes. The receiver counts a vote
  only if the sender is master-eligible (\<open>VoteCollection.addVote\<close>), so a vote carries the role of
  the incarnation that sent it, as the \<open>DiscoveryNode\<close> of the sender does.

  \<^item> \<open>Join_Msg voter voter_role candidate term position\<close> is a vote by \<open>voter\<close> for
    \<open>candidate\<close> in \<open>term\<close>, from last accepted position \<open>position\<close>.
  \<^item> \<open>Publish_Msg destination request new_value\<close> is for node \<open>destination\<close>.
  \<^item> \<open>Response_Msg voter voter_role leader position\<close> is the response of \<open>voter\<close> to \<open>leader\<close>.
  \<^item> \<open>Commit_Msg leader destination position\<close> is the commit of \<open>leader\<close> for node
    \<open>destination\<close>.

  The publication metadata reuses the abstract record. The value being published is a
  separate message field and is never changed by message delivery. A position is a term and a version.
\<close>

datatype 'v message =
    Join_Msg node role node nat position
  | Publish_Msg node publication 'v
  | Response_Msg node role node position
  | Commit_Msg node node position

text \<open>
  The in-memory state of one node: the fields of \<open>PersistedState\<close> as the node's
  \<open>CoordinationState\<close> sees them, and the transient fields of \<open>CoordinationState\<close>. Each field has
  the name of the Java field or getter that it models. The last accepted term and version form a
  single position. A vote collection is represented by its set of node IDs. The last two fields
  are the \<open>newCurrentTermQueued\<close> and \<open>newStateQueued\<close> flags of \<open>AsyncPersistedState\<close>, which say
  that the term, or the accepted state, is waiting to be written to disk. They are only ever set
  on a data node that is not master-eligible.
\<close>

record 'v node_memory_state =
  current_term :: nat
  last_accepted_position :: position
  last_accepted_value :: 'v
  last_accepted_configuration :: config
  last_committed_configuration :: config
  join_votes :: "node set"
  started_join_since_last_reboot :: bool
  election_won :: bool
  last_published_version :: nat
  last_published_configuration :: config
  publish_votes :: "node set"
  node_role :: role
  term_queued :: bool
  state_queued :: bool

text \<open>
  A node that is not master-eligible but holds data persists its term and its last accepted state
  asynchronously (\<open>GatewayMetaState.AsyncPersistedState\<close>), and replaces both voting
  configurations of the state that it writes with a marker configuration
  (\<open>AsyncPersistedState.resetVotingConfiguration\<close>). The marker contains the single ID
  \<open>STALE_STATE_CONFIG_NODE_ID\<close>, which no real node has. A node that later restarts as
  master-eligible reads this state back. It cannot win an election with such a configuration,
  because no vote is ever cast by the marker's node. The model represents the marker as
  the configuration element \<open>StaleConfigurationMarker\<close>, which is distinct from every
  \<open>ConfigNode\<close>.
\<close>

definition stale_config :: config where
  "stale_config = {StaleConfigurationMarker}"

lemma stale_config_nonempty[simp]: "stale_config \<noteq> {}" "{} \<noteq> stale_config"
  by (simp_all add: stale_config_def)

text \<open>
  What a node has written to disk: its term and its last accepted state, as in the Lucene index
  (\<open>PersistedClusterStateService\<close>). A restart reads this state back. The disk is not
  affected by the transient fields of \<open>CoordinationState\<close>.
\<close>

record 'v node_disk_state =
  disk_term :: nat
  disk_position :: position
  disk_value :: 'v
  disk_accepted_configuration :: config
  disk_committed_configuration :: config

definition disk_of :: "'v node_memory_state \<Rightarrow> 'v node_disk_state" where
  "disk_of node_memory_state =
    \<lparr>
      disk_term                    = current_term node_memory_state,
      disk_position                = last_accepted_position node_memory_state,
      disk_value                   = last_accepted_value node_memory_state,
      disk_accepted_configuration  = last_accepted_configuration node_memory_state,
      disk_committed_configuration = last_committed_configuration node_memory_state
    \<rparr>"

text \<open>
  A data node that is not master-eligible queues the writes of its term and of its last accepted
  state for its worker (\<open>AsyncPersistedState.setCurrentTerm\<close> and \<open>setLastAcceptedState\<close>). The
  accepted state is queued again when a commit changes it, which is an over-approximation: the
  state is only queued if the commit changes the metadata, and the model has no cluster UUID.
\<close>

definition queue_term :: "'v node_memory_state \<Rightarrow> 'v node_memory_state" where
  "queue_term node_memory_state =
    (if node_role node_memory_state = Data_Only then node_memory_state\<lparr>term_queued := True\<rparr> else node_memory_state)"

definition queue_state :: "'v node_memory_state \<Rightarrow> 'v node_memory_state" where
  "queue_state node_memory_state =
    (if node_role node_memory_state = Data_Only then node_memory_state\<lparr>state_queued := True\<rparr> else node_memory_state)"

text \<open>
  The position of the last published state is the current term together with the
  last published version, as in \<open>handlePublishResponse\<close>. The position of a
  publication request is its term and version.
\<close>

abbreviation last_published_position :: "'v node_memory_state \<Rightarrow> position" where
  "last_published_position node_memory_state \<equiv>
    \<lparr>
      position_term    = current_term node_memory_state,
      position_version = last_published_version node_memory_state
    \<rparr>"

end
