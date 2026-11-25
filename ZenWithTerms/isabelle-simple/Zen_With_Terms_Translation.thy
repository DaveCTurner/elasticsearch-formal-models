theory Zen_With_Terms_Translation
  imports Coordination_State_Base
begin

section \<open>The Init and Next actions of ZenWithTerms.tla\<close>

text \<open>
  A translation of the \<open>Init\<close> and \<open>Next\<close> actions of ZenWithTerms.tla, extended with the roles of
  the nodes. The node record and the messages are in \<open>Coordination_State_Base\<close>. The TLA+
  constants are parameters, except that \<open>Nodes\<close> and the permitted values are the whole of the types
  \<open>node\<close> and \<open>'v\<close>: \<open>initial_configuration\<close>
  the initial configuration and \<open>initial_value\<close> the initial value. The initial
  accepted version of each node is \<open>versions\<close>. Natural numbers represent the
  node IDs, and the opaque TLA+ values have an arbitrary Isabelle type. The
  \<open>descendant\<close> variable of the TLA+ specification is the \<open>descendant\<close> field.

  The state of a node is in two parts.

  \<^item> \<open>nodes_at\<close> is the node's state on disk, together with the transient fields of a
    master-eligible node. A master-eligible node persists every change synchronously, so for
    such a node it is also the node's in-memory state.
  \<^item> \<open>memory_at\<close> is the in-memory state of a node that is not master-eligible, which is lost when
    the node restarts. It is not used for a master-eligible node.
\<close>

record 'v tla_state =
  nodes_at :: "node \<Rightarrow> 'v node_memory_state"
  memory_at :: "node \<Rightarrow> 'v node_memory_state"
  messages :: "'v message set"
  descendant :: "(position \<times> position) set"

text \<open>
  One constructor for each disjunct of \<open>Next\<close>, with the parameters of the
  TLA+ operation except that a message parameter is replaced by its fields.
  The first node argument performs the action, except that
  \<open>Handle_Join voter voter_role candidate join_term voter_position\<close> and
  \<open>Handle_Publish_Response voter voter_role leader position\<close> are performed by the candidate
  or leader on receiving the message from \<open>voter\<close>, and \<open>Handle_Commit leader node position\<close> is
  performed by \<open>node\<close> on receiving the message from \<open>leader\<close>. \<open>Restart_Node\<close> is
  \<open>RestartNode\<close>, extended with the role of the new incarnation. \<open>Persist_Term\<close> and \<open>Persist_State\<close>
  are the writes to disk of the asynchronous worker of a data node that is not master-eligible
  (\<open>AsyncPersistedState\<close>).
\<close>

datatype 'v tla_action =
    Set_Initial_State node
  | Handle_Start_Join node node nat
  | Handle_Join node role node nat position
  | Handle_Client_Value node nat nat 'v config
  | Handle_Publish_Request node publication 'v
  | Handle_Publish_Response node role node position
  | Handle_Commit node node position
  | Restart_Node node role
  | Persist_Term node
  | Persist_State node

text \<open>The initial state (\<open>Init\<close>).\<close>

definition initial_node :: "'v \<Rightarrow> nat \<Rightarrow> 'v node_memory_state" where
  "initial_node initial_value version =
    \<lparr>
      current_term                   = 0,
      last_accepted_position         = \<lparr>position_term = 0, position_version = version\<rparr>,
      last_accepted_value            = initial_value,
      last_accepted_configuration    = {},
      last_committed_configuration   = {},
      join_votes                     = {},
      started_join_since_last_reboot = False,
      election_won                   = False,
      last_published_version         = 0,
      last_published_configuration   = {},
      publish_votes                  = {},
      node_role                      = Master_Eligible,
      term_queued                    = False,
      state_queued                   = False
    \<rparr>"

definition tla_initial :: "'v \<Rightarrow> (node \<Rightarrow> nat) \<Rightarrow> 'v tla_state" where
  "tla_initial initial_value versions =
    \<lparr>
      nodes_at   = (\<lambda>node. initial_node initial_value (versions node)),
      memory_at  = (\<lambda>node. initial_node initial_value (versions node)),
      messages   = {},
      descendant = {}
    \<rparr>"

definition put_node :: "'v tla_state \<Rightarrow> node \<Rightarrow> 'v node_memory_state \<Rightarrow> 'v tla_state" where
  "put_node state node new_node_memory_state =
    state\<lparr>nodes_at := (nodes_at state)(node := new_node_memory_state)\<rparr>"

definition put_memory :: "'v tla_state \<Rightarrow> node \<Rightarrow> 'v node_memory_state \<Rightarrow> 'v tla_state" where
  "put_memory state node new_node_memory_state =
    state\<lparr>memory_at := (memory_at state)(node := new_node_memory_state)\<rparr>"

text \<open>
  The in-memory state of a node, and its update. For a master-eligible node it is \<open>nodes_at\<close>,
  and for any other node it is \<open>memory_at\<close>.
\<close>

definition memory_state :: "'v tla_state \<Rightarrow> node \<Rightarrow> 'v node_memory_state" where
  "memory_state state node =
    (if node_role (nodes_at state node) = Master_Eligible then nodes_at state node else memory_at state node)"

definition put_memory_state :: "'v tla_state \<Rightarrow> node \<Rightarrow> 'v node_memory_state \<Rightarrow> 'v tla_state" where
  "put_memory_state state node new_node_memory_state =
    (if node_role (nodes_at state node) = Master_Eligible
     then put_node state node new_node_memory_state
     else put_memory state node new_node_memory_state)"

text \<open>
  The transient fields are cleared on a restart and on moving to a new term
  (\<open>handleStartJoin\<close>). The last published configuration reverts to the last
  accepted configuration.
\<close>

definition reset_transient :: "'v node_memory_state \<Rightarrow> 'v node_memory_state" where
  "reset_transient node_memory_state =
    node_memory_state\<lparr>
      join_votes                     := {},
      started_join_since_last_reboot := False,
      election_won                   := False,
      last_published_version         := 0,
      last_published_configuration   := last_accepted_configuration node_memory_state,
      publish_votes                  := {}
    \<rparr>"

text \<open>
  A restart may change the node's roles: any role change needs a restart, and a restart may keep
  the same roles. The \<open>Restart_Node\<close> action carries the role of the new incarnation. The node's
  disk, and, for a node that is master-eligible or holds data, its in-memory state, are loaded
  from the state on disk. A coordinating-only node starts with an empty in-memory state instead
  (\<open>GatewayMetaState.createInMemoryPersistedState\<close>).

  A coordinating-only node must still keep its persistent ID on disk
  (\<open>PersistedClusterStateService.persistNodeIdWithoutOverwritingState\<close>). Where the
  persisted term is nonzero the node may have voted or accepted a publication,
  so the state on disk is kept. Where the persisted term is zero no vote has been
  cast and no publication has been accepted, and the state is replaced by an empty
  one: the last accepted position becomes the zero position, the value becomes the initial
  value, and both configurations are empty. (The model does not treat a nonzero initial
  version, as of a cluster upgraded from before Zen2.)

  The initial incarnation of a node is taken to be master-eligible, which over-approximates the
  nodes that start without the role.
\<close>

definition empty_node :: "'v \<Rightarrow> role \<Rightarrow> 'v node_memory_state \<Rightarrow> 'v node_memory_state" where
  "empty_node initial_value new_role node_memory_state =
    (reset_transient (node_memory_state\<lparr>
      current_term                 := 0,
      last_accepted_position       := position_zero,
      last_accepted_value          := initial_value,
      last_accepted_configuration  := {},
      last_committed_configuration := {}
    \<rparr>))\<lparr>
      node_role    := new_role,
      term_queued  := False,
      state_queued := False
    \<rparr>"

definition loaded_node :: "role \<Rightarrow> 'v node_memory_state \<Rightarrow> 'v node_memory_state" where
  "loaded_node new_role node_memory_state =
    (reset_transient node_memory_state)\<lparr>
      node_role    := new_role,
      term_queued  := False,
      state_queued := False
    \<rparr>"

definition restarted_disk :: "'v \<Rightarrow> role \<Rightarrow> 'v node_memory_state \<Rightarrow> 'v node_memory_state" where
  "restarted_disk initial_value new_role node_memory_state =
    (if current_term node_memory_state = 0 \<and> new_role = Coordinating_Only
     then empty_node initial_value new_role node_memory_state
     else loaded_node new_role node_memory_state)"

definition restarted_memory :: "'v \<Rightarrow> role \<Rightarrow> 'v node_memory_state \<Rightarrow> 'v node_memory_state" where
  "restarted_memory initial_value new_role node_memory_state =
    (if new_role = Coordinating_Only
     then empty_node initial_value new_role node_memory_state
     else restarted_disk initial_value new_role node_memory_state)"

text \<open>
  \<open>IsElectionQuorum\<close> and \<open>IsPublishQuorum\<close> of the specification: the votes must
  form a quorum of both the last committed configuration and, respectively, the
  last accepted configuration and the last published configuration.
\<close>

definition is_election_quorum :: "'v node_memory_state \<Rightarrow> node set \<Rightarrow> bool" where
  "is_election_quorum node_memory_state votes \<longleftrightarrow>
    quorum (last_committed_configuration node_memory_state) votes
    \<and> quorum (last_accepted_configuration node_memory_state) votes"

definition is_publish_quorum :: "'v node_memory_state \<Rightarrow> node set \<Rightarrow> bool" where
  "is_publish_quorum node_memory_state votes \<longleftrightarrow>
    quorum (last_committed_configuration node_memory_state) votes
    \<and> quorum (last_published_configuration node_memory_state) votes"

text \<open>
  The \<open>descendant\<close> relation of the specification is an auxiliary history variable:
  it relates the position of each published state to the position of its parent, and to the
  positions of the ancestors of its parent.
\<close>

definition extend_descendant ::
  "(position \<times> position) set \<Rightarrow> position \<Rightarrow> position \<Rightarrow> (position \<times> position) set" where
  "extend_descendant descendants parent_position child_position =
    descendants \<union> {(parent_position, child_position)} \<union>
      {(ancestor_position, child_position) | ancestor_position. (ancestor_position, parent_position) \<in> descendants}"

text \<open>
  \<open>enabled\<close> holds the guards of each action and \<open>execute\<close> its effects, including
  the messages that it sends. A broadcast creates one message for every node.

  \<open>handleStartJoin\<close>, \<open>handlePublishRequest\<close> and \<open>handleCommit\<close> run on every node, as in the
  \<open>Coordinator\<close>, on the node's in-memory state. \<open>setInitialState\<close>, \<open>handleJoin\<close>,
  \<open>handleClientValue\<close> and \<open>handlePublishResponse\<close> only run on a master-eligible node: the
  \<open>Coordinator\<close> asserts this for each. A vote from a node that is not master-eligible is
  ignored by its receiver, which is why a vote carries its sender's role.
\<close>

fun enabled :: "'v tla_state \<Rightarrow> 'v tla_action \<Rightarrow> bool" where
  "enabled state (Set_Initial_State node) =
    (let node_memory_state = nodes_at state node
     in node_role node_memory_state = Master_Eligible
        \<and> last_accepted_configuration node_memory_state = {}
        \<and> position_term (last_accepted_position node_memory_state) = 0
        \<and> last_committed_configuration node_memory_state = {}
        \<and> last_published_version node_memory_state = 0
        \<and> last_published_configuration node_memory_state = {}
        \<and> \<not> election_won node_memory_state
        \<and> join_votes node_memory_state = {}
        \<and> publish_votes node_memory_state = {})"
| "enabled state (Handle_Start_Join voter candidate new_term) =
    (current_term (memory_state state voter) < new_term)"
| "enabled state (Handle_Join voter voter_role candidate join_term voter_position) =
    (let candidate_state = nodes_at state candidate
     in node_role candidate_state = Master_Eligible
        \<and> Join_Msg voter voter_role candidate join_term voter_position \<in> messages state
        \<and> join_term = current_term candidate_state
        \<and> started_join_since_last_reboot candidate_state
        \<and> voter_position \<le> last_accepted_position candidate_state
        \<and> last_accepted_configuration candidate_state \<noteq> {})"
| "enabled state (Handle_Client_Value leader new_term version new_value new_configuration) =
    (let leader_state = nodes_at state leader
     in node_role leader_state = Master_Eligible
        \<and> new_configuration \<subseteq> range ConfigNode
        \<and> new_configuration \<noteq> {}
        \<and> election_won leader_state
        \<and> last_published_version leader_state = position_version (last_accepted_position leader_state)
        \<and> new_term = current_term leader_state
        \<and> last_published_version leader_state < version
        \<and> (new_configuration \<noteq> last_accepted_configuration leader_state \<longrightarrow>
            last_committed_configuration leader_state = last_accepted_configuration leader_state)
        \<and> quorum new_configuration (join_votes leader_state))"
| "enabled state (Handle_Publish_Request node request new_value) =
    (let node_memory_state = memory_state state node
     in Publish_Msg node request new_value \<in> messages state
        \<and> position_term (publication_position request) = current_term node_memory_state
        \<and> (position_term (publication_position request) = position_term (last_accepted_position node_memory_state) \<longrightarrow>
            position_version (last_accepted_position node_memory_state) < position_version (publication_position request)))"
| "enabled state (Handle_Publish_Response voter voter_role leader position) =
    (let leader_state = nodes_at state leader
     in node_role leader_state = Master_Eligible
        \<and> Response_Msg voter voter_role leader position \<in> messages state
        \<and> election_won leader_state
        \<and> position = last_published_position leader_state)"
| "enabled state (Handle_Commit leader node position) =
    (let node_memory_state = memory_state state node
     in Commit_Msg leader node position \<in> messages state
        \<and> position_term position = current_term node_memory_state
        \<and> position = last_accepted_position node_memory_state
        \<and> (election_won node_memory_state \<longrightarrow> position_version position = last_published_version node_memory_state))"
| "enabled state (Restart_Node node new_role) = True"
| "enabled state (Persist_Term node) =
    (let node_disk_state = nodes_at state node;
         node_memory_state = memory_at state node
     in node_role node_disk_state = Data_Only
        \<and> term_queued node_memory_state
        \<and> current_term node_disk_state < current_term node_memory_state)"
| "enabled state (Persist_State node) =
    (let node_disk_state = nodes_at state node;
         node_memory_state = memory_at state node
     in node_role node_disk_state = Data_Only
        \<and> state_queued node_memory_state
        \<and> current_term node_disk_state = position_term (last_accepted_position node_memory_state))"

fun execute :: "config \<Rightarrow> 'v \<Rightarrow> 'v tla_state \<Rightarrow> 'v tla_action \<Rightarrow> 'v tla_state" where
  "execute initial_configuration initial_value state (Set_Initial_State node) =
    put_node
        state
        node
        ((nodes_at state node)\<lparr>
          last_accepted_configuration  := initial_configuration,
          last_committed_configuration := initial_configuration,
          last_accepted_value          := initial_value
        \<rparr>)"
| "execute initial_configuration initial_value state (Handle_Start_Join voter candidate new_term) =
    (let voter_state = memory_state state voter
     in (put_memory_state
             state
             voter
             (queue_term ((reset_transient voter_state)\<lparr>
               current_term                   := new_term,
               started_join_since_last_reboot := True
             \<rparr>)))
          \<lparr>messages := insert (Join_Msg
                                   voter
                                   (node_role voter_state)
                                   candidate
                                   new_term
                                   (last_accepted_position voter_state)) (messages state)\<rparr>)"
| "execute
       initial_configuration
       initial_value
       state
       (Handle_Join voter voter_role candidate join_term voter_position)
   =
    (let candidate_state = nodes_at state candidate;
         new_votes = (if voter_role = Master_Eligible
                      then insert voter (join_votes candidate_state)
                      else join_votes candidate_state);
         won = is_election_quorum candidate_state new_votes
     in put_node
            state
            candidate
            (candidate_state\<lparr>
              join_votes             := new_votes,
              election_won           := won,
              last_published_version := (if \<not> election_won candidate_state \<and> won
                then position_version (last_accepted_position candidate_state)
                else last_published_version candidate_state)
            \<rparr>))"
| "execute
       initial_configuration
       initial_value
       state
       (Handle_Client_Value leader new_term version new_value new_configuration)
   =
    (let leader_state = nodes_at state leader;
         request = \<lparr>
           publication_position        = \<lparr>position_term = new_term, position_version = version\<rparr>,
           publication_owner           = leader,
           publication_config          = new_configuration,
           publication_previous_config = last_committed_configuration leader_state
         \<rparr>
     in (put_node
             state
             leader
             (leader_state\<lparr>
               last_published_version       := version,
               last_published_configuration := new_configuration,
               publish_votes                := {}
             \<rparr>))
       \<lparr>
         messages   := messages state \<union> {Publish_Msg destination request new_value | destination. True},
         descendant := extend_descendant
                           (descendant state)
                           (last_accepted_position leader_state)
                           \<lparr>position_term = new_term, position_version = version\<rparr>
       \<rparr>)"
| "execute initial_configuration initial_value state (Handle_Publish_Request node request new_value)
   =
    (let node_memory_state = memory_state state node
     in (put_memory_state
             state
             node
             (queue_state (node_memory_state\<lparr>
               last_accepted_position       := publication_position request,
               last_accepted_value          := new_value,
               last_accepted_configuration  := publication_config request,
               last_committed_configuration := publication_previous_config request
             \<rparr>)))
          \<lparr>messages := insert (Response_Msg
                                   node
                                   (node_role node_memory_state)
                                   (publication_owner request)
                                   (publication_position request)) (messages state)\<rparr>)"
| "execute
       initial_configuration
       initial_value
       state
       (Handle_Publish_Response voter voter_role leader position)
   =
    (let leader_state = nodes_at state leader;
         new_votes = (if voter_role = Master_Eligible
                      then insert voter (publish_votes leader_state)
                      else publish_votes leader_state)
     in (put_node state leader (leader_state\<lparr>publish_votes := new_votes\<rparr>))
       \<lparr>messages := (if is_publish_quorum leader_state new_votes
         then messages state \<union> {Commit_Msg leader destination position | destination. True}
         else messages state)\<rparr>)"
| "execute initial_configuration initial_value state (Handle_Commit leader node position) =
    (let node_memory_state = memory_state state node
     in put_memory_state
            state
            node
            (queue_state (node_memory_state\<lparr>last_committed_configuration := last_accepted_configuration node_memory_state\<rparr>)))"
| "execute initial_configuration initial_value state (Restart_Node node new_role) =
    (put_node state node (restarted_disk initial_value new_role (nodes_at state node)))
      \<lparr>memory_at := (memory_at state)
          (node := restarted_memory initial_value new_role (nodes_at state node))\<rparr>"
| "execute initial_configuration initial_value state (Persist_Term node) =
    (put_node
         state
         node
         ((nodes_at state node)\<lparr>current_term := current_term (memory_at state node)\<rparr>))
      \<lparr>memory_at := (memory_at state)
          (node := (memory_at state node)\<lparr>term_queued := False\<rparr>)\<rparr>"
| "execute initial_configuration initial_value state (Persist_State node) =
    (put_node
         state
         node
         ((nodes_at state node)\<lparr>
           last_accepted_position       := last_accepted_position (memory_at state node),
           last_accepted_value          := last_accepted_value (memory_at state node),
           last_accepted_configuration  := stale_config,
           last_committed_configuration := stale_config
         \<rparr>))
      \<lparr>memory_at := (memory_at state)(node := (memory_at state node)\<lparr>state_queued := False\<rparr>)\<rparr>"

inductive tla_reachable ::
  "config \<Rightarrow> 'v \<Rightarrow> (node \<Rightarrow> nat) \<Rightarrow> 'v tla_state \<Rightarrow> bool"
  for initial_configuration initial_value versions where
  init: "initial_configuration \<subseteq> range ConfigNode \<Longrightarrow> initial_configuration \<noteq> {} \<Longrightarrow>
    tla_reachable initial_configuration initial_value versions (tla_initial initial_value versions)"
| advance: "tla_reachable initial_configuration initial_value versions s \<Longrightarrow> enabled s a \<Longrightarrow>
    tla_reachable
        initial_configuration
        initial_value
        versions
        (execute initial_configuration initial_value s a)"

definition tla_next :: "config \<Rightarrow> 'v \<Rightarrow> 'v tla_state \<Rightarrow> 'v tla_state \<Rightarrow> bool" where
  "tla_next initial_configuration initial_value state next_state \<longleftrightarrow>
    (\<exists>action. enabled state action
              \<and> next_state = execute initial_configuration initial_value state action)"

end
