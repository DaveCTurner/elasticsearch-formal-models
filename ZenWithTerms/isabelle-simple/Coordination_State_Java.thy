theory Coordination_State_Java
  imports Coordination_State_Base
begin

section \<open>Method-boundary model of CoordinationState.java\<close>

text \<open>
  A transcription of \<open>CoordinationState.java\<close> at the boundaries of its method
  calls, each of which is assumed to run to completion without interleaving. Each node has two
  states.

  \<^item> \<open>java_memory\<close> is its in-memory state: its \<open>CoordinationState\<close> and the \<open>PersistedState\<close> that
    this state reads and writes (see \<open>Coordination_State_Base\<close>). A vote collection is
    represented by the node IDs that it contains. The \<open>Join\<close> objects that it also stores, and the
    boolean results of \<open>addVote\<close> and \<open>handleJoin\<close>, do not affect the protocol state.
  \<^item> \<open>java_disk\<close> is what the node has written to disk. A master-eligible node uses a
    \<open>LucenePersistedState\<close>, which writes every change to disk before it returns. A data node
    that is not master-eligible uses an \<open>AsyncPersistedState\<close>, whose worker writes the term and
    the last accepted state later. A coordinating-only node uses an \<open>InMemoryPersistedState\<close>,
    and writes nothing. A restart reads the state back from disk.

  The messages set contains the messages that calls have returned and that are therefore available for
  delivery. A returned publication or commit is made available to every node, as in \<open>Next\<close>.
\<close>

record 'v java_state =
  java_memory :: "node \<Rightarrow> 'v node_memory_state"
  java_disk :: "node \<Rightarrow> 'v node_disk_state"
  java_messages :: "'v message set"

text \<open>
  One action for each call of \<open>CoordinationState\<close> from its caller, one for a restart, and
  one for each write of the worker of an \<open>AsyncPersistedState\<close>. Each takes the node that makes
  the call, then the arguments of the call, then the further arguments that the caller derives
  from them.

  \<^item> \<open>Java_Set_Initial_State node initial_position new_value initial_accepted_config
    initial_committed_config\<close>: \<open>setInitialState\<close> with an initial state that has position
    \<open>initial_position\<close>, the value \<open>new_value\<close>, and the given last accepted and last committed
    configurations.
  \<^item> \<open>Java_Handle_Start_Join voter candidate new_term\<close>: \<open>handleStartJoin\<close> for a
    \<open>StartJoinRequest\<close> that makes \<open>voter\<close> vote for \<open>candidate\<close> in \<open>new_term\<close>.
  \<^item> \<open>Java_Handle_Join voter voter_role candidate join_term voter_position\<close>: \<open>handleJoin\<close> on
    \<open>candidate\<close> for the \<open>Join\<close> from \<open>voter\<close>, which was sent while it had role \<open>voter_role\<close>, in
    \<open>join_term\<close> with last accepted position \<open>voter_position\<close>.
  \<^item> \<open>Java_Handle_Client_Value leader new_term version new_value new_config previous_config\<close>:
    \<open>handleClientValue\<close> for the cluster state with the given term, version, \<open>new_value\<close>, last
    accepted configuration and last committed configuration.
  \<^item> \<open>Java_Handle_Publish_Request node request new_value\<close>: \<open>handlePublishRequest\<close>.
  \<^item> \<open>Java_Handle_Publish_Response voter voter_role leader position\<close>: \<open>handlePublishResponse\<close> on
    \<open>leader\<close> for the \<open>PublishResponse\<close> with position \<open>position\<close> from \<open>voter\<close>, which was sent
    while it had role \<open>voter_role\<close>.
  \<^item> \<open>Java_Handle_Commit node leader position\<close>: \<open>handleCommit\<close> on \<open>node\<close> for the
    \<open>ApplyCommitRequest\<close> with position \<open>position\<close> from \<open>leader\<close>.
  \<^item> \<open>Java_Restart node new_role new_value\<close>: a new incarnation of \<open>node\<close> with the role
    \<open>new_role\<close>, in which \<open>CoordinationState\<close> is rebuilt from the persisted state. See
    \<open>java_restart\<close>.
  \<^item> \<open>Java_Persist_Term node\<close> and \<open>Java_Persist_State node\<close>: a write of the worker of
    \<open>node\<close>'s \<open>AsyncPersistedState\<close>.
\<close>

datatype 'v java_action =
    Java_Set_Initial_State node position 'v config config
  | Java_Handle_Start_Join node node nat
  | Java_Handle_Join node role node nat position
  | Java_Handle_Client_Value node nat nat 'v config config
  | Java_Handle_Publish_Request node publication 'v
  | Java_Handle_Publish_Response node role node position
  | Java_Handle_Commit node node position
  | Java_Restart node role 'v
  | Java_Persist_Term node
  | Java_Persist_State node

text \<open>
  \<open>VotingConfiguration.hasQuorum\<close> counts the configuration's nodes that have
  voted and compares twice that count with the size of the configuration, using
  32-bit signed integers. The election and publish quorums are those of the
  default \<open>ElectionStrategy\<close>, which adds no further constraints
  (\<open>satisfiesAdditionalQuorumConstraints\<close> holds).
\<close>

definition signed_int :: "int \<Rightarrow> int" where
  "signed_int number = (number + 2147483648) mod 4294967296 - 2147483648"

definition has_quorum :: "config \<Rightarrow> node set \<Rightarrow> bool" where
  "has_quorum configuration votes \<longleftrightarrow>
    signed_int (int (card (voting_nodes_of configuration))) < signed_int (2 * int (card (voting_nodes_of configuration \<inter> votes)))"

definition java_is_election_quorum :: "'v node_memory_state \<Rightarrow> node set \<Rightarrow> bool" where
  "java_is_election_quorum node_memory_state votes \<longleftrightarrow>
    has_quorum (last_committed_configuration node_memory_state) votes
    \<and> has_quorum (last_accepted_configuration node_memory_state) votes"

definition java_is_publish_quorum :: "'v node_memory_state \<Rightarrow> node set \<Rightarrow> bool" where
  "java_is_publish_quorum node_memory_state votes \<longleftrightarrow>
    has_quorum (last_committed_configuration node_memory_state) votes
    \<and> has_quorum (last_published_configuration node_memory_state) votes"

text \<open>
  A restart with the given new role. The node's disk, and, for a node that is master-eligible
  or holds data, its in-memory state, are read back from disk. The state is the initial value,
  and the zero position, if the disk is empty. A coordinating-only node starts with an empty
  in-memory state, and where its persisted term is zero it replaces the state on disk by an
  empty state: this is what
  \<open>PersistedClusterStateService.persistNodeIdWithoutOverwritingState\<close> does.
\<close>

definition empty_disk :: "'v \<Rightarrow> 'v node_disk_state" where
  "empty_disk initial_value =
    \<lparr>
      disk_term                    = 0,
      disk_position                = position_zero,
      disk_value                   = initial_value,
      disk_accepted_configuration  = {},
      disk_committed_configuration = {}
    \<rparr>"

definition memory_of_disk :: "role \<Rightarrow> 'v node_disk_state \<Rightarrow> 'v node_memory_state" where
  "memory_of_disk new_role node_disk_state =
    \<lparr>
      current_term                   = disk_term node_disk_state,
      last_accepted_position         = disk_position node_disk_state,
      last_accepted_value            = disk_value node_disk_state,
      last_accepted_configuration    = disk_accepted_configuration node_disk_state,
      last_committed_configuration   = disk_committed_configuration node_disk_state,
      join_votes                     = {},
      started_join_since_last_reboot = False,
      election_won                   = False,
      last_published_version         = 0,
      last_published_configuration   = disk_accepted_configuration node_disk_state,
      publish_votes                  = {},
      node_role                      = new_role,
      term_queued                    = False,
      state_queued                   = False
    \<rparr>"

text \<open>
  The only ways that a call changes the state. \<open>java_put\<close>: if the condition holds the node's
  in-memory state is replaced and the messages are added to the messages set. Otherwise nothing
  changes: this is a call that \<open>CoordinationState\<close> rejects with a
  \<open>CoordinationStateRejectedException\<close>. A master-eligible node's persisted state writes through
  to the disk before the call returns. Each call below passes the conditions that it checks, which
  exclude the Java assertions. The caller contract states those assertions that constrain the
  caller. \<open>java_persist\<close> is a write of the worker of an \<open>AsyncPersistedState\<close>: it changes the
  disk and the flags of the in-memory state.
\<close>

definition java_put ::
  "'v java_state \<Rightarrow> node \<Rightarrow> bool \<Rightarrow> 'v node_memory_state \<Rightarrow> 'v message set \<Rightarrow> 'v java_state" where
  "java_put state node condition new_node_memory_state new_messages =
    (if condition
     then state\<lparr>
       java_memory   := (java_memory state)(node := new_node_memory_state),
       java_disk     := (if node_role new_node_memory_state = Master_Eligible
                         then (java_disk state)(node := disk_of new_node_memory_state)
                         else java_disk state),
       java_messages := java_messages state \<union> new_messages
     \<rparr>
     else state)"

lemma java_put_changed:
  "java_put state node condition new_node_memory_state new_messages \<noteq> state \<Longrightarrow> condition"
  by (cases condition) (simp_all add: java_put_def)

definition java_persist ::
  "'v java_state \<Rightarrow> node \<Rightarrow> bool \<Rightarrow> 'v node_memory_state \<Rightarrow> 'v node_disk_state \<Rightarrow> 'v java_state" where
  "java_persist state node condition new_node_memory_state new_node_disk_state =
    (if condition
     then state\<lparr>
       java_memory := (java_memory state)(node := new_node_memory_state),
       java_disk   := (java_disk state)(node := new_node_disk_state)
     \<rparr>
     else state)"

lemma java_persist_changed:
  "java_persist state node condition new_node_memory_state new_node_disk_state \<noteq> state \<Longrightarrow> condition"
  by (cases condition) (simp_all add: java_persist_def)

definition java_initial :: "'v \<Rightarrow> (node \<Rightarrow> nat) \<Rightarrow> 'v java_state" where
  "java_initial initial_value versions =
    \<lparr>
      java_memory   = (\<lambda>node.
          \<lparr>
            current_term                   = 0,
            last_accepted_position         = \<lparr>position_term = 0, position_version = versions node\<rparr>,
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
          \<rparr>),
      java_disk     = (\<lambda>node.
          \<lparr>
            disk_term                    = 0,
            disk_position                = \<lparr>position_term = 0, position_version = versions node\<rparr>,
            disk_value                   = initial_value,
            disk_accepted_configuration  = {},
            disk_committed_configuration = {}
          \<rparr>),
      java_messages = {}
    \<rparr>"

text \<open>
  Each call, with the condition that it checks, the new state of the node that it updates and the
  messages that it returns. Persistence failures, external calls and scheduling are governed by
  the caller contract below. A vote is counted only if its sender is master-eligible, as in
  \<open>VoteCollection.addVote\<close>.
\<close>

fun java_call :: "'v java_state \<Rightarrow> 'v java_action \<Rightarrow> 'v java_state" where
  "java_call
       state
       (Java_Set_Initial_State
            node
            initial_position
            new_value
            initial_accepted_config
            initial_committed_config)
   =
    java_put
        state
        node
        (last_accepted_configuration (java_memory state node) = {})
        ((java_memory state node)\<lparr>
          last_accepted_position       := initial_position,
          last_accepted_value          := new_value,
          last_accepted_configuration  := initial_accepted_config,
          last_committed_configuration := initial_committed_config
        \<rparr>)
        {}"
| "java_call state (Java_Handle_Start_Join voter candidate new_term) =
    (let voter_state = java_memory state voter
     in java_put
            state
            voter
            (current_term voter_state < new_term)
            (queue_term (voter_state\<lparr>
              current_term                   := new_term,
              join_votes                     := {},
              election_won                   := False,
              last_published_version         := 0,
              last_published_configuration   := last_accepted_configuration voter_state,
              publish_votes                  := {},
              started_join_since_last_reboot := True
            \<rparr>))
            {Join_Msg
                 voter
                 (node_role voter_state)
                 candidate
                 new_term
                 (last_accepted_position voter_state)})"

| "java_call state (Java_Handle_Join voter voter_role candidate join_term voter_position) =
    (let candidate_state = java_memory state candidate;
         new_votes = (if voter_role = Master_Eligible
                      then insert voter (join_votes candidate_state)
                      else join_votes candidate_state);
         won = java_is_election_quorum candidate_state new_votes
     in java_put
            state
            candidate
            (join_term = current_term candidate_state
             \<and> started_join_since_last_reboot candidate_state
             \<and> voter_position \<le> last_accepted_position candidate_state
             \<and> last_accepted_configuration candidate_state \<noteq> {})
            (candidate_state\<lparr>
              join_votes             := new_votes,
              election_won           := won,
              last_published_version := (if won \<and> \<not> election_won candidate_state
                then position_version (last_accepted_position candidate_state)
                else last_published_version candidate_state)
            \<rparr>)
            {})"
| "java_call
       state
       (Java_Handle_Client_Value leader new_term version new_value new_config previous_config)
   =
    (let leader_state = java_memory state leader;
         request = \<lparr>
           publication_position        = \<lparr>position_term = new_term, position_version = version\<rparr>,
           publication_owner           = leader,
           publication_config          = new_config,
           publication_previous_config = previous_config
         \<rparr>
     in java_put
            state
            leader
            (election_won leader_state
             \<and> last_published_version leader_state = position_version (last_accepted_position leader_state)
             \<and> new_term = current_term leader_state
             \<and> last_published_version leader_state < version
             \<and> \<not> (new_config \<noteq> last_accepted_configuration leader_state
                  \<and> last_committed_configuration leader_state \<noteq> last_accepted_configuration leader_state)
             \<and> has_quorum new_config (join_votes leader_state))
            (leader_state\<lparr>
              last_published_version       := version,
              last_published_configuration := new_config,
              publish_votes                := {}
            \<rparr>)
            {Publish_Msg destination request new_value | destination. True})"
| "java_call state (Java_Handle_Publish_Request node request new_value) =
    (let node_memory_state = java_memory state node
     in java_put
            state
            node
            (position_term (publication_position request) = current_term node_memory_state
             \<and> \<not> (position_term (publication_position request) = position_term (last_accepted_position node_memory_state)
                  \<and> position_version (publication_position request) \<le> position_version (last_accepted_position node_memory_state)))
            (queue_state (node_memory_state\<lparr>
              last_accepted_position       := publication_position request,
              last_accepted_value          := new_value,
              last_accepted_configuration  := publication_config request,
              last_committed_configuration := publication_previous_config request
            \<rparr>))
            {Response_Msg
                 node
                 (node_role node_memory_state)
                 (publication_owner request)
                 (publication_position request)})"
| "java_call state (Java_Handle_Publish_Response voter voter_role leader position) =
    (let leader_state = java_memory state leader;
         new_votes = (if voter_role = Master_Eligible
                      then insert voter (publish_votes leader_state)
                      else publish_votes leader_state)
     in java_put
            state
            leader
            (election_won leader_state \<and> position = last_published_position leader_state)
            (leader_state\<lparr>publish_votes := new_votes\<rparr>)
            (if java_is_publish_quorum leader_state new_votes
             then {Commit_Msg leader destination position | destination. True}
             else {}))"
| "java_call state (Java_Handle_Commit node leader position) =
    (let node_memory_state = java_memory state node
     in java_put
            state
            node
            (position_term position = current_term node_memory_state
             \<and> position = last_accepted_position node_memory_state)
            (queue_state (node_memory_state\<lparr>last_committed_configuration := last_accepted_configuration node_memory_state\<rparr>))
            {})"
| "java_call state (Java_Restart node new_role new_value) =
    (let new_node_disk_state = (if disk_term (java_disk state node) = 0
                                   \<and> new_role = Coordinating_Only
                     then empty_disk new_value
                     else java_disk state node)
     in state\<lparr>
       java_memory := (java_memory state)
         (node := memory_of_disk
                      new_role
                      (if new_role = Coordinating_Only then empty_disk new_value else new_node_disk_state)),
       java_disk   := (java_disk state)(node := new_node_disk_state)
     \<rparr>)"
(* TODO This doesn't quite capture AsyncPersistedState's worker, which claims both queued
   flags and reads the current term and last accepted state together, under the mutex, and then
   writes the term followed by the state. Here each write reads the in-memory value when it
   happens, so it can persist a newer value than the one the worker claimed. The
   term-before-state ordering is already enforced by the guard of Java_Persist_State. *)
| "java_call state (Java_Persist_Term node) =
    (let node_memory_state = java_memory state node
     in java_persist
            state
            node
            (node_role node_memory_state = Data_Only
             \<and> term_queued node_memory_state
             \<and> disk_term (java_disk state node) < current_term node_memory_state)
            (node_memory_state\<lparr>term_queued := False\<rparr>)
            ((java_disk state node)\<lparr>disk_term := current_term node_memory_state\<rparr>))"
| "java_call state (Java_Persist_State node) =
    (let node_memory_state = java_memory state node
     in java_persist
            state
            node
            (node_role node_memory_state = Data_Only
             \<and> state_queued node_memory_state
             \<and> disk_term (java_disk state node) = position_term (last_accepted_position node_memory_state))
            (node_memory_state\<lparr>state_queued := False\<rparr>)
            ((java_disk state node)\<lparr>
              disk_position                := last_accepted_position node_memory_state,
              disk_value                   := last_accepted_value node_memory_state,
              disk_accepted_configuration  := stale_config,
              disk_committed_configuration := stale_config
            \<rparr>))"

section \<open>Caller contract\<close>

text \<open>
  The class does not enforce everything that it relies on. The caller must
  ensure the following whenever a call changes the state. A call that changes nothing is always
  permitted, whether the class rejects it or not.

  \<^item> Configurations are made of node IDs (the stale marker excepted, and only the
    configurations that the caller supplies must be free of it). A node can change its roles across
    restarts (\<open>Java_Restart\<close>), so any ID may be master-eligible in some
    incarnation and there is no separate set of eligible IDs.
  \<^item> The \<open>Coordinator\<close> asserts that only a master-eligible node runs \<open>setInitialState\<close>,
    \<open>handleJoin\<close>, \<open>handleClientValue\<close> and \<open>handlePublishResponse\<close>. A node of any role runs
    \<open>handleStartJoin\<close>, \<open>handlePublishRequest\<close> and \<open>handleCommit\<close>. The worker of an
    \<open>AsyncPersistedState\<close> only exists on a data node that is not master-eligible.
  \<^item> Bootstrap data is shared: the initial state has term zero, the same value and
    configuration at every node, and is set on a node that has not otherwise
    been used (the assertions of \<open>setInitialState\<close>). The configurations in
    published states contain no stale marker, and a leader's published state
    has the leader's last committed configuration (an assertion of
    \<open>handleClientValue\<close>).
  \<^item> Inputs are authentic: a join, publish request, publish response or commit is
    only supplied if the corresponding message was returned by an earlier call
    (it is in the messages).
  \<^item> A commit that reaches a leader late, for a version other than its last
    published one, is only supplied if it would change nothing, because the leader's
    last committed configuration already equals its last accepted configuration.
    Otherwise the caller must deliver the leader's own commit before it starts
    another publication. Without this, \<open>handleCommit\<close> would make a configuration
    committed that no step of the TLA+ translation commits.
\<close>

fun caller_contract ::
  "config \<Rightarrow> 'v \<Rightarrow> 'v java_state \<Rightarrow> 'v java_action \<Rightarrow> bool" where
  "caller_contract
       initial_configuration
       initial_value
       state
       (Java_Set_Initial_State
            node
            initial_position
            new_value
            initial_accepted_config
            initial_committed_config)
   =
    (let node_memory_state = java_memory state node
     in node_role node_memory_state = Master_Eligible
        \<and> initial_position = last_accepted_position node_memory_state
        \<and> position_term initial_position = 0
        \<and> initial_accepted_config = initial_configuration
        \<and> initial_committed_config = initial_configuration
        \<and> new_value = initial_value
        \<and> last_committed_configuration node_memory_state = {}
        \<and> last_published_version node_memory_state = 0
        \<and> last_published_configuration node_memory_state = {}
        \<and> \<not> election_won node_memory_state
        \<and> join_votes node_memory_state = {}
        \<and> publish_votes node_memory_state = {})"
| "caller_contract
       initial_configuration
       initial_value
       state
       (Java_Handle_Start_Join voter candidate new_term)
   =
    True"
| "caller_contract
       initial_configuration
       initial_value
       state
       (Java_Handle_Join voter voter_role candidate join_term voter_position)
   =
    (node_role (java_memory state candidate) = Master_Eligible
     \<and> Join_Msg voter voter_role candidate join_term voter_position \<in> java_messages state)"
| "caller_contract
       initial_configuration
       initial_value
       state
       (Java_Handle_Client_Value leader new_term version new_value new_config previous_config)
   =
    (node_role (java_memory state leader) = Master_Eligible
     \<and> new_config \<subseteq> range ConfigNode
     \<and> previous_config = last_committed_configuration (java_memory state leader))"
| "caller_contract
       initial_configuration
       initial_value
       state
       (Java_Handle_Publish_Request node request new_value)
   =
    (Publish_Msg node request new_value \<in> java_messages state
     \<and> publication_config request \<subseteq> range ConfigNode
     \<and> publication_previous_config request \<subseteq> range ConfigNode)"
| "caller_contract
       initial_configuration
       initial_value
       state
       (Java_Handle_Publish_Response voter voter_role leader position)
   =
    (node_role (java_memory state leader) = Master_Eligible
     \<and> Response_Msg voter voter_role leader position \<in> java_messages state)"
| "caller_contract
       initial_configuration
       initial_value
       state
       (Java_Handle_Commit node leader position)
   =
    (let node_memory_state = java_memory state node
     in Commit_Msg leader node position \<in> java_messages state
        \<and> (election_won node_memory_state
           \<and> position_version position \<noteq> last_published_version node_memory_state \<longrightarrow>
            last_committed_configuration node_memory_state = last_accepted_configuration node_memory_state))"
| "caller_contract initial_configuration initial_value state (Java_Restart node new_role new_value)
   =
    (new_value = initial_value)"
| "caller_contract initial_configuration initial_value state (Java_Persist_Term node) = True"
| "caller_contract initial_configuration initial_value state (Java_Persist_State node) = True"

text \<open>
  The reachable states are those of a caller that respects the contract. A call that
  changes nothing is always permitted. There are fewer than 2^30 nodes (\<open>node_bound\<close>), so that the
  32-bit arithmetic of \<open>has_quorum\<close> cannot overflow.
\<close>

inductive java_reachable ::
  "config \<Rightarrow> 'v \<Rightarrow>
    (node \<Rightarrow> nat) \<Rightarrow> 'v java_state \<Rightarrow> bool"
  for initial_configuration initial_value versions where
  init: "initial_configuration \<subseteq> range ConfigNode \<Longrightarrow> initial_configuration \<noteq> {} \<Longrightarrow>
    java_reachable
        initial_configuration
        initial_value
        versions
        (java_initial initial_value versions)"
| advance: "java_reachable initial_configuration initial_value versions state \<Longrightarrow>
    (java_call state action \<noteq> state \<longrightarrow> caller_contract
                                          initial_configuration
                                          initial_value
                                          state
                                          action) \<Longrightarrow>
    java_reachable initial_configuration initial_value versions (java_call state action)"

end
