`^\Large\bf
TLA+ Model of an improved Zen consensus algorithm ^'
-------------------------------------------------------------------------------------

-------------------------------- MODULE zen -----------------------------------------
\* Imported modules used in this specification
EXTENDS Naturals, FiniteSets, Sequences, TLC

----

\* `^\Large\bf Constants ^'

\* The specification first defines the constants of the model, which amount to values or sets of
\* values that are fixed.

\* Set of node ids (all master-eligible nodes)
CONSTANTS Nodes \* TODO need to model this not being a fixed set.

\* The constant "Nil" denotes a place-holder for a non-existing value
CONSTANTS Nil

\* RPC message types
CONSTANTS
  Ping,
  Join, \* only request is modeled
  AppendEntries,
  Apply \* only request is modeled

CONSTANTS
  Pinging, \* initial state, pinging is done in this state
  Become_Follower, \* pinging established another node should be master, send join request to that node
  Follower, \* node succefully joined a cluster
  Become_Master, \* pinging established this node should be master, wait for joins
  Master \* node successfully became the master (received enough joins and starts publishing CS)

----

\* `^\Large\bf Variables ^'

\* The following describes the variable state of the model.

\* Set of in-flight requests and responses sent between nodes.
VARIABLE messages

\* For simplicity we assume that each cluster state update chooses a new unique value to be added
\* to the cluster state. This allows us to check that nodes have a consistent view on CS updates.
VARIABLE nextUUID

\* The following variables capture state on a per-node basis (maps with domain Nodes).
VARIABLE discoPhase \* map from Nodes to {Pinging, Become_Follower, Follower, Become_Master, Master}

(*
  cluster state: record containing the following fields:
    nodes: subset of nodes that are part of cluster,
    master: the current master of the cluster (either a node id or Nil)
    term: the term with which this CS was published - TODO not sure this is
          well-defined. If a master fails having partially published a CS then
          the new master will publish the same CS in a later term.
    version: the version of the CS, incremented on each update
    data: the content of the cluster state (sequence of client events, which is just a unique number assigned on each new client request) 
*)
VARIABLE discoState \* persisted cluster state, used by disco module, persisted whenever updated
VARIABLE term \* used by disco module, persisted
(* TODO ISTR it's useful to split this up as it is a bit overloaded - it's
useful to have multiple term variables to capture all the different meanings.
For instance I count 5 different per-node term variables in the ZCP impl -
they're mostly either unused or equal, but they can deviate in interesting ways
when things are going wrong. *)

VARIABLE appliedState \* state visible to the other modules on the node

----

\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y 

\* Remove request from the set of messages and add response instead
Reply(response, request) == messages' = {response} \cup (messages \ {request})

\* minimum_master_nodes configured to majority of nodes
MinMasterNodes == (Cardinality(Nodes) \div 2) + 1

\* initial cluster state for node n
InitialClusterState(n) == [nodes   |-> {n},
                           master  |-> Nil,
                           term    |-> 0,
                           version |-> 0,
                           data    |-> << >>]

Init == /\ messages       = {}
        /\ nextUUID       = 1
        /\ discoState     = [n \in Nodes |-> InitialClusterState(n)]
        /\ appliedState   = discoState
        /\ discoPhase     = [n \in Nodes |-> Pinging]
        /\ term           = [n \in Nodes |-> 0]

SendPingRequest(n) ==
  /\ discoPhase[n] = Pinging \* only send pings when in Pinging mode
  /\ LET
       \* send pings to all the nodes (except self), we can still decide later not to act on
       \* some of the ping requests/responses
       pings == {([method  |-> Ping,
                   request |-> TRUE,
                   source  |-> n,
                   dest    |-> on,
                   term    |-> term[n]]) : on \in (Nodes \ {n})} \* broadcast term so that we can disrupt a master/follower with a lower term
      \* TODO shouldn't be able to unilaterally disrupt a master, it should require a quorum. However,
      \* if a master sees a Ping request with a greater term then it should itself start a yet-higher term
      \* or else there'll be a node that can't accept any of the master's AppendEntries requests.
      \* Not sure this can actually happen - we don't increment our term until we've received a quorum
      \* of Join responses, so if we exceed the master term then it's already dead.
     IN
       /\ messages' = messages \cup pings
       /\ UNCHANGED <<nextUUID, discoState, appliedState, term, discoPhase>>

HandlePingRequest(n, m) ==
  /\ m.method = Ping
  /\ m.request = TRUE
  /\ IF discoPhase /= Pinging /\ m.term > term[n]
     THEN
       /\ term' = [term EXCEPT ![n] = m.term]
       /\ discoPhase' = [discoPhase EXCEPT ![n] = Pinging] \* revert to Pinging state (maybe we could just do this here if we are Master or Follower, but not when Become_Master or Become_Follower)
     ELSE
       UNCHANGED <<term, discoPhase>>
  /\ LET
       \* use primed variables of discoPhase and term as they might have been modified by the conjunction above
       response == [method  |-> Ping,
                    request |-> FALSE,
                    source  |-> n,
                    dest    |-> m.source,
                    master  |-> IF discoPhase'[n] \in {Master, Follower} THEN discoState[n].master ELSE Nil,
                    version |-> discoState[n].version,
                    csTerm  |-> discoState[n].term, \* cluster state term
                    term    |-> term'[n], \* node term
                    phase   |-> discoPhase'[n]]
     IN
       Reply(response, m)
  /\ UNCHANGED <<nextUUID, discoState, appliedState>>

\* when node is in pinging mode, check ping responses to determine if it should become master or follower
HandlePingResponses(n) ==
  /\ discoPhase[n] = Pinging
  /\ LET
       pingResponses == { ms \in messages : ms.method = Ping /\ ms.request = FALSE /\ ms.dest = n }
          \* `messages` is the set of _sent_ messages, but here they're being treated as _received_ ones.
          \* This is ok, however, because of the `DropResponse` action which models dropped messages.
       activeMastersWithAcceptableTerm == { pr \in pingResponses : pr.master \notin {Nil, n} /\ pr.term >= term[n] }
       masterCandidates == pingResponses \cup
                           {[source |-> n,
                             version |-> discoState[n].version,
                             csTerm |-> discoState[n].term,
                             term |-> term[n],
                             phase |-> discoPhase[n]]} \* add ping response for self
     IN
       IF Cardinality(activeMastersWithAcceptableTerm) > 0
       THEN
         \E masterToJoin \in activeMastersWithAcceptableTerm:
           LET
             \* send join request to master, but stay in Pinging mode (as current term is not speculative and no voting is happening)
             joinRequest == [method  |-> Join,
                             request |-> TRUE,
                             source  |-> n,
                             dest    |-> masterToJoin.master,
                             term    |-> 0] \* this join request only works if the node is already master and does not constitute a vote
           IN
             /\ messages' = (messages \ pingResponses) \cup { joinRequest }
             /\ UNCHANGED <<nextUUID, discoState, appliedState, term, discoPhase>> \* no voting necessary to join an existing master
       ELSE
         IF Cardinality({pr.source : pr \in masterCandidates}) < MinMasterNodes \* masterCandidates contains self
         THEN
           UNCHANGED <<nextUUID, discoState, appliedState, term, discoPhase, messages>> \* noop
         ELSE
           \E bestCSCandidate \in masterCandidates :
             \A otherCandidate \in masterCandidates : 
               /\ \/ bestCSCandidate.csTerm > bestCSCandidate.csTerm 
                  \/ /\ bestCSCandidate.csTerm = otherCandidate.csTerm
                     /\ bestCSCandidate.version >= otherCandidate.version
               /\ LET
                    \* choose the node with the best cluster state
                    bestCSNode == bestCSCandidate.source
                    \* choose highest term seen + 1. If node is becoming master or follower, it already has a speculative term
                    nextTerm == Max({ IF pr.phase \in {Become_Master, Become_Follower} THEN pr.term ELSE pr.term + 1 : pr \in masterCandidates })
                    joinRequest == [method  |-> Join,
                                    request |-> TRUE,
                                    source  |-> n,
                                    dest    |-> bestCSNode,
                                    term    |-> nextTerm]
                  IN
                    /\ term' = [term EXCEPT ![n] = nextTerm]
                    /\ discoPhase' = [discoPhase EXCEPT ![n] = IF bestCSNode = n THEN Become_Master ELSE Become_Follower]
                    /\ messages' = (messages \ pingResponses) \cup (IF bestCSNode = n THEN {} ELSE { joinRequest })
                    /\ UNCHANGED <<nextUUID, discoState, appliedState>>

\* node n wants to become master and checks if it has received enough joins (= votes) for its prospective term
HandleJoinRequestsToBecomeMaster(n) ==
  /\ discoPhase[n] = Become_Master
  /\ LET
       sameTermJoins == { m \in messages : m.method = Join /\ m.request /\ m.dest = n /\ m.term = term[n] }
       voteGrantingNodes == { m.source : m \in sameTermJoins }
       newState == [discoState[n] EXCEPT !.master = n, !.nodes = @ \cup voteGrantingNodes, !.term = term[n], !.version = @ + 1, !.data = Append(@, nextUUID)]
       publishRequests == { [method  |-> AppendEntries,
                             request |-> TRUE,
                             source  |-> n,
                             dest    |-> ns,
                             term    |-> term[n],
                             state   |-> newState] : ns \in (newState.nodes \ {n}) }
     IN
       /\ Cardinality(voteGrantingNodes) + 1 >= MinMasterNodes \* +1 as we don't send a join request to ourselves
       /\ discoPhase' = [discoPhase EXCEPT ![n] = Master]
       /\ discoState' = [discoState EXCEPT ![n] = newState]
       /\ nextUUID' = nextUUID + 1
       /\ messages' = (messages \ sameTermJoins) \cup publishRequests
       /\ UNCHANGED <<appliedState, term>>

\* node n is master and lets another node join
HandleJoinRequestWhenMaster(n) ==
  /\ discoPhase[n] = Master
  /\ discoState[n] = appliedState[n] \* previous round was committed
  /\ LET
       joinRequests == { m \in messages : m.method = Join /\ m.request /\ m.dest = n }
       newState == [discoState[n] EXCEPT !.master = n, !.nodes = @ \cup { m.source : m \in joinRequests }, !.term = term[n], !.version = @ + 1, !.data = Append(@, nextUUID)]
       publishRequests == { [method  |-> AppendEntries,
                             request |-> TRUE,
                             source  |-> n,
                             dest    |-> ns,
                             term    |-> term[n],
                             state   |-> newState] : ns \in (newState.nodes \ {n}) }
     IN
       /\ discoState' = [discoState EXCEPT ![n] = newState]
       /\ nextUUID' = nextUUID + 1
       /\ messages' = (messages \ joinRequests) \cup publishRequests
       /\ UNCHANGED <<appliedState, discoPhase, term>>

\* node n (which is master) instructs other nodes to apply CS
CommitState(n) ==
  LET
    publishResponses == { m \in messages :
                            /\ m.method = AppendEntries
                            /\ m.request = FALSE
                            /\ m.dest = n
                            /\ m.term = term[n] \* can only commit stuff from my term
                            /\ m.version = discoState[n].version }
    successResponses == { pr \in publishResponses : pr.success }
    applyRequests == { [method  |-> Apply,
                        request |-> TRUE,
                        source  |-> n,
                        dest    |-> ns,
                        state   |-> discoState[n]] : ns \in (discoState[n].nodes \ {n}) }
  IN
    /\ Cardinality(successResponses) + 1 >= MinMasterNodes \* +1 as we don't send publish request to ourselves
    /\ messages' = (messages \ publishResponses) \cup applyRequests
    /\ appliedState' = [appliedState EXCEPT ![n] = discoState[n]]
    /\ UNCHANGED <<nextUUID, discoPhase, discoState, term>>


ClientRequest(n) ==
  /\ discoPhase[n] = Master
  /\ discoState[n] = appliedState[n] \* previous round was committed
  /\ LET
       newState == [discoState[n] EXCEPT !.data = Append(@, nextUUID), !.version = @ + 1]
       publishRequests == { [request |-> TRUE,
                             method  |-> AppendEntries,
                             source  |-> n,
                             dest    |-> ns,
                             term    |-> term[n],
                             state   |-> newState] : ns \in (newState.nodes \ {n}) }
     IN
       /\ nextUUID' = nextUUID + 1
       /\ discoState' = [discoState EXCEPT ![n] = newState]
       /\ messages' = messages \cup publishRequests
       /\ UNCHANGED <<appliedState, discoPhase, term>>


HandleAppendEntriesRequest(n, m) ==
  /\ m.method = AppendEntries
  /\ m.request = TRUE
  /\ IF m.term > term[n]
     THEN
       /\ term' = [term EXCEPT ![n] = m.term]
       /\ discoPhase' = [discoPhase EXCEPT ![n] = Follower]
     ELSE
       IF m.term = term[n] /\ discoPhase[n] \in {Pinging, Become_Master, Become_Follower} /\ Assert(discoPhase[n] /= Master, "two masters for same term")
       THEN
         /\ discoPhase' = [discoPhase EXCEPT ![n] = Follower]
         /\ UNCHANGED <<term>>
       ELSE
         UNCHANGED <<term, discoPhase>>
  /\ LET
       betterCS == \/ m.state.term > discoState[n].term
                   \/ /\ m.state.term = discoState[n].term
                      /\ m.state.version > discoState[n].version
       response == [method  |-> AppendEntries,
                    request |-> FALSE,
                    source  |-> n,
                    dest    |-> m.source,
                    success |-> TRUE,
                    term    |-> term'[n],
                    version |-> m.state.version]
     IN
       IF
         /\ m.term = term'[n] \* if incoming term was higher, we have adapted to that term
         /\ discoPhase'[n] = Follower \* we should have converted to follower if incoming term was greater to our term or (equal to our term and we are not Master for that term)
         /\ betterCS
       THEN
         /\ discoState' = [discoState EXCEPT ![n] = m.state]
         /\ Reply(response, m)
         /\ UNCHANGED <<appliedState, nextUUID>>
       ELSE
         /\ Reply([response EXCEPT !.success = FALSE], m)
         /\ UNCHANGED <<appliedState, discoState, nextUUID>>


\* apply committed CS to node
HandleApplyRequest(n, m) ==
  /\ m.method = Apply
  /\ m.request = TRUE
  /\ appliedState' = [appliedState EXCEPT ![n] = IF m.state.version > @.version THEN m.state ELSE @]
  /\ Assert(m.state.version > appliedState[n].version => m.state.term >= appliedState[n].term, "seen committed CS with higher version but lower term")
  /\ messages' = messages \ {m}
  /\ UNCHANGED <<discoState, nextUUID, discoPhase, term>>

\* time out and go back to pinging (e.g. node/master fault detection kicks in or waiting on ping responses / append entries responses times out)
Timeout(n) ==
  /\ discoPhase' = [discoPhase EXCEPT ![n] = Pinging]
  /\ UNCHANGED <<nextUUID, discoState, appliedState, messages, term>>

\* drop request
DropRequest(m) ==
  /\ m.request = TRUE
  /\ messages' = messages \ {m}
  /\ UNCHANGED <<nextUUID, discoState, appliedState, discoPhase, term>>

\* drop response
DropResponse(m) ==
  /\ m.request = FALSE
  /\ messages' = messages \ {m}
  /\ UNCHANGED <<nextUUID, discoState, appliedState, discoPhase, term>>

DropMessagesExcept(sm) ==
  /\ messages' = sm
  /\ UNCHANGED <<nextUUID, discoState, appliedState, discoPhase, term>>

\* handle response with higher term than we currently have
HandleResponseWithHigherTerm(n, m) ==
  /\ m.request = FALSE
  /\ m.method /= Ping \* term in pinging response could be speculative, ignore it (we actually can look at discoPhase to decide if it is speculative or not)
  /\ m.term > term[n]
  /\ messages' = messages \ {m}
  /\ term' = [term EXCEPT ![n] = m.term]
  /\ discoPhase' = [discoPhase EXCEPT ![n] = Pinging] \* revert to Pinging state
  /\ UNCHANGED <<nextUUID, discoState, appliedState>>

\* crash/restart node n (loses ephemeral state)
RestartNode(n) ==
  /\ discoPhase' = [discoPhase EXCEPT ![n] = Pinging]
  /\ discoState' = [discoState EXCEPT ![n] = [@ EXCEPT !.master = Nil, !.nodes = {n}]]
  /\ appliedState' = [appliedState EXCEPT ![n] = InitialClusterState(n)]
  /\ UNCHANGED <<nextUUID, messages, term>>

\* next-step relation
Next ==
  \/ \E n \in Nodes : SendPingRequest(n)
  \/ \E m \in messages : HandlePingRequest(m.dest, m)
  \/ \E n \in Nodes : HandlePingResponses(n)
  \/ \E n \in Nodes : HandleJoinRequestsToBecomeMaster(n)
  \/ \E n \in Nodes : HandleJoinRequestWhenMaster(n)
  \/ \E n \in Nodes : CommitState(n)
  \/ \E n \in Nodes : ClientRequest(n)
  \/ \E n \in Nodes : Timeout(n)
  \/ \E m \in messages : HandleAppendEntriesRequest(m.dest, m)
  \/ \E m \in messages : HandleApplyRequest(m.dest, m)
  \/ \E m \in messages : HandleResponseWithHigherTerm(m.dest, m)
  \/ \E m \in messages : DropRequest(m)
  \/ \E m \in messages : DropResponse(m)
  \* \/ \E sm \in SUBSET messages: DropMessagesExcept(sm)
  \/ \E n \in Nodes : RestartNode(n)

----


\* returns true if seq1 is a prefix of seq2
PrefixOf(seq1, seq2) ==
  LET
    len1 == Len(seq1)
    len2 == Len(seq2)
  IN
    len1 <= len2 /\ seq1 = SubSeq(seq2, 1, len1)

\* main invariant:
\* if node n1 has an applied cluster state with version v1 and node n2 has an applied cluster state with version v2:
\*   if v1 <= v2: state1.data must be a prefix of state2.data
\* in particular, when both have the same version, the content must be the same
StateMachineSafety ==
  \A n1, n2 \in Nodes :
    LET
      state1 == appliedState[n1]
      state2 == appliedState[n2]
    IN
      state1.version <= state2.version => PrefixOf(state1.data, state2.data)

OneMasterPerTerm ==
  \A n1, n2 \in Nodes :
    n1 /= n2 /\ discoPhase[n1] = Master /\ discoPhase[n2] = Master => term[n1] /= term[n2]

LogMatching ==
  \A n1, n2 \in Nodes :
    /\ discoState[n1].term = discoState[n2].term
    /\ discoState[n1].version = discoState[n2].version
    => discoState[n1].data = discoState[n2].data

NodeTermIsHigherThanCSTerm ==
  \A n \in Nodes : term[n] >= discoState[n].term


\* State-exploration limits
StateConstraint ==
  /\ nextUUID <= 4
  /\ \A n \in Nodes: term[n] <= 3
  /\ Cardinality(messages) <= 4
  /\ Cardinality({ m \in messages : m.method = Ping}) <= 3

====================================================================================================
