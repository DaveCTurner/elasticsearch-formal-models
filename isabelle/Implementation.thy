section \<open>Implementation\<close>

text \<open>This section presents the implementation of the algorithm.\<close>

theory Implementation
  imports Preliminaries
begin

text \<open>Each node holds the following local data.\<close>

record NodeData =
  currentNode :: Node (* identity of this node *)
  firstUncommittedSlot :: nat (* all slots strictly below this one are committed *)
  currentEra :: Era (* era of the firstUncommittedSlot slot *)
  currentConfiguration :: Configuration (* configuration of the currentEra *)
  currentClusterState :: ClusterState (* last-committed cluster state *)
  (* acceptor data *)
  lastAccepted :: PreviousPublishResponse (* term and value that were last accepted in this slot, if any *)
  currentTerm :: Term (* greatest term for which a promise was sent, and term of votes being collected *)
  (* election data *)
  electionVotes :: "Node set" (* set of nodes that have sent a JoinRequest for the current currentTerm *)
  electionWon :: bool
  electionValue :: PreviousPublishResponse
  (* learner data *)
  applyRequested :: bool (* whether an PublishRequest has been sent with slot=firstUncommittedSlot and term=currentTerm *)
  applyVotes :: "Node set"

definition lastAcceptedGreaterTermThan :: "Term \<Rightarrow> NodeData \<Rightarrow> bool"
  where
    "lastAcceptedGreaterTermThan t nd \<equiv> case lastAccepted nd of
      NoPublishResponseSent \<Rightarrow> False
      | PublishResponseSent t' _ \<Rightarrow> t' < t"

definition isQuorum :: "NodeData \<Rightarrow> Node set \<Rightarrow> bool"
  where "isQuorum nd q \<equiv> q \<in> Rep_Configuration (currentConfiguration nd)"

text \<open>This method updates the node's state when a value is committed.\<close>

definition applyValue :: "Value \<Rightarrow> NodeData \<Rightarrow> NodeData"
  where
    "applyValue x nd \<equiv> case x of
        NoOp \<Rightarrow> nd
      | Reconfigure Q \<Rightarrow> nd
          \<lparr> currentEra := nextEra (currentEra nd)
          , currentConfiguration := Q
          , electionVotes := {}
          , electionWon := False
          , electionValue := NoPublishResponseSent \<rparr>
      | SetClusterState s \<Rightarrow> nd \<lparr> currentClusterState := s \<rparr>"

text \<open>This method publishes a value via a @{term PublishRequest} message.\<close>

definition publishValue :: "Value \<Rightarrow> NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "publishValue x nd \<equiv>
        if electionWon nd \<and> \<not> applyRequested nd
              then ( nd \<lparr> applyRequested := True \<rparr>
                   , Some (PublishRequest
                             (firstUncommittedSlot nd)
                             (currentTerm nd) x) )
              else (nd, None)"

text \<open>Some elections require the new master to retry a previous attempt at publication, which
is what this method does.\<close>

definition sendElectionValueIfAppropriate :: "NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "sendElectionValueIfAppropriate nd
      \<equiv> case electionValue nd of
          PublishResponseSent _ x \<Rightarrow> publishValue x nd
          | _ \<Rightarrow> (nd, None)"

text \<open>This method updates the node's current term (if necessary) and discards any data associated
with the previous term.\<close>

definition ensureCurrentTerm :: "Term \<Rightarrow> NodeData \<Rightarrow> NodeData"
  where
    "ensureCurrentTerm t nd \<equiv>
        if currentTerm nd = t
            then nd
            else nd
              \<lparr> electionVotes := {}
              , currentTerm := t
              , electionWon := False
              , electionValue := NoPublishResponseSent
              , applyRequested := False
              , applyVotes := {} \<rparr>"

text \<open>This method updates the node's state on receipt of a vote (a @{term JoinRequest}) in an election.\<close>

definition addElectionVote :: "Node \<Rightarrow> nat => PreviousPublishResponse \<Rightarrow> NodeData \<Rightarrow> NodeData"
  where
    "addElectionVote s i a nd \<equiv> let newVotes = insert s (electionVotes nd)
      in nd \<lparr> electionVotes := newVotes
            , electionValue := combinePublishResponses (electionValue nd)
                                                     (if i = firstUncommittedSlot nd
                                                        then a
                                                        else NoPublishResponseSent)
            , electionWon := isQuorum nd newVotes \<rparr>"

text \<open>Clients request the cluster to achieve consensus on certain values using the @{term ClientValue}
message which is handled as follows.\<close>

definition handleClientValue :: "Value \<Rightarrow> NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "handleClientValue x nd \<equiv>
      if electionValue nd = NoPublishResponseSent
        then publishValue x nd
        else (nd, None)"

text \<open>A @{term StartJoin} message is checked for acceptability and then handled by updating the
node's term and yielding a @{term JoinRequest} message as follows.\<close>

definition handleStartJoin :: "Term \<Rightarrow> NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "handleStartJoin t nd \<equiv> if currentTerm nd < t \<and> era\<^sub>t t = currentEra nd
          then ( ensureCurrentTerm t nd
               , Some (JoinRequest (firstUncommittedSlot nd)
                                     t
                                    (lastAccepted nd)))
          else (nd, None)"

text \<open>A @{term JoinRequest} message is checked for acceptability and then handled as follows, perhaps
yielding a @{term PublishRequest} message.\<close>

definition handleJoinRequest :: "Node \<Rightarrow> nat \<Rightarrow> Term \<Rightarrow> PreviousPublishResponse \<Rightarrow> NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "handleJoinRequest s i t a nd \<equiv>
         if firstUncommittedSlot nd < i
             \<or> t < currentTerm nd
             \<or> (t = currentTerm nd \<and> electionWon nd)
             \<or> era\<^sub>t t \<noteq> currentEra nd
          then (nd, None)
          else let nd1 = ensureCurrentTerm t nd;
                   nd2 = addElectionVote s i a nd1
               in sendElectionValueIfAppropriate nd2"

text \<open>A @{term PublishRequest} message is checked for acceptability and then handled as follows,
yielding a @{term PublishResponse} message.\<close>

definition handlePublishRequest :: "nat \<Rightarrow> Term \<Rightarrow> Value \<Rightarrow> NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "handlePublishRequest i t x nd \<equiv>
          if currentTerm nd \<le> t
                \<and> \<not> lastAcceptedGreaterTermThan t nd
                \<and> firstUncommittedSlot nd = i
          then ( nd \<lparr> lastAccepted := PublishResponseSent t x \<rparr>
               , Some (PublishResponse i t))
          else (nd, None)"

text \<open>A @{term PublishResponse} message is checked for acceptability and handled as follows. If
this message, together with the previously-received messages, forms a quorum of votes then the
value is committed, yielding an @{term ApplyCommit} message.\<close>

definition handlePublishResponse :: "Node \<Rightarrow> nat \<Rightarrow> Term \<Rightarrow> NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "handlePublishResponse s i t nd \<equiv>
        if firstUncommittedSlot nd = i \<and> currentTerm nd \<le> t
        then let nd1 = ensureCurrentTerm t nd;
                 newVotes = insert s (applyVotes nd1)
             in (nd1 \<lparr> applyVotes := newVotes \<rparr>,
                 if isQuorum nd newVotes then Some (ApplyCommit i t) else None)
        else (nd, None)"

text \<open>An @{term ApplyCommit} message is applied to the current node's state, updating its configuration
and \textt{ClusterState} via the @{term applyValue} method. It yields no messages.\<close>

definition handleApplyCommit :: "nat \<Rightarrow> Term \<Rightarrow> NodeData \<Rightarrow> NodeData"
  where
    "handleApplyCommit i t nd \<equiv> 
        if i = firstUncommittedSlot nd
        then case lastAccepted nd of
            PublishResponseSent t' x' \<Rightarrow>
              if t = t'
              then applyValue x'
                      nd \<lparr> firstUncommittedSlot := i + 1
                         , lastAccepted := NoPublishResponseSent
                         , applyRequested := False
                         , electionValue := NoPublishResponseSent \<rparr>
              else nd
          | NoPublishResponseSent \<Rightarrow> nd
        else nd"

text \<open>A @{term Reboot} message simulates the effect of a reboot, discarding any ephemeral state but
preserving the persistent state. It yields no messages.\<close>

definition handleReboot :: "NodeData \<Rightarrow> NodeData"
  where
    "handleReboot nd \<equiv> 
      \<lparr> currentNode = currentNode nd
      , firstUncommittedSlot = firstUncommittedSlot nd
      , currentEra = currentEra nd
      , currentConfiguration = currentConfiguration nd
      , currentClusterState = currentClusterState nd
      , lastAccepted = lastAccepted nd
      , currentTerm = currentTerm nd
      , electionVotes = {}
      , electionWon = False
      , electionValue = NoPublishResponseSent
      , applyRequested = True
      , applyVotes = {} \<rparr>"

text \<open>This function dispatches incoming messages to the appropriate handler method, and
routes any responses to the appropriate places. In particular, @{term JoinRequest} messages
(sent by the @{term handleStartJoin} method) and
@{term PublishResponse} messages (sent by the @{term handlePublishRequest} method) are
only sent to a single node, whereas all other responses are broadcast to all nodes.\<close>

definition ProcessMessage :: "NodeData \<Rightarrow> RoutedMessage \<Rightarrow> (NodeData * RoutedMessage option)"
  where
    "ProcessMessage nd msg \<equiv>
      let respondTo =
          (\<lambda> d (nd, mmsg). case mmsg of
               None \<Rightarrow> (nd, None)
             | Some msg \<Rightarrow> (nd,
                 Some \<lparr> sender = currentNode nd, destination = d,
                             payload = msg \<rparr>));
          respondToSender = respondTo (OneNode (sender msg));
          respondToAll    = respondTo Broadcast
      in
        if destination msg \<in> { Broadcast, OneNode (currentNode nd) }
        then case payload msg of
          StartJoin t
              \<Rightarrow> respondToSender (handleStartJoin t nd)
          | JoinRequest i t a
              \<Rightarrow> respondToAll (handleJoinRequest (sender msg) i t a nd)
          | ClientValue x
              \<Rightarrow> respondToAll (handleClientValue x nd)
          | PublishRequest i t x
              \<Rightarrow> respondToSender (handlePublishRequest i t x nd)
          | PublishResponse i t
              \<Rightarrow> respondToAll (handlePublishResponse (sender msg) i t nd)
          | ApplyCommit i t
              \<Rightarrow> (handleApplyCommit i t nd, None)
          | Reboot
              \<Rightarrow> (handleReboot nd, None)
        else (nd, None)"

end
