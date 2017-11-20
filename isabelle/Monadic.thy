theory Monadic
  imports Implementation
begin

datatype 'a Action = Action "RoutedMessage \<Rightarrow> NodeData \<Rightarrow> (NodeData * RoutedMessage list * 'a)"

definition return :: "'a \<Rightarrow> 'a Action" where "return a \<equiv> Action (\<lambda> _ nd. (nd, [], a))"

definition bind :: "'a Action \<Rightarrow> ('a \<Rightarrow> 'b Action) \<Rightarrow> 'b Action" (infixr "\<bind>" 100)
  where "ma \<bind> mf \<equiv> case ma of
    Action unwrapped_ma \<Rightarrow> Action (\<lambda> env nd0. case unwrapped_ma env nd0 of
      (nd1, msgs0, a) \<Rightarrow> case mf a of
        Action unwrapped_mb \<Rightarrow> case unwrapped_mb env nd1 of
          (nd2, msgs1, b) \<Rightarrow> (nd2, msgs0 @ msgs1, b))"

definition runM :: "'a Action \<Rightarrow> RoutedMessage \<Rightarrow> NodeData \<Rightarrow> (NodeData * RoutedMessage list * 'a)"
  where "runM ma \<equiv> case ma of Action unwrapped_ma \<Rightarrow> unwrapped_ma"

lemma runM_action[simp]: "runM (Action f) = f" by (simp add: runM_def)
lemma runM_inject[intro]: "(\<And>rm nd. runM ma rm nd = runM mb rm nd) \<Longrightarrow> ma = mb" by (cases ma, cases mb, auto simp add: runM_def)

lemma runM_return[simp]: "runM (return a) rm nd = (nd, [], a)" unfolding runM_def return_def by simp
lemma runM_bind: "runM (a \<bind> f) rm nd0 = (case runM a rm nd0 of (nd1, msgs1, b) \<Rightarrow> case runM (f b) rm nd1 of (nd2, msgs2, c) \<Rightarrow> (nd2, msgs1@msgs2, c))"
  unfolding runM_def bind_def apply (cases "a", auto)
  by (metis (no_types, lifting) Action.case Action.exhaust case_prod_conv old.prod.exhaust)

lemma return_bind[simp]: "return a \<bind> f = f a" unfolding return_def bind_def by (cases "f a", auto)
lemma bind_return[simp]: "a \<bind> return = a" unfolding return_def bind_def by (cases "a", auto)

lemma bind_bind_assoc[simp]: "((a \<bind> f) \<bind> g) = (a \<bind> (\<lambda>x. f x \<bind> g))" (is "?LHS = ?RHS")
proof (intro runM_inject)
  fix nd0 rm
  show "runM ?LHS rm nd0 = runM ?RHS rm nd0"
  proof (cases "runM a rm nd0")
    case fields1: (fields nd1 msgs1 b)
    show ?thesis
    proof (cases "runM (f b) rm nd1")
      case fields2: (fields nd2 msgs2 c)
      show ?thesis by (cases "runM (g c) rm nd2", simp add: runM_bind fields1 fields2)
    qed
  qed
qed

definition thn :: "'a Action \<Rightarrow> 'b Action \<Rightarrow> 'b Action" (infixr "\<then>" 100) where "a \<then> b \<equiv> a \<bind> (\<lambda>_. b)"
lemma runM_thn: "runM (a \<then> b) rm nd0 = (case runM a rm nd0 of (nd1, msgs1, _) \<Rightarrow> case runM b rm nd1 of (nd2, msgs2, c) \<Rightarrow> (nd2, msgs1@msgs2, c))"
  unfolding thn_def runM_bind by simp

lemma return_thn[simp]: "return a \<then> b = b" by (auto simp add: runM_thn)

lemma thn_thn_assoc[simp]: "((a \<then> b) \<then> c) = (a \<then> (b \<then> c))" (is "?LHS = ?RHS")
proof (intro runM_inject)
  fix rm nd0
  show "runM ?LHS rm nd0 = runM ?RHS rm nd0"
  proof (cases "runM a rm nd0")
    case fields1: (fields nd1 msgs1)
    show ?thesis
    proof (cases "runM b rm nd1")
      case fields2: (fields nd2 msgs2)
      show ?thesis by (cases "runM c rm nd2", simp add: runM_thn fields1 fields2)
    qed
  qed
qed

lemma thn_bind_assoc[simp]: "((a \<then> b) \<bind> c) = (a \<then> (b \<bind> c))" (is "?LHS = ?RHS")
proof (intro runM_inject)
  fix rm nd0
  show "runM ?LHS rm nd0 = runM ?RHS rm nd0"
  proof (cases "runM a rm nd0")
    case fields1: (fields nd1 msgs1 r1)
    show ?thesis
    proof (cases "runM b rm nd1")
      case fields2: (fields nd2 msgs2 r2)
      show ?thesis by (cases "runM (c r2) rm nd2", simp add: runM_thn runM_bind fields1 fields2)
    qed
  qed
qed

lemma bind_thn_assoc[simp]: "((a \<bind> b) \<then> c) = (a \<bind> (\<lambda>x. b x \<then> c))" (is "?LHS = ?RHS")
proof (intro runM_inject)
  fix rm nd0
  show "runM ?LHS rm nd0 = runM ?RHS rm nd0"
  proof (cases "runM a rm nd0")
    case fields1: (fields nd1 msgs1 r1)
    show ?thesis
    proof (cases "runM (b r1) rm nd1")
      case fields2: (fields nd2 msgs2 r2)
      show ?thesis by (cases "runM c rm nd2", simp add: runM_thn runM_bind fields1 fields2)
    qed
  qed
qed

definition askCurrentMessage :: "RoutedMessage Action" where "askCurrentMessage \<equiv> Action (\<lambda>rm nd. (nd, [], rm))"
lemma runM_askCurrentMessage[simp]: "runM askCurrentMessage rm nd = (nd, [], rm)" by (simp add: runM_def askCurrentMessage_def)
lemma runM_askCurrentMessage_continue[simp]: "runM (askCurrentMessage \<bind> f) rm nd = runM (f rm) rm nd" by (simp add: runM_bind)

lemma ask_ask_continue[simp]: "askCurrentMessage \<bind> (\<lambda>rm. askCurrentMessage \<bind> f rm) = askCurrentMessage \<bind> (\<lambda>rm. f rm rm)" by (auto simp add: runM_bind)
lemma ask_thn[simp]: "askCurrentMessage \<then> f = f" by (auto simp add: runM_thn)

definition getNodeData :: "NodeData Action" where "getNodeData \<equiv> Action (\<lambda>_ nd. (nd, [], nd))"
definition setNodeData :: "NodeData \<Rightarrow> unit Action" where "setNodeData nd \<equiv> Action (\<lambda>_ _. (nd, [], ()))"

lemma runM_getNodeData[simp]: "runM  getNodeData      rm nd = (nd,  [], nd)" by (simp add: runM_def getNodeData_def)
lemma runM_setNodeData[simp]: "runM (setNodeData nd') rm nd = (nd', [], ())" by (simp add: runM_def setNodeData_def)

lemma runM_getNodeData_continue[simp]: "runM (getNodeData \<bind> f) rm nd = runM (f nd) rm nd" by (simp add: runM_bind)
lemma runM_setNodeData_continue[simp]: "runM (setNodeData nd' \<then> a) rm nd = runM a rm nd'" by (simp add: runM_thn)

lemma get_thn[simp]: "getNodeData \<then> f = f" by (auto simp add: runM_thn)
lemma get_set[simp]: "getNodeData \<bind> setNodeData = return ()" by (auto simp add: runM_bind)
lemma set_get[simp]: "setNodeData nd \<then> getNodeData = setNodeData nd \<then> return nd" by (auto simp add: runM_thn)
lemma set_set[simp]: "setNodeData nd1 \<then> setNodeData nd2 = setNodeData nd2" by (auto simp add: runM_thn)

lemma get_get_continue[simp]: "getNodeData \<bind> (\<lambda>nd. getNodeData \<bind> f nd) = getNodeData \<bind> (\<lambda> nd. f nd nd)" by (auto simp add: runM_bind)
lemma get_set_continue[simp]: "getNodeData \<bind> (\<lambda>nd. setNodeData nd \<then> a) = a" by (auto simp add: runM_bind runM_thn)
lemma set_get_continue[simp]: "setNodeData nd \<then> (getNodeData \<bind> a) = setNodeData nd \<then> a nd" by (auto simp add: runM_bind runM_thn)
lemma set_set_continue[simp]: "setNodeData nd1 \<then> (setNodeData nd2 \<then> a) = setNodeData nd2 \<then> a" by (auto simp add: runM_bind runM_thn)

definition modifyNodeData :: "(NodeData \<Rightarrow> NodeData) \<Rightarrow> unit Action" where "modifyNodeData f = getNodeData \<bind> (setNodeData \<circ> f)"

lemma runM_modifyNodeData[simp]: "runM (modifyNodeData f) rm nd = (f nd, [], ())" by (simp add: modifyNodeData_def runM_bind)
lemma runM_modifyNodeData_continue[simp]: "runM (modifyNodeData f \<then> a) rm nd = runM a rm (f nd)" by (simp add: runM_thn)

lemma modify_modify[simp]: "modifyNodeData f \<then> modifyNodeData g = modifyNodeData (g \<circ> f)" by (auto simp add: runM_thn)
lemma set_modify[simp]: "modifyNodeData f \<then> setNodeData nd = setNodeData nd" by (auto simp add: runM_thn)
lemma modify_set[simp]: "setNodeData nd \<then> modifyNodeData f = setNodeData (f nd)" by (auto simp add: runM_thn)
lemma modify_get[simp]: "modifyNodeData f \<then> getNodeData = getNodeData \<bind> (\<lambda> nd. modifyNodeData f \<then> return (f nd))" by (auto simp add: runM_thn runM_bind)

lemma modify_modify_continue[simp]: "modifyNodeData f \<then> modifyNodeData g \<then> a = modifyNodeData (g \<circ> f) \<then> a" by (auto simp add: runM_thn)
lemma set_modify_continue[simp]: "modifyNodeData f \<then> setNodeData nd \<then> a = setNodeData nd \<then> a" by (auto simp add: runM_thn)
lemma modify_set_continue[simp]: "setNodeData nd \<then> modifyNodeData f \<then> a = setNodeData (f nd) \<then> a" by (auto simp add: runM_thn)
lemma modify_get_continue[simp]: "modifyNodeData f \<then> getNodeData  \<bind> a  = getNodeData \<bind> (\<lambda> nd. modifyNodeData f \<then> a (f nd))" by (auto simp add: runM_thn runM_bind)

definition tell :: "RoutedMessage list \<Rightarrow> unit Action" where "tell rms \<equiv> Action (\<lambda>_ nd. (nd, rms, ()))"
lemma runM_tell[simp]: "runM (tell rms) rm nd = (nd, rms, ())" by (simp add: runM_def tell_def)

lemma tell_tell[simp]: "tell rms1 \<then> tell rms2 = tell (rms1@rms2)" by (auto simp add: runM_thn)
lemma tell_set[simp]: "tell rms \<then> setNodeData nd = setNodeData nd \<then> tell rms" by (auto simp add: runM_thn)
lemma tell_get[simp]: "tell rms \<then> getNodeData = getNodeData \<bind> (\<lambda>nd. tell rms \<then> return nd)" by (auto simp add: runM_thn runM_bind)
lemma tell_modify[simp]: "tell rms \<then> modifyNodeData nd = modifyNodeData nd \<then> tell rms" by (auto simp add: runM_thn)

lemma tell_tell_continue[simp]: "tell rms1 \<then> tell rms2 \<then> a = tell (rms1@rms2) \<then> a" by (metis tell_tell thn_thn_assoc)
lemma tell_set_continue[simp]: "tell rms \<then> setNodeData nd \<then> a = setNodeData nd \<then> tell rms \<then> a" by (auto simp add: runM_thn)
lemma tell_get_continue[simp]: "tell rms \<then> getNodeData \<bind> a = getNodeData \<bind> (\<lambda>nd. tell rms \<then> a nd)" by (auto simp add: runM_thn runM_bind)
lemma tell_modify_continue[simp]: "tell rms \<then> modifyNodeData nd \<then> a = modifyNodeData nd \<then> tell rms \<then> a" by (auto simp add: runM_thn)

definition send :: "RoutedMessage \<Rightarrow> unit Action" where "send rm = tell [rm]"

lemma send_tell[simp]: "send rm \<then> tell rms = tell (rm#rms)" by (simp add: send_def)
lemma tell_send[simp]: "tell rms \<then> send rm = tell (rms@[rm])" by (simp add: send_def)
lemma send_send[simp]: "send rm1 \<then> send rm2 = tell [rm1,rm2]" by (simp add: send_def)
lemma send_set[simp]: "send rm \<then> setNodeData nd = setNodeData nd \<then> send rm" by (simp add: send_def)
lemma send_get[simp]: "send rm \<then> getNodeData = getNodeData \<bind> (\<lambda>nd. send rm \<then> return nd)" by (simp add: send_def)
lemma send_modify[simp]: "send rm \<then> modifyNodeData nd = modifyNodeData nd \<then> send rm" by (simp add: send_def)

lemma send_tell_continue[simp]: "send rm \<then> tell rms \<then> a = tell (rm#rms) \<then> a" by (simp add: send_def)
lemma tell_send_continue[simp]: "tell rms \<then> send rm \<then> a = tell (rms@[rm]) \<then> a" by (simp add: send_def)
lemma send_send_continue[simp]: "send rm1 \<then> send rm2 \<then> a = tell [rm1,rm2] \<then> a" by (simp add: send_def)
lemma send_set_continue[simp]: "send rm \<then> setNodeData nd \<then> a = setNodeData nd \<then> send rm \<then> a" by (simp add: send_def)
lemma send_get_continue[simp]: "send rm \<then> getNodeData \<bind> a = getNodeData \<bind> (\<lambda>nd. send rm \<then> a nd)" by (simp add: send_def)
lemma send_modify_continue[simp]: "send rm \<then> modifyNodeData nd \<then> a = modifyNodeData nd \<then> send rm \<then> a" by (simp add: send_def)

definition gets :: "(NodeData \<Rightarrow> 'a) \<Rightarrow> 'a Action" where "gets f \<equiv> getNodeData \<bind> (\<lambda>nd. return (f nd))"
definition getCurrentClusterState where "getCurrentClusterState = gets currentClusterState"
definition getCurrentNode where "getCurrentNode = gets currentNode"
definition getCurrentTerm where "getCurrentTerm = gets currentTerm"
definition getCurrentVotingNodes where "getCurrentVotingNodes = gets currentVotingNodes"
definition getElectionValueForced where "getElectionValueForced = gets electionValueForced"
definition getElectionWon where "getElectionWon = gets electionWon"
definition getFirstUncommittedSlot where "getFirstUncommittedSlot = gets firstUncommittedSlot"
definition getJoinVotes where "getJoinVotes = gets joinVotes"
definition getLastAcceptedTerm where "getLastAcceptedTerm = gets lastAcceptedTerm"
definition getLastAcceptedValue where "getLastAcceptedValue = gets lastAcceptedValue"
definition getPublishPermitted where "getPublishPermitted = gets publishPermitted"
definition getPublishVotes where "getPublishVotes = gets publishVotes"

definition sets where "sets f x = modifyNodeData (f (\<lambda>_. x))"
definition setCurrentClusterState where "setCurrentClusterState = sets currentClusterState_update"
definition setCurrentNode where "setCurrentNode = sets currentNode_update"
definition setCurrentTerm where "setCurrentTerm = sets currentTerm_update"
definition setCurrentVotingNodes where "setCurrentVotingNodes = sets currentVotingNodes_update"
definition setElectionValueForced where "setElectionValueForced = sets electionValueForced_update"
definition setElectionWon where "setElectionWon = sets electionWon_update"
definition setFirstUncommittedSlot where "setFirstUncommittedSlot = sets firstUncommittedSlot_update"
definition setJoinVotes where "setJoinVotes = sets joinVotes_update"
definition setLastAcceptedTerm where "setLastAcceptedTerm = sets lastAcceptedTerm_update"
definition setLastAcceptedValue where "setLastAcceptedValue = sets lastAcceptedValue_update"
definition setPublishPermitted where "setPublishPermitted = sets publishPermitted_update"
definition setPublishVotes where "setPublishVotes = sets publishVotes_update"

definition modifies where "modifies f g = modifyNodeData (f g)"
definition modifyJoinVotes where "modifyJoinVotes = modifies joinVotes_update"
definition modifyPublishVotes where "modifyPublishVotes = modifies publishVotes_update"
definition modifyCurrentClusterState where "modifyCurrentClusterState = modifies currentClusterState_update"

definition whenTrue :: "bool \<Rightarrow> unit Action \<Rightarrow> unit Action" where "whenTrue c a \<equiv> if c then a else return ()"
definition bailOutIf :: "bool \<Rightarrow> unit Action \<Rightarrow> unit Action" where "bailOutIf \<equiv> whenTrue \<circ> Not"

lemma whenTrue_simps[simp]:
  "whenTrue True a = a"
  "whenTrue False a = return ()"
  "bailOutIf True a = return ()"
  "bailOutIf False a = a"
  unfolding whenTrue_def bailOutIf_def by auto

lemma runM_whenTrue: "runM (whenTrue c a) rm nd = (if c then runM a rm nd else (nd, [], ()))"
  by (auto simp add: whenTrue_def)
lemma runM_bailOutIf: "runM (bailOutIf c a) rm nd = (if c then (nd, [], ()) else runM a rm nd)"
  by (auto simp add: bailOutIf_def)

lemma runM_whenTrue_thn: "runM (whenTrue c a \<then> b) rm nd = (if c then runM (a \<then> b) rm nd else runM b rm nd)"
  by (auto simp add: whenTrue_def)

definition whenCorrectDestination :: "unit Action \<Rightarrow> unit Action"
  where "whenCorrectDestination go \<equiv> getCurrentNode \<bind> (\<lambda>n. askCurrentMessage \<bind> (\<lambda>m. whenTrue (destination m \<in> { Broadcast, OneNode n }) go))"

lemma runM_whenCorrectDestination:
  "runM (whenCorrectDestination go) rm nd = (if destination rm \<in> { Broadcast, OneNode (currentNode nd) } then runM go rm nd else (nd, [], ()))"
  by (simp add: whenCorrectDestination_def getCurrentNode_def gets_def)

definition broadcast :: "Message \<Rightarrow> unit Action"
  where "broadcast msg \<equiv> getCurrentNode \<bind> (\<lambda>n. send \<lparr> sender = n, destination = Broadcast, payload = msg \<rparr>)"

lemma runM_broadcast[simp]: "runM (broadcast msg) rm nd = (nd, [\<lparr> sender = currentNode nd, destination = Broadcast, payload = msg \<rparr>], ())"
  by (simp add: broadcast_def getCurrentNode_def gets_def send_def)

definition respond :: "Message \<Rightarrow> unit Action"
  where "respond msg \<equiv> getCurrentNode \<bind> (\<lambda>n. askCurrentMessage \<bind> (\<lambda>m. send \<lparr> sender = n, destination = OneNode (sender m), payload = msg \<rparr>))"

lemma runM_respond[simp]: "runM (respond msg) rm nd = (nd, [\<lparr> sender = currentNode nd, destination = OneNode (sender rm), payload = msg \<rparr>], ())"
  by (simp add: respond_def getCurrentNode_def gets_def send_def)

definition doStartJoin :: "Term \<Rightarrow> unit Action"
  where
    "doStartJoin newTerm \<equiv>

      getCurrentTerm \<bind> (\<lambda>currentTerm.
      bailOutIf (newTerm \<le> currentTerm) (

      setJoinVotes {} \<then>
      setElectionWon False \<then>
      setCurrentTerm newTerm \<then>
      setElectionValueForced False \<then>
      setPublishPermitted True \<then>
      setPublishVotes {} \<then>

      getFirstUncommittedSlot \<bind> (\<lambda>firstUncommittedSlot.
      getLastAcceptedTerm \<bind> (\<lambda>lastAcceptedTerm.
      respond (JoinRequest firstUncommittedSlot newTerm lastAcceptedTerm)))))"

definition doJoinRequestCurrentSlot :: "Node \<Rightarrow> Term option \<Rightarrow> unit Action"
  where
    "doJoinRequestCurrentSlot requestSender requestLastAcceptedTerm \<equiv>

      getLastAcceptedTerm \<bind> (\<lambda>lastAcceptedTerm.
      getElectionValueForced \<bind> (\<lambda>electionValueForced.

      whenTrue (requestLastAcceptedTerm = None
             \<or> requestLastAcceptedTerm = lastAcceptedTerm
             \<or> (maxTermOption requestLastAcceptedTerm lastAcceptedTerm = lastAcceptedTerm \<and> electionValueForced)) (

        modifyJoinVotes (insert requestSender) \<then>
        whenTrue (requestLastAcceptedTerm \<noteq> None) (setElectionValueForced True) \<then>

        getJoinVotes \<bind> (\<lambda>joinVotes.
        getCurrentVotingNodes \<bind> (\<lambda>currentVotingNodes.

        let electionWon' = card (joinVotes \<inter> currentVotingNodes) * 2 > card currentVotingNodes in
        setElectionWon electionWon' \<then>
        bailOutIf (\<not> electionWon') (

        getPublishPermitted \<bind> (\<lambda>publishPermitted.
        bailOutIf (\<not> publishPermitted) (
        setPublishPermitted False \<then>

        getFirstUncommittedSlot \<bind> (\<lambda>firstUncommittedSlot.
        getCurrentTerm \<bind> (\<lambda>currentTerm.
        getLastAcceptedValue \<bind> (\<lambda>lastAcceptedValue.
        broadcast (PublishRequest firstUncommittedSlot currentTerm lastAcceptedValue))))))))))))"

definition doJoinRequest :: "Node \<Rightarrow> Slot \<Rightarrow> Term \<Rightarrow> Term option \<Rightarrow> unit Action"
  where
    "doJoinRequest s i t a \<equiv>

      getFirstUncommittedSlot \<bind> (\<lambda>firstUncommittedSlot.
      bailOutIf (firstUncommittedSlot < i) (

      getCurrentTerm \<bind> (\<lambda>currentTerm.
      bailOutIf (t \<noteq> currentTerm) (

      if i = firstUncommittedSlot
        then doJoinRequestCurrentSlot s a
        else doJoinRequestCurrentSlot s None))))"

definition doClientValue :: "Value \<Rightarrow> unit Action"
  where
    "doClientValue x \<equiv>
      
      getElectionWon \<bind> (\<lambda>electionWon.
      bailOutIf (\<not> electionWon) (
 
      getPublishPermitted \<bind> (\<lambda>publishPermitted.
      bailOutIf (\<not> publishPermitted) (

      getElectionValueForced \<bind> (\<lambda>electionValueForced.
      bailOutIf (electionValueForced) (

      setPublishPermitted False \<then>

      getCurrentTerm \<bind> (\<lambda>currentTerm.
      getFirstUncommittedSlot \<bind> (\<lambda>firstUncommittedSlot.
      broadcast (PublishRequest firstUncommittedSlot currentTerm x)))))))))"

definition doPublishRequest :: "Slot \<Rightarrow> Term \<Rightarrow> Value \<Rightarrow> unit Action"
  where
    "doPublishRequest i t x \<equiv>

      getFirstUncommittedSlot \<bind> (\<lambda>firstUncommittedSlot.
      bailOutIf (i \<noteq> firstUncommittedSlot) (

      getCurrentTerm \<bind> (\<lambda>currentTerm.
      bailOutIf (t \<noteq> currentTerm) (

      setLastAcceptedTerm (Some t) \<then>
      setLastAcceptedValue x \<then>
      respond (PublishResponse i t)))))"

definition doPublishResponse :: "Node \<Rightarrow> Slot \<Rightarrow> Term \<Rightarrow> unit Action"
  where
    "doPublishResponse s i t \<equiv>

      getFirstUncommittedSlot \<bind> (\<lambda>firstUncommittedSlot.
      bailOutIf (i \<noteq> firstUncommittedSlot) (

      getCurrentTerm \<bind> (\<lambda>currentTerm.
      bailOutIf (t \<noteq> currentTerm) (

      modifyPublishVotes (insert s) \<then>
      getPublishVotes \<bind> (\<lambda>publishVotes.
      getCurrentVotingNodes \<bind> (\<lambda>currentVotingNodes.
      whenTrue (card (publishVotes \<inter> currentVotingNodes) * 2 > card currentVotingNodes) (

        broadcast (ApplyCommit i t))))))))"

definition doApplyCommit :: "Slot \<Rightarrow> Term \<Rightarrow> unit Action"
  where
    "doApplyCommit i t \<equiv>

      getFirstUncommittedSlot \<bind> (\<lambda>firstUncommittedSlot.
      bailOutIf (i \<noteq> firstUncommittedSlot) (

      getLastAcceptedTerm \<bind> (\<lambda>lastAcceptedTerm.
      bailOutIf (Some t \<noteq> lastAcceptedTerm) (

      getLastAcceptedValue \<bind> (\<lambda>lastAcceptedValue.

      (case lastAcceptedValue of 
        ClusterStateDiff diff
            \<Rightarrow> modifyCurrentClusterState diff
        | Reconfigure votingNodes
            \<Rightarrow> setCurrentVotingNodes (set votingNodes) \<then>
               getJoinVotes \<bind> (\<lambda>joinVotes.
               setElectionWon (card (joinVotes \<inter> (set votingNodes)) * 2 > card (set votingNodes)))
        | NoOp \<Rightarrow> return ()) \<then>

      setFirstUncommittedSlot (i + 1) \<then>
      setLastAcceptedValue NoOp \<then>
      setLastAcceptedTerm None \<then>
      setPublishPermitted True \<then>
      setElectionValueForced False \<then>
      setPublishVotes {})))))"

definition doCatchUpRequest :: "unit Action"
  where
    "doCatchUpRequest \<equiv>

      getFirstUncommittedSlot \<bind> (\<lambda>firstUncommittedSlot.
      getCurrentTerm \<bind> (\<lambda>currentTerm.
      getCurrentVotingNodes \<bind> (\<lambda>currentVotingNodes.
      getCurrentClusterState \<bind> (\<lambda>currentClusterState.

      respond (CatchUpResponse firstUncommittedSlot currentTerm currentVotingNodes currentClusterState)))))"

definition doCatchUpResponse :: "Slot \<Rightarrow> Term \<Rightarrow> Node set \<Rightarrow> ClusterState \<Rightarrow> unit Action"
  where
    "doCatchUpResponse i t conf cs \<equiv>

      getFirstUncommittedSlot \<bind> (\<lambda>firstUncommittedSlot.
      bailOutIf (i \<le> firstUncommittedSlot) (

      getCurrentTerm \<bind> (\<lambda>currentTerm.
      bailOutIf (t \<noteq> currentTerm) (

      setFirstUncommittedSlot i \<then>    
      setLastAcceptedValue NoOp \<then>
      setLastAcceptedTerm None \<then>
      setPublishPermitted False \<then>
      setElectionValueForced False \<then>
      setPublishVotes {} \<then>
      setCurrentVotingNodes conf \<then>
      setCurrentClusterState cs \<then>
      setJoinVotes {} \<then>
      setElectionWon False))))"

definition doReboot :: "unit Action"
  where
    "doReboot \<equiv> modifyNodeData (\<lambda>nd. 
                  \<lparr> currentNode = currentNode nd
                  , firstUncommittedSlot = firstUncommittedSlot nd
                  , currentTerm = currentTerm nd
                  , currentVotingNodes = currentVotingNodes nd
                  , currentClusterState = currentClusterState nd
                  , lastAcceptedTerm = lastAcceptedTerm nd
                  , lastAcceptedValue = lastAcceptedValue nd
                  , joinVotes = {}
                  , electionWon = False
                  , electionValueForced = False
                  , publishPermitted = False
                  , publishVotes = {} \<rparr>)"

definition ProcessMessageAction :: "unit Action"
  where "ProcessMessageAction \<equiv> Action (\<lambda> rm nd. case ProcessMessage nd rm of (nd', messageOption) \<Rightarrow> (nd', case messageOption of None \<Rightarrow> [] | Some m \<Rightarrow> [m], ()))"

definition dispatchMessage :: "unit Action"
  where "dispatchMessage \<equiv> whenCorrectDestination (askCurrentMessage \<bind> (\<lambda>m. case payload m of
          StartJoin t \<Rightarrow> doStartJoin t
          | JoinRequest i t a \<Rightarrow> doJoinRequest (sender m) i t a
          | ClientValue x \<Rightarrow> doClientValue x
          | PublishRequest i t x \<Rightarrow> doPublishRequest i t x
          | PublishResponse i t \<Rightarrow> doPublishResponse (sender m) i t
          | ApplyCommit i t \<Rightarrow> doApplyCommit i t
          | CatchUpRequest \<Rightarrow> doCatchUpRequest
          | CatchUpResponse i t conf cs \<Rightarrow> doCatchUpResponse i t conf cs
          | Reboot \<Rightarrow> doReboot
          ))"

lemma monadic_implementation_is_faithful:
  "dispatchMessage = ProcessMessageAction"
proof (intro runM_inject)
  fix rm nd
  show "runM dispatchMessage rm nd = runM ProcessMessageAction rm nd" (is "?LHS = ?RHS")
  proof (cases "destination rm \<in> {Broadcast, OneNode (currentNode nd)}")
    case False
    thus ?thesis
      unfolding ProcessMessageAction_def dispatchMessage_def whenCorrectDestination_def getCurrentNode_def gets_def ProcessMessage_def Let_def
      by auto
  next
    case dest_ok: True

    show ?thesis
    proof (cases "payload rm")
      case (StartJoin t)

      consider
        (a) "t \<le> currentTerm nd"
        | (b) "currentTerm nd < t" "case lastAcceptedTerm nd of None \<Rightarrow> False | Some x \<Rightarrow> t \<le> x"
        | (c) "currentTerm nd < t" "case lastAcceptedTerm nd of None \<Rightarrow> True | Some x \<Rightarrow> x < t"
      proof (cases "t \<le> currentTerm nd")
        case True thus ?thesis by (intro a)
      next
        case 1: False
        with b c show ?thesis
          by (cases "case lastAcceptedTerm nd of None \<Rightarrow> False | Some x \<Rightarrow> t \<le> x", auto, cases "lastAcceptedTerm nd", auto)
      qed

      thus ?thesis
      proof cases
        case a
        with StartJoin dest_ok show ?thesis
          by (simp add: ProcessMessageAction_def dispatchMessage_def runM_whenCorrectDestination ProcessMessage_def Let_def
              doStartJoin_def getCurrentTerm_def gets_def getLastAcceptedTerm_def setJoinVotes_def sets_def setCurrentTerm_def setElectionValueForced_def
              setPublishPermitted_def setPublishVotes_def getFirstUncommittedSlot_def handleStartJoin_def ensureCurrentTerm_def setElectionWon_def)
      next
        case b
        with StartJoin dest_ok show ?thesis
          by (cases "lastAcceptedTerm nd ", simp_all add: ProcessMessageAction_def dispatchMessage_def runM_whenCorrectDestination ProcessMessage_def Let_def
              doStartJoin_def getCurrentTerm_def gets_def getLastAcceptedTerm_def setJoinVotes_def sets_def setCurrentTerm_def setElectionValueForced_def
              setPublishPermitted_def setPublishVotes_def getFirstUncommittedSlot_def handleStartJoin_def ensureCurrentTerm_def setElectionWon_def)
      next
        case c with StartJoin dest_ok show ?thesis
          by (cases "lastAcceptedTerm nd", simp_all add: ProcessMessageAction_def dispatchMessage_def runM_whenCorrectDestination ProcessMessage_def Let_def
              doStartJoin_def getCurrentTerm_def gets_def getLastAcceptedTerm_def setJoinVotes_def sets_def setCurrentTerm_def setElectionValueForced_def
              setPublishPermitted_def setPublishVotes_def getFirstUncommittedSlot_def handleStartJoin_def ensureCurrentTerm_def setElectionWon_def)
      qed

    next
      case (JoinRequest i t a)

      show ?thesis
      proof (cases "firstUncommittedSlot nd < i")
        case True
        with JoinRequest dest_ok show ?thesis
          by (simp add: dispatchMessage_def runM_whenCorrectDestination
              doJoinRequest_def gets_def getFirstUncommittedSlot_def ProcessMessage_def
              ProcessMessageAction_def handleJoinRequest_def)
      next
        case False hence le: "i \<le> firstUncommittedSlot nd" by simp

        show ?thesis
        proof (cases "t = currentTerm nd")
          case False
          with JoinRequest dest_ok le show ?thesis
            by (simp add: dispatchMessage_def runM_whenCorrectDestination
                doJoinRequest_def gets_def getFirstUncommittedSlot_def getCurrentTerm_def
                ProcessMessage_def ProcessMessageAction_def handleJoinRequest_def)

        next
          case t: True

          show ?thesis
          proof (cases "i = firstUncommittedSlot nd")
            case False
            with JoinRequest dest_ok le t show ?thesis
              by (simp add: dispatchMessage_def runM_whenCorrectDestination Let_def
                doJoinRequest_def doJoinRequestCurrentSlot_def runM_bailOutIf
                gets_def getFirstUncommittedSlot_def getCurrentTerm_def getLastAcceptedTerm_def
                getElectionValueForced_def getJoinVotes_def getCurrentVotingNodes_def
                getPublishPermitted_def getLastAcceptedValue_def
                modifies_def modifyJoinVotes_def 
                sets_def setElectionWon_def setPublishPermitted_def
                ProcessMessage_def ProcessMessageAction_def handleJoinRequest_def
                addElectionVote_def publishValue_def isQuorum_def majorities_def)
          next
            case True
            with JoinRequest dest_ok le t show ?thesis
              by (simp add: dispatchMessage_def runM_whenCorrectDestination Let_def
                  doJoinRequest_def doJoinRequestCurrentSlot_def
                  runM_bailOutIf runM_whenTrue_thn runM_whenTrue
                  gets_def getFirstUncommittedSlot_def getCurrentTerm_def getLastAcceptedTerm_def
                  getElectionValueForced_def getJoinVotes_def getCurrentVotingNodes_def
                  getPublishPermitted_def getLastAcceptedValue_def
                  modifies_def modifyJoinVotes_def 
                  sets_def setElectionWon_def setPublishPermitted_def setElectionValueForced_def
                  ProcessMessage_def ProcessMessageAction_def handleJoinRequest_def
                  addElectionVote_def publishValue_def isQuorum_def majorities_def)
          qed
        qed
      qed

    next
      case (ClientValue x) with dest_ok show ?thesis
        by (simp add: ProcessMessageAction_def dispatchMessage_def runM_whenCorrectDestination
            doClientValue_def gets_def getElectionValueForced_def getElectionWon_def
            runM_bailOutIf getPublishPermitted_def setPublishPermitted_def sets_def
            getCurrentTerm_def getFirstUncommittedSlot_def ProcessMessage_def handleClientValue_def
            publishValue_def)

    next
      case (PublishRequest i t x) with dest_ok show ?thesis
        by (simp add: ProcessMessageAction_def dispatchMessage_def runM_whenCorrectDestination
          doPublishRequest_def gets_def getCurrentTerm_def getFirstUncommittedSlot_def
          sets_def setLastAcceptedTerm_def setLastAcceptedValue_def respond_def getCurrentNode_def runM_bailOutIf send_def
          ProcessMessage_def handlePublishRequest_def)

    next
      case (PublishResponse i t) with dest_ok show ?thesis
        by (simp add: ProcessMessageAction_def dispatchMessage_def runM_whenCorrectDestination
          doPublishResponse_def gets_def getCurrentTerm_def getFirstUncommittedSlot_def
          broadcast_def getCurrentNode_def runM_bailOutIf send_def
          modifyPublishVotes_def modifies_def getPublishVotes_def getCurrentVotingNodes_def
          runM_whenTrue
          ProcessMessage_def handlePublishResponse_def commitIfQuorate_def isQuorum_def majorities_def)

    next
      case (ApplyCommit i t)

      show ?thesis
      proof (cases "lastAcceptedValue nd")
        case NoOp
        with ApplyCommit dest_ok show ?thesis
          by (simp add: ProcessMessageAction_def dispatchMessage_def runM_whenCorrectDestination
            doApplyCommit_def runM_bailOutIf
            gets_def getFirstUncommittedSlot_def getLastAcceptedTerm_def getLastAcceptedValue_def
            sets_def setFirstUncommittedSlot_def setLastAcceptedValue_def setLastAcceptedTerm_def
            setPublishPermitted_def setElectionValueForced_def setPublishVotes_def
            ProcessMessage_def handleApplyCommit_def applyAcceptedValue_def)
      next
        case Reconfigure
        with ApplyCommit dest_ok show ?thesis
          by (simp add: ProcessMessageAction_def dispatchMessage_def runM_whenCorrectDestination
            doApplyCommit_def runM_bailOutIf
            gets_def getFirstUncommittedSlot_def getLastAcceptedTerm_def getLastAcceptedValue_def
            getJoinVotes_def
            sets_def setFirstUncommittedSlot_def setLastAcceptedValue_def setLastAcceptedTerm_def
            setPublishPermitted_def setElectionValueForced_def setPublishVotes_def
            setCurrentVotingNodes_def setElectionWon_def
            ProcessMessage_def handleApplyCommit_def applyAcceptedValue_def majorities_def)
      next
        case ClusterStateDiff
        with ApplyCommit dest_ok show ?thesis
          by (simp add: ProcessMessageAction_def dispatchMessage_def runM_whenCorrectDestination
            doApplyCommit_def runM_bailOutIf
            gets_def getFirstUncommittedSlot_def getLastAcceptedTerm_def getLastAcceptedValue_def
            sets_def setFirstUncommittedSlot_def setLastAcceptedValue_def setLastAcceptedTerm_def
            modifies_def modifyCurrentClusterState_def
            setPublishPermitted_def setElectionValueForced_def setPublishVotes_def
            ProcessMessage_def handleApplyCommit_def applyAcceptedValue_def)
      qed

    next
      case CatchUpRequest
      with dest_ok show ?thesis
        by (simp add: ProcessMessageAction_def dispatchMessage_def runM_whenCorrectDestination
          doCatchUpRequest_def
          gets_def getFirstUncommittedSlot_def getCurrentVotingNodes_def getCurrentClusterState_def getCurrentTerm_def
          ProcessMessage_def handleCatchUpRequest_def)

    next
      case (CatchUpResponse i conf cs)
      with dest_ok show ?thesis
        by (simp add: ProcessMessageAction_def dispatchMessage_def runM_whenCorrectDestination
            doCatchUpResponse_def gets_def getFirstUncommittedSlot_def getCurrentTerm_def
            runM_bailOutIf
            sets_def setFirstUncommittedSlot_def setLastAcceptedValue_def setLastAcceptedTerm_def
            setPublishPermitted_def setElectionValueForced_def setPublishVotes_def
            setCurrentVotingNodes_def setCurrentClusterState_def setJoinVotes_def
            setElectionWon_def
            ProcessMessage_def handleCatchUpResponse_def)

    next
      case Reboot
      with dest_ok show ?thesis
        by (simp add: ProcessMessageAction_def dispatchMessage_def runM_whenCorrectDestination
          doReboot_def ProcessMessage_def handleReboot_def)
    qed
  qed
qed

end




























































