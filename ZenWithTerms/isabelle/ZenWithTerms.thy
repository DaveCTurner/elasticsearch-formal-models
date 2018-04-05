theory ZenWithTerms
  imports "../../common/isabelle/TLA-Utils"
begin

lemma card_insert_le_general: "card A \<le> card (insert x A)"
proof (cases "finite A")
  case True thus ?thesis by (intro card_insert_le)
qed simp

typedecl Value
typedecl Node

definition ValidConfigs :: "Node set set"
  where "ValidConfigs \<equiv> {vs. finite vs \<and> vs \<noteq> {}}"

definition modifyAt :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"
  where "modifyAt f a0 mb a \<equiv> if a = a0 then mb (f a) else f a"

lemma modifyAt_eq_simp[simp]: "modifyAt f a mb a = mb (f a)" by (simp add: modifyAt_def)
lemma modifyAt_ne_simp[simp]: "a \<noteq> a0 \<Longrightarrow> modifyAt f a0 mb a = f a" by (simp add: modifyAt_def)

definition modified :: "('a \<Rightarrow> 'b) stfun \<Rightarrow> 'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> action"
  where "modified f a mb st \<equiv> f (snd st) = modifyAt (f (fst st)) a mb"

definition updated :: "('a \<Rightarrow> 'b) stfun \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> action"
  where "updated f a b = modified f a (\<lambda>_. b)"

record DescendentsEntry =
  prevT :: nat
  prevI :: nat
  nextT :: nat
  nextI :: nat

record JoinPayload =
  jp_laTerm     :: nat
  jp_laVersion  :: nat

record PublishRequestPayload =
  prq_version  :: nat
  prq_value    :: Value
  prq_config   :: "Node set"
  prq_currConf :: "Node set"

record PublishResponsePayload =
  prs_version  :: nat

record CommitPayload =
  c_version  :: nat

datatype Payload
  = Join            JoinPayload
  | PublishRequest  PublishRequestPayload
  | PublishResponse PublishResponsePayload
  | Commit          CommitPayload

record Message =
  source  :: Node
  dest    :: Node
  "term"  :: nat (* quoting needed because 'term' is a reserved word *)
  payload :: Payload

definition laTerm    :: "Message \<Rightarrow> nat" where "laTerm     m \<equiv> case payload m of Join jp \<Rightarrow> jp_laTerm     jp"
definition laVersion :: "Message \<Rightarrow> nat" where "laVersion  m \<equiv> case payload m of Join jp \<Rightarrow> jp_laVersion  jp"
definition version   :: "Message \<Rightarrow> nat" where "version  m \<equiv> case payload m of
    PublishRequest  prq \<Rightarrow> prq_version  prq
  | PublishResponse prs \<Rightarrow> prs_version  prs
  | Commit          c   \<Rightarrow> c_version    c"
definition "value"   :: "Message \<Rightarrow> Value" where "value m \<equiv> case payload m of
    PublishRequest  prq \<Rightarrow> prq_value prq"
definition config    :: "Message \<Rightarrow> Node set" where "config m \<equiv> case payload m of
    PublishRequest  prq \<Rightarrow> prq_config prq"
definition currConf  :: "Message \<Rightarrow> Node set" where "currConf m \<equiv> case payload m of
    PublishRequest  prq \<Rightarrow> prq_currConf prq"

datatype TermVersion  = TermVersion  nat (* term *) nat (* version  *)

instantiation TermVersion  :: linorder
begin
fun less_TermVersion  :: "TermVersion  \<Rightarrow> TermVersion  \<Rightarrow> bool" where
  "less_TermVersion  (TermVersion  t1 i1) (TermVersion  t2 i2) = (t1 < t2 \<or> (t1 = t2 \<and> i1 < i2))"
definition less_eq_TermVersion  :: "TermVersion  \<Rightarrow> TermVersion  \<Rightarrow> bool" where
  "less_eq_TermVersion  ti1 ti2 = (ti1 = ti2 \<or> ti1 < ti2)"
instance proof
  fix x y z :: TermVersion
  obtain tx ix where x: "x = TermVersion  tx ix" by (cases x, auto)
  obtain ty iy where y: "y = TermVersion  ty iy" by (cases y, auto)
  obtain tz iz where z: "z = TermVersion  tz iz" by (cases z, auto)

  from x y z
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" "x \<le> x" "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" "x \<le> y \<or> y \<le> x" by (auto simp add: less_eq_TermVersion_def)
qed
end

locale ZenWithTerms =
  (* real variables *)
  fixes currentTerm                 :: "(Node \<Rightarrow> nat)      stfun"
  fixes lastCommittedConfiguration  :: "(Node \<Rightarrow> Node set) stfun"
  fixes lastAcceptedTerm            :: "(Node \<Rightarrow> nat)      stfun"
  fixes lastAcceptedVersion         :: "(Node \<Rightarrow> nat)      stfun"
  fixes lastAcceptedValue           :: "(Node \<Rightarrow> Value)    stfun"
  fixes lastAcceptedConfiguration   :: "(Node \<Rightarrow> Node set) stfun"
  fixes joinVotes                   :: "(Node \<Rightarrow> Node set) stfun"
  fixes startedJoinSinceLastReboot  :: "(Node \<Rightarrow> bool)     stfun"
  fixes electionWon                 :: "(Node \<Rightarrow> bool)     stfun"
  fixes lastPublishedVersion        :: "(Node \<Rightarrow> nat)      stfun"
  fixes publishVotes                :: "(Node \<Rightarrow> Node set) stfun"
    (* message history *)
  fixes messages                    :: "Message set stfun"
    (* artificial variables *)
  fixes descendant                  :: "DescendentsEntry set stfun"
  fixes initialConfiguration        :: "Node set stfun" (* constant *)
  fixes initialValue                :: "Value stfun" (* constant *)
  fixes leaderHistory               :: "(nat \<times> Node) set stfun"
  fixes basedOn                     :: "(TermVersion  \<times> TermVersion) set stfun"
    (* TODO idea: track last-committed term + version, to link the current state to the proposals *)
  fixes vars defines "vars \<equiv> LIFT (messages, descendant, currentTerm, lastCommittedConfiguration,
    lastAcceptedTerm, lastAcceptedVersion, lastAcceptedValue, lastAcceptedConfiguration, joinVotes,
    startedJoinSinceLastReboot, electionWon, lastPublishedVersion, publishVotes,
    initialConfiguration, initialValue, leaderHistory, basedOn)"
    (* IsQuorum predicate *)
  fixes IsQuorum :: "Node set \<Rightarrow> Node set \<Rightarrow> bool"
  defines "IsQuorum votes qconfig \<equiv> card (votes \<inter> qconfig) * 2 > card qconfig"
    (* ElectionWon predicate *)
  fixes ElectionWon :: "Node \<Rightarrow> Node set \<Rightarrow> stpred"
  defines "ElectionWon n votes \<equiv> PRED
    ( IsQuorum<#votes,id<lastCommittedConfiguration,#n>>
    \<and> IsQuorum<#votes,id<lastAcceptedConfiguration,#n>>
    )"
    (* Initial state *)
  fixes Initial :: stpred
  defines "Initial \<equiv> PRED
      messages = #{}
    \<and> descendant = #{}
    \<and> (\<forall>n. id<currentTerm,#n> = #0)
    \<and> (\<exists> vc. #vc \<in> #ValidConfigs \<and> (\<forall>n. id<lastCommittedConfiguration,#n> = #vc)) (* agreement on initial configuration *)
    \<and> (\<forall>n. id<lastAcceptedTerm,#n> = #0)
    \<and> (\<forall>n. id<lastAcceptedTerm,#n> = #0)
    \<and> (\<forall>n. id<lastAcceptedVersion,#n> = #0)
    \<and> (\<exists> v. \<forall>n. id<lastAcceptedValue,#n> = #v) (* agreement on initial value *)
    \<and> (\<forall>n. id<lastAcceptedConfiguration,#n> = id<lastCommittedConfiguration,#n>)
    \<and> (\<forall>n. id<joinVotes,#n> = #{})
    \<and> (\<forall>n. id<startedJoinSinceLastReboot,#n> = #False)
    \<and> (\<forall>n. id<electionWon,#n> = #False)
    \<and> (\<forall>n. id<lastPublishedVersion,#n> = #0)
    \<and> (\<forall>n. id<publishVotes,#n> = #{})
    \<and> (\<forall>n. id<lastAcceptedConfiguration,#n> = initialConfiguration)
    \<and> (\<forall>n. id<lastAcceptedValue,#n> = initialValue)
    \<and> leaderHistory = #{}
    \<and> basedOn = #{}"
    (* HandleStartJoin *)
    (* Send join request from node n to node nm for term t *)
  fixes HandleStartJoin :: "Node \<Rightarrow> Node \<Rightarrow> nat \<Rightarrow> action"
  defines "HandleStartJoin n nm t \<equiv> ACT
    (id<$currentTerm,#n> < #t
      \<and> (\<exists> joinRequest. (\<exists> lastAcceptedTerm_n lastAcceptedVersion_n.
                              #lastAcceptedTerm_n     = id<$lastAcceptedTerm,#n>
                            \<and> #lastAcceptedVersion_n = id<$lastAcceptedVersion,#n>
                            \<and> #(joinRequest = \<lparr> source = n, dest = nm, term = t, payload = Join \<lparr> jp_laTerm = lastAcceptedTerm_n, jp_laVersion  = lastAcceptedVersion_n \<rparr> \<rparr>))
          \<and> updated currentTerm                n t
          \<and> updated lastPublishedVersion       n 0
          \<and> updated startedJoinSinceLastReboot n True
          \<and> updated electionWon                n False
          \<and> updated joinVotes                  n {}
          \<and> updated publishVotes               n {}
          \<and> messages$ = ($messages \<union> #{ joinRequest })
          \<and> unchanged (lastCommittedConfiguration, lastAcceptedConfiguration, lastAcceptedVersion,
                lastAcceptedValue, lastAcceptedTerm, descendant, initialConfiguration, initialValue,
                leaderHistory, basedOn)))"
    (* HandleJoinRequest *)
    (* node n handles a join request and checks if it has received enough joins (= votes) for its term to be elected as master *)
  fixes HandleJoinRequest :: "Node \<Rightarrow> Message \<Rightarrow> action"
  defines "HandleJoinRequest n m \<equiv> ACT
    ( #(case payload m of Join _ \<Rightarrow> True | _ \<Rightarrow> False)
    \<and> #(term m) = id<$currentTerm,#n>
    \<and> id<$startedJoinSinceLastReboot,#n>
    \<and> ( #(laTerm m) < id<$lastAcceptedTerm,#n>
      \<or> ( #(laTerm     m) = id<$lastAcceptedTerm,#n>
        \<and> #(laVersion  m) \<le> id<$lastAcceptedVersion,#n>))
    \<and> modified joinVotes   n (insert (source m))
    \<and> (\<exists> joinVotes_n electionNowWon. #joinVotes_n = id<joinVotes$,#n>
                                   \<and> #electionNowWon = $(ElectionWon n joinVotes_n)
          \<and> updated electionWon n electionNowWon)
    \<and> (if id<$electionWon,#n> = #False \<and> id<electionWon$,#n> = #True
        then (\<exists> lai. #lai = id<$lastAcceptedVersion,#n>
                  \<and> updated lastPublishedVersion  n lai)
        else unchanged lastPublishedVersion)
    \<and> (if id<electionWon$,#n> then leaderHistory$ = (insert (term m, n))<$leaderHistory> else unchanged leaderHistory)
    \<and> unchanged (lastCommittedConfiguration, currentTerm, publishVotes, messages, descendant,
                 lastAcceptedVersion, lastAcceptedValue, lastAcceptedConfiguration,
                 lastAcceptedTerm, startedJoinSinceLastReboot, initialConfiguration, initialValue, basedOn))"
    (* ClientRequest *)
    (* client causes a cluster state change v with configuration vs *)
  fixes ClientRequest :: "Node \<Rightarrow> Value \<Rightarrow> Node set \<Rightarrow> action"
  defines "ClientRequest n v vs \<equiv> ACT
    ( id<$electionWon,#n>
    \<and> id<$lastPublishedVersion,#n> = id<$lastAcceptedVersion,#n> (* means we have the last published value / config (useful for CAS operations, where we need to read the previous value first) *)
    \<and> (#vs \<noteq> id<$lastAcceptedConfiguration,#n> \<longrightarrow> id<$lastCommittedConfiguration,#n> = id<$lastAcceptedConfiguration,#n>) (* only allow reconfiguration if there is not already a reconfiguration in progress *)
    \<and> (IsQuorum<id<$joinVotes,#n>,#vs>) (* only allow reconfiguration if we have a quorum of (join) votes for the new config *)
    \<and> (\<exists> newPublishVersion  publishRequests newEntry matchingElems newTransitiveElems
          currentTerm_n lastCommittedConfiguration_n lastAcceptedTerm_n lastAcceptedVersion_n.
            #currentTerm_n          = id<$currentTerm,#n>
          \<and> #lastCommittedConfiguration_n = id<$lastCommittedConfiguration,#n>
          \<and> #lastAcceptedTerm_n     = id<$lastAcceptedTerm,#n>
          \<and> #lastAcceptedVersion_n = id<$lastAcceptedVersion,#n>

          \<and> #newPublishVersion  = id<$lastPublishedVersion,#n> + #1
          \<and> #publishRequests = #(\<Union> ns \<in> UNIV. {
                \<lparr> source = n, dest = ns, term = currentTerm_n
                , payload = PublishRequest \<lparr> prq_version  = newPublishVersion
                                           , prq_value = v
                                           , prq_config = vs
                                           , prq_currConf = lastCommittedConfiguration_n \<rparr>\<rparr>})
          \<and> #newEntry = #\<lparr> prevT = lastAcceptedTerm_n
                         , prevI = lastAcceptedVersion_n
                         , nextT = currentTerm_n
                         , nextI = newPublishVersion  \<rparr>
          \<and> #matchingElems = (\<lambda>d. { e \<in> d. nextT e = prevT newEntry \<and> nextI e = prevI newEntry})<$descendant>
          \<and> #newTransitiveElems = #(\<Union> e \<in> matchingElems. {\<lparr> prevT = prevT e, prevI = prevI e, nextT = nextT newEntry, nextI = nextI newEntry \<rparr>})

          \<and> descendant$ = ($descendant \<union> #{newEntry} \<union> #newTransitiveElems)
          \<and> updated lastPublishedVersion  n newPublishVersion
          \<and> updated publishVotes    n {}
          \<and> messages$ = ($messages \<union> #publishRequests)
          \<and> basedOn$ = (insert ( TermVersion  currentTerm_n newPublishVersion
                                , TermVersion  lastAcceptedTerm_n lastAcceptedVersion_n ))<$basedOn>
          \<and> unchanged (startedJoinSinceLastReboot, lastCommittedConfiguration, currentTerm, electionWon,
                      lastAcceptedVersion, lastAcceptedValue, lastAcceptedTerm,
                      lastAcceptedConfiguration, joinVotes, initialConfiguration, initialValue,
                      leaderHistory)))"
    (* HandlePublishRequest *)
    (* handle publish request m on node n *)
  fixes HandlePublishRequest :: "Node \<Rightarrow> Message \<Rightarrow> action"
  defines "HandlePublishRequest n m \<equiv> ACT
    ( #(case payload m of PublishRequest _ \<Rightarrow> True | _ \<Rightarrow> False)
    \<and> #(term m) = id<$currentTerm,#n>
    \<and> ((#(term m) = id<$lastAcceptedTerm,#n>) \<longrightarrow> (id<$lastAcceptedVersion,#n> < #(version  m)))
    \<and> updated lastAcceptedTerm           n (term     m)
    \<and> updated lastAcceptedVersion        n (version  m)
    \<and> updated lastAcceptedValue          n (value    m)
    \<and> updated lastAcceptedConfiguration  n (config   m)
    \<and> updated lastCommittedConfiguration n (currConf m)
    \<and> messages$ = (insert \<lparr> source = n, dest = source m, term = term m
                          , payload = PublishResponse \<lparr> prs_version  = version  m \<rparr> \<rparr>)<$messages>
    \<and> unchanged (startedJoinSinceLastReboot, currentTerm, descendant, electionWon, lastPublishedVersion, joinVotes,
                  publishVotes, initialConfiguration, initialValue, leaderHistory, basedOn))"
    (* HandlePublishResponse *)
    (* node n commits a change *)
  fixes HandlePublishResponse :: "Node \<Rightarrow> Message \<Rightarrow> action"
  defines "HandlePublishResponse n m \<equiv> ACT
    ( #(case payload m of PublishResponse _ \<Rightarrow> True | _ \<Rightarrow> False)
    \<and> #(term     m) = id<$currentTerm,#n>
    \<and> #(version  m) = id<$lastPublishedVersion,#n>
    \<and> modified publishVotes n (insert (source m))
    \<and> (if IsQuorum<id<publishVotes$,#n>,id<$lastCommittedConfiguration,#n>>
        then (\<exists> commitRequests currentTerm_n lastPublishedVersion_n.
                  #lastPublishedVersion_n = id<$lastPublishedVersion,#n>
                \<and> #commitRequests = #(\<Union> ns \<in> UNIV. {
                        \<lparr> source = n, dest = ns, term = term m
                        , payload = Commit \<lparr> c_version  = version  m \<rparr> \<rparr>})
                \<and> messages$ = ($messages \<union> #commitRequests))
        else unchanged messages)
    \<and> unchanged (startedJoinSinceLastReboot, lastCommittedConfiguration, currentTerm, electionWon, descendant,
                   lastAcceptedVersion, lastAcceptedValue, lastAcceptedTerm, lastAcceptedConfiguration,
                   lastPublishedVersion, joinVotes, initialConfiguration, initialValue, leaderHistory, basedOn))"
    (* HandleCommitRequest *)
    (* apply committed configuration to node n *)
  fixes HandleCommitRequest :: "Node \<Rightarrow> Message \<Rightarrow> action"
  defines "HandleCommitRequest n m \<equiv> ACT
    ( #(case payload m of Commit _ \<Rightarrow> True | _ \<Rightarrow> False)
    \<and> #(term     m) = id<$currentTerm,#n>
    \<and> #(term     m) = id<$lastAcceptedTerm,#n>
    \<and> #(version  m) = id<$lastAcceptedVersion,#n>
    \<and> (\<exists> lastAcceptedConfiguration_n. #lastAcceptedConfiguration_n = id<$lastAcceptedConfiguration,#n>
          \<and> updated lastCommittedConfiguration n lastAcceptedConfiguration_n)
    \<and> unchanged (currentTerm, joinVotes, messages, lastAcceptedTerm, lastAcceptedValue, startedJoinSinceLastReboot,
                 descendant, electionWon, lastAcceptedConfiguration, lastAcceptedVersion,
                 lastPublishedVersion, publishVotes, initialConfiguration, initialValue, leaderHistory, basedOn))"
    (* RestartNode *)
    (* crash/restart node n (loses ephemeral state) *)
  fixes RestartNode :: "Node \<Rightarrow> action"
  defines "RestartNode n \<equiv> ACT
    ( updated electionWon                n False
    \<and> updated startedJoinSinceLastReboot n False
    \<and> updated joinVotes                  n {}
    \<and> updated lastPublishedVersion       n 0
    \<and> updated publishVotes               n {}
    \<and> unchanged (messages, lastAcceptedVersion, currentTerm, lastCommittedConfiguration, descendant,
                 lastAcceptedTerm, lastAcceptedValue, lastAcceptedConfiguration, initialConfiguration,
                 initialValue, leaderHistory, basedOn))"
    (* Next *)
    (* next-step relation *)
  fixes Next :: action
  defines "Next \<equiv> ACT
    ( (\<exists> n nm tm. HandleStartJoin n nm tm) (* NB deviation from TLA+ model: here we try arbitrary terms *)
    \<or> (\<exists> m. #m \<in> $messages \<and> HandleJoinRequest (dest m) m)
    \<or> (\<exists> n v vs. #vs \<in> #ValidConfigs \<and> ClientRequest n v vs)
    \<or> (\<exists> m. #m \<in> $messages \<and> HandlePublishRequest  (dest m) m)
    \<or> (\<exists> m. #m \<in> $messages \<and> HandlePublishResponse (dest m) m)
    \<or> (\<exists> m. #m \<in> $messages \<and> HandleCommitRequest   (dest m) m)
    \<or> (\<exists> n. RestartNode n))"
    (* Spec *)
    (* Complete specification *)
  fixes Spec :: temporal
  defines "Spec \<equiv> TEMP Init Initial \<and> \<box>[Next]_vars"

context ZenWithTerms
begin


lemma square_Next_cases [consumes 1, case_names unchanged HandleStartJoin HandleJoinRequest ClientRequest
    HandlePublishRequest HandlePublishResponse_NoQuorum HandlePublishResponse_Quorum HandleCommitRequest RestartNode]:
  assumes Next: "(s,t) \<Turnstile> [Next]_vars"
  assumes unchanged:
    "\<lbrakk> messages                  t = messages                   s
    ; descendant                 t = descendant                 s
    ; currentTerm                t = currentTerm                s
    ; lastCommittedConfiguration t = lastCommittedConfiguration s
    ; lastAcceptedTerm           t = lastAcceptedTerm           s
    ; lastAcceptedVersion        t = lastAcceptedVersion        s
    ; lastAcceptedValue          t = lastAcceptedValue          s
    ; lastAcceptedConfiguration  t = lastAcceptedConfiguration  s
    ; joinVotes                  t = joinVotes                  s
    ; startedJoinSinceLastReboot t = startedJoinSinceLastReboot s
    ; electionWon                t = electionWon                s
    ; lastPublishedVersion       t = lastPublishedVersion       s
    ; publishVotes               t = publishVotes               s
    ; initialConfiguration       t = initialConfiguration       s
    ; initialValue               t = initialValue               s
    ; leaderHistory              t = leaderHistory              s
    ; basedOn                    t = basedOn                    s
    \<rbrakk> \<Longrightarrow> P"
  assumes HandleStartJoin: "\<And>nf nm tm newJoinRequest.
    \<lbrakk> currentTerm s nf < tm
    ; newJoinRequest = \<lparr> source = nf, dest = nm, term = tm
        , payload = Join \<lparr> jp_laTerm = lastAcceptedTerm s nf, jp_laVersion  = lastAcceptedVersion  s nf \<rparr> \<rparr>
    ; messages                         t    = insert newJoinRequest (messages s)
    ; descendant                       t    = descendant                 s
    ; \<And>n'. currentTerm                t n' = (if n' = nf then tm else currentTerm s n')
    ; lastCommittedConfiguration       t    = lastCommittedConfiguration s
    ; lastAcceptedTerm                 t    = lastAcceptedTerm           s
    ; lastAcceptedVersion              t    = lastAcceptedVersion        s
    ; lastAcceptedValue                t    = lastAcceptedValue          s
    ; lastAcceptedConfiguration        t    = lastAcceptedConfiguration  s
    ; \<And>n'. joinVotes                  t n' = (if n' = nf then {}    else joinVotes       s n')
    ; \<And>n'. startedJoinSinceLastReboot t n' = (if n' = nf then True  else startedJoinSinceLastReboot   s n')
    ; \<And>n'. electionWon                t n' = (if n' = nf then False else electionWon     s n')
    ; \<And>n'. lastPublishedVersion       t n' = (if n' = nf then 0     else lastPublishedVersion  s n')
    ; \<And>n'. publishVotes               t n' = (if n' = nf then {}    else publishVotes    s n')
    ; \<And>n'. currentTerm s n' \<le> currentTerm t n'
    ; initialConfiguration             t    = initialConfiguration       s
    ; initialValue                     t    = initialValue               s
    ; leaderHistory                    t    = leaderHistory              s
    ; basedOn                          t    = basedOn                    s
    \<rbrakk> \<Longrightarrow> P"
  assumes HandleJoinRequest: "\<And>nf nm laTerm_m laVersion_m.
    \<lbrakk> \<lparr> source = nf, dest = nm, term = currentTerm s nm
      , payload = Join \<lparr> jp_laTerm = laTerm_m, jp_laVersion  = laVersion_m \<rparr> \<rparr> \<in> messages s
    ; startedJoinSinceLastReboot s nm
    ; laTerm_m < lastAcceptedTerm s nm \<or> (laTerm_m = lastAcceptedTerm s nm \<and> laVersion_m \<le> lastAcceptedVersion  s nm)
    ; messages                   t    = messages                   s 
    ; descendant                 t    = descendant                 s
    ; currentTerm                t    = currentTerm                s
    ; lastCommittedConfiguration t    = lastCommittedConfiguration s
    ; lastAcceptedTerm           t    = lastAcceptedTerm           s
    ; lastAcceptedVersion        t    = lastAcceptedVersion        s
    ; lastAcceptedValue          t    = lastAcceptedValue          s
    ; lastAcceptedConfiguration  t    = lastAcceptedConfiguration  s
    ; \<And>n'. joinVotes            t n' = (if n' = nm then insert nf (joinVotes s nm) else joinVotes s n')
    ; startedJoinSinceLastReboot t    = startedJoinSinceLastReboot s
    ; \<And>n'. electionWon          t n' = (if n' = nm then IsQuorum (joinVotes t nm) (lastCommittedConfiguration s nm) \<and> IsQuorum (joinVotes t nm) (lastAcceptedConfiguration s nm) else electionWon s n')
    ; \<And>n'. lastPublishedVersion t n' = (if n' = nm then if \<not>(electionWon s nm) \<and> electionWon t nm then lastAcceptedVersion  s nm else lastPublishedVersion  s n' else lastPublishedVersion  s n')
    ; publishVotes               t    = publishVotes               s
    ; initialConfiguration       t    = initialConfiguration       s
    ; initialValue               t    = initialValue               s
    ; leaderHistory              t    = (if electionWon t nm then insert (currentTerm s nm, nm) (leaderHistory s) else (leaderHistory s))
    ; basedOn                    t    = basedOn                    s
    \<rbrakk> \<Longrightarrow> P"
  assumes ClientRequest: "\<And>nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems.
    \<lbrakk> electionWon s nm
    ; vs \<in> ValidConfigs
    ; lastPublishedVersion  s nm = lastAcceptedVersion  s nm
    ; vs \<noteq> lastAcceptedConfiguration s nm \<Longrightarrow> lastCommittedConfiguration s nm = lastAcceptedConfiguration s nm
    ; IsQuorum (joinVotes s nm) vs
    ; newPublishVersion  = lastPublishedVersion  s nm + 1
    ; newPublishRequests = (\<Union> nf \<in> UNIV. {
                \<lparr> source = nm, dest = nf, term = currentTerm s nm
                , payload = PublishRequest \<lparr> prq_version  = newPublishVersion
                                           , prq_value    = v
                                           , prq_config   = vs
                                           , prq_currConf = lastCommittedConfiguration s nm \<rparr>\<rparr>})
    ; newEntry = \<lparr> prevT = lastAcceptedTerm     s nm
                 , prevI = lastAcceptedVersion  s nm
                 , nextT = currentTerm          s nm
                 , nextI = newPublishVersion  \<rparr>
    ; matchingElems = { e \<in> descendant s. nextT e = prevT newEntry \<and> nextI e = prevI newEntry}
    ; newTransitiveElems = (\<Union> e \<in> matchingElems. {\<lparr> prevT = prevT e, prevI = prevI e, nextT = nextT newEntry, nextI = nextI newEntry \<rparr>})
    ; messages                   t    = (messages s) \<union> newPublishRequests
    ; descendant                 t    = (descendant s) \<union> insert newEntry newTransitiveElems
    ; currentTerm                t    = currentTerm                s
    ; lastCommittedConfiguration t    = lastCommittedConfiguration s
    ; lastAcceptedTerm           t    = lastAcceptedTerm           s
    ; lastAcceptedVersion        t    = lastAcceptedVersion        s
    ; lastAcceptedValue          t    = lastAcceptedValue          s
    ; lastAcceptedConfiguration  t    = lastAcceptedConfiguration  s
    ; joinVotes                  t    = joinVotes                  s
    ; startedJoinSinceLastReboot t    = startedJoinSinceLastReboot s
    ; electionWon                t    = electionWon                s
    ; \<And>n'. lastPublishedVersion t n' = (if n' = nm then newPublishVersion  else lastPublishedVersion  s n')
    ; \<And>n'. publishVotes         t n' = (if n' = nm then {} else publishVotes s n')
    ; initialConfiguration       t    = initialConfiguration       s
    ; initialValue               t    = initialValue               s
    ; leaderHistory              t    = leaderHistory              s
    ; basedOn                    t    = insert ( TermVersion  (currentTerm s nm)      newPublishVersion
                                               , TermVersion  (lastAcceptedTerm s nm) (lastAcceptedVersion  s nm))
                                               (basedOn s)
    \<rbrakk> \<Longrightarrow> P"
  assumes HandlePublishRequest: "\<And>nf nm newVersion  newValue newConfig currConfig.
    \<lbrakk> \<lparr> source = nm, dest = nf, term = currentTerm s nf
      , payload = PublishRequest \<lparr> prq_version  = newVersion, prq_value = newValue, prq_config = newConfig, prq_currConf = currConfig \<rparr> \<rparr> \<in> messages s
    ; currentTerm s nf = lastAcceptedTerm s nf \<Longrightarrow> lastAcceptedVersion  s nf < newVersion
    ; messages t = insert \<lparr> source = nf, dest = nm, term = currentTerm s nf, payload = PublishResponse \<lparr> prs_version  = newVersion  \<rparr> \<rparr> (messages s)
    ; descendant                       t    = descendant                 s
    ; currentTerm                      t    = currentTerm                s
    ; \<And>n'. lastCommittedConfiguration t n' = (if n' = nf then currConfig       else lastCommittedConfiguration s n')
    ; \<And>n'. lastAcceptedTerm           t n' = (if n' = nf then currentTerm s nf else lastAcceptedTerm           s n')
    ; \<And>n'. lastAcceptedVersion        t n' = (if n' = nf then newVersion       else lastAcceptedVersion        s n')
    ; \<And>n'. lastAcceptedValue          t n' = (if n' = nf then newValue         else lastAcceptedValue          s n')
    ; \<And>n'. lastAcceptedConfiguration  t n' = (if n' = nf then newConfig        else lastAcceptedConfiguration  s n')
    ; joinVotes                        t    = joinVotes                  s
    ; startedJoinSinceLastReboot       t    = startedJoinSinceLastReboot s
    ; electionWon                      t    = electionWon                s
    ; lastPublishedVersion             t    = lastPublishedVersion       s
    ; publishVotes                     t    = publishVotes               s
    ; initialConfiguration             t    = initialConfiguration       s
    ; initialValue                     t    = initialValue               s
    ; leaderHistory                    t    = leaderHistory              s
    ; basedOn                          t    = basedOn                    s
    \<rbrakk> \<Longrightarrow> P"
  assumes HandlePublishResponse_NoQuorum: "\<And>nf nm.
    \<lbrakk> \<lparr> source = nf, dest = nm, term = currentTerm s nm
      , payload = PublishResponse \<lparr> prs_version  = lastPublishedVersion  s nm \<rparr> \<rparr> \<in> messages s
    ; \<not> IsQuorum (publishVotes t nm) (lastCommittedConfiguration s nm)
    ; messages                   t    = messages                   s
    ; descendant                 t    = descendant                 s
    ; currentTerm                t    = currentTerm                s
    ; lastCommittedConfiguration t    = lastCommittedConfiguration s
    ; lastAcceptedTerm           t    = lastAcceptedTerm           s
    ; lastAcceptedVersion        t    = lastAcceptedVersion        s
    ; lastAcceptedValue          t    = lastAcceptedValue          s
    ; lastAcceptedConfiguration  t    = lastAcceptedConfiguration  s
    ; joinVotes                  t    = joinVotes                  s
    ; startedJoinSinceLastReboot t    = startedJoinSinceLastReboot s
    ; electionWon                t    = electionWon                s
    ; lastPublishedVersion       t    = lastPublishedVersion       s
    ; \<And>n'. publishVotes         t n' = (if n' = nm then insert nf (publishVotes s nm) else publishVotes s n')
    ; initialConfiguration       t    = initialConfiguration       s
    ; initialValue               t    = initialValue               s
    ; leaderHistory              t    = leaderHistory              s
    ; basedOn                    t    = basedOn                    s
    \<rbrakk> \<Longrightarrow> P"
  assumes HandlePublishResponse_Quorum: "\<And>nf nm.
    \<lbrakk> \<lparr> source = nf, dest = nm, term = currentTerm s nm
      , payload = PublishResponse \<lparr> prs_version  = lastPublishedVersion  s nm \<rparr> \<rparr> \<in> messages s
    ; IsQuorum (publishVotes t nm) (lastCommittedConfiguration s nm)
    ; messages                   t    = messages s \<union> (\<Union> n \<in> UNIV. {\<lparr> source = nm, dest = n, term = currentTerm s nm, payload = Commit \<lparr> c_version  = lastPublishedVersion  s nm \<rparr> \<rparr>})
    ; descendant                 t    = descendant                 s
    ; currentTerm                t    = currentTerm                s
    ; lastCommittedConfiguration t    = lastCommittedConfiguration s
    ; lastAcceptedTerm           t    = lastAcceptedTerm           s
    ; lastAcceptedVersion        t    = lastAcceptedVersion        s
    ; lastAcceptedValue          t    = lastAcceptedValue          s
    ; lastAcceptedConfiguration  t    = lastAcceptedConfiguration  s
    ; joinVotes                  t    = joinVotes                  s
    ; startedJoinSinceLastReboot t    = startedJoinSinceLastReboot s
    ; electionWon                t    = electionWon                s
    ; lastPublishedVersion       t    = lastPublishedVersion       s
    ; \<And>n'. publishVotes         t n' = (if n' = nm then insert nf (publishVotes s nm) else publishVotes s n')
    ; initialConfiguration       t    = initialConfiguration       s
    ; initialValue               t    = initialValue               s
    ; leaderHistory              t    = leaderHistory              s
    ; basedOn                    t    = basedOn                    s
    \<rbrakk> \<Longrightarrow> P"
  assumes HandleCommitRequest: "\<And>nf nm.
    \<lbrakk> \<lparr> source = nm, dest = nf, term = currentTerm s nf
      , payload = Commit \<lparr> c_version  = lastAcceptedVersion  s nf \<rparr> \<rparr> \<in> messages s
    ; lastAcceptedTerm s nf = currentTerm s nf
    ; messages                   t          = messages                   s
    ; descendant                 t          = descendant                 s
    ; currentTerm                t          = currentTerm                s
    ; \<And>n'. lastCommittedConfiguration t n' = (if n' = nf then lastAcceptedConfiguration s nf else lastCommittedConfiguration s n')
    ; lastAcceptedTerm           t          = lastAcceptedTerm           s
    ; lastAcceptedVersion        t          = lastAcceptedVersion        s
    ; lastAcceptedValue          t          = lastAcceptedValue          s
    ; lastAcceptedConfiguration  t          = lastAcceptedConfiguration  s
    ; joinVotes                  t          = joinVotes                  s
    ; startedJoinSinceLastReboot t          = startedJoinSinceLastReboot s
    ; electionWon                t          = electionWon                s
    ; lastPublishedVersion       t          = lastPublishedVersion       s
    ; publishVotes               t          = publishVotes               s
    ; initialConfiguration       t          = initialConfiguration       s
    ; initialValue               t          = initialValue               s
    ; leaderHistory              t          = leaderHistory              s
    ; basedOn                    t          = basedOn                    s
    \<rbrakk> \<Longrightarrow> P" 
  assumes RestartNode: "\<And>nr.
    \<lbrakk> messages                         t    = messages                   s
    ; descendant                       t    = descendant                 s
    ; currentTerm                      t    = currentTerm                s
    ; lastCommittedConfiguration       t    = lastCommittedConfiguration s
    ; lastAcceptedTerm                 t    = lastAcceptedTerm           s
    ; lastAcceptedVersion              t    = lastAcceptedVersion        s
    ; lastAcceptedValue                t    = lastAcceptedValue          s
    ; lastAcceptedConfiguration        t    = lastAcceptedConfiguration  s
    ; \<And>n'. joinVotes                  t n' = (if n' = nr then {}    else joinVotes                  s n')
    ; \<And>n'. startedJoinSinceLastReboot t n' = (if n' = nr then False else startedJoinSinceLastReboot s n')
    ; \<And>n'. electionWon                t n' = (if n' = nr then False else electionWon                s n')
    ; \<And>n'. lastPublishedVersion       t n' = (if n' = nr then 0     else lastPublishedVersion       s n')
    ; \<And>n'. publishVotes               t n' = (if n' = nr then {}    else publishVotes               s n')
    ; initialConfiguration             t    = initialConfiguration       s
    ; initialValue                     t    = initialValue               s
    ; leaderHistory                    t    = leaderHistory              s
    ; basedOn                          t    = basedOn                    s
    \<rbrakk> \<Longrightarrow> P" 
  shows "P"
proof -
  from Next show P unfolding square_def Next_def
  proof (elim temp_disjE temp_exE temp_conjE)
    assume "(s,t) \<Turnstile> unchanged vars"
    thus P by (intro unchanged, auto simp add: vars_def)
  next
    fix n nm tm
    define joinRequest where "joinRequest \<equiv> \<lparr> source = n, dest = nm, term = tm
        , payload = Join \<lparr> jp_laTerm = lastAcceptedTerm s n, jp_laVersion  = lastAcceptedVersion  s n \<rparr> \<rparr>"
    assume p: "(s,t) \<Turnstile> HandleStartJoin n nm tm"

    have "\<And>n'. currentTerm s n' \<le> currentTerm t n'"
      using p
      by (auto simp add: HandleStartJoin_def updated_def modified_def modifyAt_def)

    with p show  P
      by (intro HandleStartJoin [of n tm joinRequest nm],
          auto simp add: HandleStartJoin_def updated_def modified_def joinRequest_def)
  next
    fix m
    assume p: "(s,t) \<Turnstile> #m \<in> $messages" "(s,t) \<Turnstile> HandleJoinRequest (dest m) m"

    from p obtain jp where jp: "payload m = Join jp" by (cases "payload m", auto simp add: HandleJoinRequest_def)
    from p have term_m: "term m = currentTerm s (dest m)" by (auto simp add: HandleJoinRequest_def)

    have jp_eq: "jp = \<lparr>jp_laTerm = laTerm m, jp_laVersion  = laVersion  m\<rparr>"
      by (simp add: laTerm_def jp laVersion_def)

    have "m = \<lparr> source = source m, dest = dest m, term = currentTerm s (dest m), payload = Join jp \<rparr>"
      by (simp add: jp term_m)
    with p jp_eq have is_message: "\<lparr> source = source m, dest = dest m, term = currentTerm s (dest m), payload = Join \<lparr>jp_laTerm = laTerm m, jp_laVersion  = laVersion  m\<rparr> \<rparr> \<in> messages s" by simp

    from p is_message show P
      apply (intro HandleJoinRequest [of "source m" "dest m" "laTerm m" "laVersion  m"])
      by (auto simp add: HandleJoinRequest_def updated_def modified_def ElectionWon_def modifyAt_def)
  next
    fix nm v vs
    assume p: "(s,t) \<Turnstile> #vs \<in> #ValidConfigs" "(s,t) \<Turnstile> ClientRequest nm v vs"

    from p show P
      apply (intro ClientRequest [of nm vs])
      by (auto simp add: ClientRequest_def updated_def modified_def)
  next
    fix m
    assume p: "(s,t) \<Turnstile> #m \<in> $messages" "(s,t) \<Turnstile> HandlePublishRequest (dest m) m"

    from p obtain prq where prq: "payload m = PublishRequest prq" by (cases "payload m", auto simp add: HandlePublishRequest_def)
    from p have term_m: "term m = currentTerm s (dest m)" by (auto simp add: HandlePublishRequest_def)

    have prq_eq: "prq = \<lparr>prq_version  = version  m, prq_value = value m, prq_config = config m, prq_currConf = currConf m\<rparr>"
      by (simp add: version_def prq value_def config_def currConf_def)

    have "m = \<lparr> source = source m, dest = dest m, term = currentTerm s (dest m), payload = PublishRequest prq \<rparr>"
      by (simp add: prq term_m)
    with p prq_eq have is_message: "\<lparr> source = source m, dest = dest m, term = currentTerm s (dest m)
            , payload = PublishRequest \<lparr>prq_version  = version  m
                                        , prq_value = value m, prq_config = config m, prq_currConf = currConf m\<rparr> \<rparr> \<in> messages s" by simp

    from p is_message show P
      apply (intro HandlePublishRequest [of "source m" "dest m" "version  m" "value m" "config m" "currConf m"])
      by (auto simp add: HandlePublishRequest_def updated_def modified_def)
  next
    fix m
    assume p: "(s,t) \<Turnstile> #m \<in> $messages" "(s,t) \<Turnstile> HandlePublishResponse (dest m) m"

    from p obtain prs where prs: "payload m = PublishResponse prs" by (cases "payload m", auto simp add: HandlePublishResponse_def)
    from p have term_m: "term m = currentTerm s (dest m)" by (auto simp add: HandlePublishResponse_def)

    have prq_eq: "prs = \<lparr>prs_version  = version  m\<rparr>" by (simp add: version_def prs)

    have "m = \<lparr> source = source m, dest = dest m, term = currentTerm s (dest m), payload = PublishResponse prs \<rparr>"
      by (simp add: prs term_m)
    with p prq_eq have is_message: "\<lparr> source = source m, dest = dest m, term = currentTerm s (dest m)
            , payload = PublishResponse \<lparr>prs_version  = version  m\<rparr> \<rparr> \<in> messages s" by simp

    show P
    proof (cases "IsQuorum (publishVotes t (dest m)) (lastCommittedConfiguration s (dest m))")
      case False
      with p is_message show P
        apply (intro HandlePublishResponse_NoQuorum [of "source m" "dest m"])
        by (auto simp add: HandlePublishResponse_def updated_def modified_def)
    next
      case True
      with p is_message show P
        apply (intro HandlePublishResponse_Quorum [of "source m" "dest m"])
        by (auto simp add: HandlePublishResponse_def updated_def modified_def)
    qed
  next
    fix m
    assume p: "(s,t) \<Turnstile> #m \<in> $messages" "(s,t) \<Turnstile> HandleCommitRequest (dest m) m"
    from p have payload_eq: "payload m = Commit \<lparr>c_version  = lastAcceptedVersion  s (dest m)\<rparr>"
      by (cases "payload m", auto simp add: HandleCommitRequest_def version_def)

    have "m = \<lparr> source = source m, dest = dest m, term = term m, payload = Commit \<lparr>c_version  = lastAcceptedVersion  s (dest m)\<rparr> \<rparr>" by (simp add: payload_eq)
    with p have is_message: "\<lparr> source = source m, dest = dest m, term = currentTerm s (dest m), payload = Commit \<lparr>c_version  = lastAcceptedVersion  s (dest m)\<rparr> \<rparr> \<in> messages s"
      by (auto simp add: HandleCommitRequest_def)

    from p show P
      apply (intro HandleCommitRequest [of "source m" "dest m"])
      by (auto simp add: HandleCommitRequest_def is_message updated_def modified_def)
  next
    fix n assume p: "(s,t) \<Turnstile> RestartNode n"
    thus P
      by (intro RestartNode [of n], auto simp add: RestartNode_def updated_def modified_def)
  qed
qed

lemma IsQuorum_insert:
  assumes "IsQuorum vs conf"
  shows "IsQuorum (insert v vs) conf"
proof -
  have "card (vs \<inter> conf) \<le> card (insert v vs \<inter> conf)"
  proof (intro card_mono)
    have 1: "finite (vs \<inter> conf)"
      apply (rule ccontr)
      using assms by (auto simp add: IsQuorum_def)
    have 2: "insert v vs \<inter> conf \<subseteq> insert v (vs \<inter> conf)" by auto
    from 1 finite_subset [OF 2]
    show "finite (insert v vs \<inter> conf)" by simp
  qed auto
  with assms show ?thesis by (auto simp add: IsQuorum_def)
qed

definition messagesTo :: "(Node \<Rightarrow> Message set) stfun"
  where "messagesTo s n \<equiv> { m \<in> messages s. dest m = n }"

definition isJoin :: "Message \<Rightarrow> bool"
  where "isJoin m \<equiv> case payload m of Join _ \<Rightarrow> True | _ \<Rightarrow> False"
definition isPublishRequest :: "Message \<Rightarrow> bool"
  where "isPublishRequest m \<equiv> case payload m of PublishRequest _ \<Rightarrow> True | _ \<Rightarrow> False"
definition isPublishResponse :: "Message \<Rightarrow> bool"
  where "isPublishResponse m \<equiv> case payload m of PublishResponse _ \<Rightarrow> True | _ \<Rightarrow> False"
definition isCommit :: "Message \<Rightarrow> bool"
  where "isCommit m \<equiv> case payload m of Commit _ \<Rightarrow> True | _ \<Rightarrow> False"

definition termVersion  :: "Node \<Rightarrow> TermVersion  stfun"
  where "termVersion  n s \<equiv> if startedJoinSinceLastReboot s n
                              then TermVersion  (currentTerm s n) (lastPublishedVersion  s n)
                              else TermVersion  (Suc (currentTerm s n)) 0"
(* if startedJoinSinceLastReboot is true then the node must increase its term before doing anything interesting,
so it is effectively at (term+1, 0) *)

definition msgTermVersion  :: "Message \<Rightarrow> TermVersion"
  where "msgTermVersion  m \<equiv> TermVersion  (term m) (version  m)"

definition TheJoin :: "Node \<Rightarrow> Node \<Rightarrow> Message stfun" where "TheJoin nf nm s \<equiv> 
  THE m. source m = nf \<and> dest m = nm \<and> term m = currentTerm s nm \<and> isJoin m \<and> m \<in> messages s"

definition FiniteMessagesTo :: stpred
  where "FiniteMessagesTo s \<equiv> \<forall>n. finite (messagesTo s n)"

definition JoinRequestsAtMostCurrentTerm :: stpred where "JoinRequestsAtMostCurrentTerm s \<equiv> 
  \<forall> m. isJoin m \<longrightarrow> m \<in> messages s \<longrightarrow> term m \<le> currentTerm s (source m)"

definition JoinRequestsUniquePerTerm :: stpred where "JoinRequestsUniquePerTerm s \<equiv> 
  \<forall> m1 m2. m1 \<in> messages s \<longrightarrow> m2 \<in> messages s 
      \<longrightarrow> isJoin m1 \<longrightarrow> isJoin m2 \<longrightarrow> source m1 = source m2 \<longrightarrow> term m1 = term m2
      \<longrightarrow> m1 = m2"

definition JoinVotesFaithful :: stpred where "JoinVotesFaithful s \<equiv> 
  \<forall> nm nf. nf \<in> joinVotes s nm
      \<longrightarrow> (\<exists> joinPayload. \<lparr> source = nf, dest = nm, term = currentTerm s nm, payload = Join joinPayload \<rparr> \<in> messages s)"

definition JoinVotesImpliesStartedJoin :: stpred where "JoinVotesImpliesStartedJoin s \<equiv>
  \<forall> n. joinVotes s n \<noteq> {} \<longrightarrow> startedJoinSinceLastReboot s n"

definition TheJoinProperty :: stpred where "TheJoinProperty s \<equiv>
  \<forall> nm nf. nf \<in> joinVotes s nm
    \<longrightarrow> source (TheJoin nf nm s) = nf
      \<and> dest (TheJoin nf nm s) = nm
      \<and> term (TheJoin nf nm s) = currentTerm s nm
      \<and> isJoin (TheJoin nf nm s)
      \<and> TheJoin nf nm s \<in> messages s"

definition MessagePositiveTerm :: stpred where "MessagePositiveTerm s \<equiv>
  \<forall>m \<in> messages s. term m > 0"

definition TermIncreasedByJoin :: stpred where "TermIncreasedByJoin s \<equiv>
  \<forall>n. currentTerm s n > 0 \<longrightarrow> (\<exists> m \<in> messages s. isJoin m \<and> currentTerm s n = term m)"

definition LastAcceptedTermInPast :: stpred where "LastAcceptedTermInPast s \<equiv>
  \<forall>n. lastAcceptedTerm s n \<le> currentTerm s n"

definition LastAcceptedDataSource :: stpred where "LastAcceptedDataSource s \<equiv>
  \<forall>n. if lastAcceptedTerm s n = 0
        then lastAcceptedVersion       s n = 0
           \<and> lastAcceptedValue         s n = initialValue s
           \<and> lastAcceptedConfiguration s n = initialConfiguration s
        else (\<exists> m \<in> messages s. isPublishRequest m
                                        \<and> lastAcceptedTerm          s n = term     m
                                        \<and> lastAcceptedVersion       s n = version  m
                                        \<and> lastAcceptedValue         s n = value    m
                                        \<and> lastAcceptedConfiguration s n = config   m)"

definition AllConfigurations :: "Node set set stfun" where "AllConfigurations s \<equiv>
  insert (initialConfiguration s) (config ` { m \<in> messages s. isPublishRequest m })"

definition AllConfigurationsValid :: stpred where "AllConfigurationsValid s \<equiv>
  AllConfigurations s \<subseteq> ValidConfigs"

definition CommittedConfigurations :: "Node set set stfun" where "CommittedConfigurations s \<equiv>
  insert (initialConfiguration s)
    { c. (\<exists> mPub \<in> messages s. isPublishRequest mPub \<and> config mPub = c
           \<and> (\<exists> mCom \<in> messages s. isCommit mCom \<and> term mCom = term mPub \<and> version  mCom = version  mPub)) }"

definition CurrentConfigurationSource :: stpred where "CurrentConfigurationSource s \<equiv>
  \<forall>n. lastCommittedConfiguration s n \<in> CommittedConfigurations s"

definition CurrentConfigurationMsgSource :: stpred where "CurrentConfigurationMsgSource s \<equiv>
  \<forall>m \<in> messages s. isPublishRequest m \<longrightarrow> currConf m \<in> CommittedConfigurations s"

definition PublicationsInPastTerm :: stpred where "PublicationsInPastTerm s \<equiv>
  \<forall>m \<in> messages s. isPublishRequest m \<longrightarrow> term m \<le> currentTerm s (source m)"

definition PublishRequestVersionPositive :: stpred where "PublishRequestVersionPositive s \<equiv>
  \<forall> m \<in> messages s. isPublishRequest m \<longrightarrow> 0 < version  m"

definition LeaderHistoryFaithful :: stpred where "LeaderHistoryFaithful s \<equiv>
  \<forall>n. electionWon s n \<longrightarrow> (currentTerm s n, n) \<in> leaderHistory s"

definition LeaderHistoryBounded :: stpred where "LeaderHistoryBounded s \<equiv>
  \<forall>n tm. (tm, n) \<in> leaderHistory s \<longrightarrow> tm \<le> currentTerm s n"

definition PublishRequestFromHistoricalLeader :: stpred where "PublishRequestFromHistoricalLeader s \<equiv>
  \<forall>m \<in> messages s. isPublishRequest m \<longrightarrow> (term m, source m) \<in> leaderHistory s"

definition BasedOnIncreasing :: stpred where "BasedOnIncreasing s \<equiv>
  \<forall> tPrev iPrev tCurr iCurr. (TermVersion  tCurr iCurr, TermVersion  tPrev iPrev) \<in> basedOn s
    \<longrightarrow> iCurr = Suc iPrev \<and> tPrev \<le> tCurr"

definition PublishRequestBasedOn :: stpred where "PublishRequestBasedOn s \<equiv>
  \<forall> m \<in> messages s. isPublishRequest m \<longrightarrow> (\<exists> tiPrev. (TermVersion  (term m) (version  m), tiPrev) \<in> basedOn s)"

definition BasedOnPublishRequest :: stpred where "BasedOnPublishRequest s \<equiv>
  \<forall> tiPrev tCurr iCurr. (TermVersion  tCurr iCurr, tiPrev) \<in> basedOn s
    \<longrightarrow> (\<exists> m \<in> messages s. isPublishRequest m \<and> term m = tCurr \<and> version  m = iCurr)"

definition BasedOnBasedOn :: stpred where "BasedOnBasedOn s \<equiv>
  \<forall> tiCurr tPrev iPrev. (tiCurr, TermVersion  tPrev iPrev) \<in> basedOn s \<longrightarrow> 0 < iPrev
    \<longrightarrow> (\<exists> tiPrevPrev. (TermVersion  tPrev iPrev, tiPrevPrev) \<in> basedOn s)"

definition ElectionWonQuorumBelow :: "nat \<Rightarrow> stpred" where "ElectionWonQuorumBelow termBound s \<equiv>
  \<forall> n. currentTerm s n < termBound \<longrightarrow> electionWon s n
    \<longrightarrow> IsQuorum (joinVotes s n) (lastCommittedConfiguration s n)
      \<and> IsQuorum (joinVotes s n) (lastAcceptedConfiguration s n)"

definition OneMasterPerTermBelow :: "nat \<Rightarrow> stpred" where "OneMasterPerTermBelow termBound s \<equiv>
  \<forall> n1 n2 tm. tm < termBound \<longrightarrow> (tm, n1) \<in> leaderHistory s \<longrightarrow> (tm, n2) \<in> leaderHistory s
    \<longrightarrow> n1 = n2"

definition PublishRequestImpliesElectionWonBelow :: "nat \<Rightarrow> stpred" where "PublishRequestImpliesElectionWonBelow termBound s \<equiv>
  \<forall> m \<in> messages s. term m < termBound \<longrightarrow> isPublishRequest m \<longrightarrow> currentTerm s (source m) = term m
    \<longrightarrow> startedJoinSinceLastReboot s (source m) \<longrightarrow> electionWon s (source m)"

definition PublishRequestImpliesQuorumBelow :: "nat \<Rightarrow> stpred" where "PublishRequestImpliesQuorumBelow termBound s \<equiv>
  \<forall> m \<in> messages s. term m < termBound \<longrightarrow> isPublishRequest m \<longrightarrow> currentTerm s (source m) = term m \<longrightarrow> electionWon s (source m)
               \<longrightarrow> IsQuorum (joinVotes s (source m)) (config m)
                 \<and> IsQuorum (joinVotes s (source m)) (currConf m)"

definition PublishRequestSentByMasterBelow :: "nat \<Rightarrow> stpred" where "PublishRequestSentByMasterBelow termBound s \<equiv>
  \<forall> m n. m \<in> messages s \<longrightarrow> term m = currentTerm s n \<longrightarrow> term m < termBound \<longrightarrow> isPublishRequest m \<longrightarrow> electionWon s n
    \<longrightarrow> n = source m"

definition PublishVersionNonzeroOnlyIfElectionWonBelow :: "nat \<Rightarrow> stpred" where "PublishVersionNonzeroOnlyIfElectionWonBelow termBound s \<equiv>
  \<forall> n. currentTerm s n < termBound \<longrightarrow> 0 < lastPublishedVersion  s n \<longrightarrow> electionWon s n"

definition EndOfTermIsPermanentBelow :: "nat \<Rightarrow> stpred" where "EndOfTermIsPermanentBelow termBound s \<equiv>
  \<forall> n. (currentTerm s n, n) \<in> leaderHistory s \<longrightarrow> currentTerm s n < termBound \<longrightarrow> startedJoinSinceLastReboot s n \<longrightarrow> electionWon s n"

definition PublishRequestVersionAtMostSenderBelow :: "nat \<Rightarrow> stpred" where "PublishRequestVersionAtMostSenderBelow termBound s \<equiv>
  \<forall> m \<in> messages s. isPublishRequest m \<longrightarrow> term m < termBound \<longrightarrow> msgTermVersion  m \<le> termVersion  (source m) s"

definition PublishRequestsUniquePerTermVersionBelow :: "nat \<Rightarrow> stpred" where "PublishRequestsUniquePerTermVersionBelow termBound s \<equiv>
  \<forall> m1 m2. m1 \<in> messages s \<longrightarrow> m2 \<in> messages s \<longrightarrow> isPublishRequest m1 \<longrightarrow> isPublishRequest m2
    \<longrightarrow> term m1 < termBound \<longrightarrow> term m1 = term m2 \<longrightarrow> version  m1 = version  m2
    \<longrightarrow> payload m1 = payload m2"

definition BasedOnUniqueBelow :: "nat \<Rightarrow> stpred" where "BasedOnUniqueBelow termBound s \<equiv>
  \<forall> tiPrev1 tiPrev2 tCurr iCurr. tCurr < termBound
      \<longrightarrow> (TermVersion  tCurr iCurr, tiPrev1) \<in> basedOn s \<longrightarrow> (TermVersion  tCurr iCurr, tiPrev2) \<in> basedOn s
      \<longrightarrow> tiPrev1 = tiPrev2"

definition LeaderMustAcceptItsPublishRequestsBelow :: "nat \<Rightarrow> stpred" where "LeaderMustAcceptItsPublishRequestsBelow termBound s \<equiv>
  \<forall> m \<in> messages s. isPublishRequest m \<longrightarrow> lastAcceptedVersion  s (source m) = lastPublishedVersion  s (source m)
                      \<longrightarrow> term m = currentTerm s (source m) \<longrightarrow> term m < termBound \<longrightarrow> electionWon s (source m)
       \<longrightarrow> lastAcceptedTerm s (source m) = currentTerm s (source m)"

definition PublishRequestsContiguousWithinTermBelow :: "nat \<Rightarrow> stpred" where "PublishRequestsContiguousWithinTermBelow termBound s \<equiv>
  \<forall> m1 m2. m1 \<in> messages s \<longrightarrow> m2 \<in> messages s \<longrightarrow> isPublishRequest m1 \<longrightarrow> isPublishRequest m2
    \<longrightarrow> term m1 = term m2 \<longrightarrow> term m1 < termBound \<longrightarrow> version  m1 < version  m2
    \<longrightarrow> (TermVersion  (term m2) (version  m2), TermVersion  (term m2) (version  m2 - 1)) \<in> basedOn s"

lemma CommittedConfigurationsSubsetAll: "CommittedConfigurations s \<subseteq> AllConfigurations s"
  by (auto simp add: CommittedConfigurations_def AllConfigurations_def)

context
  fixes s t
  assumes Next: "(s,t) \<Turnstile> [Next]_vars"
begin

lemma FiniteMessagesTo_step:
  assumes "s \<Turnstile> FiniteMessagesTo"
  shows "(s,t) \<Turnstile> FiniteMessagesTo$"
proof -
  from assms have hyp: "\<And>n. finite (messagesTo s n)"
    by (auto simp add: FiniteMessagesTo_def)

  {
    fix n
    from Next hyp have "finite (messagesTo t n)"
    proof (cases rule: square_Next_cases)
      case (HandleStartJoin nf nm tm newJoinRequest)
      from hyp have "finite (insert newJoinRequest (messagesTo s n))" by simp
      moreover have "\<And>n. messagesTo t n \<subseteq> insert newJoinRequest (messagesTo s n)"
        unfolding messagesTo_def HandleStartJoin by auto
      ultimately show ?thesis by (metis finite_subset)
    next
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
      from hyp have "finite (insert \<lparr>source = nm, dest = n, term = currentTerm s nm, payload = PublishRequest \<lparr>prq_version  = newPublishVersion, prq_value = v, prq_config = vs, prq_currConf = lastCommittedConfiguration s nm\<rparr> \<rparr> (messagesTo s n))" by simp
      moreover have "\<And>n. messagesTo t n \<subseteq> insert \<lparr>source = nm, dest = n, term = currentTerm s nm, payload = PublishRequest \<lparr>prq_version  = newPublishVersion, prq_value = v, prq_config = vs, prq_currConf = lastCommittedConfiguration s nm\<rparr> \<rparr> (messagesTo s n)"
        unfolding messagesTo_def ClientRequest by auto
      ultimately show "finite (messagesTo t n)" by (metis finite_subset)
    next
      case (HandlePublishRequest nf nm newVersion  newValue newConfig currConfig)
      from hyp have "finite (insert \<lparr>source = nf, dest = nm, term = currentTerm s nf, payload = PublishResponse \<lparr>prs_version  = newVersion\<rparr>\<rparr> (messagesTo s n))" by simp
      moreover have "\<And>n. messagesTo t n \<subseteq> insert \<lparr>source = nf, dest = nm, term = currentTerm s nf, payload = PublishResponse \<lparr>prs_version  = newVersion\<rparr>\<rparr> (messagesTo s n)"
        unfolding messagesTo_def HandlePublishRequest by auto
      ultimately show "finite (messagesTo t n)" by (metis finite_subset)
    next
      case (HandlePublishResponse_NoQuorum nf nm)
      from hyp have "finite (insert \<lparr>source = nm, dest = n, term = currentTerm s nm, payload = Commit \<lparr>c_version  = lastPublishedVersion  s nm\<rparr>\<rparr> (messagesTo s n))" by simp
      moreover have "\<And>n. messagesTo t n \<subseteq> insert \<lparr>source = nm, dest = n, term = currentTerm s nm, payload = Commit \<lparr>c_version  = lastPublishedVersion  s nm\<rparr>\<rparr> (messagesTo s n)"
        unfolding messagesTo_def HandlePublishResponse_NoQuorum by auto
      ultimately show "finite (messagesTo t n)" by (metis finite_subset)
    next
      case (HandlePublishResponse_Quorum nf nm)
      from hyp have "finite (insert \<lparr>source = nm, dest = n, term = currentTerm s nm, payload = Commit \<lparr>c_version  = lastPublishedVersion  s nm\<rparr>\<rparr> (messagesTo s n))" by simp
      moreover have "\<And>n. messagesTo t n \<subseteq> insert \<lparr>source = nm, dest = n, term = currentTerm s nm, payload = Commit \<lparr>c_version  = lastPublishedVersion  s nm\<rparr>\<rparr> (messagesTo s n)"
        unfolding messagesTo_def HandlePublishResponse_Quorum by auto
      ultimately show "finite (messagesTo t n)" by (metis finite_subset)
    qed (auto simp add: messagesTo_def)
  }
  thus ?thesis by (simp add: FiniteMessagesTo_def)
qed

lemma JoinRequestsAtMostCurrentTerm_step:
  assumes "s \<Turnstile> JoinRequestsAtMostCurrentTerm"
  shows "(s,t) \<Turnstile> JoinRequestsAtMostCurrentTerm$"
proof -
  from assms have hyp: "\<And>m. isJoin m \<Longrightarrow> m \<in> messages s \<Longrightarrow> term m \<le> currentTerm s (source m)"
    by (auto simp add: JoinRequestsAtMostCurrentTerm_def)
  {
    fix m
    assume isJoin: "isJoin m" with hyp have hyp: "m \<in> messages s \<Longrightarrow> term m \<le> currentTerm s (source m)" by simp
    assume prem: "m : messages t"

    from Next hyp prem have "term m \<le> currentTerm t (source m)"
    proof (cases rule: square_Next_cases)
      case (HandleStartJoin nf nm tm newJoinRequest)
      from prem have "m = newJoinRequest \<or> m \<in> messages s" by (simp add: HandleStartJoin)
      thus ?thesis
      proof (elim disjE)
        assume "m \<in> messages s"
        note hyp [OF this]
        also from HandleStartJoin have "currentTerm s (source m) \<le> currentTerm t (source m)" by simp
        finally show ?thesis .
      next
        assume "m = newJoinRequest" thus ?thesis by (simp add: HandleStartJoin)
      qed
    qed auto
  }
  thus ?thesis by (auto simp add: JoinRequestsAtMostCurrentTerm_def)
qed

lemma JoinRequestsUniquePerTerm_step:
  assumes "s \<Turnstile> JoinRequestsUniquePerTerm"
  assumes "s \<Turnstile> JoinRequestsAtMostCurrentTerm"
  shows "(s,t) \<Turnstile> JoinRequestsUniquePerTerm$"
proof -
  from assms
  have prem: "\<And>m. isJoin m \<Longrightarrow> m \<in> messages s \<Longrightarrow> term m \<le> currentTerm s (source m)"
    and hyp: "\<And>m1 m2. m1 \<in> messages s \<Longrightarrow> m2 \<in> messages s \<Longrightarrow> isJoin m1 \<Longrightarrow> isJoin m2 \<Longrightarrow> source m1 = source m2 \<Longrightarrow> term m1 = term m2 \<Longrightarrow> m1 = m2"
    by (auto simp add: JoinRequestsAtMostCurrentTerm_def JoinRequestsUniquePerTerm_def)

  {
    fix m1 m2
    assume isJoin: "isJoin m1" "isJoin m2"
    assume msgs: "m1 \<in> messages t" "m2 \<in> messages t"
    assume source_eq: "source m1 = source m2" and term_eq: "term m1 = term m2"

    from Next hyp isJoin msgs source_eq term_eq have "m1 = m2"
    proof (cases rule: square_Next_cases)
      case (HandleStartJoin nf nm tm newJoinRequest)
      from isJoin source_eq term_eq hyp have hyp: "m1 \<in> messages s \<Longrightarrow> m2 \<in> messages s \<Longrightarrow> m1 = m2" by simp
      from msgs have "m1 = newJoinRequest \<or> m1 \<in> messages s" "m2 = newJoinRequest \<or> m2 \<in> messages s" by (simp_all add: HandleStartJoin)
      thus ?thesis
      proof (elim disjE)
        assume "m1 \<in> messages s" "m2 \<in> messages s" with hyp show ?thesis by metis
      next
        assume "m1 = newJoinRequest" "m2 = newJoinRequest" thus ?thesis by simp
      next
        assume m1: "m1 \<in> messages s" and m2: "m2 = newJoinRequest"
        from m1 isJoin prem have "term m1 \<le> currentTerm s (source m1)" by metis
        also from m2 source_eq have "source m1 = nf" by (simp add: HandleStartJoin)
        hence "currentTerm s (source m1) < tm" by (simp add: HandleStartJoin)
        also from m2 have "tm = term m2" by (simp add: HandleStartJoin)
        also note term_eq
        finally show ?thesis by simp
      next
        assume m1: "m1 = newJoinRequest" and m2: "m2 \<in> messages s"
        from m2 isJoin prem have "term m2 \<le> currentTerm s (source m2)" by metis
        also from m1 source_eq have "source m2 = nf" by (simp add: HandleStartJoin)
        hence "currentTerm s (source m2) < tm" by (simp add: HandleStartJoin)
        also from m1 have "tm = term m1" by (simp add: HandleStartJoin)
        also note term_eq
        finally show ?thesis by simp
      qed
    qed (auto simp add: isJoin_def)
  }
  thus ?thesis by (simp add: JoinRequestsUniquePerTerm_def)
qed

lemma messages_increasing:
  "messages s \<subseteq> messages t"
  using Next by (cases rule: square_Next_cases, auto)

lemma terms_increasing:
  shows "currentTerm s n \<le> currentTerm t n"
  using Next by (cases rule: square_Next_cases, auto)

lemma JoinVotesFaithful_step:
  assumes "s \<Turnstile> JoinVotesFaithful"
  shows "(s,t) \<Turnstile> JoinVotesFaithful$"
proof -
  from assms have hyp: "\<And>nm nf. nf \<in> joinVotes s nm \<Longrightarrow> \<exists> joinPayload. \<lparr> source = nf, dest = nm, term = currentTerm s nm, payload = Join joinPayload \<rparr> \<in> messages s"
    by (auto simp add: JoinVotesFaithful_def)

  {
    fix nm0 nf0
    assume prem: "nf0 \<in> joinVotes t nm0"

    from Next hyp prem have "\<exists> joinPayload. \<lparr> source = nf0, dest = nm0, term = currentTerm t nm0, payload = Join joinPayload \<rparr> \<in> messages s"
    proof (cases rule: square_Next_cases)
      case (HandleStartJoin nf nm tm newJoinRequest)
      with hyp prem show ?thesis by (cases "nm0 = nf", auto)
    next
      case (RestartNode nr)
      with hyp prem show ?thesis by (cases "nm0 = nr", auto)
    next
      case (HandleJoinRequest nf nm laTerm_m laVersion_m)
      thus ?thesis
      proof (cases "nm0 = nm \<and> nf0 = nf")
        case False
        with prem have "nf0 \<in> joinVotes s nm0" by (cases "nm0 = nm", auto simp add: HandleJoinRequest)
        with hyp show ?thesis by (auto simp add: HandleJoinRequest)
      qed auto
    qed auto
    with messages_increasing have "\<exists>joinPayload. \<lparr>source = nf0, dest = nm0, term = currentTerm t nm0, payload = Join joinPayload\<rparr> \<in> messages t" by auto
  }
  thus ?thesis by (auto simp add: JoinVotesFaithful_def)
qed

lemma JoinVotesImpliesStartedJoin_step:
 assumes "s \<Turnstile> JoinVotesImpliesStartedJoin"
  shows "(s,t) \<Turnstile> JoinVotesImpliesStartedJoin$"
proof -
  from assms have hyp: "\<And>n. joinVotes s n \<noteq> {} \<Longrightarrow> startedJoinSinceLastReboot s n"
    by (auto simp add: JoinVotesImpliesStartedJoin_def)

  {
    fix n
    assume prem: "joinVotes t n \<noteq> {}"

    from Next hyp prem have "startedJoinSinceLastReboot t n"
    proof (cases rule: square_Next_cases)
      case (HandleStartJoin nf nm tm newJoinRequest)
      with hyp prem show ?thesis by (cases "nf = n", auto)
    next
      case (HandleJoinRequest nf nm laTerm_m laVersion_m)
      with hyp prem show ?thesis by (cases "nm = n", auto)
    next
      case (RestartNode nr)
      with hyp prem show ?thesis by (cases "nr = n", auto)
    qed auto
  }
  thus ?thesis by (auto simp add: JoinVotesImpliesStartedJoin_def)
qed

lemma MessagePositiveTerm_step:
  assumes "s \<Turnstile> MessagePositiveTerm"
  assumes "s \<Turnstile> JoinVotesFaithful"
  shows "(s,t) \<Turnstile> MessagePositiveTerm$"
proof -
  from assms
  have  hyp1: "\<And>m. m \<in> messages s \<Longrightarrow> term m > 0"
    and hyp2: "\<And> nm nf. nf \<in> joinVotes s nm \<Longrightarrow> \<exists> joinPayload. \<lparr> source = nf, dest = nm, term = currentTerm s nm, payload = Join joinPayload \<rparr> \<in> messages s"
    by (auto simp add: MessagePositiveTerm_def JoinVotesFaithful_def)
  {
    fix m
    assume prem: "m \<in> messages t"
    from Next hyp1 prem have "term m > 0"
    proof (cases rule: square_Next_cases)
      case (HandleStartJoin nf nm tm newJoinRequest)
      from prem have "m \<in> messages s \<or> term m = tm" by (auto simp add: HandleStartJoin)
      with hyp1 HandleStartJoin show ?thesis by auto
    next
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
      hence "vs \<in> ValidConfigs" "IsQuorum (joinVotes s nm) vs" by simp_all
      then obtain voter where "voter \<in> joinVotes s nm"
        by (cases "joinVotes s nm \<inter> vs = {}", auto simp add: ValidConfigs_def IsQuorum_def)
      with hyp2 obtain joinPayload where "\<lparr> source = voter, dest = nm, term = currentTerm s nm, payload = Join joinPayload \<rparr> \<in> messages s" by auto
      from hyp1 [OF this] have "0 < currentTerm s nm" by simp
      with hyp1 prem show ?thesis by (auto simp add: ClientRequest)
    next
      case (HandlePublishRequest nf nm newVersion  newValue newConfig currConfig)
      with hyp1 [of "\<lparr>source = nm, dest = nf, term = currentTerm s nf, payload = PublishRequest \<lparr>prq_version  = newVersion, prq_value = newValue, prq_config = newConfig, prq_currConf = currConfig\<rparr>\<rparr>"]
      have "0 < currentTerm s nf" by auto
      with hyp1 prem show ?thesis by (auto simp add: HandlePublishRequest)
    next
      case (HandlePublishResponse_Quorum nf nm)
      with hyp1 [of "\<lparr>source = nf, dest = nm, term = currentTerm s nm, payload = PublishResponse \<lparr>prs_version  = lastPublishedVersion  s nm\<rparr>\<rparr>"]
      have "0 < currentTerm s nm" by auto
      with hyp1 prem show ?thesis by (auto simp add: HandlePublishResponse_Quorum)
    qed simp_all
  }
  thus ?thesis by (auto simp add: MessagePositiveTerm_def)
qed

lemma TermIncreasedByJoin_step:
  assumes "s \<Turnstile> TermIncreasedByJoin"
  shows "(s,t) \<Turnstile> TermIncreasedByJoin$"
proof -
  from assms have hyp: "\<And>n. currentTerm s n > 0 \<Longrightarrow> \<exists> m \<in> messages s. isJoin m \<and> currentTerm s n = term m"
    by (auto simp add: TermIncreasedByJoin_def)

  {
    fix n
    assume prem: "currentTerm t n > 0"
    from Next hyp prem have "\<exists> m \<in> messages t. isJoin m \<and> currentTerm t n = term m"
    proof (cases rule: square_Next_cases)
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
      with hyp prem have "\<exists> m \<in> messages s. isJoin m \<and> currentTerm t n = term m" by auto
      thus ?thesis by (auto simp add: ClientRequest)
    next
      case (HandlePublishResponse_Quorum nf nm)
      with hyp prem have "\<exists> m \<in> messages s. isJoin m \<and> currentTerm t n = term m" by auto
      thus ?thesis by (auto simp add: HandlePublishResponse_Quorum)
    qed (auto simp add: isJoin_def)
  }
  thus ?thesis by (auto simp add: TermIncreasedByJoin_def)
qed

lemma LastAcceptedTermInPast_step:
  assumes "s \<Turnstile> LastAcceptedTermInPast"
  shows "(s,t) \<Turnstile> LastAcceptedTermInPast$"
proof -
  from assms have hyp: "\<And>n. lastAcceptedTerm s n \<le> currentTerm s n"
    by (auto simp add: LastAcceptedTermInPast_def)

  {
    fix n
    from Next hyp have "lastAcceptedTerm t n \<le> currentTerm s n"
      by (cases rule: square_Next_cases, auto)
    also have "... \<le> currentTerm t n"
      by (intro terms_increasing Next)
    finally have "lastAcceptedTerm t n \<le> ..." .
  }
  thus ?thesis by (auto simp add: LastAcceptedTermInPast_def)
qed

lemma LastAcceptedDataSource_step:
  assumes "s \<Turnstile> LastAcceptedDataSource"
  assumes "s \<Turnstile> MessagePositiveTerm"
  assumes "s \<Turnstile> LastAcceptedTermInPast"
  shows "(s,t) \<Turnstile> LastAcceptedDataSource$"
proof -
  define P where "\<And>s n. P s n \<equiv>
      if lastAcceptedTerm s n = 0
        then lastAcceptedVersion       s n = 0
           \<and> lastAcceptedValue         s n = initialValue s
           \<and> lastAcceptedConfiguration s n = initialConfiguration s
        else (\<exists> m \<in> messages s. isPublishRequest m
                                        \<and> lastAcceptedTerm          s n = term     m
                                        \<and> lastAcceptedVersion       s n = version  m
                                        \<and> lastAcceptedValue         s n = value    m
                                        \<and> lastAcceptedConfiguration s n = config   m)"

  from assms
  have  hyp1: "\<And>n. P s n"
    and hyp2: "\<And>m. m \<in> messages s \<Longrightarrow> term m > 0"
    and hyp3: "\<And>n. lastAcceptedTerm s n \<le> currentTerm s n"
    by (auto simp add: MessagePositiveTerm_def LastAcceptedDataSource_def LastAcceptedTermInPast_def P_def)

  {
    fix n

    from Next
    have "lastAcceptedTerm t n \<in> {lastAcceptedTerm s n, currentTerm s n}"
      by (cases rule: square_Next_cases, auto)
    with hyp3 have lastAcceptedTerm_increasing: "lastAcceptedTerm s n \<le> lastAcceptedTerm t n" by auto

    have "P t n"
    proof (cases "lastAcceptedTerm t n = 0")
      case term'0: True
      with lastAcceptedTerm_increasing have "lastAcceptedTerm s n = 0" by simp
      with hyp1 [of n] have lastAcceptedData: "lastAcceptedTerm s n = 0"
        "lastAcceptedVersion  s n = 0" "lastAcceptedValue s n = initialValue s"
        "lastAcceptedConfiguration s n = initialConfiguration s"
        by (auto simp add: P_def)

      from Next have "lastAcceptedTerm t n = 0 \<and> lastAcceptedVersion  t n = 0
        \<and> lastAcceptedValue t n = initialValue t \<and> lastAcceptedConfiguration t n = initialConfiguration t"
      proof (cases rule: square_Next_cases)
        case (HandlePublishRequest nf nm newVersion  newValue newConfig currConfig)
        with hyp2 [of "\<lparr>source = nm, dest = nf, term = currentTerm s nf, payload = PublishRequest \<lparr>prq_version  = newVersion, prq_value = newValue, prq_config = newConfig, prq_currConf = currConfig\<rparr>\<rparr>"]
        have "0 < currentTerm s nf" by simp
        with term'0 show ?thesis by (auto simp add: HandlePublishRequest lastAcceptedData)
      qed (simp_all add: lastAcceptedData)
      thus ?thesis by (simp add: term'0 P_def)
    next
      case term'Pos: False
      from Next term'Pos hyp1 have "\<exists> m \<in> messages t. isPublishRequest m
                                        \<and> lastAcceptedTerm          t n = term     m
                                        \<and> lastAcceptedVersion       t n = version  m
                                        \<and> lastAcceptedValue         t n = value    m
                                        \<and> lastAcceptedConfiguration t n = config   m"
      proof (cases rule: square_Next_cases)
        case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
        with term'Pos hyp1 have "\<exists> m \<in> messages s. isPublishRequest m
                                        \<and> lastAcceptedTerm          s n = term     m
                                        \<and> lastAcceptedVersion       s n = version  m
                                        \<and> lastAcceptedValue         s n = value    m
                                        \<and> lastAcceptedConfiguration s n = config   m"
          by (auto simp add: P_def)
        thus ?thesis by (auto simp add: P_def ClientRequest)
      next
        case (HandlePublishRequest nf nm newVersion  newValue newConfig currConfig)
        show ?thesis
        proof (cases "n = nf")
          case False
          with term'Pos hyp1 HandlePublishRequest show ?thesis by (auto simp add: P_def)
        next
          case True
          with term'Pos hyp1 HandlePublishRequest show ?thesis
            by (intro bexI [where x = "\<lparr>source = nm, dest = nf, term = currentTerm s nf, payload = PublishRequest \<lparr>prq_version  = newVersion, prq_value = newValue, prq_config = newConfig, prq_currConf = currConfig\<rparr>\<rparr>"],
                auto simp add: isPublishRequest_def version_def value_def config_def)
        qed
      next
        case (HandlePublishResponse_Quorum nf nm)
        with term'Pos hyp1 have "\<exists> m \<in> messages s. isPublishRequest m
                                        \<and> lastAcceptedTerm          s n = term     m
                                        \<and> lastAcceptedVersion       s n = version  m
                                        \<and> lastAcceptedValue         s n = value    m
                                        \<and> lastAcceptedConfiguration s n = config   m"
          by (auto simp add: P_def)
        thus ?thesis by (auto simp add: P_def HandlePublishResponse_Quorum)
      qed (auto simp add: P_def)
      with term'Pos show ?thesis by (auto simp add: P_def)
    qed
  }
  thus ?thesis by (auto simp add: LastAcceptedDataSource_def P_def)
qed

lemma CommittedConfigurations_increasing: "CommittedConfigurations s \<subseteq> CommittedConfigurations t"
proof -
  from Next have initialConfiguration_eq[simp]: "initialConfiguration t = initialConfiguration s" by (cases rule: square_Next_cases)
  show "CommittedConfigurations s \<subseteq> CommittedConfigurations t"
    unfolding CommittedConfigurations_def using messages_increasing
    by (auto simp add: CommittedConfigurations_def)
qed

lemma CurrentConfigurationSource_step:
  assumes "s \<Turnstile> CurrentConfigurationSource"
  assumes "s \<Turnstile> LastAcceptedDataSource"
  assumes "s \<Turnstile> CurrentConfigurationMsgSource"
  assumes "s \<Turnstile> MessagePositiveTerm"
  shows "(s,t) \<Turnstile> CurrentConfigurationSource$"
proof -
  from assms
  have  hyp1: "\<And>n. lastCommittedConfiguration s n \<in> CommittedConfigurations s"
    and hyp2: "\<And>n. if lastAcceptedTerm s n = 0 then lastAcceptedVersion  s n = 0 \<and> lastAcceptedValue s n = initialValue s \<and> lastAcceptedConfiguration s n = initialConfiguration s
      else \<exists>m\<in>messages s. isPublishRequest m \<and> lastAcceptedTerm s n = term m \<and> lastAcceptedVersion  s n = version  m \<and> lastAcceptedValue s n = value m \<and> lastAcceptedConfiguration s n = config m"
    and hyp3: "\<And>m. \<lbrakk> m \<in> messages s; isPublishRequest m \<rbrakk> \<Longrightarrow> currConf m \<in> CommittedConfigurations s"
    and hyp4: "\<And>m. m \<in> messages s \<Longrightarrow> term m > 0"
    by (auto simp add: CurrentConfigurationSource_def CurrentConfigurationMsgSource_def LastAcceptedDataSource_def MessagePositiveTerm_def)

  from Next
  have CommittedConfigurations_subset: "CommittedConfigurations s \<subseteq> CommittedConfigurations t"
    by (cases rule: square_Next_cases, auto simp add: CommittedConfigurations_def)

  {
    fix n
    from Next have "lastCommittedConfiguration t n \<in> insert (lastCommittedConfiguration s n) (CommittedConfigurations t)"
    proof (cases rule: square_Next_cases)
      case (HandlePublishRequest nf nm newVersion  newValue newConfig currConfig)
      show ?thesis
      proof (cases "nf = n")
        case True
        hence "lastCommittedConfiguration t n = currConf \<lparr>source = nm, dest = nf,
              term = currentTerm s nf, payload = PublishRequest \<lparr>prq_version  = newVersion, prq_value = newValue, prq_config = newConfig, prq_currConf = currConfig\<rparr>\<rparr>"
          by (simp add: HandlePublishRequest currConf_def)
        also from HandlePublishRequest have "... \<in> CommittedConfigurations s"
          by (intro hyp3, auto simp add: isPublishRequest_def)
        also note CommittedConfigurations_subset
        finally show ?thesis by simp
      qed (simp add: HandlePublishRequest)
    next
      case (HandleCommitRequest nf nm)
      show ?thesis
      proof (cases "nf = n")
        case False
        thus ?thesis by (simp add: HandleCommitRequest)
      next
        case nf_eq_n: True

        from HandleCommitRequest hyp4 [of "\<lparr>source = nm, dest = nf, term = currentTerm s nf, payload = Commit \<lparr>c_version  = lastAcceptedVersion  s nf\<rparr>\<rparr>"]
        have "0 < lastAcceptedTerm s nf" by simp
        with hyp2 [of n]
        obtain mPub where mPub: "mPub \<in> messages s" "isPublishRequest mPub" "lastAcceptedTerm s n = term mPub"
          "lastAcceptedVersion  s n = version  mPub" "lastAcceptedValue s n = value mPub" "lastAcceptedConfiguration s n = config mPub"
          unfolding nf_eq_n by auto

        have "lastAcceptedConfiguration s n \<in> CommittedConfigurations t"
          unfolding CommittedConfigurations_def
        proof (intro insertI2 CollectI bexI conjI)
          from mPub show "isPublishRequest mPub" "config mPub = lastAcceptedConfiguration s n" by simp_all
          show "isCommit \<lparr>source = nm, dest = n, term = currentTerm s n, payload = Commit \<lparr>c_version  = lastAcceptedVersion  s n\<rparr>\<rparr>" by (simp add: isCommit_def nf_eq_n)
          from mPub show "mPub \<in> messages t" by (simp add: HandleCommitRequest)
          from HandleCommitRequest mPub show "term \<lparr>source = nm, dest = n, term = currentTerm s n, payload = Commit \<lparr>c_version  = lastAcceptedVersion  s n\<rparr>\<rparr> = term mPub"
            "version  \<lparr>source = nm, dest = n, term = currentTerm s n, payload = Commit \<lparr>c_version  = lastAcceptedVersion  s n\<rparr>\<rparr> = version  mPub"
            "\<lparr>source = nm, dest = n, term = currentTerm s n, payload = Commit \<lparr>c_version  = lastAcceptedVersion  s n\<rparr>\<rparr> \<in> messages t"
            by (simp_all add: nf_eq_n version_def)
        qed
        thus ?thesis by (simp add: HandleCommitRequest nf_eq_n)
      qed
    qed simp_all
    also have "... \<subseteq> CommittedConfigurations t"
    proof (intro iffD2 [OF insert_subset] conjI subset_refl)
      from hyp1 [of n] CommittedConfigurations_increasing show "lastCommittedConfiguration s n \<in> CommittedConfigurations t" by auto
    qed
    finally have "lastCommittedConfiguration t n \<in> CommittedConfigurations t".
  }
  with hyp1 show ?thesis by (auto simp add: CurrentConfigurationSource_def)
qed

lemma CurrentConfigurationMsgSource_step:
  assumes "s \<Turnstile> CurrentConfigurationSource"
  assumes "s \<Turnstile> CurrentConfigurationMsgSource"
  shows "(s,t) \<Turnstile> CurrentConfigurationMsgSource$"
proof -
  from assms
  have  hyp1: "\<And>n. lastCommittedConfiguration s n \<in> CommittedConfigurations s"
    and hyp2: "\<And>m. \<lbrakk> m \<in> messages s; isPublishRequest m \<rbrakk> \<Longrightarrow> currConf m \<in> CommittedConfigurations s"
    by (auto simp add: CurrentConfigurationSource_def CurrentConfigurationMsgSource_def)

  {
    fix m
    assume prem: "m \<in> messages t" "isPublishRequest m"
    with Next hyp2 have "currConf m \<in> CommittedConfigurations s"
    proof (cases rule: square_Next_cases)
      case (HandleStartJoin nf nm tm newJoinRequest)
      from prem have "m \<in> messages s" unfolding HandleStartJoin by (auto simp add: isPublishRequest_def)
      with hyp2 prem show "currConf m \<in> CommittedConfigurations s" by simp
    next
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
      with prem have "m \<in> messages s \<or> m \<in> newPublishRequests" by auto
      thus ?thesis
      proof (elim disjE)
        assume "m : messages s"
        with hyp2 prem show "currConf m \<in> CommittedConfigurations s" by simp
      next
        assume "m \<in> newPublishRequests"
        hence "currConf m = lastCommittedConfiguration s nm"
          by (auto simp add: ClientRequest currConf_def)
        also note hyp1
        finally show ?thesis .
      qed
    next
      case (HandlePublishRequest nf nm newVersion  newValue newConfig currConfig)
      from prem have "m \<in> messages s" unfolding HandlePublishRequest by (auto simp add: isPublishRequest_def)
      with hyp2 prem show "currConf m \<in> CommittedConfigurations s" by simp
    next
      case (HandlePublishResponse_Quorum nf nm)
      from prem have "m \<in> messages s" unfolding HandlePublishResponse_Quorum by (auto simp add: isPublishRequest_def)
      with hyp2 prem show "currConf m \<in> CommittedConfigurations s" by simp
    qed (auto simp add: CommittedConfigurations_def)
    also note CommittedConfigurations_increasing
    finally have "currConf m \<in> CommittedConfigurations t" .
  }
  thus ?thesis by (auto simp add: CurrentConfigurationMsgSource_def)
qed

lemma CommittedConfigurations_subset_AllConfigurations:
  "s \<Turnstile> CommittedConfigurations \<subseteq> AllConfigurations"
  by (auto simp add: CommittedConfigurations_def AllConfigurations_def) 

lemma AllConfigurationsValid_step:
  assumes "s \<Turnstile> AllConfigurationsValid"
  shows "(s,t) \<Turnstile> AllConfigurationsValid$"
proof -
  from assms have hyp: "\<And>m. \<lbrakk> m \<in> messages s; isPublishRequest m \<rbrakk> \<Longrightarrow> config m \<in> ValidConfigs"
    and init: "initialConfiguration s \<in> ValidConfigs"
    by (auto simp add: AllConfigurationsValid_def AllConfigurations_def)

  from Next init have "initialConfiguration t \<in> ValidConfigs"
    by (cases rule: square_Next_cases, simp_all)
  moreover
  {
    fix m
    assume prem: "m \<in> messages t" "isPublishRequest m"
    from Next hyp prem have "config m \<in> ValidConfigs"
    proof (cases rule: square_Next_cases)
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
      with prem have "m \<in> messages s \<or> m \<in> newPublishRequests" by auto
      thus ?thesis
      proof (elim disjE)
        assume "m \<in> messages s" with prem hyp show ?thesis by simp
      next
        assume "m \<in> newPublishRequests"
        hence "config m = vs" by (auto simp add: ClientRequest config_def)
        with ClientRequest show ?thesis by simp
      qed
    qed (auto simp add: isPublishRequest_def)
  }
  ultimately show ?thesis by (auto simp add: AllConfigurationsValid_def AllConfigurations_def)
qed

lemma PublicationsInPastTerm_step:
  assumes "s \<Turnstile> PublicationsInPastTerm"
  shows "(s,t) \<Turnstile> PublicationsInPastTerm$"
proof -
  from assms have hyp: "\<And>m. \<lbrakk> m \<in> messages s; isPublishRequest m \<rbrakk> \<Longrightarrow> term m \<le> currentTerm s (source m)"
    by (auto simp add: PublicationsInPastTerm_def)

  {
    fix m
    assume prem: "m \<in> messages t" "isPublishRequest m"
    from Next hyp prem have "term m \<le> currentTerm s (source m)"
      by (cases rule: square_Next_cases, auto simp add: isPublishRequest_def)
    also have "... \<le> currentTerm t (source m)"
      by (intro terms_increasing Next)
    finally have "term m \<le> ..." .
  }
  thus ?thesis by (auto simp add: PublicationsInPastTerm_def)
qed

lemma PublishRequestVersionPositive_step:
  assumes "s \<Turnstile> PublishRequestVersionPositive"
  shows "(s,t) \<Turnstile> PublishRequestVersionPositive$"
proof -
  from assms have hyp: "\<And>m. \<lbrakk> m \<in> messages s; isPublishRequest m \<rbrakk> \<Longrightarrow> 0 < version  m"
    by (auto simp add: PublishRequestVersionPositive_def)

  {
    fix m
    assume prem: "m \<in> messages t" "isPublishRequest m"
    from Next hyp prem have "0 < version  m"
      by (cases rule: square_Next_cases, auto simp add: isPublishRequest_def version_def)
  }
  thus ?thesis by (auto simp add: PublishRequestVersionPositive_def)
qed

lemma LeaderHistoryFaithful_step:
  assumes "s \<Turnstile> LeaderHistoryFaithful"
  shows "(s,t) \<Turnstile> LeaderHistoryFaithful$"
proof -
  from assms have hyp: "\<And>n. electionWon s n \<Longrightarrow> (currentTerm s n, n) \<in> leaderHistory s"
    by (auto simp add: LeaderHistoryFaithful_def)

  {
    fix n
    assume prem: "electionWon t n"
    from Next hyp prem have "(currentTerm t n, n) \<in> leaderHistory t"
    proof (cases rule: square_Next_cases)
      case (HandleStartJoin nf nm tm newJoinRequest)
      with hyp prem show ?thesis by (cases "n = nf", auto)
    next
      case (RestartNode nr)
      with hyp prem show ?thesis by (cases "n = nr", auto)
    next
      case (HandleJoinRequest nf nm laTerm_m laVersion_m)
      with hyp prem show ?thesis by (cases "n = nm", auto)
    qed auto
  }
  thus ?thesis by (auto simp add: LeaderHistoryFaithful_def)
qed

lemma LeaderHistoryBounded_step:
  assumes "s \<Turnstile> LeaderHistoryBounded"
  shows "(s,t) \<Turnstile> LeaderHistoryBounded$"
proof -
  from assms have hyp: "\<And>n tm. (tm, n) \<in> leaderHistory s \<Longrightarrow> tm \<le> currentTerm s n"
    by (auto simp add: LeaderHistoryBounded_def)

  {
    fix n tm
    assume prem: "(tm, n) \<in> leaderHistory t"
    from Next hyp prem have "tm \<le> currentTerm t n"
    proof (cases rule: square_Next_cases)
      case (HandleStartJoin nf nm tmj newJoinRequest)
      with hyp prem have "tm \<le> currentTerm s n" by (auto simp add: HandleStartJoin)
      also from HandleStartJoin have "... \<le> currentTerm t n" by auto
      finally show ?thesis by simp
    next
      case (HandleJoinRequest nf nm laTerm_m laVersion_m)
      with hyp prem show ?thesis
        by (cases "electionWon t nm", auto)
    qed auto
  }
  thus ?thesis by (auto simp add: LeaderHistoryBounded_def)
qed

lemma PublishRequestFromHistoricalLeader_step:
  assumes "s \<Turnstile> PublishRequestFromHistoricalLeader"
  assumes "s \<Turnstile> LeaderHistoryFaithful"
  shows "(s,t) \<Turnstile> PublishRequestFromHistoricalLeader$"
proof -
  from assms
  have  hyp1: "\<And>m. \<lbrakk> m \<in> messages s; isPublishRequest m \<rbrakk> \<Longrightarrow> (term m, source m) \<in> leaderHistory s"
    and hyp2: "\<And>n. electionWon s n \<Longrightarrow> (currentTerm s n, n) \<in> leaderHistory s"
    by (auto simp add: PublishRequestFromHistoricalLeader_def LeaderHistoryFaithful_def)

  {
    fix m
    assume prem: "m \<in> messages t" "isPublishRequest m"
    from Next hyp1 prem have "(term m, source m) \<in> leaderHistory t"
    proof (cases rule: square_Next_cases)
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
      with prem have "m \<in> messages s \<or> m \<in> newPublishRequests" by auto
      thus ?thesis
      proof (elim disjE)
        assume "m \<in> messages s"
        with ClientRequest hyp1 prem show ?thesis by (auto simp add: isPublishRequest_def)
      next
        assume "m \<in> newPublishRequests"
        thus ?thesis by (auto simp add: ClientRequest hyp2)
      qed
    next
    qed (auto simp add: isPublishRequest_def)
  }
  thus ?thesis by (auto simp add: PublishRequestFromHistoricalLeader_def)
qed

lemma BasedOnIncreasing_step:
  assumes "s \<Turnstile> BasedOnIncreasing"
  assumes "s \<Turnstile> LastAcceptedTermInPast"
  shows "(s,t) \<Turnstile> BasedOnIncreasing$"
proof -
  from assms
  have  hyp1: "\<And>tPrev iPrev tCurr iCurr. (TermVersion  tCurr iCurr, TermVersion  tPrev iPrev) \<in> basedOn s \<Longrightarrow> iCurr = Suc iPrev"
    and hyp2: "\<And>tPrev iPrev tCurr iCurr. (TermVersion  tCurr iCurr, TermVersion  tPrev iPrev) \<in> basedOn s \<Longrightarrow> tPrev \<le> tCurr"
    and hyp3: "\<And>n. lastAcceptedTerm s n \<le> currentTerm s n"
    by (auto simp add: BasedOnIncreasing_def LastAcceptedTermInPast_def)

  {
    fix tPrev iPrev tCurr iCurr
    assume prem: "(TermVersion  tCurr iCurr, TermVersion  tPrev iPrev) \<in> basedOn t"
    from Next hyp1 hyp2 prem have "iCurr = Suc iPrev \<and> tPrev \<le> tCurr"
    proof (cases rule: square_Next_cases)
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
      from ClientRequest prem consider
        (s) "(TermVersion  tCurr iCurr, TermVersion  tPrev iPrev) \<in> basedOn s"
        | (new) "tPrev = lastAcceptedTerm s nm" "iPrev = lastAcceptedVersion  s nm"
          "tCurr = currentTerm s nm" "iCurr = Suc (lastAcceptedVersion  s nm)"
        by auto
      thus ?thesis
      proof (cases)
        case s with hyp1 hyp2 show ?thesis by simp
      next
        case new with hyp3 [of nm] show ?thesis by simp
      qed
    qed (auto simp add: isPublishRequest_def)
  }
  thus ?thesis by (auto simp add: BasedOnIncreasing_def)
qed

lemma PublishRequestBasedOn_step:
  assumes "s \<Turnstile> PublishRequestBasedOn"
  shows "(s,t) \<Turnstile> PublishRequestBasedOn$"
proof -
  from assms
  have  hyp1: "\<And>m. \<lbrakk> m \<in> messages s; isPublishRequest m \<rbrakk> \<Longrightarrow> \<exists> tiPrev. (TermVersion  (term m) (version  m), tiPrev) \<in> basedOn s"
    by (auto simp add: PublishRequestBasedOn_def)

  {
    fix m assume prem: "m \<in> messages t" "isPublishRequest m"
    from Next hyp1 prem
    have "\<exists> tiPrev. (TermVersion  (term m) (version  m), tiPrev) \<in> basedOn t"
    proof (cases rule: square_Next_cases)
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
      with prem have "m \<in> messages s \<or> m \<in> newPublishRequests" by auto
      thus ?thesis
      proof (elim disjE)
        assume "m \<in> messages s" with prem hyp1 obtain tiPrev where "(TermVersion  (term m) (version  m), tiPrev) \<in> basedOn s" by auto
        also from ClientRequest have "basedOn s \<subseteq> basedOn t" by auto
        finally show ?thesis by auto
      next
        assume "m \<in> newPublishRequests"
        thus ?thesis unfolding ClientRequest by (elim UN_E insertE, auto simp add: version_def)
      qed
    qed (auto simp add: isPublishRequest_def)
  }
  thus ?thesis by (auto simp add: PublishRequestBasedOn_def)
qed

lemma BasedOnPublishRequest_step:
  assumes "s \<Turnstile> BasedOnPublishRequest"
  shows "(s,t) \<Turnstile> BasedOnPublishRequest$"
proof -
  from assms
  have  hyp1: "\<And> tiPrev tCurr iCurr. (TermVersion  tCurr iCurr, tiPrev) \<in> basedOn s
    \<Longrightarrow> \<exists> m \<in> messages s. isPublishRequest m \<and> term m = tCurr \<and> version  m = iCurr"
    by (auto simp add: BasedOnPublishRequest_def)

  {
    fix tiPrev tCurr iCurr assume prem: "(TermVersion  tCurr iCurr, tiPrev) \<in> basedOn t"
    from Next hyp1 prem
    have "\<exists> m \<in> messages t. isPublishRequest m \<and> term m = tCurr \<and> version  m = iCurr"
    proof (cases rule: square_Next_cases)
      case (HandlePublishResponse_Quorum nf nm)
      with hyp1 prem have "\<exists> m \<in> messages s. isPublishRequest m \<and> term m = tCurr \<and> version  m = iCurr" by auto
      thus ?thesis unfolding HandlePublishResponse_Quorum by auto
    next
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
      from prem consider
        (s) "(TermVersion  tCurr iCurr, tiPrev) \<in> basedOn s"
        | (new) "tiPrev = TermVersion  (lastAcceptedTerm s nm) (lastAcceptedVersion  s nm)" "tCurr = currentTerm s nm" "iCurr = Suc (lastAcceptedVersion  s nm)"
        unfolding ClientRequest by auto
      thus ?thesis
      proof cases
        case s with hyp1 have "\<exists>m\<in>messages s. isPublishRequest m \<and> term m = tCurr \<and> version  m = iCurr" by simp
        thus ?thesis unfolding ClientRequest by auto
      next
        case new
        have "\<exists>m\<in>newPublishRequests. isPublishRequest m \<and> term m = tCurr \<and> version  m = iCurr"
          by (auto simp add: ClientRequest new version_def isPublishRequest_def)
        thus ?thesis unfolding ClientRequest by auto
      qed
    qed (auto simp add: isPublishRequest_def)
  }
  thus ?thesis by (auto simp add: BasedOnPublishRequest_def)
qed

lemma BasedOnBasedOn_step:
  assumes "s \<Turnstile> BasedOnBasedOn"
  assumes "s \<Turnstile> PublishRequestBasedOn"
  assumes "s \<Turnstile> LastAcceptedDataSource"
  shows "(s,t) \<Turnstile> BasedOnBasedOn$"
proof -
  from assms
  have  hyp1: "\<And>tiCurr tPrev iPrev. \<lbrakk> (tiCurr, TermVersion  tPrev iPrev) \<in> basedOn s; 0 < iPrev \<rbrakk>
    \<Longrightarrow> \<exists> tiPrevPrev. (TermVersion  tPrev iPrev, tiPrevPrev) \<in> basedOn s"
    and hyp2: "\<And>m. \<lbrakk> m \<in> messages s; isPublishRequest m \<rbrakk>
      \<Longrightarrow> \<exists> tiPrev. (TermVersion  (term m) (version  m), tiPrev) \<in> basedOn s"
    and hyp3: "\<And>n. if lastAcceptedTerm s n = 0
        then lastAcceptedVersion       s n = 0
           \<and> lastAcceptedValue         s n = initialValue s
           \<and> lastAcceptedConfiguration s n = initialConfiguration s
        else (\<exists> m \<in> messages s. isPublishRequest m
                                        \<and> lastAcceptedTerm          s n = term     m
                                        \<and> lastAcceptedVersion       s n = version  m
                                        \<and> lastAcceptedValue         s n = value    m
                                        \<and> lastAcceptedConfiguration s n = config   m)"
    by (auto simp add: BasedOnBasedOn_def PublishRequestBasedOn_def LastAcceptedDataSource_def)

  {
    fix tiCurr tPrev iPrev
    assume prem: "(tiCurr, TermVersion  tPrev iPrev) \<in> basedOn t" "0 < iPrev"
    from Next hyp1 prem
    have "\<exists> tiPrevPrev. (TermVersion  tPrev iPrev, tiPrevPrev) \<in> basedOn t"
    proof (cases rule: square_Next_cases)
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
      from prem consider
        (s) "(tiCurr, TermVersion  tPrev iPrev) \<in> basedOn s"
        | (new) "tPrev = lastAcceptedTerm s nm" "iPrev = lastAcceptedVersion  s nm"
          "tiCurr = TermVersion  (currentTerm s nm) (Suc (lastAcceptedVersion  s nm))"
        unfolding ClientRequest by auto
      thus ?thesis
      proof cases
        case s
        with prem have "\<exists> tiPrevPrev. (TermVersion  tPrev iPrev, tiPrevPrev) \<in> basedOn s" by (intro hyp1)
        thus ?thesis by (auto simp add: ClientRequest)
      next
        case new with hyp3 [of nm] prem
        obtain m where m: "m \<in> messages s" "isPublishRequest m" "term m = tPrev" "version  m = iPrev"
          by (cases "lastAcceptedTerm s nm = 0", auto)
        with hyp2 obtain tiPrevPrev where "(TermVersion  tPrev iPrev, tiPrevPrev) \<in> basedOn s" by auto
        thus ?thesis unfolding ClientRequest by auto
      qed
    qed (auto simp add: isPublishRequest_def)
  }
  thus ?thesis by (auto simp add: BasedOnBasedOn_def)
qed

lemma PublishRequestImpliesElectionWonBelow_step:
  assumes "s \<Turnstile> PublishRequestImpliesElectionWonBelow termBound"
  assumes "s \<Turnstile> PublicationsInPastTerm"
  assumes "s \<Turnstile> ElectionWonQuorumBelow termBound"
  shows "(s,t) \<Turnstile> PublishRequestImpliesElectionWonBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>m. \<lbrakk> m \<in> messages s; term m < termBound; isPublishRequest m; currentTerm s (source m) = term m; startedJoinSinceLastReboot s (source m) \<rbrakk> \<Longrightarrow> electionWon s (source m)"
    and hyp2: "\<And>m. \<lbrakk> m \<in> messages s; isPublishRequest m \<rbrakk> \<Longrightarrow> term m \<le> currentTerm s (source m)"
    and hyp3: "\<And>n. \<lbrakk> currentTerm s n < termBound; electionWon s n \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s n) (lastCommittedConfiguration s n)"
    and hyp4: "\<And>n. \<lbrakk> currentTerm s n < termBound; electionWon s n \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s n) (lastAcceptedConfiguration s n)"
    by (auto simp add: PublishRequestImpliesElectionWonBelow_def PublicationsInPastTerm_def ElectionWonQuorumBelow_def)

  {
    fix m
    assume prem: "m \<in> messages t" "term m < termBound" "isPublishRequest m" "currentTerm t (source m) = term m" "startedJoinSinceLastReboot t (source m)"
    from Next have "electionWon t (source m)"
    proof (cases rule: square_Next_cases)
      case unchanged
      with hyp1 prem show ?thesis by simp
    next
      case (HandleStartJoin nf nm tm newJoinRequest)
      show ?thesis
      proof (cases "source m = nf")
        case False
        hence "electionWon t (source m) = electionWon s (source m)" by (simp add: HandleStartJoin)
        also from prem have "electionWon s (source m)"
          by (intro hyp1, auto simp add: HandleStartJoin isPublishRequest_def False)
        finally show ?thesis .
      next
        case True
        from prem have "term m \<le> currentTerm s (source m)"
          by (intro hyp2, auto simp add: HandleStartJoin isPublishRequest_def)
        also from HandleStartJoin True have "... < currentTerm t (source m)" by auto
        also from prem have "... = term m" by simp
        finally show ?thesis by simp
      qed
    next
      case (HandleJoinRequest nf nm laTerm_m laVersion_m)
      show ?thesis
      proof (cases "source m = nm")
        case False with HandleJoinRequest hyp1 prem show ?thesis by (auto)
      next
        case True
        have joinVotes_increase: "\<And>vs. card (joinVotes s (source m) \<inter> vs) \<le> card (joinVotes t (source m) \<inter> vs)" 
        proof -
          fix vs
          show "?thesis vs"
          proof (cases "nf \<in> vs")
            case False thus ?thesis by (simp add: HandleJoinRequest)
          next
            case _: True
            hence eq: "joinVotes t (source m) \<inter> vs = insert nf (joinVotes s (source m) \<inter> vs)" by (auto simp add: HandleJoinRequest True)
            show ?thesis unfolding eq by (intro card_insert_le_general)
          qed
        qed
        from prem have "electionWon s (source m)"
          by (intro hyp1, auto simp add: HandleJoinRequest)
        with prem have "IsQuorum (joinVotes s (source m)) (lastCommittedConfiguration s (source m)) \<and> IsQuorum (joinVotes s (source m)) (lastAcceptedConfiguration s (source m))"
          by (intro conjI hyp3 hyp4, simp_all add: HandleJoinRequest)
        with joinVotes_increase
        have "IsQuorum (joinVotes t (source m)) (lastCommittedConfiguration s (source m)) \<and> IsQuorum (joinVotes t (source m)) (lastAcceptedConfiguration s (source m))"
          unfolding IsQuorum_def using less_le_trans mult_le_mono1 by blast
        thus ?thesis by (simp add: HandleJoinRequest True)
      qed
    next
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
      with hyp1 prem show ?thesis by auto
    next
      case (HandlePublishRequest nf nm newVersion  newValue newConfig currConfig)
      have "electionWon t (source m) = electionWon s (source m)" by (simp add: HandlePublishRequest)
      also from prem have "..." by (intro hyp1, auto simp add: HandlePublishRequest isPublishRequest_def)
      finally show ?thesis by simp
    next
      case (HandlePublishResponse_NoQuorum nf nm)
      with hyp1 prem show ?thesis by auto
    next
      case (HandlePublishResponse_Quorum nf nm)
      have "electionWon t (source m) = electionWon s (source m)" by (simp add: HandlePublishResponse_Quorum)
      also from prem have "..." by (intro hyp1, auto simp add: HandlePublishResponse_Quorum isPublishRequest_def)
      finally show ?thesis by simp
    next
      case (HandleCommitRequest nf nm)
      with hyp1 prem show ?thesis by auto
    next
      case (RestartNode nr)
      with hyp1 prem show ?thesis by (cases "nr = source m", auto)
    qed
  }
  thus ?thesis by (auto simp add: PublishRequestImpliesElectionWonBelow_def)
qed

lemma PublishRequestImpliesQuorumBelow_step:
  assumes "s \<Turnstile> PublishRequestImpliesQuorumBelow termBound"
  assumes "s \<Turnstile> ElectionWonQuorumBelow termBound"
  assumes "s \<Turnstile> PublishRequestImpliesElectionWonBelow termBound"
  shows "(s,t) \<Turnstile> PublishRequestImpliesQuorumBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>m. \<lbrakk> m \<in> messages s; term m < termBound; isPublishRequest m; currentTerm s (source m) = term m;
                     electionWon s (source m) \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s (source m)) (config m)"
    and hyp2: "\<And>m. \<lbrakk> m \<in> messages s; term m < termBound; isPublishRequest m; currentTerm s (source m) = term m;
                     electionWon s (source m) \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s (source m)) (currConf m)"
    and hyp3: "\<And>n. \<lbrakk> currentTerm s n < termBound; electionWon s n \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s n) (lastCommittedConfiguration      s n)"
    and hyp4: "\<And>n. \<lbrakk> currentTerm s n < termBound; electionWon s n \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s n) (lastAcceptedConfiguration s n)"
    and hyp5: "\<And>m. \<lbrakk> m \<in> messages s; term m < termBound; isPublishRequest m; currentTerm s (source m) = term m; startedJoinSinceLastReboot s (source m) \<rbrakk> \<Longrightarrow> electionWon s (source m)"
    by (auto simp add: ElectionWonQuorumBelow_def PublishRequestImpliesQuorumBelow_def PublishRequestImpliesElectionWonBelow_def)

  {
    fix m assume prem: "m \<in> messages t" "term m < termBound" "isPublishRequest m" "currentTerm t (source m) = term m" "electionWon t (source m)"
    from Next have "IsQuorum (joinVotes t (source m)) (config m) \<and> IsQuorum (joinVotes t (source m)) (currConf m)"
    proof (cases rule: square_Next_cases)
      case unchanged with hyp1 hyp2 prem show ?thesis by auto
    next
      case (HandleStartJoin nf nm tm newJoinRequest)
      with hyp1 hyp2 prem show ?thesis by (cases "nf = source m", auto)
    next
      case (HandleJoinRequest nf nm laTerm_m laVersion_m)
      show ?thesis
      proof (cases "source m = nm")
        case False with HandleJoinRequest hyp1 hyp2 prem show ?thesis by (auto)
      next
        case True
        from prem have electionWon: "electionWon s (source m)"
          by (intro hyp5, auto simp add: True HandleJoinRequest)
        have joinVotes_increase: "\<And>vs. card (joinVotes s (source m) \<inter> vs) \<le> card (joinVotes t (source m) \<inter> vs)" 
        proof -
          fix vs
          show "?thesis vs"
          proof (cases "nf \<in> vs")
            case False thus ?thesis by (simp add: HandleJoinRequest)
          next
            case _: True
            hence eq: "joinVotes t (source m) \<inter> vs = insert nf (joinVotes s (source m) \<inter> vs)" by (auto simp add: HandleJoinRequest True)
            show ?thesis unfolding eq by (intro card_insert_le_general)
          qed
        qed
        from prem electionWon have "IsQuorum (joinVotes s (source m)) (config m) \<and> IsQuorum (joinVotes s (source m)) (currConf m)"
          by (intro conjI hyp1 hyp2, simp_all add: HandleJoinRequest True)
        with joinVotes_increase
        have "IsQuorum (joinVotes t (source m)) (config m) \<and> IsQuorum (joinVotes t (source m)) (currConf m)"
          unfolding IsQuorum_def using less_le_trans mult_le_mono1 by blast
        thus ?thesis by (simp add: HandleJoinRequest True)
      qed
    next
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
      with prem have "m \<in> messages s \<or> m \<in> newPublishRequests" by auto
      thus ?thesis
      proof (elim disjE)
        assume "m \<in> messages s" with ClientRequest prem hyp1 hyp2 show ?thesis by auto
      next
        assume m_new: "m \<in> newPublishRequests"
        hence config_m: "config m = vs"
          and currConf_m: "currConf m = lastCommittedConfiguration s (source m)"
          and source_m: "source m = nm" 
          by (auto simp add: ClientRequest config_def currConf_def)

        from ClientRequest have joinVotes_eq: "joinVotes t = joinVotes s" by simp

        from prem have "IsQuorum (joinVotes t (source m)) (currConf m)"
          unfolding currConf_m joinVotes_eq by (intro hyp3, auto simp add: ClientRequest)
        moreover from ClientRequest have "IsQuorum (joinVotes t (source m)) (config m)"
          unfolding config_m source_m by simp
        ultimately show ?thesis by simp
      qed
    next
      case (HandlePublishRequest nf nm newVersion  newValue newConfig currConfig)
      from prem have "m \<in> messages s" by (auto simp add: HandlePublishRequest isPublishRequest_def)
      with HandlePublishRequest hyp1 hyp2 prem show ?thesis by auto
    next
      case (HandlePublishResponse_NoQuorum nf nm)
      with hyp1 hyp2 prem show ?thesis by auto
    next
      case (HandlePublishResponse_Quorum nf nm)
      from prem have "m \<in> messages s" by (auto simp add: HandlePublishResponse_Quorum isPublishRequest_def)
      with HandlePublishResponse_Quorum hyp1 hyp2 prem show ?thesis by (cases "nm = source m", auto)
    next
      case (HandleCommitRequest nf nm)
      with hyp1 hyp2 prem show ?thesis by auto
    next
      case (RestartNode nr)
      with hyp1 hyp2 prem show ?thesis
      proof (cases "nr = source m")
        case True with prem RestartNode show ?thesis by auto
      qed auto
    qed
  }
  thus ?thesis by (auto simp add: PublishRequestImpliesQuorumBelow_def)
qed

lemma ElectionWonQuorumBelow_step:
  assumes "s \<Turnstile> ElectionWonQuorumBelow termBound"
  assumes "s \<Turnstile> PublishRequestImpliesQuorumBelow termBound"
  assumes "s \<Turnstile> PublishRequestSentByMasterBelow termBound"
  shows "(s,t) \<Turnstile> ElectionWonQuorumBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>n. \<lbrakk> currentTerm s n < termBound; electionWon s n \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s n) (lastCommittedConfiguration      s n)"
    and hyp2: "\<And>n. \<lbrakk> currentTerm s n < termBound; electionWon s n \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s n) (lastAcceptedConfiguration s n)"
    and hyp3: "\<And>m. \<lbrakk> m \<in> messages s; term m < termBound; isPublishRequest m; currentTerm s (source m) = term m;
                     electionWon s (source m) \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s (source m)) (config m)"
    and hyp4: "\<And>m. \<lbrakk> m \<in> messages s; term m < termBound; isPublishRequest m; currentTerm s (source m) = term m;
                     electionWon s (source m) \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s (source m)) (currConf m)"
    and hyp5: "\<And>m n. \<lbrakk> m \<in> messages s; term m = currentTerm s n; term m < termBound; isPublishRequest m; electionWon s n \<rbrakk>
                    \<Longrightarrow> n = source m"
    by (auto simp add: ElectionWonQuorumBelow_def PublishRequestImpliesQuorumBelow_def PublishRequestSentByMasterBelow_def)

  {
    fix n
    assume prem: "currentTerm t n < termBound" "electionWon t n"
    from Next
    have "IsQuorum (joinVotes t n) (lastCommittedConfiguration t n) \<and> IsQuorum (joinVotes t n) (lastAcceptedConfiguration t n)"
    proof (cases rule: square_Next_cases)
      case unchanged
      with hyp1 hyp2 prem show ?thesis by simp
    next
      case (HandleStartJoin nf nm tm newJoinRequest)
      with hyp1 hyp2 prem show ?thesis by (cases "nf = n", simp_all)
    next
      case (HandleJoinRequest nf nm laTerm_m laVersion_m)
      with hyp1 hyp2 prem show ?thesis by (cases "nm = n", simp_all)
    next
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
      with hyp1 hyp2 prem show ?thesis by simp
    next
      case (HandlePublishResponse_NoQuorum nf nm)
      with hyp1 hyp2 prem show ?thesis by simp
    next
      case (HandlePublishResponse_Quorum nf nm)
      with hyp1 hyp2 prem show ?thesis by simp
    next
      case (HandleCommitRequest nf nm)
      with hyp1 hyp2 prem show ?thesis by (cases "nf = n", simp_all)
    next
      case (RestartNode nr)
      with hyp1 hyp2 prem show ?thesis by (cases "nr = n", simp_all)
    next
      case (HandlePublishRequest nf nm newVersion  newValue newConfig currConfig)

      define publishRequest where "publishRequest \<equiv> \<lparr>source = nm, dest = nf, term = currentTerm s nf, payload = PublishRequest \<lparr>prq_version  = newVersion, prq_value = newValue, prq_config = newConfig, prq_currConf = currConfig\<rparr>\<rparr>"

      show ?thesis
      proof (cases "nf = n")
        case False with HandlePublishRequest hyp1 hyp2 prem show ?thesis by auto
      next
        case nf_eq_n: True

        have config_eqs: "joinVotes t = joinVotes s"
          "lastCommittedConfiguration t n = currConf publishRequest"
          "lastAcceptedConfiguration t n = config publishRequest"
          by (simp_all add: HandlePublishRequest nf_eq_n currConf_def config_def publishRequest_def)

        from HandlePublishRequest prem
        have n_source: "n = source publishRequest"
          by (intro hyp5, auto simp add: publishRequest_def isPublishRequest_def nf_eq_n)
        hence nm_eq_n: "nm = n" by (simp add: nf_eq_n publishRequest_def)

        from nf_eq_n n_source nm_eq_n
        show ?thesis unfolding config_eqs unfolding n_source
          apply (intro conjI hyp3 hyp4)
          using prem HandlePublishRequest
          by (auto simp add: publishRequest_def nf_eq_n isPublishRequest_def nm_eq_n)
      qed
    qed
  }
  thus ?thesis by (auto simp add: ElectionWonQuorumBelow_def)
qed

lemma PublishRequestSentByMasterBelow_step:
  assumes "s \<Turnstile> PublishRequestSentByMasterBelow termBound"
  assumes "t \<Turnstile> OneMasterPerTermBelow termBound" (* DANGER - need to show this for the after state first *)
  assumes "s \<Turnstile> LeaderHistoryFaithful"
  assumes "s \<Turnstile> PublishRequestFromHistoricalLeader"
  shows "(s,t) \<Turnstile> PublishRequestSentByMasterBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>m n. \<lbrakk> m \<in> messages s; term m = currentTerm s n; term m < termBound; isPublishRequest m; electionWon s n \<rbrakk>
                    \<Longrightarrow> n = source m"
    and hyp2: "\<And>n1 n2 tm. \<lbrakk> tm < termBound; (tm, n1) \<in> leaderHistory t; (tm, n2) \<in> leaderHistory t \<rbrakk> \<Longrightarrow> n1 = n2"
    and hyp3: "\<And>n. electionWon s n \<Longrightarrow> (currentTerm s n, n) \<in> leaderHistory s"
    and hyp4: "\<And>m. \<lbrakk> m \<in> messages s; isPublishRequest m \<rbrakk> \<Longrightarrow> (term m, source m) \<in> leaderHistory s"
    by (auto simp add: OneMasterPerTermBelow_def PublishRequestSentByMasterBelow_def
        LeaderHistoryFaithful_def PublishRequestFromHistoricalLeader_def)

  {
    fix m n
    assume prem: "m \<in> messages t" "term m = currentTerm t n" "term m < termBound" "isPublishRequest m" "electionWon t n"
    from Next
    have "n = source m"
    proof (cases rule: square_Next_cases)
      case unchanged
      with hyp1 prem show ?thesis by simp
    next
      case (HandleStartJoin nf nm tm newJoinRequest)
      from prem have "n \<noteq> nf" by (auto simp add: HandleStartJoin)
      with prem have "m \<in> messages s" "term m = currentTerm s n" "currentTerm s n < termBound" "isPublishRequest m \<Longrightarrow> electionWon s n" 
        by (auto simp add: HandleStartJoin isPublishRequest_def)
      with prem hyp1 show ?thesis by auto
    next
      case (HandleJoinRequest nf nm laTerm_m laVersion_m)
      show ?thesis
      proof (cases "n = nm")
        case False with HandleJoinRequest hyp1 prem show ?thesis by auto
      next
        case n_eq_nm: True
        show ?thesis
        proof (intro hyp2)
          from prem show "currentTerm s n < termBound" by (simp add: HandleJoinRequest)
          from prem show "(currentTerm s n, n) \<in> leaderHistory t" by (auto simp add: HandleJoinRequest n_eq_nm)
          from prem have "(term m, source m) \<in> leaderHistory s" by (intro hyp4, auto simp add: HandleJoinRequest)
          with prem show "(currentTerm s n, source m) \<in> leaderHistory t" by (auto simp add: HandleJoinRequest)
        qed
      qed
    next
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
      with prem have "m \<in> messages s \<or> m \<in> newPublishRequests" by auto
      thus ?thesis
      proof (elim disjE)
        assume "m \<in> messages s" with ClientRequest hyp1 hyp2 prem show ?thesis by auto
      next
        assume m_new: "m \<in> newPublishRequests"
        show "n = source m"
        proof (intro hyp2)
          from prem show "currentTerm s n < termBound" by (auto simp add: ClientRequest)
          from prem hyp3 show "(currentTerm s n, n) \<in> leaderHistory t" by (auto simp add: ClientRequest)
          from m_new prem have "(currentTerm s n, source m) = (currentTerm s nm, nm)"
            by (auto simp add: ClientRequest)
          also from ClientRequest hyp3 have "... \<in> leaderHistory t" by auto
          finally show "(currentTerm s n, source m) \<in> leaderHistory t" .
        qed
      qed
    next
      case (HandlePublishResponse_NoQuorum nf nm)
      with hyp1 prem show ?thesis by simp
    next
      case (HandlePublishResponse_Quorum nf nm)
      with hyp1 prem show ?thesis by (auto simp add: isPublishRequest_def)
    next
      case (HandleCommitRequest nf nm)
      with hyp1 prem show ?thesis by simp
    next
      case (RestartNode nr)
      show ?thesis
      proof (cases "n = nr")
        case False with RestartNode hyp1 hyp2 prem show ?thesis by auto
      next
        case True with prem RestartNode show ?thesis by auto
      qed
    next
      case (HandlePublishRequest nf nm newVersion  newValue newConfig currConfig)
      with hyp1 prem show ?thesis by (cases "nf = n", auto simp add: isPublishRequest_def)
    qed
  }
  thus ?thesis by (auto simp add: PublishRequestSentByMasterBelow_def)
qed

lemma PublishVersionNonzeroOnlyIfElectionWonBelow_step:
  assumes "s \<Turnstile> PublishVersionNonzeroOnlyIfElectionWonBelow termBound"
  assumes "s \<Turnstile> ElectionWonQuorumBelow termBound"
  shows "(s,t) \<Turnstile> PublishVersionNonzeroOnlyIfElectionWonBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>n. \<lbrakk> currentTerm s n < termBound; 0 < lastPublishedVersion  s n \<rbrakk> \<Longrightarrow> electionWon s n"
    and hyp2: "\<And>n. \<lbrakk> currentTerm s n < termBound; electionWon s n \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s n) (lastCommittedConfiguration s n)"
    and hyp3: "\<And>n. \<lbrakk> currentTerm s n < termBound; electionWon s n \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s n) (lastAcceptedConfiguration s n)"
    by (auto simp add: PublishVersionNonzeroOnlyIfElectionWonBelow_def ElectionWonQuorumBelow_def)

  {
    fix n
    assume prem: "currentTerm t n < termBound" "0 < lastPublishedVersion  t n"
    from Next hyp1 prem have "electionWon t n"
    proof (cases rule: square_Next_cases)
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
      with hyp1 prem show ?thesis by (cases "n = nm", auto)
    next
      case (HandleJoinRequest nf nm laTerm_m laVersion_m)
      show ?thesis
      proof (cases "nm = n")
        case False with HandleJoinRequest hyp1 prem show ?thesis by auto
      next
        case nm_eq_n: True
        show ?thesis
        proof (cases "0 < lastPublishedVersion  s n")
          case False
          with prem show ?thesis
            by (cases "\<not> electionWon s n \<and> electionWon t n", auto simp add: HandleJoinRequest nm_eq_n)
        next
          case True
          with prem have "electionWon s n" by (intro hyp1, auto simp add: HandleJoinRequest)
          with prem hyp2 hyp3 
          have  1: "IsQuorum (joinVotes t n) (lastCommittedConfiguration t n)" 
            and 2: "IsQuorum (joinVotes t n) (lastAcceptedConfiguration t n)" 
            by (auto simp add: HandleJoinRequest nm_eq_n IsQuorum_insert)
          thus ?thesis by (simp add: HandleJoinRequest nm_eq_n)
        qed
      qed
    qed auto
  }
  thus ?thesis by (auto simp add: PublishVersionNonzeroOnlyIfElectionWonBelow_def)
qed

lemma EndOfTermIsPermanentBelow_step:
  assumes "s \<Turnstile> EndOfTermIsPermanentBelow termBound"
  assumes "s \<Turnstile> LeaderHistoryBounded"
  assumes "s \<Turnstile> ElectionWonQuorumBelow termBound"
  shows "(s,t) \<Turnstile> EndOfTermIsPermanentBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>n. \<lbrakk> (currentTerm s n, n) \<in> leaderHistory s; currentTerm s n < termBound; startedJoinSinceLastReboot s n \<rbrakk> \<Longrightarrow> electionWon s n"
    and hyp2: "\<And>n tm. (tm, n) \<in> leaderHistory s \<Longrightarrow> tm \<le> currentTerm s n"
    and hyp3: "\<And>n. \<lbrakk> currentTerm s n < termBound; electionWon s n \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s n) (lastCommittedConfiguration s n)"
    and hyp4: "\<And>n. \<lbrakk> currentTerm s n < termBound; electionWon s n \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s n) (lastAcceptedConfiguration s n)"
    by (auto simp add: EndOfTermIsPermanentBelow_def LeaderHistoryBounded_def ElectionWonQuorumBelow_def)

  {
    fix n
    assume prem: "currentTerm t n < termBound" "(currentTerm t n, n) \<in> leaderHistory t" "startedJoinSinceLastReboot t n"
    from Next hyp1 prem have "electionWon t n"
    proof (cases rule: square_Next_cases)
      case unchanged
      with hyp1 prem show ?thesis by auto
    next
      case (HandleStartJoin nf nm tm newJoinRequest)
      show ?thesis
      proof (cases "nf = n")
        case False
        with HandleStartJoin hyp1 prem show ?thesis by auto
      next
        case True
        from prem HandleStartJoin have "currentTerm t n \<le> currentTerm s n"
          by (intro hyp2, auto)
        also from HandleStartJoin have "currentTerm s n < currentTerm t n" by (auto simp add: True)
        finally show ?thesis by simp
      qed
    next
      case (HandleJoinRequest nf nm laTerm_m laVersion_m)
      show ?thesis
      proof (cases "nm = n")
        case False
        with HandleJoinRequest hyp1 prem have "electionWon s n"
          by (intro hyp1, cases "electionWon t nm", auto)
        with False show ?thesis by (auto simp add: HandleJoinRequest)
      next
        case nm_eq_n: True
        show ?thesis 
        proof (cases "electionWon t n")
          case True thus ?thesis by simp
        next
          case False with HandleJoinRequest nm_eq_n have leaderHistory_eq: "leaderHistory t = leaderHistory s" by auto
          from prem have "electionWon s n" by (intro hyp1, simp_all add: leaderHistory_eq HandleJoinRequest)
          with prem hyp3 [of n] hyp4 [of n]
          have "IsQuorum (joinVotes t n) (lastCommittedConfiguration t n)"
            "IsQuorum (joinVotes t n) (lastAcceptedConfiguration t n)"
            by (auto simp add: HandleJoinRequest IsQuorum_insert)
          thus ?thesis unfolding HandleJoinRequest by (simp add: nm_eq_n)
        qed
      qed
    next
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
      with hyp1 prem show ?thesis by auto
    next
      case (HandlePublishRequest nf nm newVersion  newValue newConfig currConfig)
      with hyp1 prem show ?thesis by auto
    next
      case (HandlePublishResponse_NoQuorum nf nm)
      with hyp1 prem show ?thesis by auto
    next
      case (HandlePublishResponse_Quorum nf nm)
      with hyp1 prem show ?thesis by auto
    next
      case (HandleCommitRequest nf nm)
      with hyp1 prem show ?thesis by auto
    next
      case (RestartNode nr)
      with hyp1 prem show ?thesis by auto
    qed
  }
  thus ?thesis by (auto simp add: EndOfTermIsPermanentBelow_def)
qed

lemma termVersion_nondecreasing:
  assumes "PublishVersionNonzeroOnlyIfElectionWonBelow termBound s"
  assumes "currentTerm s n < termBound"
  shows "termVersion  n s \<le> termVersion  n t"
  using Next
proof (cases rule: square_Next_cases)
  case (HandleJoinRequest nf nm laTerm_m laVersion_m)
  show ?thesis
  proof (cases "nm = n")
    case False
    with HandleJoinRequest show ?thesis by (auto simp add: termVersion_def less_eq_TermVersion_def)
  next
    case True
    {
      assume notLeader: "\<not> electionWon s nm"
      have "\<not> (0 < lastPublishedVersion  s n)"
      proof (intro notI)
        assume "0 < lastPublishedVersion  s n"
        with assms notLeader show False by (auto simp add: PublishVersionNonzeroOnlyIfElectionWonBelow_def True)
      qed
    }
    thus ?thesis by (auto simp add: termVersion_def HandleJoinRequest less_eq_TermVersion_def)
  qed
qed (auto simp add: termVersion_def less_eq_TermVersion_def)

lemma PublishRequestVersionBelowSenderBelow_step:
  assumes "s \<Turnstile> PublishRequestVersionAtMostSenderBelow termBound"
  assumes "s \<Turnstile> JoinVotesImpliesStartedJoin"
  assumes "s \<Turnstile> PublishVersionNonzeroOnlyIfElectionWonBelow termBound"
  shows "(s,t) \<Turnstile> PublishRequestVersionAtMostSenderBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>m. \<lbrakk> m \<in> messages s; isPublishRequest m; term m < termBound \<rbrakk> \<Longrightarrow> msgTermVersion  m \<le> termVersion  (source m) s"
    and hyp2: "\<And>n. joinVotes s n \<noteq> {} \<Longrightarrow> startedJoinSinceLastReboot s n"
    by (auto simp add: PublishRequestVersionAtMostSenderBelow_def JoinVotesImpliesStartedJoin_def)

  {
    fix m
    assume prem: "m \<in> messages t" "isPublishRequest m" "term m < termBound"
    with hyp1 have hyp1: "m \<in> messages s \<Longrightarrow> msgTermVersion  m \<le> termVersion  (source m) s" by simp

    have "msgTermVersion  m \<le> termVersion  (source m) t"
    proof (cases "currentTerm s (source m) < termBound")
      case False
      with prem have "term m < currentTerm s (source m)" by auto
      also note terms_increasing
      finally show ?thesis by (auto simp add: msgTermVersion_def termVersion_def less_eq_TermVersion_def)
    next
      case True
      have termVersion_source_nondecreasing: "termVersion  (source m) s \<le> termVersion  (source m) t"
        by (intro termVersion_nondecreasing [of termBound] assms True)

      from Next hyp1 prem have "msgTermVersion  m \<le> termVersion  (source m) t \<or> msgTermVersion  m \<le> termVersion  (source m) s"
      proof (cases rule: square_Next_cases)
        case unchanged
        with hyp1 prem show ?thesis by (auto simp add: msgTermVersion_def termVersion_def)
      next
        case (HandleStartJoin nf nm tm newJoinRequest)
        with hyp1 prem show ?thesis by (auto simp add: msgTermVersion_def termVersion_def isPublishRequest_def)
      next
        case (HandleJoinRequest nf nm laTerm_m laVersion_m)
        with hyp1 prem show ?thesis by (auto simp add: msgTermVersion_def termVersion_def isPublishRequest_def)
      next
        case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
        from prem have "m \<in> messages s \<or> m \<in> newPublishRequests" by (auto simp add: ClientRequest)
        thus ?thesis
        proof (elim disjE)
          assume "m \<in> messages s"
          with hyp1 prem ClientRequest show ?thesis by (auto simp add: msgTermVersion_def termVersion_def isPublishRequest_def)
        next
          assume m_new: "m \<in> newPublishRequests"
          hence source_eq: "source m = nm" by (auto simp add: ClientRequest)

          from m_new have 1: "msgTermVersion  m = TermVersion  (currentTerm s nm) (Suc (lastAcceptedVersion  s nm))"
            by (auto simp add: msgTermVersion_def ClientRequest version_def)

          from ClientRequest have "IsQuorum (joinVotes s nm) vs" by simp
          hence "startedJoinSinceLastReboot s nm" by (intro hyp2, auto simp add: IsQuorum_def)
          with ClientRequest have 2: "termVersion  (source m) t = TermVersion  (currentTerm s nm) (Suc (lastAcceptedVersion  s nm))"
            by (auto simp add: termVersion_def source_eq)

          show ?thesis by (simp add: 1 2)
        qed
      next
        case (HandlePublishRequest nf nm newVersion  newValue newConfig currConfig)
        with hyp1 prem show ?thesis by (auto simp add: msgTermVersion_def termVersion_def isPublishRequest_def)
      next
        case (HandlePublishResponse_NoQuorum nf nm)
        with hyp1 prem show ?thesis by (auto simp add: msgTermVersion_def termVersion_def isPublishRequest_def)
      next
        case (HandlePublishResponse_Quorum nf nm)
        with hyp1 prem show ?thesis by (auto simp add: msgTermVersion_def termVersion_def isPublishRequest_def)
      next
        case (HandleCommitRequest nf nm)
        with hyp1 prem show ?thesis by (auto simp add: msgTermVersion_def termVersion_def isPublishRequest_def)
      next
        case (RestartNode nr)
        with hyp1 prem show ?thesis by (auto simp add: msgTermVersion_def termVersion_def isPublishRequest_def)
      qed
      thus "msgTermVersion  m \<le> termVersion  (source m) t"
      proof (elim disjE)
        assume "msgTermVersion  m \<le> termVersion  (source m) s" also note termVersion_source_nondecreasing
        finally show ?thesis .
      qed
    qed
  }
  thus ?thesis by (auto simp add: PublishRequestVersionAtMostSenderBelow_def)
qed

lemma PublishRequestsUniquePerTermVersionBelow_step:
  assumes "s \<Turnstile> PublishRequestsUniquePerTermVersionBelow termBound"
  assumes "s \<Turnstile> PublishRequestVersionAtMostSenderBelow termBound"
  assumes "s \<Turnstile> OneMasterPerTermBelow termBound"
  assumes "s \<Turnstile> PublishRequestFromHistoricalLeader"
  assumes "s \<Turnstile> LeaderHistoryFaithful"
  assumes "s \<Turnstile> JoinVotesImpliesStartedJoin"
  shows "(s,t) \<Turnstile> PublishRequestsUniquePerTermVersionBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>m1 m2. \<lbrakk> m1 \<in> messages s; m2 \<in> messages s; isPublishRequest m1; isPublishRequest m2;
     term m1 < termBound; term m1 = term m2; version  m1 = version  m2 \<rbrakk> \<Longrightarrow> payload m1 = payload m2"
    unfolding PublishRequestsUniquePerTermVersionBelow_def by metis
  from assms
  have  hyp2: "\<And>m. \<lbrakk> m \<in> messages s; isPublishRequest m; term m < termBound \<rbrakk> \<Longrightarrow> msgTermVersion  m \<le> termVersion  (source m) s"
    and hyp3: "\<And>n1 n2 tm. \<lbrakk> tm < termBound; (tm, n1) \<in> leaderHistory s; (tm, n2) \<in> leaderHistory s \<rbrakk> \<Longrightarrow> n1 = n2"
    and hyp4: "\<And>m. \<lbrakk> m \<in> messages s; isPublishRequest m \<rbrakk> \<Longrightarrow> (term m, source m) \<in> leaderHistory s"
    and hyp5: "\<And>n. electionWon s n \<Longrightarrow> (currentTerm s n, n) \<in> leaderHistory s"
    and hyp6: "\<And>n. joinVotes s n \<noteq> {} \<Longrightarrow> startedJoinSinceLastReboot s n"
    by (auto simp add: PublishRequestVersionAtMostSenderBelow_def OneMasterPerTermBelow_def
        PublishRequestFromHistoricalLeader_def LeaderHistoryFaithful_def JoinVotesImpliesStartedJoin_def)

  {
    fix m1 m2
    assume prem: "m1 \<in> messages t" "m2 \<in> messages t" "isPublishRequest m1" "isPublishRequest m2"
     "term m1 < termBound" "term m1 = term m2" "version  m1 = version  m2"

    with hyp1 have hyp1: "m1 \<in> messages s \<Longrightarrow> m2 \<in> messages s \<Longrightarrow> payload m1 = payload m2" by metis

    from Next prem hyp1 have "payload m1 = payload m2"
    proof (cases rule: square_Next_cases)
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)

      from ClientRequest
      have startedJoinSinceLastReboot_nm: "startedJoinSinceLastReboot s nm"
        by (intro hyp6, auto simp add: IsQuorum_def)

      have newMsg_leaderHistory: "\<And>m. m \<in> newPublishRequests \<Longrightarrow> (term m, source m) \<in> leaderHistory s"
      proof -
        fix m assume "m \<in> newPublishRequests"
        hence eqs: "source m = nm" "term m = currentTerm s nm" by (auto simp add: ClientRequest)
        from ClientRequest have "(currentTerm s nm, nm) \<in> leaderHistory s" by (intro hyp5)
        with eqs show "(term m, source m) \<in> leaderHistory s" by simp
      qed

      have source_eq: "source m1 = source m2"
      proof (intro hyp3)
        from prem show "term m1 < termBound" by simp
        from prem have "m1 \<in> messages s \<or> m1 \<in> newPublishRequests" by (auto simp add: ClientRequest)
        with prem show "(term m1, source m1) \<in> leaderHistory s"
          by (metis hyp4 newMsg_leaderHistory)
        from prem have "m2 \<in> messages s \<or> m2 \<in> newPublishRequests" by (auto simp add: ClientRequest)
        with prem have "(term m2, source m2) \<in> leaderHistory s"
          by (metis hyp4 newMsg_leaderHistory)
        with prem show "(term m1, source m2) \<in> leaderHistory s" by simp
      qed

      from prem consider
        (old_old) "m1 \<in> messages s" "m2 \<in> messages s"
        | (old_new) "m1 \<in> messages s" "m2 \<in> newPublishRequests"
        | (new_old) "m1 \<in> newPublishRequests" "m2 \<in> messages s"
        | (new_new) "m1 \<in> newPublishRequests" "m2 \<in> newPublishRequests"
        unfolding ClientRequest by auto
      thus ?thesis
      proof cases
        case old_old with hyp1 show ?thesis by simp
      next
        case new_new with ClientRequest show ?thesis by auto
      next
        case old_new
        with prem have "msgTermVersion  m1 \<le> termVersion  (source m1) s" by (intro hyp2)
        also have "... = termVersion  (source m2) s" by (simp add: source_eq)
        also from old_new have "... = termVersion  nm s" by (auto simp add: ClientRequest)
        also from ClientRequest startedJoinSinceLastReboot_nm have "... < termVersion  nm t" by (auto simp add: termVersion_def)
        also from ClientRequest old_new startedJoinSinceLastReboot_nm have "... = msgTermVersion  m2" by (auto simp add: msgTermVersion_def termVersion_def version_def)
        also from prem have "... = msgTermVersion  m1" by (simp add: msgTermVersion_def)
        finally show ?thesis by simp
      next
        case new_old
        with prem have "msgTermVersion  m2 \<le> termVersion  (source m2) s" by (intro hyp2, auto)
        also have "... = termVersion  (source m1) s" by (simp add: source_eq)
        also from new_old have "... = termVersion  nm s" by (auto simp add: ClientRequest)
        also from ClientRequest startedJoinSinceLastReboot_nm have "... < termVersion  nm t" by (auto simp add: termVersion_def)
        also from ClientRequest new_old startedJoinSinceLastReboot_nm have "... = msgTermVersion  m1" by (auto simp add: msgTermVersion_def termVersion_def version_def)
        also from prem have "... = msgTermVersion  m2" by (simp add: msgTermVersion_def)
        finally show ?thesis by simp
      qed
    qed (auto simp add: isPublishRequest_def)
  }
  thus ?thesis unfolding PublishRequestsUniquePerTermVersionBelow_def by (simp only: unl_after, metis)
qed

lemma BasedOnUniqueBelow_step:
  assumes "s \<Turnstile> BasedOnUniqueBelow termBound"
  assumes "s \<Turnstile> PublishRequestVersionAtMostSenderBelow termBound"
  assumes "s \<Turnstile> BasedOnPublishRequest"
  assumes "s \<Turnstile> PublishRequestSentByMasterBelow termBound"
  assumes "s \<Turnstile> JoinVotesImpliesStartedJoin"
  shows "(s,t) \<Turnstile> BasedOnUniqueBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>tiPrev1 tiPrev2 tCurr iCurr. \<lbrakk> tCurr < termBound;
        (TermVersion  tCurr iCurr, tiPrev1) \<in> basedOn s; (TermVersion  tCurr iCurr, tiPrev2) \<in> basedOn s \<rbrakk>
      \<Longrightarrow> tiPrev1 = tiPrev2"
    and hyp2: "\<And>m. \<lbrakk> m \<in> messages s; isPublishRequest m; term m < termBound \<rbrakk> \<Longrightarrow> msgTermVersion  m \<le> termVersion  (source m) s"
    and hyp3: "\<And>tiPrev tCurr iCurr. (TermVersion  tCurr iCurr, tiPrev) \<in> basedOn s
      \<Longrightarrow> \<exists> m \<in> messages s. isPublishRequest m \<and> term m = tCurr \<and> version  m = iCurr"
    and hyp4: "\<And>m n. \<lbrakk> m \<in> messages s; term m = currentTerm s n; term m < termBound; isPublishRequest m; electionWon s n \<rbrakk>
      \<Longrightarrow> n = source m"
    and hyp5: "\<And>n. joinVotes s n \<noteq> {} \<Longrightarrow> startedJoinSinceLastReboot s n"
    by (auto simp add: BasedOnUniqueBelow_def PublishRequestVersionAtMostSenderBelow_def
        BasedOnPublishRequest_def PublishRequestSentByMasterBelow_def JoinVotesImpliesStartedJoin_def)

  {
    fix tiPrev1 tiPrev2 tCurr iCurr
    assume prem: "tCurr < termBound"
      "(TermVersion  tCurr iCurr, tiPrev1) \<in> basedOn t"
      "(TermVersion  tCurr iCurr, tiPrev2) \<in> basedOn t"

    from Next prem hyp1 have "tiPrev1 = tiPrev2"
    proof (cases rule: square_Next_cases)
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)

      from ClientRequest have "IsQuorum (joinVotes s nm) vs" by simp
      hence startedJoinSinceLastReboot: "startedJoinSinceLastReboot s nm" by (intro hyp5, auto simp add: IsQuorum_def)

      from prem consider
        (old_old) "(TermVersion  tCurr iCurr, tiPrev1) \<in> basedOn s" "(TermVersion  tCurr iCurr, tiPrev2) \<in> basedOn s"
        | (old_new) "(TermVersion  tCurr iCurr, tiPrev1) \<in> basedOn s"
          "tCurr = currentTerm s nm" "iCurr = Suc (lastAcceptedVersion  s nm)"
          "tiPrev2 = TermVersion  (lastAcceptedTerm s nm) (lastAcceptedVersion  s nm)"
        | (new_old) "(TermVersion  tCurr iCurr, tiPrev2) \<in> basedOn s"
          "tCurr = currentTerm s nm" "iCurr = Suc (lastAcceptedVersion  s nm)"
          "tiPrev1 = TermVersion  (lastAcceptedTerm s nm) (lastAcceptedVersion  s nm)"
        | (new_new) "tiPrev1 = tiPrev2"
        by (auto simp add: ClientRequest)
      thus ?thesis
      proof cases
        case new_new thus ?thesis by simp
      next
        case old_old with hyp1 prem show ?thesis by simp
      next
        case old_new
        with hyp3 obtain m where m: "m \<in> messages s" "isPublishRequest m" "term m = tCurr" "version  m = iCurr" by metis
        from m prem old_new have nm_eq: "nm = source m" by (intro hyp4, auto simp add: ClientRequest)
        from m prem have "msgTermVersion  m \<le> termVersion  nm s" unfolding nm_eq by (intro hyp2, auto)
        thus ?thesis
          by (simp add: msgTermVersion_def m old_new termVersion_def startedJoinSinceLastReboot ClientRequest less_eq_TermVersion_def)
      next
        case new_old
        with hyp3 obtain m where m: "m \<in> messages s" "isPublishRequest m" "term m = tCurr" "version  m = iCurr" by metis
        from m prem new_old have nm_eq: "nm = source m" by (intro hyp4, auto simp add: ClientRequest)
        from m prem have "msgTermVersion  m \<le> termVersion  nm s" unfolding nm_eq by (intro hyp2, auto)
        thus ?thesis
          by (simp add: msgTermVersion_def m new_old termVersion_def startedJoinSinceLastReboot ClientRequest less_eq_TermVersion_def)
      qed
    qed auto
  }
  thus ?thesis unfolding BasedOnUniqueBelow_def by auto
qed

lemma LeaderMustAcceptItsPublishRequestsBelow_step:
  assumes "s \<Turnstile> LeaderMustAcceptItsPublishRequestsBelow termBound"
  assumes "s \<Turnstile> PublishRequestImpliesElectionWonBelow termBound"
  shows "(s,t) \<Turnstile> LeaderMustAcceptItsPublishRequestsBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>m. \<lbrakk> m \<in> messages s; isPublishRequest m; lastAcceptedVersion  s (source m) = lastPublishedVersion  s (source m);
                     term m = currentTerm s (source m); term m < termBound; electionWon s (source m) \<rbrakk>
      \<Longrightarrow> lastAcceptedTerm s (source m) = currentTerm s (source m)"
    and hyp2: "\<And>m. \<lbrakk> m \<in> messages s; term m < termBound; isPublishRequest m; currentTerm s (source m) = term m;
                     startedJoinSinceLastReboot s (source m) \<rbrakk> \<Longrightarrow> electionWon s (source m)"
    unfolding LeaderMustAcceptItsPublishRequestsBelow_def PublishRequestImpliesElectionWonBelow_def
    by metis+

  {
    fix m
    assume prem: "m \<in> messages t" "isPublishRequest m" "lastAcceptedVersion  t (source m) = lastPublishedVersion  t (source m)"
      "term m = currentTerm t (source m)" "term m < termBound" "electionWon t (source m)"

    from Next prem hyp1 have "lastAcceptedTerm t (source m) = currentTerm t (source m)"
    proof (cases rule: square_Next_cases)
      case (HandleJoinRequest nf nm laTerm_m laVersion_m)
      show ?thesis
      proof (cases "source m = nm")
        case False with HandleJoinRequest hyp1 prem show ?thesis by auto
      next
        case nm_eq: True

        show ?thesis
          unfolding HandleJoinRequest
        proof (intro hyp1)
          from prem show "m \<in> messages s" "isPublishRequest m"
            "term m = currentTerm s (source m)" "term m < termBound"
            unfolding HandleJoinRequest by simp_all
          show "electionWon s (source m)"
          proof (intro hyp2)
            from prem show "m \<in> messages s" "isPublishRequest m"
              "currentTerm s (source m) = term m" "term m < termBound"
              unfolding HandleJoinRequest by simp_all
            from HandleJoinRequest show "startedJoinSinceLastReboot s (source m)" by (simp add: nm_eq)
          qed
          with prem show "lastAcceptedVersion  s (source m) = lastPublishedVersion  s (source m)"
            by (auto simp add: HandleJoinRequest)
        qed
      qed
    next
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
      show ?thesis
      proof (cases "source m = nm")
        case False with ClientRequest hyp1 prem show ?thesis by auto
      next
        case nm_eq: True
        from prem have "m \<in> messages s \<or> m \<in> newPublishRequests" unfolding ClientRequest by auto
        thus ?thesis
        proof (elim disjE)
          assume old: "m \<in> messages s"
          show ?thesis
            unfolding ClientRequest
          proof (intro hyp1 old prem)
            from prem show "term m = currentTerm s (source m)" by (simp add: ClientRequest)
            from ClientRequest 
            show "lastAcceptedVersion  s (source m) = lastPublishedVersion  s (source m)" "electionWon s (source m)" 
              by (simp_all add: nm_eq)
          qed
        next
          assume new: "m \<in> newPublishRequests"
          from prem show ?thesis by (auto simp add: ClientRequest nm_eq)
        qed
      qed
    next
      case (RestartNode nr)
      with prem hyp1 show ?thesis by (cases "source m = nr", auto simp add: isPublishRequest_def)
    qed (auto simp add: isPublishRequest_def)
  }
  thus ?thesis unfolding LeaderMustAcceptItsPublishRequestsBelow_def by auto
qed

lemma PublishRequestsContiguousWithinTermBelow_step:
  assumes "s \<Turnstile> PublishRequestsContiguousWithinTermBelow termBound"
  assumes "s \<Turnstile> PublishRequestVersionAtMostSenderBelow termBound"
  assumes "s \<Turnstile> JoinVotesImpliesStartedJoin"
  assumes "s \<Turnstile> PublishRequestSentByMasterBelow termBound"
  assumes "s \<Turnstile> LastAcceptedTermInPast"
  assumes "s \<Turnstile> LeaderMustAcceptItsPublishRequestsBelow termBound"
  shows "(s,t) \<Turnstile> PublishRequestsContiguousWithinTermBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>m1 m2. \<lbrakk> m1 \<in> messages s; m2 \<in> messages s; isPublishRequest m1; isPublishRequest m2; term m1 = term m2; term m1 < termBound; version  m1 < version  m2 \<rbrakk>
      \<Longrightarrow> (TermVersion  (term m2) (version  m2), TermVersion  (term m2) (version  m2 - 1)) \<in> basedOn s"
    and hyp2: "\<And>m. \<lbrakk> m \<in> messages s; isPublishRequest m; term m < termBound \<rbrakk> \<Longrightarrow> msgTermVersion  m \<le> termVersion  (source m) s"
    and hyp3: "\<And>n. joinVotes s n \<noteq> {} \<Longrightarrow> startedJoinSinceLastReboot s n"
    and hyp4: "\<And>m n. \<lbrakk> m \<in> messages s; term m = currentTerm s n; term m < termBound; isPublishRequest m; electionWon s n \<rbrakk>
      \<Longrightarrow> n = source m"
    and hyp5: "\<And>n. lastAcceptedTerm s n \<le> currentTerm s n"
    and hyp6: "\<And>m. \<lbrakk> m \<in> messages s; isPublishRequest m; lastAcceptedVersion  s (source m) = lastPublishedVersion  s (source m);
                     term m = currentTerm s (source m); term m < termBound; electionWon s (source m) \<rbrakk>
      \<Longrightarrow> lastAcceptedTerm s (source m) = currentTerm s (source m)"
    unfolding PublishRequestsContiguousWithinTermBelow_def PublishRequestVersionAtMostSenderBelow_def
        JoinVotesImpliesStartedJoin_def PublishRequestSentByMasterBelow_def LastAcceptedTermInPast_def
        LeaderMustAcceptItsPublishRequestsBelow_def
    by metis+

  {
    fix m1 m2
    assume prem: "m1 \<in> messages t" "m2 \<in> messages t" "isPublishRequest m1" "isPublishRequest m2" "term m1 = term m2" "term m1 < termBound" "version  m1 < version  m2"

    from Next prem hyp1 have "(TermVersion  (term m2) (version  m2), TermVersion  (term m2) (version  m2 - 1)) \<in> basedOn t"
    proof (cases rule: square_Next_cases)
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)

      from ClientRequest have "IsQuorum (joinVotes s nm) vs" by simp
      hence startedJoinSinceLastReboot: "startedJoinSinceLastReboot s nm" by (intro hyp3, auto simp add: IsQuorum_def)

      from prem consider
        (old_old) "m1 \<in> messages s" "m2 \<in> messages s"
        | (old_new) "m1 \<in> messages s" "m2 \<in> newPublishRequests"
        | (new_old) "m1 \<in> newPublishRequests" "m2 \<in> messages s"
        | (new_new) "m1 \<in> newPublishRequests" "m2 \<in> newPublishRequests"
        unfolding ClientRequest by auto
      thus ?thesis
      proof cases
        case old_old with prem hyp1 have "(TermVersion  (term m2) (version  m2), TermVersion  (term m2) (version  m2 - 1)) \<in> basedOn s" by simp
        with ClientRequest show ?thesis by auto
      next
        case new_new with prem show ?thesis by (auto simp add: ClientRequest version_def)
      next
        case new_old
        from new_old prem have nm_eq: "nm = source m2" by (intro hyp4, auto simp add: ClientRequest)
        from new_old prem have "msgTermVersion  m2 \<le> termVersion  nm s" unfolding nm_eq by (intro hyp2, auto)
        with new_old prem show ?thesis
          by (auto simp add: msgTermVersion_def termVersion_def startedJoinSinceLastReboot less_eq_TermVersion_def ClientRequest version_def)
      next
        case old_new
        from old_new prem have nm_eq: "nm = source m1" "nm = source m2" by (intro hyp4, auto simp add: ClientRequest)

        have "lastAcceptedTerm s nm = currentTerm s nm"
          unfolding nm_eq
        proof (intro hyp6)
          from old_new show "m1 \<in> messages s" by simp
          from prem show "isPublishRequest m1" "term m1 < termBound" by simp_all
          from ClientRequest show "electionWon s (source m1)" by (simp add: nm_eq)
          from prem have "term m1 = term m2" by simp
          also from ClientRequest old_new have "term m2 = currentTerm s nm" by auto
          finally show "term m1 = currentTerm s (source m1)" by (simp add: nm_eq)
          from ClientRequest show "lastAcceptedVersion  s (source m1) = lastPublishedVersion  s (source m1)" by (simp add: nm_eq)
        qed

        moreover from old_new prem have "(TermVersion  (term m2) (version  m2), TermVersion  (lastAcceptedTerm s nm) (version  m2 - 1)) \<in> basedOn t"
          by (auto simp add: ClientRequest isPublishRequest_def version_def)

        moreover from old_new have "term m2 = currentTerm s nm" by (auto simp add: ClientRequest)

        ultimately show ?thesis by simp
      qed
    qed (auto simp add: isPublishRequest_def)
  }
  thus ?thesis unfolding PublishRequestsContiguousWithinTermBelow_def by auto
qed

end

lemma FiniteMessagesTo_INV: "\<turnstile> Spec \<longrightarrow> \<box>FiniteMessagesTo"
proof invariant
  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> Init FiniteMessagesTo"
    by (auto simp add: Spec_def Initial_def Init_def FiniteMessagesTo_def messagesTo_def)

  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> stable FiniteMessagesTo"
  proof (intro Stable actionI temp_impI)
    show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> \<box>[Next]_vars" by (simp add: Spec_def)
    fix s t assume "(s, t) \<Turnstile> $FiniteMessagesTo \<and> [Next]_vars"
    thus "(s,t) \<Turnstile> FiniteMessagesTo$" by (intro FiniteMessagesTo_step, auto)
  qed
qed

lemma JoinRequestsAtMostCurrentTerm_INV: "\<turnstile> Spec \<longrightarrow> \<box>JoinRequestsAtMostCurrentTerm"
proof invariant
  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> Init JoinRequestsAtMostCurrentTerm"
    by (auto simp add: Spec_def Initial_def Init_def JoinRequestsAtMostCurrentTerm_def)

  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> stable JoinRequestsAtMostCurrentTerm"
  proof (intro Stable actionI temp_impI)
    show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> \<box>[Next]_vars" by (simp add: Spec_def)
    fix s t assume "(s,t) \<Turnstile> $JoinRequestsAtMostCurrentTerm \<and> [Next]_vars"
    thus "(s,t) \<Turnstile> JoinRequestsAtMostCurrentTerm$" by (intro JoinRequestsAtMostCurrentTerm_step, auto)
  qed
qed

lemma JoinRequestsUniquePerTerm_INV: "\<turnstile> Spec \<longrightarrow> \<box>JoinRequestsUniquePerTerm"
proof invariant
  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> Init JoinRequestsUniquePerTerm"
    by (auto simp add: Spec_def Initial_def Init_def JoinRequestsUniquePerTerm_def)

  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> stable JoinRequestsUniquePerTerm"
  proof (intro Stable actionI temp_impI)
    from imp_box_before_afterI [OF JoinRequestsAtMostCurrentTerm_INV]
    show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> \<box>([Next]_vars \<and> $JoinRequestsAtMostCurrentTerm)"
      by (auto simp add: Spec_def Valid_def more_temp_simps)

    fix s t assume "(s,t) \<Turnstile> $JoinRequestsUniquePerTerm \<and> [Next]_vars \<and> $JoinRequestsAtMostCurrentTerm"
    thus "(s,t) \<Turnstile> JoinRequestsUniquePerTerm$" by (intro JoinRequestsUniquePerTerm_step, auto)
  qed
qed

lemma JoinVotesFaithful_INV: "\<turnstile> Spec \<longrightarrow> \<box>JoinVotesFaithful"
proof invariant
  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> Init JoinVotesFaithful"
    by (auto simp add: Spec_def Initial_def Init_def JoinVotesFaithful_def)

  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> stable JoinVotesFaithful"
  proof (intro Stable actionI temp_impI)
    show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> \<box>[Next]_vars"
      by (auto simp add: Spec_def Valid_def more_temp_simps)

    fix s t assume "(s,t) \<Turnstile> $JoinVotesFaithful \<and> [Next]_vars"
    thus "(s,t) \<Turnstile> JoinVotesFaithful$" by (intro JoinVotesFaithful_step, auto)
  qed
qed

lemma TheJoinProperty_INV: "\<turnstile> Spec \<longrightarrow> \<box>TheJoinProperty"
proof -
  from JoinRequestsUniquePerTerm_INV JoinVotesFaithful_INV
  have "\<turnstile> Spec \<longrightarrow> \<box>(JoinVotesFaithful \<and> JoinRequestsUniquePerTerm)"
    by (auto simp add: more_temp_simps Valid_def)

  also have "\<turnstile> \<box>(JoinVotesFaithful \<and> JoinRequestsUniquePerTerm) \<longrightarrow> \<box>TheJoinProperty"
  proof (intro STL4 intI temp_impI, elim temp_conjE)
    fix s
    assume s: "JoinVotesFaithful s" "JoinRequestsUniquePerTerm s"
    show "TheJoinProperty s"
      unfolding TheJoinProperty_def
    proof (intro allI impI)
      fix nm nf
      assume nf: "nf \<in> joinVotes s nm"

      with s obtain joinPayload where msg: "\<lparr>source = nf, dest = nm, term = currentTerm s nm, payload = Join joinPayload\<rparr> \<in> messages s"
        by (auto simp add: JoinVotesFaithful_def)

      define P where "P \<equiv> \<lambda>m. source m = nf \<and> dest m = nm \<and> term m = currentTerm s nm \<and> isJoin m \<and> m \<in> messages s"

      have 1: "TheJoin nf nm s = The P" by (simp add: P_def TheJoin_def)
      have "P (TheJoin nf nm s)"
        unfolding 1 
      proof (intro theI [where P = P])
        from msg show "P \<lparr>source = nf, dest = nm, term = currentTerm s nm, payload = Join joinPayload\<rparr>" by (simp add: P_def isJoin_def)
        fix m' assume m': "P m'"

        from s have eqI: "\<And>m1 m2. \<lbrakk> m1 \<in> messages s; m2 \<in> messages s; isJoin m1; isJoin m2; source m1 = source m2; term m1 = term m2 \<rbrakk> \<Longrightarrow> m1 = m2"
          by (auto simp add: JoinRequestsUniquePerTerm_def)

        from m' msg show "m' = \<lparr>source = nf, dest = nm, term = currentTerm s nm, payload = Join joinPayload\<rparr>"
          by (intro eqI, auto simp add: P_def isJoin_def)
      qed
      thus "source (TheJoin nf nm s) = nf \<and> dest (TheJoin nf nm s) = nm
          \<and> term (TheJoin nf nm s) = currentTerm s nm \<and> isJoin (TheJoin nf nm s) \<and> TheJoin nf nm s \<in> messages s"
        by (auto simp add: P_def)
    qed
  qed
  finally show ?thesis .
qed

lemma MessagePositiveTerm_INV: "\<turnstile> Spec \<longrightarrow> \<box>MessagePositiveTerm"
proof invariant
  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> Init MessagePositiveTerm"
    by (auto simp add: Spec_def Initial_def Init_def MessagePositiveTerm_def)

  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> stable MessagePositiveTerm"
  proof (intro Stable actionI temp_impI)
    from imp_box_before_afterI [OF JoinVotesFaithful_INV]
    show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> \<box>([Next]_vars \<and> $JoinVotesFaithful)"
      by (auto simp add: Spec_def Valid_def more_temp_simps)

    fix s t assume "(s,t) \<Turnstile> $MessagePositiveTerm \<and> [Next]_vars \<and> $JoinVotesFaithful"
    thus "(s,t) \<Turnstile> MessagePositiveTerm$" by (intro MessagePositiveTerm_step, auto)
  qed
qed

lemma TermIncreasedByJoin_INV: "\<turnstile> Spec \<longrightarrow> \<box>TermIncreasedByJoin"
proof invariant
  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> Init TermIncreasedByJoin"
    by (auto simp add: Spec_def Initial_def Init_def TermIncreasedByJoin_def)

  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> stable TermIncreasedByJoin"
  proof (intro Stable actionI temp_impI)
    show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> \<box>[Next]_vars"
      by (auto simp add: Spec_def Valid_def more_temp_simps)

    fix s t assume "(s,t) \<Turnstile> $TermIncreasedByJoin \<and> [Next]_vars"
    thus "(s,t) \<Turnstile> TermIncreasedByJoin$" by (intro TermIncreasedByJoin_step, auto)
  qed
qed

lemma LastAcceptedTermInPast_INV: "\<turnstile> Spec \<longrightarrow> \<box>LastAcceptedTermInPast"
proof invariant
  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> Init LastAcceptedTermInPast"
    by (auto simp add: Spec_def Initial_def Init_def LastAcceptedTermInPast_def)

  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> stable LastAcceptedTermInPast"
  proof (intro Stable actionI temp_impI)
    show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> \<box>[Next]_vars"
      by (auto simp add: Spec_def Valid_def more_temp_simps)

    fix s t assume "(s,t) \<Turnstile> $LastAcceptedTermInPast \<and> [Next]_vars"
    thus "(s,t) \<Turnstile> LastAcceptedTermInPast$" by (intro LastAcceptedTermInPast_step, auto)
  qed
qed

lemma LastAcceptedDataSource_INV: "\<turnstile> Spec \<longrightarrow> \<box>LastAcceptedDataSource"
proof invariant
  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> Init LastAcceptedDataSource"
    by (auto simp add: Spec_def Initial_def Init_def LastAcceptedDataSource_def)

  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> stable LastAcceptedDataSource"
  proof (intro Stable actionI temp_impI)
    from imp_box_before_afterI [OF MessagePositiveTerm_INV]
      imp_box_before_afterI [OF LastAcceptedTermInPast_INV]
    show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> \<box>([Next]_vars \<and> $MessagePositiveTerm \<and> $LastAcceptedTermInPast)"
      by (auto simp add: Spec_def Valid_def more_temp_simps)

    fix s t assume "(s,t) \<Turnstile> $LastAcceptedDataSource \<and> [Next]_vars \<and> $MessagePositiveTerm \<and> $LastAcceptedTermInPast"
    thus "(s,t) \<Turnstile> LastAcceptedDataSource$" by (intro LastAcceptedDataSource_step, auto)
  qed
qed

lemma CurrentConfigurationSource_INV: "\<turnstile> Spec \<longrightarrow> \<box>CurrentConfigurationSource"
  and CurrentConfigurationMsgSource_INV: "\<turnstile> Spec \<longrightarrow> \<box>CurrentConfigurationMsgSource"
proof -
  define P where "P \<equiv> LIFT (CurrentConfigurationSource \<and> CurrentConfigurationMsgSource)"
  have "\<turnstile> Spec \<longrightarrow> \<box>P"
  proof invariant
    show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> Init P"
      by (auto simp add: Spec_def Initial_def Init_def P_def 
          CurrentConfigurationSource_def CurrentConfigurationMsgSource_def CommittedConfigurations_def)

    show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> stable P"
    proof (intro Stable actionI temp_impI)
      from imp_box_before_afterI [OF LastAcceptedDataSource_INV]
        imp_box_before_afterI [OF MessagePositiveTerm_INV]
      show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> \<box>([Next]_vars \<and> $LastAcceptedDataSource \<and> $MessagePositiveTerm)"
        by (auto simp add: Spec_def Valid_def more_temp_simps)

      fix s t assume a: "(s,t) \<Turnstile> $P \<and> [Next]_vars \<and> $LastAcceptedDataSource \<and> $MessagePositiveTerm"
      from a have "(s,t) \<Turnstile> CurrentConfigurationSource$"
        by (intro CurrentConfigurationSource_step, auto simp add: P_def)
      moreover from a have "(s,t) \<Turnstile> CurrentConfigurationMsgSource$" 
        by (intro CurrentConfigurationMsgSource_step, auto simp add: P_def)
      ultimately show "(s,t) \<Turnstile> P$"
        by (auto simp add: P_def CurrentConfigurationSource_def CurrentConfigurationMsgSource_def)
    qed
  qed
  thus "\<turnstile> Spec \<longrightarrow> \<box>CurrentConfigurationSource" "\<turnstile> Spec \<longrightarrow> \<box>CurrentConfigurationMsgSource"
    by (auto simp add: more_temp_simps P_def)
qed

lemma AllConfigurationsValid_INV: "\<turnstile> Spec \<longrightarrow> \<box>AllConfigurationsValid"
proof invariant
  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> Init AllConfigurationsValid"
    by (auto simp add: Spec_def Initial_def Init_def AllConfigurationsValid_def AllConfigurations_def)

  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> stable AllConfigurationsValid"
  proof (intro Stable actionI temp_impI)
    show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> \<box>[Next]_vars"
      by (auto simp add: Spec_def Valid_def more_temp_simps)

    fix s t assume "(s,t) \<Turnstile> $AllConfigurationsValid \<and> [Next]_vars"
    thus "(s,t) \<Turnstile> AllConfigurationsValid$" by (intro AllConfigurationsValid_step, auto)
  qed
qed

lemma PublicationsInPastTerm_INV: "\<turnstile> Spec \<longrightarrow> \<box>PublicationsInPastTerm"
proof invariant
  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> Init PublicationsInPastTerm"
    by (auto simp add: Spec_def Initial_def Init_def PublicationsInPastTerm_def)

  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> stable PublicationsInPastTerm"
  proof (intro Stable actionI temp_impI)
    show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> \<box>[Next]_vars"
      by (auto simp add: Spec_def Valid_def more_temp_simps)

    fix s t assume "(s,t) \<Turnstile> $PublicationsInPastTerm \<and> [Next]_vars"
    thus "(s,t) \<Turnstile> PublicationsInPastTerm$" by (intro PublicationsInPastTerm_step, auto)
  qed
qed

lemma LeaderHistoryFaithful_INV: "\<turnstile> Spec \<longrightarrow> \<box>LeaderHistoryFaithful"
proof invariant
  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> Init LeaderHistoryFaithful"
    by (auto simp add: Spec_def Initial_def Init_def LeaderHistoryFaithful_def)

  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> stable LeaderHistoryFaithful"
  proof (intro Stable actionI temp_impI)
    show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> \<box>[Next]_vars"
      by (auto simp add: Spec_def Valid_def more_temp_simps)

    fix s t assume "(s,t) \<Turnstile> $LeaderHistoryFaithful \<and> [Next]_vars"
    thus "(s,t) \<Turnstile> LeaderHistoryFaithful$" by (intro LeaderHistoryFaithful_step, auto)
  qed
qed

lemma PublishRequestFromHistoricalLeader_INV: "\<turnstile> Spec \<longrightarrow> \<box>PublishRequestFromHistoricalLeader"
proof invariant
  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> Init PublishRequestFromHistoricalLeader"
    by (auto simp add: Spec_def Initial_def Init_def PublishRequestFromHistoricalLeader_def)

  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> stable PublishRequestFromHistoricalLeader"
  proof (intro Stable actionI temp_impI)
    from imp_box_before_afterI [OF LeaderHistoryFaithful_INV]
    show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> \<box>([Next]_vars \<and> $LeaderHistoryFaithful)"
      by (auto simp add: Spec_def Valid_def more_temp_simps)

    fix s t assume "(s,t) \<Turnstile> $PublishRequestFromHistoricalLeader \<and> [Next]_vars \<and> $LeaderHistoryFaithful"
    thus "(s,t) \<Turnstile> PublishRequestFromHistoricalLeader$" by (intro PublishRequestFromHistoricalLeader_step, auto)
  qed
qed

lemma ElectionWonQuorumBelow_0: "\<turnstile> Spec \<longrightarrow> \<box>(ElectionWonQuorumBelow 0)"
  by (intro temp_impI necT [temp_use] intI, auto simp add: ElectionWonQuorumBelow_def)

lemma OneMasterPerTermBelow_0: "\<turnstile> Spec \<longrightarrow> \<box>(OneMasterPerTermBelow 0)"
  by (intro temp_impI necT [temp_use] intI, auto simp add: OneMasterPerTermBelow_def)

lemma ElectionWonQuorumBelow_Suc:
  assumes hyp1: "\<turnstile> Spec \<longrightarrow> \<box>(ElectionWonQuorumBelow termBound)"
  shows "\<turnstile> Spec \<longrightarrow> \<box>(ElectionWonQuorumBelow (Suc termBound))"
proof invariant
  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> Init (ElectionWonQuorumBelow (Suc termBound))"
    by (auto simp add: Spec_def Initial_def Init_def ElectionWonQuorumBelow_def)

  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> stable (ElectionWonQuorumBelow (Suc termBound))"
  proof (intro Stable actionI temp_impI)
    from imp_box_before_afterI [OF hyp1]
    show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> \<box>([Next]_vars \<and> ElectionWonQuorumBelow termBound$)"
      by (auto simp add: Spec_def Valid_def more_temp_simps)

    fix s t assume "(s,t) \<Turnstile> $ElectionWonQuorumBelow (Suc termBound) \<and> [Next]_vars \<and> ElectionWonQuorumBelow termBound$"
    thus "(s,t) \<Turnstile> ElectionWonQuorumBelow (Suc termBound)$" by (intro ElectionWonQuorumBelow_step, auto)
  qed
qed

lemma PublishRequestImpliesElectionWon_INV: "\<turnstile> Spec \<longrightarrow> \<box>PublishRequestImpliesElectionWon"
proof invariant
  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> Init PublishRequestImpliesElectionWon"
    by (auto simp add: Spec_def Initial_def Init_def PublishRequestImpliesElectionWon_def)

  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> stable PublishRequestImpliesElectionWon"
  proof (intro Stable actionI temp_impI)
    from imp_box_before_afterI [OF PublicationsInPastTerm_INV]
    show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> \<box>([Next]_vars \<and> $PublicationsInPastTerm)"
      by (auto simp add: Spec_def Valid_def more_temp_simps)

    fix s t assume "(s,t) \<Turnstile> $PublishRequestImpliesElectionWon \<and> [Next]_vars \<and> $PublicationsInPastTerm"
    thus "(s,t) \<Turnstile> PublishRequestImpliesElectionWon$"
      by (intro PublishRequestImpliesElectionWon_step, auto)
  qed
qed
