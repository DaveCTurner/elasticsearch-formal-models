theory Spec
  imports Preliminaries
begin

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
  fixes lastPublishedConfiguration  :: "(Node \<Rightarrow> Node set) stfun"
  fixes lastPublishedVersion        :: "(Node \<Rightarrow> nat)      stfun"
  fixes publishVotes                :: "(Node \<Rightarrow> Node set) stfun"
    (* message history *)
  fixes messages                    :: "Message set stfun"
    (* artificial variables *)
  fixes descendant                  :: "DescendentsEntry set stfun"
  fixes initialConfiguration        :: "Node set stfun" (* constant *)
  fixes initialValue                :: "Value stfun" (* constant *)
  fixes leaderHistory               :: "(nat \<times> Node) set stfun"
  fixes basedOn                     :: "(TermVersion \<times> TermVersion) set stfun"
    (* TODO idea: track last-committed term + version, to link the current state to the proposals *)
  fixes vars defines "vars \<equiv> LIFT (currentTerm, lastCommittedConfiguration, lastAcceptedTerm,
      lastAcceptedVersion, lastAcceptedValue, lastAcceptedConfiguration, joinVotes, startedJoinSinceLastReboot,
      electionWon, lastPublishedConfiguration, lastPublishedVersion, publishVotes, messages, descendant,
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
      (\<forall>n. id<currentTerm,#n> = #0)
    \<and> (\<forall>n. id<lastCommittedConfiguration,#n> = initialConfiguration) (* agreement on initial configuration *)
    \<and> (\<forall>n. id<lastAcceptedTerm,#n> = #0)
    \<and> (\<forall>n. id<lastAcceptedVersion,#n> = #0)
    \<and> (\<forall>n. id<lastAcceptedValue,#n> = initialValue)
    \<and> (\<forall>n. id<lastAcceptedConfiguration,#n> = initialConfiguration)
    \<and> (\<forall>n. id<joinVotes,#n> = #{})
    \<and> (\<forall>n. id<startedJoinSinceLastReboot,#n> = #False)
    \<and> (\<forall>n. id<electionWon,#n> = #False)
    (*\<and> (\<forall>n. id<lastPublishedConfiguration,#n> = initialConfiguration) NB deviation from TLA+ model - this is irrelevant until electionWon, so can leave it unspecified. *)
    (*\<and> (\<forall>n. id<lastPublishedVersion,#n> = #0)                         NB deviation from TLA+ model - this is irrelevant until electionWon, so can leave it unspecified. *)
    \<and> (\<forall>n. id<publishVotes,#n> = #{})
    \<and> messages = #{}
    \<and> descendant = #{}
    \<and> initialConfiguration \<in> #ValidConfigs
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
          \<and> updated     currentTerm                n t
          \<and> unspecified lastPublishedVersion       n (* NB deviation from TLA+ model - this is irrelevant until electionWon, so can leave it unspecified. *)
          \<and> unspecified lastPublishedConfiguration n (* NB deviation from TLA+ model - this is irrelevant until electionWon, so can leave it unspecified. *)
          \<and> updated     startedJoinSinceLastReboot n True
          \<and> updated     electionWon                n False
          \<and> updated     joinVotes                  n {}
          \<and> updated     publishVotes               n {}
          \<and> messages$ = ($messages \<union> #{ joinRequest })
          \<and> unchanged (lastCommittedConfiguration, lastAcceptedTerm, lastAcceptedVersion, lastAcceptedValue,
                       lastAcceptedConfiguration, descendant, initialConfiguration,
                       initialValue, leaderHistory, basedOn)))"
    (* HandleJoinRequest *)
    (* node n handles a join request and checks if it has received enough joins (= votes) for its term to be elected as master *)
  fixes HandleJoinRequest :: "Node \<Rightarrow> Message \<Rightarrow> action"
  defines "HandleJoinRequest n m \<equiv> ACT
    ( #(case payload m of Join _ \<Rightarrow> True | _ \<Rightarrow> False)
    \<and> #(term m) = id<$currentTerm,#n>
    \<and> id<$startedJoinSinceLastReboot,#n>
    \<and> ( #(laTerm m) < id<$lastAcceptedTerm,#n>
      \<or> ( #(laTerm     m) = id<$lastAcceptedTerm,#n>
        \<and> #(laVersion  m) \<le> id<$lastAcceptedVersion,#n>)) (* TODO is this needed? *)
    \<and> modified joinVotes   n (insert (source m))
    \<and> (\<exists> joinVotes_n electionNowWon. #joinVotes_n = id<joinVotes$,#n>
                                   \<and> #electionNowWon = $(ElectionWon n joinVotes_n)
          \<and> updated electionWon n electionNowWon)
    \<and> (if id<$electionWon,#n> = #False \<and> id<electionWon$,#n>
        then (\<exists> lav. #lav = id<$lastAcceptedVersion,#n>
                  \<and> updated lastPublishedVersion n lav)
           \<and> (\<exists> lac. #lac = id<$lastAcceptedConfiguration,#n>
                  \<and> updated lastPublishedConfiguration n lac) (* NB deviation from TLA+ model in which lastPublishedConfiguration := lastAcceptedConfiguration occurs during HandleStartJoin *)
        else unchanged (lastPublishedVersion, lastPublishedConfiguration))
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

          \<and> #newPublishVersion  = id<$lastPublishedVersion,#n> + #1 (* NB deviation from TLA+ model in which an arbitrarily large newPublishVersion can be chosen *)
          \<and> #publishRequests = #(\<Union> ns \<in> UNIV. {
                \<lparr> source = n, dest = ns, term = currentTerm_n
                , payload = PublishRequest \<lparr> prq_version  = newPublishVersion
                                           , prq_value = v
                                           , prq_config = vs
                                           , prq_commConf = lastCommittedConfiguration_n \<rparr>\<rparr>})
          \<and> #newEntry = #\<lparr> prevT = lastAcceptedTerm_n
                         , prevI = lastAcceptedVersion_n
                         , nextT = currentTerm_n
                         , nextI = newPublishVersion  \<rparr>
          \<and> #matchingElems = (\<lambda>d. { e \<in> d. nextT e = prevT newEntry \<and> nextI e = prevI newEntry})<$descendant>
          \<and> #newTransitiveElems = #(\<Union> e \<in> matchingElems. {\<lparr> prevT = prevT e, prevI = prevI e, nextT = nextT newEntry, nextI = nextI newEntry \<rparr>})

          \<and> descendant$ = ($descendant \<union> #{newEntry} \<union> #newTransitiveElems)
          \<and> updated lastPublishedVersion       n newPublishVersion
          \<and> updated lastPublishedConfiguration n vs
          \<and> updated publishVotes               n {}
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
    \<and> ((#(term m) = id<$lastAcceptedTerm,#n>) \<longrightarrow> (id<$lastAcceptedVersion,#n> < #(version m)))
    \<and> updated lastAcceptedTerm           n (term     m)
    \<and> updated lastAcceptedVersion        n (version  m)
    \<and> updated lastAcceptedValue          n (value    m)
    \<and> updated lastAcceptedConfiguration  n (config   m)
    \<and> updated lastCommittedConfiguration n (commConf m)
    \<and> messages$ = (insert \<lparr> source = n, dest = source m, term = term m
                          , payload = PublishResponse \<lparr> prs_version  = version m \<rparr> \<rparr>)<$messages>
    \<and> unchanged (startedJoinSinceLastReboot, currentTerm, descendant, electionWon, lastPublishedVersion, lastPublishedConfiguration, joinVotes,
                  publishVotes, initialConfiguration, initialValue, leaderHistory, basedOn))"
    (* HandlePublishResponse *)
    (* node n commits a change *)
  fixes HandlePublishResponse :: "Node \<Rightarrow> Message \<Rightarrow> action"
  defines "HandlePublishResponse n m \<equiv> ACT
    ( id<$electionWon,#n>
    \<and> #(case payload m of PublishResponse _ \<Rightarrow> True | _ \<Rightarrow> False)
    \<and> #(term     m) = id<$currentTerm,#n>
    \<and> #(version  m) = id<$lastPublishedVersion,#n>
    \<and> modified publishVotes n (insert (source m))
    \<and> (if IsQuorum<id<publishVotes$,#n>,id<$lastCommittedConfiguration,#n>>
        \<and> IsQuorum<id<publishVotes$,#n>,id<$lastPublishedConfiguration,#n>>
        then (\<exists> commitRequests currentTerm_n.
                  #commitRequests = #(\<Union> ns \<in> UNIV. {
                        \<lparr> source = n, dest = ns, term = term m
                        , payload = Commit \<lparr> c_version  = version m \<rparr> \<rparr>})
                \<and> messages$ = ($messages \<union> #commitRequests))
        else unchanged messages)
    \<and> unchanged (startedJoinSinceLastReboot, lastCommittedConfiguration, currentTerm, electionWon, descendant,
                   lastAcceptedVersion, lastAcceptedValue, lastAcceptedTerm, lastAcceptedConfiguration,
                   lastPublishedVersion, lastPublishedConfiguration, joinVotes, initialConfiguration, initialValue, leaderHistory, basedOn))"
    (* HandleCommitRequest *)
    (* apply committed configuration to node n *)
  fixes HandleCommitRequest :: "Node \<Rightarrow> Message \<Rightarrow> action"
  defines "HandleCommitRequest n m \<equiv> ACT
    ( #(case payload m of Commit _ \<Rightarrow> True | _ \<Rightarrow> False)
    \<and> #(term     m) = id<$currentTerm,#n>
    \<and> #(term     m) = id<$lastAcceptedTerm,#n>
    \<and> #(version  m) = id<$lastAcceptedVersion,#n>
    \<and> (id<$electionWon,#n> \<longrightarrow> id<$lastAcceptedVersion,#n> = id<$lastPublishedVersion,#n>)
    \<and> (\<exists> lastAcceptedConfiguration_n. #lastAcceptedConfiguration_n = id<$lastAcceptedConfiguration,#n>
          \<and> updated lastCommittedConfiguration n lastAcceptedConfiguration_n)
    \<and> unchanged (currentTerm, joinVotes, messages, lastAcceptedTerm, lastAcceptedValue, startedJoinSinceLastReboot,
                 descendant, electionWon, lastAcceptedConfiguration, lastAcceptedVersion,
                 lastPublishedVersion, lastPublishedConfiguration, publishVotes, initialConfiguration, initialValue, leaderHistory, basedOn))"
    (* RestartNode *)
    (* crash/restart node n (loses ephemeral state) *)
  fixes RestartNode :: "Node \<Rightarrow> action"
  defines "RestartNode n \<equiv> ACT
    ( updated     electionWon                n False
    \<and> updated     startedJoinSinceLastReboot n False
    \<and> updated     joinVotes                  n {}
    \<and> unspecified lastPublishedVersion       n (* NB deviation from TLA+ model - this is irrelevant until electionWon, so can leave it unspecified. *)
    \<and> unspecified lastPublishedConfiguration n (* NB deviation from TLA+ model - this is irrelevant until electionWon, so can leave it unspecified. *)
    \<and> updated     publishVotes               n {}
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

end