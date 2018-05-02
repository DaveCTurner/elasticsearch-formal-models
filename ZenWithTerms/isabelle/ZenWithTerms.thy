theory ZenWithTerms
  imports Spec
begin

lemma laTerm_simps[simp]: "laTerm \<lparr> source = nf, dest = nm, term = tm, payload = Join \<lparr> jp_laTerm = tm', jp_laVersion = vn \<rparr> \<rparr> = tm'"
  by (simp add: laTerm_def)

lemma laVersion_simps[simp]: "laVersion \<lparr> source = nf, dest = nm, term = tm, payload = Join \<lparr> jp_laTerm = tm', jp_laVersion = vn \<rparr> \<rparr> = vn"
  by (simp add: laVersion_def)

lemma version_simps[simp]:
  "version \<lparr> source = nm, dest = nf, term = tm, payload = PublishRequest \<lparr> prq_version = vn, prq_value = v, prq_config = c, prq_commConf = cc \<rparr> \<rparr> = vn"
  "version \<lparr> source = nf, dest = nm, term = tm, payload = PublishResponse \<lparr> prs_version = vn  \<rparr> \<rparr> = vn"
  "version \<lparr> source = nm, dest = nf, term = tm, payload = Commit \<lparr> c_version = vn \<rparr> \<rparr> = vn"
  by (simp_all add: version_def)

lemma value_simps[simp]:
  "value \<lparr> source = nm, dest = nf, term = tm, payload = PublishRequest \<lparr> prq_version = vn, prq_value = v, prq_config = c, prq_commConf = cc \<rparr> \<rparr> = v"
  by (simp add: value_def)

lemma config_simps[simp]:
  "config \<lparr> source = nm, dest = nf, term = tm, payload = PublishRequest \<lparr> prq_version = vn, prq_value = v, prq_config = c, prq_commConf = cc \<rparr> \<rparr> = c"
  by (simp add: config_def)

lemma commConf_simps[simp]:
  "commConf \<lparr> source = nm, dest = nf, term = tm, payload = PublishRequest \<lparr> prq_version = vn, prq_value = v, prq_config = c, prq_commConf = cc \<rparr> \<rparr> = cc"
  by (simp add: commConf_def)

context ZenWithTerms
begin

lemma IsQuorum_intersects:
  assumes valid: "conf \<in> ValidConfigs"
  assumes quorum1: "IsQuorum votes1 conf"
  assumes quorum2: "IsQuorum votes2 conf"
  shows "votes1 \<inter> votes2 \<noteq> {}"
proof (intro notI)
  assume disjoint: "votes1 \<inter> votes2 = {}"

  from quorum1 quorum2
  have "2 * card conf < 2 * card (votes1 \<inter> conf) + 2 * card (votes2 \<inter> conf)" by (simp add: IsQuorum_def)

  also have "card ((votes1 \<inter> conf) \<union> (votes2 \<inter> conf)) = card (votes1 \<inter> conf) + card (votes2 \<inter> conf)"
  proof (intro card_Un_disjoint)
    from valid show "finite (votes1 \<inter> conf)" "finite (votes2 \<inter> conf)" by (auto simp add: ValidConfigs_def)
    from disjoint show "votes1 \<inter> conf \<inter> (votes2 \<inter> conf) = {}" by auto
  qed
  hence "2 * card (votes1 \<inter> conf) + 2 * card (votes2 \<inter> conf) = 2 * card ((votes1 \<inter> conf) \<union> (votes2 \<inter> conf))" by simp

  also from valid have "... \<le> 2 * card conf"
    unfolding mult_le_cancel1
    by (intro impI card_mono, auto simp add: ValidConfigs_def)

  finally show False by simp
qed

definition sentJoins            :: "Message set stfun" where "sentJoins            s \<equiv> { m \<in> messages s. case payload m of Join _ \<Rightarrow> True | _ \<Rightarrow> False }"
definition sentPublishRequests  :: "Message set stfun" where "sentPublishRequests  s \<equiv> { m \<in> messages s. case payload m of PublishRequest _ \<Rightarrow> True | _ \<Rightarrow> False }"
definition sentPublishResponses :: "Message set stfun" where "sentPublishResponses s \<equiv> { m \<in> messages s. case payload m of PublishResponse _ \<Rightarrow> True | _ \<Rightarrow> False }"
definition sentCommits          :: "Message set stfun" where "sentCommits          s \<equiv> { m \<in> messages s. case payload m of Commit _ \<Rightarrow> True | _ \<Rightarrow> False }"

lemma square_Next_cases [consumes 1, case_names unchanged HandleStartJoin HandleJoinRequest ClientRequest
    HandlePublishRequest HandlePublishResponse_NoQuorum HandlePublishResponse_Quorum HandleCommitRequest RestartNode]:
  assumes Next: "(s,t) \<Turnstile> [Next]_vars"
  assumes unchanged:
    "\<lbrakk> messages                  t = messages                   s
    ; sentJoins                  t = sentJoins                  s
    ; sentPublishRequests        t = sentPublishRequests        s
    ; sentPublishResponses       t = sentPublishResponses       s
    ; sentCommits                t = sentCommits                s
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
    ; lastPublishedConfiguration t = lastPublishedConfiguration s
    ; publishVotes               t = publishVotes               s
    ; initialConfiguration       t = initialConfiguration       s
    ; initialValue               t = initialValue               s
    ; leaderHistory              t = leaderHistory              s
    ; basedOn                    t = basedOn                    s
    \<rbrakk> \<Longrightarrow> P"
  assumes HandleStartJoin: "\<And>nf nm tm newJoinRequest.
    \<lbrakk> currentTerm s nf < tm
    ; newJoinRequest = \<lparr> source = nf, dest = nm, term = tm
        , payload = Join \<lparr> jp_laTerm = lastAcceptedTerm s nf, jp_laVersion = lastAcceptedVersion s nf \<rparr> \<rparr>
    ; messages                         t    = insert newJoinRequest (messages s)
    ; sentJoins                        t    = insert newJoinRequest (sentJoins s)
    ; sentPublishRequests              t    = sentPublishRequests        s
    ; sentPublishResponses             t    = sentPublishResponses       s
    ; sentCommits                      t    = sentCommits                s
    ; descendant                       t    = descendant                 s
    ; \<And>n'. currentTerm                t n' = (if n' = nf then tm else currentTerm s n')
    ; lastCommittedConfiguration       t    = lastCommittedConfiguration s
    ; lastAcceptedTerm                 t    = lastAcceptedTerm           s
    ; lastAcceptedVersion              t    = lastAcceptedVersion        s
    ; lastAcceptedValue                t    = lastAcceptedValue          s
    ; lastAcceptedConfiguration        t    = lastAcceptedConfiguration  s
    ; \<And>n'. joinVotes                  t n' = (if n' = nf then {}    else joinVotes                  s n')
    ; joinVotes t nf = {}
    ; \<And>n'. startedJoinSinceLastReboot t n' = (if n' = nf then True  else startedJoinSinceLastReboot s n')
    ; startedJoinSinceLastReboot t nf
    ; \<And>n'. electionWon                t n' = (if n' = nf then False else electionWon                s n')
    ; \<not> electionWon t nf
    ; \<And>n'. publishVotes               t n' = (if n' = nf then {}    else publishVotes               s n')
    ; publishVotes t nf = {}
    ; \<And>n'. n' \<noteq> nf \<Longrightarrow> lastPublishedVersion       t n' = lastPublishedVersion       s n'
    ; \<And>n'. n' \<noteq> nf \<Longrightarrow> lastPublishedConfiguration t n' = lastPublishedConfiguration s n'
    ; \<And>n'. currentTerm s n' \<le> currentTerm t n'
    ; initialConfiguration             t    = initialConfiguration       s
    ; initialValue                     t    = initialValue               s
    ; leaderHistory                    t    = leaderHistory              s
    ; basedOn                          t    = basedOn                    s
    \<rbrakk> \<Longrightarrow> P"
  assumes HandleJoinRequest: "\<And>nf nm laTerm_m laVersion_m.
    \<lbrakk> \<lparr> source = nf, dest = nm, term = currentTerm s nm
      , payload = Join \<lparr> jp_laTerm = laTerm_m, jp_laVersion  = laVersion_m \<rparr> \<rparr> \<in> sentJoins s
    ; startedJoinSinceLastReboot s nm
    ; laTerm_m < lastAcceptedTerm s nm \<or> (laTerm_m = lastAcceptedTerm s nm \<and> laVersion_m \<le> lastAcceptedVersion  s nm)
    ; messages                         t    = messages                   s 
    ; sentJoins                        t    = sentJoins                  s
    ; sentPublishRequests              t    = sentPublishRequests        s
    ; sentPublishResponses             t    = sentPublishResponses       s
    ; sentCommits                      t    = sentCommits                s
    ; descendant                       t    = descendant                 s
    ; currentTerm                      t    = currentTerm                s
    ; lastCommittedConfiguration       t    = lastCommittedConfiguration s
    ; lastAcceptedTerm                 t    = lastAcceptedTerm           s
    ; lastAcceptedVersion              t    = lastAcceptedVersion        s
    ; lastAcceptedValue                t    = lastAcceptedValue          s
    ; lastAcceptedConfiguration        t    = lastAcceptedConfiguration  s
    ; \<And>n'. joinVotes                  t n' = (if n' = nm then insert nf (joinVotes s nm) else joinVotes s n')
    ; startedJoinSinceLastReboot       t    = startedJoinSinceLastReboot s
    ; \<And>n'. electionWon                t n' = (if n' = nm then IsQuorum (joinVotes t nm) (lastCommittedConfiguration s nm) \<and> IsQuorum (joinVotes t nm) (lastAcceptedConfiguration s nm) else electionWon s n')
    ; \<And>n'. lastPublishedVersion       t n' = (if n' = nm then if \<not>(electionWon s nm) \<and> electionWon t nm then lastAcceptedVersion       s nm else lastPublishedVersion        s n' else lastPublishedVersion        s n')
    ; \<And>n'. lastPublishedConfiguration t n' = (if n' = nm then if \<not>(electionWon s nm) \<and> electionWon t nm then lastAcceptedConfiguration s nm else lastPublishedConfiguration  s n' else lastPublishedConfiguration  s n')
    ; publishVotes                     t    = publishVotes               s
    ; initialConfiguration             t    = initialConfiguration       s
    ; initialValue                     t    = initialValue               s
    ; leaderHistory                    t    = (if electionWon t nm then insert (currentTerm s nm, nm) (leaderHistory s) else (leaderHistory s))
    ; basedOn                          t    = basedOn                    s
    \<rbrakk> \<Longrightarrow> P"
  assumes ClientRequest: "\<And>nm v vs newPublishVersion newPublishRequests newEntry matchingElems newTransitiveElems.
    \<lbrakk> electionWon s nm
    ; vs \<in> ValidConfigs
    ; lastPublishedVersion s nm = lastAcceptedVersion s nm
    ; vs \<noteq> lastAcceptedConfiguration s nm \<Longrightarrow> lastCommittedConfiguration s nm = lastAcceptedConfiguration s nm
    ; IsQuorum (joinVotes s nm) vs
    ; newPublishVersion  = lastPublishedVersion s nm + 1
    ; newPublishRequests = (\<Union> nf \<in> UNIV. {
                \<lparr> source = nm, dest = nf, term = currentTerm s nm
                , payload = PublishRequest \<lparr> prq_version  = newPublishVersion
                                           , prq_value    = v
                                           , prq_config   = vs
                                           , prq_commConf = lastCommittedConfiguration s nm \<rparr>\<rparr>})
    ; newEntry = \<lparr> prevT = lastAcceptedTerm    s nm
                 , prevI = lastAcceptedVersion s nm
                 , nextT = currentTerm         s nm
                 , nextI = newPublishVersion  \<rparr>
    ; matchingElems = { e \<in> descendant s. nextT e = prevT newEntry \<and> nextI e = prevI newEntry}
    ; newTransitiveElems = (\<Union> e \<in> matchingElems. {\<lparr> prevT = prevT e, prevI = prevI e, nextT = nextT newEntry, nextI = nextI newEntry \<rparr>})
    ; messages                         t    = (messages s) \<union> newPublishRequests
    ; sentJoins                        t    = sentJoins                  s
    ; sentPublishRequests              t    = sentPublishRequests        s \<union> newPublishRequests
    ; sentPublishResponses             t    = sentPublishResponses       s
    ; sentCommits                      t    = sentCommits                s
    ; descendant                       t    = (descendant s) \<union> insert newEntry newTransitiveElems
    ; currentTerm                      t    = currentTerm                s
    ; lastCommittedConfiguration       t    = lastCommittedConfiguration s
    ; lastAcceptedTerm                 t    = lastAcceptedTerm           s
    ; lastAcceptedVersion              t    = lastAcceptedVersion        s
    ; lastAcceptedValue                t    = lastAcceptedValue          s
    ; lastAcceptedConfiguration        t    = lastAcceptedConfiguration  s
    ; joinVotes                        t    = joinVotes                  s
    ; startedJoinSinceLastReboot       t    = startedJoinSinceLastReboot s
    ; electionWon                      t    = electionWon                s
    ; \<And>n'. lastPublishedVersion       t n' = (if n' = nm then newPublishVersion else lastPublishedVersion       s n')
    ; \<And>n'. lastPublishedConfiguration t n' = (if n' = nm then vs                else lastPublishedConfiguration s n')
    ; \<And>n'. publishVotes               t n' = (if n' = nm then {}                else publishVotes               s n')
    ; initialConfiguration             t    = initialConfiguration       s
    ; initialValue                     t    = initialValue               s
    ; leaderHistory                    t    = leaderHistory              s
    ; basedOn                          t    = insert ( TermVersion  (currentTerm      s nm)  newPublishVersion
                                                     , TermVersion  (lastAcceptedTerm s nm) (lastAcceptedVersion s nm))
                                                     (basedOn s)
    \<rbrakk> \<Longrightarrow> P"
  assumes HandlePublishRequest: "\<And>nf nm newVersion newValue newConfig commConfig.
    \<lbrakk> \<lparr> source = nm, dest = nf, term = currentTerm s nf
      , payload = PublishRequest \<lparr> prq_version = newVersion, prq_value = newValue, prq_config = newConfig, prq_commConf = commConfig \<rparr> \<rparr> \<in> sentPublishRequests s
    ; currentTerm s nf = lastAcceptedTerm s nf \<Longrightarrow> lastAcceptedVersion  s nf < newVersion
    ; messages t = insert \<lparr> source = nf, dest = nm, term = currentTerm s nf, payload = PublishResponse \<lparr> prs_version = newVersion \<rparr> \<rparr> (messages s)
    ; sentJoins                        t    = sentJoins                  s
    ; sentPublishRequests              t    = sentPublishRequests        s
    ; sentPublishResponses             t    = insert \<lparr> source = nf, dest = nm, term = currentTerm s nf, payload = PublishResponse \<lparr> prs_version = newVersion \<rparr> \<rparr> (sentPublishResponses s)
    ; sentCommits                      t    = sentCommits                s
    ; descendant                       t    = descendant                 s
    ; currentTerm                      t    = currentTerm                s
    ; \<And>n'. lastCommittedConfiguration t n' = (if n' = nf then commConfig       else lastCommittedConfiguration s n')
    ; \<And>n'. lastAcceptedTerm           t n' = (if n' = nf then currentTerm s nf else lastAcceptedTerm           s n')
    ; \<And>n'. lastAcceptedVersion        t n' = (if n' = nf then newVersion       else lastAcceptedVersion        s n')
    ; \<And>n'. lastAcceptedValue          t n' = (if n' = nf then newValue         else lastAcceptedValue          s n')
    ; \<And>n'. lastAcceptedConfiguration  t n' = (if n' = nf then newConfig        else lastAcceptedConfiguration  s n')
    ; joinVotes                        t    = joinVotes                  s
    ; startedJoinSinceLastReboot       t    = startedJoinSinceLastReboot s
    ; electionWon                      t    = electionWon                s
    ; lastPublishedVersion             t    = lastPublishedVersion       s
    ; lastPublishedConfiguration       t    = lastPublishedConfiguration s
    ; publishVotes                     t    = publishVotes               s
    ; initialConfiguration             t    = initialConfiguration       s
    ; initialValue                     t    = initialValue               s
    ; leaderHistory                    t    = leaderHistory              s
    ; basedOn                          t    = basedOn                    s
    \<rbrakk> \<Longrightarrow> P"
  assumes HandlePublishResponse_NoQuorum: "\<And>nf nm.
    \<lbrakk> electionWon s nm
    ; \<lparr> source = nf, dest = nm, term = currentTerm s nm
      , payload = PublishResponse \<lparr> prs_version = lastPublishedVersion  s nm \<rparr> \<rparr> \<in> sentPublishResponses s
    ;   \<not> IsQuorum (publishVotes t nm) (lastCommittedConfiguration s nm)
      \<or> \<not> IsQuorum (publishVotes t nm) (lastPublishedConfiguration s nm)
    ; messages                   t    = messages                   s
    ; sentJoins                  t    = sentJoins                  s
    ; sentPublishRequests        t    = sentPublishRequests        s
    ; sentPublishResponses       t    = sentPublishResponses       s
    ; sentCommits                t    = sentCommits                s
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
    ; lastPublishedConfiguration t    = lastPublishedConfiguration s
    ; \<And>n'. publishVotes         t n' = (if n' = nm then insert nf (publishVotes s nm) else publishVotes s n')
    ; initialConfiguration       t    = initialConfiguration       s
    ; initialValue               t    = initialValue               s
    ; leaderHistory              t    = leaderHistory              s
    ; basedOn                    t    = basedOn                    s
    \<rbrakk> \<Longrightarrow> P"
  assumes HandlePublishResponse_Quorum: "\<And>nf nm.
    \<lbrakk> electionWon s nm
    ; \<lparr> source = nf, dest = nm, term = currentTerm s nm
      , payload = PublishResponse \<lparr> prs_version = lastPublishedVersion  s nm \<rparr> \<rparr> \<in> sentPublishResponses s
    ; IsQuorum (publishVotes t nm) (lastCommittedConfiguration s nm)
    ; IsQuorum (publishVotes t nm) (lastPublishedConfiguration s nm)
    ; messages                   t    = messages s \<union> (\<Union> n \<in> UNIV. {\<lparr> source = nm, dest = n, term = currentTerm s nm, payload = Commit \<lparr> c_version  = lastPublishedVersion  s nm \<rparr> \<rparr>})
    ; sentJoins                  t    = sentJoins                  s
    ; sentPublishRequests        t    = sentPublishRequests        s
    ; sentPublishResponses       t    = sentPublishResponses       s
    ; sentCommits                t    = sentCommits                s \<union> (\<Union> n \<in> UNIV. {\<lparr> source = nm, dest = n, term = currentTerm s nm, payload = Commit \<lparr> c_version  = lastPublishedVersion  s nm \<rparr> \<rparr>})
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
    ; lastPublishedConfiguration t    = lastPublishedConfiguration s
    ; \<And>n'. publishVotes         t n' = (if n' = nm then insert nf (publishVotes s nm) else publishVotes s n')
    ; initialConfiguration       t    = initialConfiguration       s
    ; initialValue               t    = initialValue               s
    ; leaderHistory              t    = leaderHistory              s
    ; basedOn                    t    = basedOn                    s
    \<rbrakk> \<Longrightarrow> P"
  assumes HandleCommitRequest: "\<And>nf nm.
    \<lbrakk> \<lparr> source = nm, dest = nf, term = currentTerm s nf
      , payload = Commit \<lparr> c_version = lastAcceptedVersion s nf \<rparr> \<rparr> \<in> sentCommits s
    ; lastAcceptedTerm s nf = currentTerm s nf
    ; electionWon s nf \<longrightarrow> lastPublishedVersion s nf = lastAcceptedVersion s nf
    ; messages                   t          = messages                   s
    ; sentJoins                  t          = sentJoins                  s
    ; sentPublishRequests        t          = sentPublishRequests        s
    ; sentPublishResponses       t          = sentPublishResponses       s
    ; sentCommits                t          = sentCommits                s
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
    ; lastPublishedConfiguration t          = lastPublishedConfiguration s
    ; publishVotes               t          = publishVotes               s
    ; initialConfiguration       t          = initialConfiguration       s
    ; initialValue               t          = initialValue               s
    ; leaderHistory              t          = leaderHistory              s
    ; basedOn                    t          = basedOn                    s
    \<rbrakk> \<Longrightarrow> P" 
  assumes RestartNode: "\<And>nr.
    \<lbrakk> messages                         t    = messages                   s
    ; sentJoins                        t    = sentJoins                  s
    ; sentPublishRequests              t    = sentPublishRequests        s
    ; sentPublishResponses             t    = sentPublishResponses       s
    ; sentCommits                      t    = sentCommits                s
    ; descendant                       t    = descendant                 s
    ; currentTerm                      t    = currentTerm                s
    ; lastCommittedConfiguration       t    = lastCommittedConfiguration s
    ; lastAcceptedTerm                 t    = lastAcceptedTerm           s
    ; lastAcceptedVersion              t    = lastAcceptedVersion        s
    ; lastAcceptedValue                t    = lastAcceptedValue          s
    ; lastAcceptedConfiguration        t    = lastAcceptedConfiguration  s
    ; \<And>n'. joinVotes                  t n' = (if n' = nr then {}    else joinVotes                  s n')
    ; joinVotes t nr = {}
    ; \<And>n'. startedJoinSinceLastReboot t n' = (if n' = nr then False else startedJoinSinceLastReboot s n')
    ; startedJoinSinceLastReboot t nr = False
    ; \<And>n'. electionWon                t n' = (if n' = nr then False else electionWon                s n')
    ; \<not> electionWon t nr
    ; \<And>n'. publishVotes               t n' = (if n' = nr then {}    else publishVotes               s n')
    ; publishVotes t nr = {}
    ; \<And>n'. n' \<noteq> nr \<Longrightarrow> lastPublishedVersion       t n' = lastPublishedVersion       s n'
    ; \<And>n'. n' \<noteq> nr \<Longrightarrow> lastPublishedConfiguration t n' = lastPublishedConfiguration s n'
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
    thus P by (intro unchanged, auto simp add: vars_def sentJoins_def sentPublishRequests_def sentPublishResponses_def sentCommits_def)
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
          auto simp add: HandleStartJoin_def updated_def modified_def joinRequest_def unspecified_def
          sentJoins_def sentPublishRequests_def sentPublishResponses_def sentCommits_def)
  next
    fix m
    assume p: "(s,t) \<Turnstile> #m \<in> $messages" "(s,t) \<Turnstile> HandleJoinRequest (dest m) m"

    from p obtain jp where jp: "payload m = Join jp" by (cases "payload m", auto simp add: HandleJoinRequest_def)
    from p have term_m: "term m = currentTerm s (dest m)" by (auto simp add: HandleJoinRequest_def)

    from jp have jp_eq: "jp = \<lparr>jp_laTerm = laTerm m, jp_laVersion  = laVersion  m\<rparr>"
      by (cases m, cases jp, simp)

    have "m = \<lparr> source = source m, dest = dest m, term = currentTerm s (dest m), payload = Join jp \<rparr>"
      by (simp add: jp term_m)
    with p jp_eq have is_message: "\<lparr> source = source m, dest = dest m, term = currentTerm s (dest m), payload = Join \<lparr>jp_laTerm = laTerm m, jp_laVersion  = laVersion  m\<rparr> \<rparr> \<in> messages s" by simp

    from p is_message show P
      apply (intro HandleJoinRequest [of "source m" "dest m" "laTerm m" "laVersion m"])
      by (auto simp add: HandleJoinRequest_def updated_def modifyAt_def modified_def ElectionWon_def
          sentJoins_def sentPublishRequests_def sentPublishResponses_def sentCommits_def)
  next
    fix nm v vs
    assume p: "(s,t) \<Turnstile> #vs \<in> #ValidConfigs" "(s,t) \<Turnstile> ClientRequest nm v vs"

    from p show P
      apply (intro ClientRequest [of nm vs])
      by (auto simp add: ClientRequest_def updated_def modified_def
          sentJoins_def sentPublishRequests_def sentPublishResponses_def sentCommits_def)
  next
    fix m
    assume p: "(s,t) \<Turnstile> #m \<in> $messages" "(s,t) \<Turnstile> HandlePublishRequest (dest m) m"

    from p obtain prq where prq: "payload m = PublishRequest prq" by (cases "payload m", auto simp add: HandlePublishRequest_def)
    from p have term_m: "term m = currentTerm s (dest m)" by (auto simp add: HandlePublishRequest_def)

    from prq have prq_eq: "prq = \<lparr>prq_version  = version  m, prq_value = value m, prq_config = config m, prq_commConf = commConf m\<rparr>"
      by (cases m, cases prq, simp)

    have "m = \<lparr> source = source m, dest = dest m, term = currentTerm s (dest m), payload = PublishRequest prq \<rparr>"
      by (simp add: prq term_m)
    with p prq_eq have is_message: "\<lparr> source = source m, dest = dest m, term = currentTerm s (dest m)
            , payload = PublishRequest \<lparr>prq_version  = version  m
                                        , prq_value = value m, prq_config = config m, prq_commConf = commConf m\<rparr> \<rparr> \<in> messages s" by simp

    from p is_message show P
      apply (intro HandlePublishRequest [of "source m" "dest m" "version  m" "value m" "config m" "commConf m"])
      by (auto simp add: HandlePublishRequest_def updated_def modified_def
          sentJoins_def sentPublishRequests_def sentPublishResponses_def sentCommits_def)
  next
    fix m
    assume p: "(s,t) \<Turnstile> #m \<in> $messages" "(s,t) \<Turnstile> HandlePublishResponse (dest m) m"

    from p obtain prs where prs: "payload m = PublishResponse prs" by (cases "payload m", auto simp add: HandlePublishResponse_def)
    from p have term_m: "term m = currentTerm s (dest m)" by (auto simp add: HandlePublishResponse_def)

    from prs have prs_eq: "prs = \<lparr>prs_version  = version m\<rparr>" by (cases m, cases prs, simp)

    have "m = \<lparr> source = source m, dest = dest m, term = currentTerm s (dest m), payload = PublishResponse prs \<rparr>"
      by (simp add: prs term_m)
    with p prs_eq have is_message: "\<lparr> source = source m, dest = dest m, term = currentTerm s (dest m)
            , payload = PublishResponse \<lparr>prs_version  = version  m\<rparr> \<rparr> \<in> messages s" by simp

    show P
    proof (cases "IsQuorum (publishVotes t (dest m)) (lastCommittedConfiguration s (dest m))
                \<and> IsQuorum (publishVotes t (dest m)) (lastPublishedConfiguration s (dest m))")
      case False
      with p is_message show P
        apply (intro HandlePublishResponse_NoQuorum [where nm = "dest m" and nm = "source m"])
        by (auto simp add: HandlePublishResponse_def updated_def modified_def
            sentJoins_def sentPublishRequests_def sentPublishResponses_def sentCommits_def)
    next
      case True
      with p is_message show P
        apply (intro HandlePublishResponse_Quorum [where nm = "dest m" and nm = "source m"])
        by (auto simp add: HandlePublishResponse_def updated_def modified_def
            sentJoins_def sentPublishRequests_def sentPublishResponses_def sentCommits_def)
    qed
  next
    fix m
    assume p: "(s,t) \<Turnstile> #m \<in> $messages" "(s,t) \<Turnstile> HandleCommitRequest (dest m) m"
    from p have payload_eq: "payload m = Commit \<lparr>c_version = lastAcceptedVersion s (dest m)\<rparr>"
      by (cases "payload m", auto simp add: HandleCommitRequest_def version_def)

    have "m = \<lparr> source = source m, dest = dest m, term = term m, payload = Commit \<lparr>c_version  = lastAcceptedVersion s (dest m)\<rparr> \<rparr>" by (simp add: payload_eq)
    with p have is_message: "\<lparr> source = source m, dest = dest m, term = currentTerm s (dest m), payload = Commit \<lparr>c_version = lastAcceptedVersion s (dest m)\<rparr> \<rparr> \<in> messages s"
      by (auto simp add: HandleCommitRequest_def)

    from p show P
      apply (intro HandleCommitRequest [of "source m" "dest m"])
      by (auto simp add: HandleCommitRequest_def is_message updated_def modified_def
          sentJoins_def sentPublishRequests_def sentPublishResponses_def sentCommits_def)
  next
    fix n assume p: "(s,t) \<Turnstile> RestartNode n"
    thus P
      by (intro RestartNode [of n], auto simp add: RestartNode_def updated_def modified_def unspecified_def
          sentJoins_def sentPublishRequests_def sentPublishResponses_def sentCommits_def)
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

lemma IsQuorum_mono:
  assumes "IsQuorum vs conf"
  assumes "vs \<subseteq> vs'"
  assumes "finite vs'"
  shows "IsQuorum vs' conf"
proof -
  from assms
  have "card (vs \<inter> conf) \<le> card (vs' \<inter> conf)"
  proof (intro card_mono)
    from `finite vs'` show "finite (vs' \<inter> conf)" by auto
  qed auto
  with assms show ?thesis by (auto simp add: IsQuorum_def)
qed

definition messagesTo :: "(Node \<Rightarrow> Message set) stfun"
  where "messagesTo s n \<equiv> { m \<in> messages s. dest m = n }"

definition termVersion  :: "Node \<Rightarrow> TermVersion  stfun"
  where "termVersion  n s \<equiv> if startedJoinSinceLastReboot s n
                              then TermVersion  (currentTerm s n) (if electionWon s n then lastPublishedVersion s n else 0)
                              else TermVersion  (Suc (currentTerm s n)) 0"
    (* if startedJoinSinceLastReboot is true then the node must increase its term before doing anything interesting,
so it is effectively at (term+1, 0) *)

definition msgTermVersion :: "Message \<Rightarrow> TermVersion"
  where "msgTermVersion m \<equiv> TermVersion (term m) (version m)"

definition laTermVersion :: "(Node \<Rightarrow> TermVersion) stfun"
  where "laTermVersion s n \<equiv> TermVersion (lastAcceptedTerm s n) (lastAcceptedVersion s n)"

definition publishResponsesBelow :: "Node \<Rightarrow> nat \<Rightarrow> Message set stfun" where "publishResponsesBelow n tm s \<equiv>
  { mprs \<in> sentPublishResponses s. source mprs = n \<and> term mprs < tm }"

definition lastAcceptedTermVersionBelow :: "Node \<Rightarrow> nat \<Rightarrow> TermVersion stfun" where "lastAcceptedTermVersionBelow n tm s \<equiv>
  let publishResponses = publishResponsesBelow n tm s
  in if publishResponses = {} then TermVersion 0 0 else Max (msgTermVersion ` publishResponses)"

(* The termWinningConfiguration is the configuration that was used to win an election in a
particular term. It is the lastAcceptedConfiguration of the winning node at the time the election
was won, which can be calculated by looking at the PublishResponse messages that that node sent in
earlier terms. *)

definition termWinningConfiguration :: "nat \<Rightarrow> Node set stfun" where "termWinningConfiguration tm s \<equiv>
  let n = (SOME n. (tm, n) \<in> leaderHistory s);
      mprq = (SOME mprq. mprq \<in> sentPublishRequests s \<and> msgTermVersion mprq = lastAcceptedTermVersionBelow n tm s)
  in if lastAcceptedTermVersionBelow n tm s = TermVersion 0 0 then initialConfiguration s else config mprq"

definition TheJoin :: "Node \<Rightarrow> Node \<Rightarrow> Message stfun" where "TheJoin nf nm s \<equiv> 
  THE m. source m = nf \<and> dest m = nm \<and> term m = currentTerm s nm \<and> m \<in> sentJoins s"

definition FiniteMessagesTo :: stpred
  where "FiniteMessagesTo s \<equiv> \<forall>n. finite (messagesTo s n)"

definition FiniteJoins :: stpred
  where "FiniteJoins s \<equiv> finite (sentJoins s)"

definition FinitePublishResponses :: stpred
  where "FinitePublishResponses s \<equiv> finite (sentPublishResponses s)"

definition FiniteTermVersions :: stpred
  where "FiniteTermVersions s \<equiv> finite (msgTermVersion ` messages s)"

definition JoinRequestsAtMostCurrentTerm :: stpred where "JoinRequestsAtMostCurrentTerm s \<equiv> 
  \<forall> m \<in> sentJoins s. term m \<le> currentTerm s (source m)"

definition JoinRequestsUniquePerTerm :: stpred where "JoinRequestsUniquePerTerm s \<equiv> 
  \<forall> m1 m2. m1 \<in> sentJoins s \<longrightarrow> m2 \<in> sentJoins s 
      \<longrightarrow> source m1 = source m2 \<longrightarrow> term m1 = term m2
      \<longrightarrow> m1 = m2"

definition JoinVotesFaithful :: stpred where "JoinVotesFaithful s \<equiv> 
  \<forall> nm nf. nf \<in> joinVotes s nm
      \<longrightarrow> (\<exists> joinPayload. \<lparr> source = nf, dest = nm, term = currentTerm s nm, payload = Join joinPayload \<rparr> \<in> sentJoins s
              \<and> TermVersion (jp_laTerm joinPayload) (jp_laVersion joinPayload) \<le> laTermVersion s nm)"

definition JoinVotesImpliesStartedJoin :: stpred where "JoinVotesImpliesStartedJoin s \<equiv>
  \<forall> n. joinVotes s n \<noteq> {} \<longrightarrow> startedJoinSinceLastReboot s n"

definition ElectionWonImpliesStartedJoin :: stpred where "ElectionWonImpliesStartedJoin s \<equiv>
  \<forall> n. electionWon s n \<longrightarrow> startedJoinSinceLastReboot s n"

definition TheJoinProperty :: stpred where "TheJoinProperty s \<equiv>
  \<forall> nm nf. nf \<in> joinVotes s nm
    \<longrightarrow> source (TheJoin nf nm s) = nf
      \<and> dest (TheJoin nf nm s) = nm
      \<and> term (TheJoin nf nm s) = currentTerm s nm
      \<and> TheJoin nf nm s \<in> sentJoins s"

definition MessagePositiveTerm :: stpred where "MessagePositiveTerm s \<equiv>
  \<forall>m \<in> messages s. term m > 0"

definition TermIncreasedByJoin :: stpred where "TermIncreasedByJoin s \<equiv>
  \<forall>n. currentTerm s n > 0 \<longrightarrow> (\<exists> m \<in> sentJoins s. currentTerm s n = term m)"

definition LastAcceptedTermInPast :: stpred where "LastAcceptedTermInPast s \<equiv>
  \<forall>n. lastAcceptedTerm s n \<le> currentTerm s n"

definition LastAcceptedDataSource :: stpred where "LastAcceptedDataSource s \<equiv>
  \<forall>n. if lastAcceptedTerm s n = 0
        then lastAcceptedVersion       s n = 0
           \<and> lastAcceptedValue         s n = initialValue s
           \<and> lastAcceptedConfiguration s n = initialConfiguration s
        else (\<exists> m \<in> sentPublishRequests s. lastAcceptedTerm          s n = term     m
                                         \<and> lastAcceptedVersion       s n = version  m
                                         \<and> lastAcceptedValue         s n = value    m
                                         \<and> lastAcceptedConfiguration s n = config   m)"

definition PublishedConfigurations :: "Node set set stfun" where "PublishedConfigurations s \<equiv>
  insert (initialConfiguration s) (config ` sentPublishRequests s)"

definition PublishedConfigurationsValid :: stpred where "PublishedConfigurationsValid s \<equiv>
  PublishedConfigurations s \<subseteq> ValidConfigs"

definition CommittedConfigurations :: "Node set set stfun" where "CommittedConfigurations s \<equiv>
  insert (initialConfiguration s)
    { c. (\<exists> mprq \<in> sentPublishRequests s. config mprq = c
           \<and> (\<exists> mc \<in> sentCommits s. msgTermVersion mc = msgTermVersion mprq)) }"

definition CommittedConfigurationsPublished :: stpred where "CommittedConfigurationsPublished s \<equiv>
  CommittedConfigurations s \<subseteq> PublishedConfigurations s"

definition PublishedConfigurationSource :: stpred where "PublishedConfigurationSource s \<equiv>
  \<forall>n. electionWon s n \<longrightarrow> lastPublishedConfiguration s n \<in> PublishedConfigurations s"

definition AcceptedConfigurationSource :: stpred where "AcceptedConfigurationSource s \<equiv>
  \<forall>n. lastAcceptedConfiguration s n \<in> PublishedConfigurations s"

definition CurrentConfigurationSource :: stpred where "CurrentConfigurationSource s \<equiv>
  \<forall>n. lastCommittedConfiguration s n \<in> CommittedConfigurations s"

definition CurrentConfigurationMsgSource :: stpred where "CurrentConfigurationMsgSource s \<equiv>
  \<forall>m \<in> sentPublishRequests s. commConf m \<in> CommittedConfigurations s"

definition PublicationsInPastTerm :: stpred where "PublicationsInPastTerm s \<equiv>
  \<forall>m \<in> sentPublishRequests s. term m \<le> currentTerm s (source m)"

definition PublishResponseBeforeLastAccepted :: stpred where "PublishResponseBeforeLastAccepted s \<equiv>
  \<forall>m \<in> sentPublishResponses s. msgTermVersion m \<le> laTermVersion s (source m)"

definition PublishResponseForLastAccepted :: stpred where "PublishResponseForLastAccepted s \<equiv>
  \<forall>n. 0 < lastAcceptedTerm s n \<longrightarrow> (\<exists> m \<in> sentPublishResponses s. source m = n \<and> msgTermVersion m = laTermVersion s n)"

definition TermWinningConfigurationHasQuorumBelow :: "nat \<Rightarrow> stpred" where "TermWinningConfigurationHasQuorumBelow termBound s \<equiv>
  \<forall> tm < termBound. \<forall> n. (tm, n) \<in> leaderHistory s \<longrightarrow> IsQuorum (source ` { j \<in> sentJoins s. dest j = n \<and> term j = tm \<and> TermVersion (laTerm j) (laVersion j) \<le> lastAcceptedTermVersionBelow n tm s }) (termWinningConfiguration tm s)"

definition PublishRequestVersionPositive :: stpred where "PublishRequestVersionPositive s \<equiv>
  \<forall> m \<in> sentPublishRequests s. 0 < version  m"

definition LeaderHistoryFaithful :: stpred where "LeaderHistoryFaithful s \<equiv>
  \<forall>n. electionWon s n \<longrightarrow> (currentTerm s n, n) \<in> leaderHistory s"

definition LeaderHistoryBounded :: stpred where "LeaderHistoryBounded s \<equiv>
  \<forall>n tm. (tm, n) \<in> leaderHistory s \<longrightarrow> tm \<le> currentTerm s n"

definition PublishRequestFromHistoricalLeader :: stpred where "PublishRequestFromHistoricalLeader s \<equiv>
  \<forall>m \<in> sentPublishRequests s. (term m, source m) \<in> leaderHistory s"

definition BasedOnIncreasing :: stpred where "BasedOnIncreasing s \<equiv>
  \<forall> tPrev iPrev tCurr iCurr. (TermVersion  tCurr iCurr, TermVersion  tPrev iPrev) \<in> basedOn s
    \<longrightarrow> iCurr = Suc iPrev \<and> tPrev \<le> tCurr"

definition PublishRequestBasedOn :: stpred where "PublishRequestBasedOn s \<equiv>
  \<forall> m \<in> sentPublishRequests s. \<exists> tiPrev. (TermVersion  (term m) (version  m), tiPrev) \<in> basedOn s"

definition BasedOnPublishRequest :: stpred where "BasedOnPublishRequest s \<equiv>
  \<forall> tiPrev tCurr iCurr. (TermVersion  tCurr iCurr, tiPrev) \<in> basedOn s
    \<longrightarrow> (\<exists> m \<in> sentPublishRequests s. term m = tCurr \<and> version  m = iCurr)"

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
  \<forall> m \<in> sentPublishRequests s. term m < termBound \<longrightarrow> currentTerm s (source m) = term m
    \<longrightarrow> startedJoinSinceLastReboot s (source m) \<longrightarrow> electionWon s (source m)"

definition PublishRequestImpliesQuorumBelow :: "nat \<Rightarrow> stpred" where "PublishRequestImpliesQuorumBelow termBound s \<equiv> (* TODO rename this to distinguish from PublishRequestMeansQuorumBelow *)
  \<forall> m \<in> sentPublishRequests s. term m < termBound \<longrightarrow> currentTerm s (source m) = term m \<longrightarrow> electionWon s (source m)
               \<longrightarrow> IsQuorum (joinVotes s (source m)) (config m)
                 \<and> IsQuorum (joinVotes s (source m)) (commConf m)"

definition PublishRequestSentByMasterBelow :: "nat \<Rightarrow> stpred" where "PublishRequestSentByMasterBelow termBound s \<equiv>
  \<forall> m n. m \<in> sentPublishRequests s \<longrightarrow> term m = currentTerm s n \<longrightarrow> term m < termBound \<longrightarrow> electionWon s n
    \<longrightarrow> n = source m"

definition EndOfTermIsPermanentBelow :: "nat \<Rightarrow> stpred" where "EndOfTermIsPermanentBelow termBound s \<equiv>
  \<forall> n. (currentTerm s n, n) \<in> leaderHistory s \<longrightarrow> currentTerm s n < termBound \<longrightarrow> startedJoinSinceLastReboot s n \<longrightarrow> electionWon s n"

definition PublishRequestVersionAtMostSenderBelow :: "nat \<Rightarrow> stpred" where "PublishRequestVersionAtMostSenderBelow termBound s \<equiv>
  \<forall> m \<in> sentPublishRequests s. term m < termBound \<longrightarrow> msgTermVersion m \<le> termVersion (source m) s"

definition PublishRequestsUniquePerTermVersionBelow :: "nat \<Rightarrow> stpred" where "PublishRequestsUniquePerTermVersionBelow termBound s \<equiv>
  \<forall> m1 m2. m1 \<in> sentPublishRequests s \<longrightarrow> m2 \<in> sentPublishRequests s
    \<longrightarrow> term m1 < termBound \<longrightarrow> term m1 = term m2 \<longrightarrow> version m1 = version m2
    \<longrightarrow> payload m1 = payload m2"

definition BasedOnUniqueBelow :: "nat \<Rightarrow> stpred" where "BasedOnUniqueBelow termBound s \<equiv>
  \<forall> tiPrev1 tiPrev2 tCurr iCurr. tCurr < termBound
      \<longrightarrow> (TermVersion tCurr iCurr, tiPrev1) \<in> basedOn s \<longrightarrow> (TermVersion tCurr iCurr, tiPrev2) \<in> basedOn s
      \<longrightarrow> tiPrev1 = tiPrev2"

definition LeaderMustAcceptItsPublishRequestsBelow :: "nat \<Rightarrow> stpred" where "LeaderMustAcceptItsPublishRequestsBelow termBound s \<equiv>
  \<forall> m \<in> sentPublishRequests s. lastAcceptedVersion s (source m) = lastPublishedVersion s (source m)
                      \<longrightarrow> term m = currentTerm s (source m) \<longrightarrow> term m < termBound \<longrightarrow> electionWon s (source m)
       \<longrightarrow> lastAcceptedTerm s (source m) = currentTerm s (source m)"

definition PublishRequestsContiguousWithinTermBelow :: "nat \<Rightarrow> stpred" where "PublishRequestsContiguousWithinTermBelow termBound s \<equiv>
  \<forall> m1 m2. m1 \<in> sentPublishRequests s \<longrightarrow> m2 \<in> sentPublishRequests s
    \<longrightarrow> term m1 = term m2 \<longrightarrow> term m1 < termBound \<longrightarrow> version m1 < version m2
    \<longrightarrow> (TermVersion (term m2) (version m2), TermVersion (term m2) (version m2 - 1)) \<in> basedOn s"

definition NewLeaderHasExpectedLastPublishedVersion :: stpred where "NewLeaderHasExpectedLastPublishedVersion s \<equiv>
  \<forall> n. electionWon s n \<longrightarrow> lastAcceptedTerm s n \<noteq> currentTerm s n
        \<longrightarrow> lastPublishedVersion s n \<in> { lastAcceptedVersion s n, Suc (lastAcceptedVersion s n) }"

definition NewLeaderSentNoMessagesYetBelow :: "nat \<Rightarrow> stpred" where "NewLeaderSentNoMessagesYetBelow termBound s \<equiv>
  \<forall> n m. electionWon s n \<longrightarrow> lastAcceptedTerm s n \<noteq> currentTerm s n \<longrightarrow> lastAcceptedVersion s n = lastPublishedVersion s n \<longrightarrow> currentTerm s n < termBound
    \<longrightarrow> m \<in> sentPublishRequests s \<longrightarrow> term m \<noteq> currentTerm s n"

definition NewLeaderCanOnlySendOneMessageBelow :: "nat \<Rightarrow> stpred" where "NewLeaderCanOnlySendOneMessageBelow termBound s \<equiv>
  \<forall> m \<in> sentPublishRequests s. term m < termBound
    \<longrightarrow> term m = currentTerm s (source m)
    \<longrightarrow> electionWon s (source m)
    \<longrightarrow> currentTerm s (source m) \<noteq> lastAcceptedTerm s (source m)
    \<longrightarrow> version m = lastPublishedVersion s (source m)"

definition LeaderCannotPublishWithoutAcceptingPreviousRequestBelow :: "nat \<Rightarrow> stpred" where "LeaderCannotPublishWithoutAcceptingPreviousRequestBelow termBound s \<equiv>
  \<forall> n. electionWon s n \<longrightarrow> currentTerm s n < termBound \<longrightarrow> lastPublishedVersion s n \<in> {lastAcceptedVersion s n, Suc (lastAcceptedVersion s n)}"

definition LastPublishedVersionImpliesLastPublishedConfigurationBelow :: "nat \<Rightarrow> stpred" where "LastPublishedVersionImpliesLastPublishedConfigurationBelow termBound s \<equiv>
  \<forall> m \<in> sentPublishRequests s. term m < termBound
    \<longrightarrow> term m = currentTerm s (source m)
    \<longrightarrow> electionWon s (source m)
    \<longrightarrow> version m = lastPublishedVersion s (source m)
    \<longrightarrow> config m = lastPublishedConfiguration s (source m)"

definition LastPublishedVersionImpliesLastCommittedConfigurationBelow :: "nat \<Rightarrow> stpred" where "LastPublishedVersionImpliesLastCommittedConfigurationBelow termBound s \<equiv>
  \<forall> m \<in> sentPublishRequests s. term m < termBound
    \<longrightarrow> term m = currentTerm s (source m)
    \<longrightarrow> electionWon s (source m)
    \<longrightarrow> version m = lastPublishedVersion s (source m)
    \<longrightarrow> msgTermVersion m \<notin> msgTermVersion ` sentCommits s
    \<longrightarrow> commConf m = lastCommittedConfiguration s (source m)"

definition LastAcceptedConfigurationEitherCommittedOrPublishedBelow :: "nat \<Rightarrow> stpred" where "LastAcceptedConfigurationEitherCommittedOrPublishedBelow termBound s \<equiv>
  \<forall>n. electionWon s n \<longrightarrow> currentTerm s n < termBound \<longrightarrow> lastAcceptedConfiguration s n \<in> { lastCommittedConfiguration s n, lastPublishedConfiguration s n }"

definition CommitMeansLaterPublicationsBelow :: "nat \<Rightarrow> stpred" where "CommitMeansLaterPublicationsBelow termBound s \<equiv>
  \<forall> mc \<in> sentCommits s. \<forall> mp \<in> sentPublishRequests s. term mc < term mp \<longrightarrow> term mp < termBound \<longrightarrow> version mc < version mp"

definition CommittedVersionsUniqueBelow :: "nat \<Rightarrow> stpred" where "CommittedVersionsUniqueBelow termBound s \<equiv>
  \<forall> mc1 mc2. mc1 \<in> sentCommits s \<longrightarrow> mc2 \<in> sentCommits s \<longrightarrow> term mc1 < termBound \<longrightarrow> term mc2 < termBound
    \<longrightarrow> version mc1 = version mc2 \<longrightarrow> term mc1 = term mc2"

definition CommitMeansPublishResponse :: stpred where "CommitMeansPublishResponse s \<equiv>
  \<forall> mc \<in> sentCommits s. \<exists> mprs \<in> sentPublishResponses s. msgTermVersion mc = msgTermVersion mprs \<and> source mc = dest mprs"

definition PublishResponseMeansPublishRequest :: stpred where "PublishResponseMeansPublishRequest s \<equiv>
  \<forall> mprs \<in> sentPublishResponses s. \<exists> mprq \<in> sentPublishRequests s. msgTermVersion mprs = msgTermVersion mprq \<and> dest mprs = source mprq"

definition JoinLimitsPublishResponses :: stpred where "JoinLimitsPublishResponses s \<equiv>
  \<forall> mj mprs. mj \<in> sentJoins s \<longrightarrow> mprs \<in> sentPublishResponses s \<longrightarrow> source mj = source mprs \<longrightarrow> term mprs < term mj
    \<longrightarrow> msgTermVersion mprs \<le> TermVersion (laTerm mj) (laVersion mj)"

definition JoinTermNewerThanLastAccepted :: stpred where "JoinTermNewerThanLastAccepted s \<equiv>
  \<forall> mj \<in> sentJoins s. laTerm mj < term mj"

definition JoinVotesFinite :: stpred where "JoinVotesFinite s \<equiv>
  \<forall> n. finite (joinVotes s n)"

definition PublishVotesOnlyCollectedByLeadersBelow :: "nat \<Rightarrow> stpred" where "PublishVotesOnlyCollectedByLeadersBelow termBound s \<equiv>
  \<forall> n. currentTerm s n < termBound \<longrightarrow> publishVotes s n \<noteq> {} \<longrightarrow> electionWon s n"

definition PublishVotesAreResponsesBelow :: "nat \<Rightarrow> stpred" where "PublishVotesAreResponsesBelow termBound s \<equiv>
  \<forall> n. currentTerm s n < termBound \<longrightarrow> publishVotes s n \<subseteq> source ` { mprs \<in> sentPublishResponses s. msgTermVersion mprs = termVersion n s }"

definition CommitMeansQuorumBelow :: "nat \<Rightarrow> stpred" where "CommitMeansQuorumBelow termBound s \<equiv>
  \<forall> mc \<in> sentCommits s. term mc < termBound \<longrightarrow> (\<exists> mprq \<in> sentPublishRequests s.
      msgTermVersion mprq = msgTermVersion mc
    \<and> IsQuorum (source ` { mprs \<in> sentPublishResponses s. msgTermVersion mprs = msgTermVersion mc }) (config mprq)
    \<and> IsQuorum (source ` { mprs \<in> sentPublishResponses s. msgTermVersion mprs = msgTermVersion mc }) (commConf mprq))"

definition PublishRequestMeansQuorumBelow :: "nat \<Rightarrow> stpred" where "PublishRequestMeansQuorumBelow termBound s \<equiv>
  \<forall> mprq \<in> sentPublishRequests s. term mprq < termBound
      \<longrightarrow> IsQuorum (source ` { j \<in> sentJoins s. dest j = source mprq \<and> term j = term mprq }) (config mprq)
        \<and> IsQuorum (source ` { j \<in> sentJoins s. dest j = source mprq \<and> term j = term mprq }) (commConf mprq)"

lemma CommittedConfigurations_subset_PublishedConfigurations:
  "CommittedConfigurationsPublished s"
  by (auto simp add: CommittedConfigurationsPublished_def CommittedConfigurations_def PublishedConfigurations_def sentPublishRequests_def) 

context
  fixes s t                                                                                                      
  assumes Next: "(s,t) \<Turnstile> [Next]_vars"
begin

lemma sentJoins_increasing: "sentJoins s \<subseteq> sentJoins t" using Next by (cases rule: square_Next_cases, auto)
lemma sentPublishRequests_increasing: "sentPublishRequests s \<subseteq> sentPublishRequests t" using Next by (cases rule: square_Next_cases, auto)
lemma sentPublishResponses_increasing: "sentPublishResponses s \<subseteq> sentPublishResponses t" using Next by (cases rule: square_Next_cases, auto)
lemma sentCommits_increasing: "sentCommits s \<subseteq> sentCommits t" using Next by (cases rule: square_Next_cases, auto)
lemma terms_increasing: shows "currentTerm s n \<le> currentTerm t n" using Next by (cases rule: square_Next_cases, auto)

lemma PublishRequestMeansQuorumBelow_step:
  assumes "s \<Turnstile> PublishRequestMeansQuorumBelow termBound"
  assumes "s \<Turnstile> FiniteJoins"
  assumes "s \<Turnstile> JoinVotesFaithful"
  assumes "s \<Turnstile> ElectionWonQuorumBelow termBound"
  shows "(s,t) \<Turnstile> PublishRequestMeansQuorumBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>mprq. \<lbrakk> mprq \<in> sentPublishRequests s; term mprq < termBound \<rbrakk> \<Longrightarrow> IsQuorum (source ` { j \<in> sentJoins s. dest j = source mprq \<and> term j = term mprq }) (config mprq)"
    and hyp2: "\<And>mprq. \<lbrakk> mprq \<in> sentPublishRequests s; term mprq < termBound \<rbrakk> \<Longrightarrow> IsQuorum (source ` { j \<in> sentJoins s. dest j = source mprq \<and> term j = term mprq }) (commConf mprq)"
    and hyp3: "\<And>n. finite (sentJoins s)"
    and hyp4: "\<And>nm nf. nf \<in> joinVotes s nm \<Longrightarrow> \<exists>joinPayload. \<lparr>source = nf, dest = nm, term = currentTerm s nm, payload = Join joinPayload\<rparr> \<in> sentJoins s \<and> TermVersion (jp_laTerm joinPayload) (jp_laVersion joinPayload) \<le> laTermVersion s nm"
    and hyp5: "\<And>n. \<lbrakk> currentTerm s n < termBound; electionWon s n \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s n) (lastCommittedConfiguration s n)"
    unfolding PublishRequestMeansQuorumBelow_def FiniteJoins_def JoinVotesFaithful_def
      ElectionWonQuorumBelow_def
    by auto

  from Next hyp3 have hyp3': "\<And>n. finite (sentJoins t)"
    by (cases rule: square_Next_cases, auto)

  {
    fix mprq
    assume prem: "mprq \<in> sentPublishRequests t" "term mprq < termBound"

    {
      fix c
      assume s: "IsQuorum (source ` { j \<in> sentJoins s. dest j = source mprq \<and> term j = term mprq }) c"
      from sentJoins_increasing have "IsQuorum (source ` { j \<in> sentJoins t. dest j = source mprq \<and> term j = term mprq }) c"
        by (intro IsQuorum_mono [OF s] finite_imageI finite_subset [OF _ hyp3'] image_mono, auto)
    }
    note IsQuorum_stable = this

    from Next hyp1 hyp2 prem
    have "(IsQuorum (source ` { j \<in> sentJoins s. dest j = source mprq \<and> term j = term mprq }) (config mprq)
         \<and> IsQuorum (source ` { j \<in> sentJoins s. dest j = source mprq \<and> term j = term mprq }) (commConf mprq))"
    proof (cases rule: square_Next_cases)
      case (ClientRequest nm v vs newPublishVersion newPublishRequests newEntry matchingElems newTransitiveElems)
      from prem consider (old) "mprq \<in> sentPublishRequests s" | (new) "mprq \<in> newPublishRequests" by (auto simp add: ClientRequest)
      thus ?thesis
      proof cases
        case old with ClientRequest hyp1 hyp2 prem show ?thesis by simp
      next
        case new
        hence config_eqs: "config mprq = vs" "commConf mprq = lastCommittedConfiguration s nm"
          by (auto simp add: ClientRequest)

        {
          fix c
          assume receivedQuorum: "IsQuorum (joinVotes s nm) c"
          have "IsQuorum (source ` { j \<in> sentJoins s. dest j = source mprq \<and> term j = term mprq }) c"
            using sentJoins_increasing
          proof (intro IsQuorum_mono [OF receivedQuorum] finite_imageI finite_subset [OF _ hyp3] subsetI)
            fix nf assume "nf \<in> joinVotes s nm"
            from hyp4 [OF this] new
            show "nf \<in> source ` {j \<in> sentJoins s. dest j = source mprq \<and> term j = term mprq}"
              by (elim exE, intro image_eqI, auto simp add: ClientRequest)
          qed auto
        }
        note IsQuorumI = this

        from new prem ClientRequest have "currentTerm s nm < termBound" by auto
        thus ?thesis unfolding config_eqs by (intro conjI IsQuorumI hyp5 ClientRequest)
      qed
    qed auto
    with IsQuorum_stable
    have "IsQuorum (source ` { j \<in> sentJoins t. dest j = source mprq \<and> term j = term mprq }) (config mprq)
        \<and> IsQuorum (source ` { j \<in> sentJoins t. dest j = source mprq \<and> term j = term mprq }) (commConf mprq)"
      by auto
  }
  thus ?thesis by (auto simp add: PublishRequestMeansQuorumBelow_def)
qed

lemma LastPublishedVersionImpliesLastCommittedConfigurationBelow_step:
  assumes "s \<Turnstile> LastPublishedVersionImpliesLastCommittedConfigurationBelow termBound"
  assumes "s \<Turnstile> PublishRequestVersionAtMostSenderBelow termBound"
  assumes "s \<Turnstile> PublishRequestImpliesElectionWonBelow termBound"
  assumes "s \<Turnstile> ElectionWonImpliesStartedJoin"
  assumes "s \<Turnstile> PublishRequestsUniquePerTermVersionBelow termBound"
  assumes "s \<Turnstile> LeaderCannotPublishWithoutAcceptingPreviousRequestBelow termBound"
  assumes "s \<Turnstile> PublishRequestSentByMasterBelow termBound"
  assumes "s \<Turnstile> NewLeaderCanOnlySendOneMessageBelow termBound"
  shows "(s,t) \<Turnstile> LastPublishedVersionImpliesLastCommittedConfigurationBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound; term m = currentTerm s (source m);
    electionWon s (source m); version m = lastPublishedVersion s (source m);
    msgTermVersion m \<notin> msgTermVersion ` sentCommits s \<rbrakk> \<Longrightarrow> commConf m = lastCommittedConfiguration s (source m)"
    and hyp2: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound \<rbrakk> \<Longrightarrow> msgTermVersion m \<le> termVersion (source m) s"
    and hyp3: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound; currentTerm s (source m) = term m; startedJoinSinceLastReboot s (source m) \<rbrakk> \<Longrightarrow> electionWon s (source m)"
    unfolding LastPublishedVersionImpliesLastCommittedConfigurationBelow_def
      PublishRequestVersionAtMostSenderBelow_def
      PublishRequestImpliesElectionWonBelow_def
    by auto

  from assms 
  have  hyp5: "\<And>n. electionWon s n \<Longrightarrow> startedJoinSinceLastReboot s n"
    and hyp6: "\<And>m1 m2. \<lbrakk> m1 \<in> sentPublishRequests s; m2 \<in> sentPublishRequests s; term m1 < termBound; term m1 = term m2; version m1 = version m2 \<rbrakk> \<Longrightarrow> payload m1 = payload m2"
    and hyp7: "\<And>n. \<lbrakk> electionWon s n; currentTerm s n < termBound \<rbrakk> \<Longrightarrow> lastPublishedVersion s n \<in> {lastAcceptedVersion s n, Suc (lastAcceptedVersion s n)}"
    and hyp8: "\<And>m n. \<lbrakk> m \<in> sentPublishRequests s; term m = currentTerm s n; term m < termBound; electionWon s n \<rbrakk> \<Longrightarrow> n = source m"
    and hyp9: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound; term m = currentTerm s (source m); electionWon s (source m); currentTerm s (source m) \<noteq> lastAcceptedTerm s (source m) \<rbrakk> \<Longrightarrow> version m = lastPublishedVersion s (source m)"
    unfolding ElectionWonImpliesStartedJoin_def PublishRequestsUniquePerTermVersionBelow_def
      LeaderCannotPublishWithoutAcceptingPreviousRequestBelow_def
      PublishRequestSentByMasterBelow_def
      NewLeaderCanOnlySendOneMessageBelow_def
    by metis+

  {
    fix mprq
    assume prem: "mprq \<in> sentPublishRequests t" "electionWon t (source mprq)"
      "term mprq = currentTerm t (source mprq)" "version mprq = lastPublishedVersion t (source mprq)"
      "term mprq < termBound"
      "msgTermVersion mprq \<notin> msgTermVersion ` sentCommits t"
    from Next hyp1 prem
    have "commConf mprq = lastCommittedConfiguration t (source mprq)"
    proof (cases rule: square_Next_cases)
      case unchanged
      with hyp1 prem show ?thesis by auto
    next
      case (HandleStartJoin nf nm tm newJoinRequest)
      from prem have ne: "nf \<noteq> source mprq" by (intro notI, simp add: HandleStartJoin)
      with HandleStartJoin have "termVersion (source mprq) t = termVersion (source mprq) s" unfolding termVersion_def by auto
      with ne hyp1 prem HandleStartJoin show ?thesis by auto
    next
      case (HandleJoinRequest nf nm laTerm_m laVersion_m)
      show ?thesis
      proof (cases "source mprq = nm")
        case False
        with prem have "commConf mprq = lastCommittedConfiguration s (source mprq)"
          by (intro hyp1, auto simp add: HandleJoinRequest)
        with False show ?thesis by (auto simp add: HandleJoinRequest)
      next
        case source_eq_nm: True
        with HandleJoinRequest prem
        have electionWon: "electionWon s (source mprq)" by (intro hyp3, auto simp add: termVersion_def msgTermVersion_def)
        with prem have "commConf mprq = lastCommittedConfiguration s (source mprq)"
          by (intro hyp1, auto simp add: HandleJoinRequest termVersion_def)
        with electionWon source_eq_nm show ?thesis by (auto simp add: HandleJoinRequest)
      qed
    next
      case (ClientRequest nm v vs newPublishVersion newPublishRequests newEntry matchingElems newTransitiveElems)
      with prem consider (newRequest) "mprq \<in> newPublishRequests" | (oldRequest) "mprq \<in> sentPublishRequests s" by auto
      thus ?thesis
      proof cases
        case newRequest thus ?thesis by (auto simp add: ClientRequest)
      next
        case oldRequest
        have ne: "source mprq \<noteq> nm"
        proof (intro notI)
          assume source_eq_nm: "source mprq = nm"
          with ClientRequest hyp5 have flags: "electionWon s (source mprq)" "electionWon t (source mprq)"
            "startedJoinSinceLastReboot s (source mprq)" "startedJoinSinceLastReboot t (source mprq)"
            by auto

          from flags prem have "termVersion (source mprq) t = msgTermVersion mprq" by (simp add: msgTermVersion_def termVersion_def)
          also from oldRequest prem have "msgTermVersion mprq \<le> termVersion (source mprq) s" by (intro hyp2)
          also from flags source_eq_nm have "termVersion (source mprq) s < termVersion (source mprq) t"
            by (simp add: termVersion_def ClientRequest)
          finally show False by simp
        qed
        with prem have "commConf mprq = lastCommittedConfiguration s (source mprq)"
          by (intro hyp1, auto simp add: ClientRequest termVersion_def)
        with ne show ?thesis by (auto simp add: ClientRequest)
      qed
    next
      case (HandlePublishRequest nf nm newVersion newValue newConfig commConfig)
      show ?thesis
      proof (cases "source mprq = nf")
        case False
        with prem have "commConf mprq = lastCommittedConfiguration s (source mprq)"
          by (intro hyp1, auto simp add: HandlePublishRequest termVersion_def)
        with False show ?thesis by (auto simp add: HandlePublishRequest)
      next
        case True
        let ?mprq' = "\<lparr>source = nm, dest = nf, term = currentTerm s nf, payload = PublishRequest \<lparr>prq_version = newVersion, prq_value = newValue, prq_config = newConfig, prq_commConf = commConfig\<rparr>\<rparr>"
        have "payload mprq = payload ?mprq'"
        proof (intro hyp6)
          from prem show "mprq \<in> sentPublishRequests s" "term mprq < termBound" "term mprq = term ?mprq'" by (auto simp add: HandlePublishRequest True)
          from HandlePublishRequest show "?mprq' \<in> sentPublishRequests s" by simp

          from prem HandlePublishRequest True
          have "nf = source ?mprq'"
            by (intro hyp8, auto)
          hence nm_nf: "nm = nf" by simp

          from prem True HandlePublishRequest hyp5 have flags: "electionWon s nf" "startedJoinSinceLastReboot s nf" by auto

          from prem have lastPublishedVersion_options: "lastPublishedVersion s nf \<in> {lastAcceptedVersion s nf, Suc (lastAcceptedVersion s nf)}"
            by (intro hyp7, auto simp add: True HandlePublishRequest)

          show "version mprq = version ?mprq'"
          proof (cases "currentTerm s nf = lastAcceptedTerm s nf")
            case newLeader: False
            with prem HandlePublishRequest True
            have "version ?mprq' = lastPublishedVersion s (source ?mprq')" by (intro hyp9, auto simp add: nm_nf)
            with prem show ?thesis by (simp add: True nm_nf HandlePublishRequest)
          next
            case oldLeader: True
            show ?thesis
            proof (intro order_antisym)
              from oldLeader HandlePublishRequest have "lastAcceptedVersion s nf < newVersion" by auto
              with lastPublishedVersion_options have "lastPublishedVersion s nf \<le> newVersion" by auto
              with prem True show "version mprq \<le> version ?mprq'" by (auto simp add: HandlePublishRequest)
            next
              from prem HandlePublishRequest True
              have "msgTermVersion ?mprq' \<le> termVersion (source ?mprq') s"
                by (intro hyp2, auto)
              also have "... = TermVersion (currentTerm s nf) (lastPublishedVersion s nf)"
                using flags by (auto simp add: nm_nf termVersion_def)
              finally show "version ?mprq' \<le> version mprq" using prem by (auto simp add: HandlePublishRequest msgTermVersion_def less_eq_TermVersion_def True)
            qed
          qed
        qed

        hence "commConf mprq = commConfig" by (simp add: commConf_def)
        also have "commConfig = lastCommittedConfiguration t (source mprq)" by (simp add: HandlePublishRequest True)
        finally show ?thesis .
      qed
    next
      case (HandlePublishResponse_NoQuorum nf nm)
      with hyp1 prem show ?thesis unfolding termVersion_def HandlePublishResponse_NoQuorum by auto
    next
      case (HandlePublishResponse_Quorum nf nm)
      from prem
      have "msgTermVersion mprq \<notin> msgTermVersion ` sentCommits s" by (auto simp add: HandlePublishResponse_Quorum)
      with HandlePublishResponse_Quorum hyp1 prem show ?thesis unfolding termVersion_def HandlePublishResponse_Quorum by auto
    next
      case (HandleCommitRequest nf nm)
      show ?thesis
      proof (cases "source mprq = nf")
        case False
        with hyp1 prem show ?thesis unfolding termVersion_def HandleCommitRequest by auto
      next
        case True
        let ?mc = "\<lparr>source = nm, dest = nf, term = currentTerm s nf, payload = Commit \<lparr>c_version = lastAcceptedVersion s nf\<rparr>\<rparr>"
        from prem True HandleCommitRequest hyp5 have flags: "electionWon s nf" "startedJoinSinceLastReboot s nf" "currentTerm s nf < termBound" by auto
        with HandleCommitRequest have accepted: "lastPublishedVersion s nf = lastAcceptedVersion s nf" by auto
        from HandleCommitRequest prem
        have "msgTermVersion mprq \<in> msgTermVersion ` sentCommits s"
          by (intro image_eqI [where x = ?mc], auto simp add: msgTermVersion_def True accepted)
        with prem show ?thesis by (auto simp add: HandleCommitRequest)
      qed
    next
      case (RestartNode nr)
      from prem have ne: "nr \<noteq> source mprq" by (intro notI, simp add: RestartNode)
      with RestartNode have "termVersion (source mprq) t = termVersion (source mprq) s" unfolding termVersion_def by auto
      with ne hyp1 prem RestartNode show ?thesis by auto
    qed
  }
  thus ?thesis by (auto simp add: LastPublishedVersionImpliesLastCommittedConfigurationBelow_def)
qed

lemma JoinVotesFinite_step:
  assumes "s \<Turnstile> JoinVotesFinite"
  shows "(s,t) \<Turnstile> JoinVotesFinite$"
  using Next assms
  unfolding JoinVotesFinite_def
  by (cases rule: square_Next_cases, auto)

lemma PublishVotesOnlyCollectedByLeadersBelow_step:
  assumes "s \<Turnstile> PublishVotesOnlyCollectedByLeadersBelow termBound"
  assumes "s \<Turnstile> ElectionWonQuorumBelow termBound"
  assumes "s \<Turnstile> JoinVotesFinite"
  shows "(s,t) \<Turnstile> PublishVotesOnlyCollectedByLeadersBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>n. \<lbrakk> currentTerm s n < termBound; publishVotes s n \<noteq> {} \<rbrakk> \<Longrightarrow> electionWon s n"
    and hyp2: "\<And>n. \<lbrakk> currentTerm s n < termBound; electionWon s n \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s n) (lastCommittedConfiguration s n)"
    and hyp3: "\<And>n. \<lbrakk> currentTerm s n < termBound; electionWon s n \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s n) (lastAcceptedConfiguration s n)"
    and hyp4: "\<And>n. finite (joinVotes s n)"
    unfolding PublishVotesOnlyCollectedByLeadersBelow_def ElectionWonQuorumBelow_def JoinVotesFinite_def
    by auto

  {
    fix n
    assume prem: "currentTerm t n < termBound" "publishVotes t n \<noteq> {}"
    from Next hyp1 prem
    have "electionWon t n"
    proof (cases rule: square_Next_cases)
      case (HandleStartJoin nf nm tm newJoinRequest)
      with hyp1 prem show ?thesis by (cases "nf = n", auto)
    next
      case (RestartNode nr)
      with hyp1 prem show ?thesis by (cases "nr = n", auto)
    next
      case (ClientRequest nm v vs newPublishVersion newPublishRequests newEntry matchingElems newTransitiveElems)
      with hyp1 prem show ?thesis by (cases "nm = n", auto)
    next
      case (HandleJoinRequest nf nm laTerm_m laVersion_m)
      with prem hyp1 have electionWon: "electionWon s n"
        and termBound: "currentTerm s n < termBound"
        and joinVotes_increasing: "joinVotes s n \<subseteq> joinVotes t n" by auto

      from HandleJoinRequest hyp4 [of n] have joinVotes_finite: "finite (joinVotes t n)" by auto
      
      have q1: "IsQuorum (joinVotes t n) (lastCommittedConfiguration s n)"
        by (intro IsQuorum_mono [OF hyp2] electionWon termBound joinVotes_increasing joinVotes_finite)
      have q2: "IsQuorum (joinVotes t n) (lastAcceptedConfiguration s n)"
        by (intro IsQuorum_mono [OF hyp3] electionWon termBound joinVotes_increasing joinVotes_finite)

      from q1 q2 electionWon
      show ?thesis unfolding HandleJoinRequest by auto
    next
      case (HandlePublishResponse_NoQuorum nf nm)
      with hyp1 prem show ?thesis by (cases "nm = n", auto)
    next
      case (HandlePublishResponse_Quorum nf nm)
      with hyp1 prem show ?thesis by (cases "nm = n", auto)
    next
    qed auto
  }
  thus ?thesis by (auto simp add: PublishVotesOnlyCollectedByLeadersBelow_def)
qed

lemma PublishVotesAreResponsesBelow_step:
  assumes "s \<Turnstile> PublishVotesAreResponsesBelow termBound"
  assumes "s \<Turnstile> PublishVotesOnlyCollectedByLeadersBelow termBound"
  assumes "s \<Turnstile> ElectionWonQuorumBelow termBound"
  assumes "s \<Turnstile> JoinVotesFinite"
  assumes "s \<Turnstile> ElectionWonImpliesStartedJoin"
  shows "(s,t) \<Turnstile> PublishVotesAreResponsesBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>n. currentTerm s n < termBound \<Longrightarrow> publishVotes s n \<subseteq> source ` { mprs \<in> sentPublishResponses s. msgTermVersion mprs = termVersion n s }"
    and hyp2: "\<And>n. \<lbrakk> currentTerm s n < termBound; publishVotes s n \<noteq> {} \<rbrakk> \<Longrightarrow> electionWon s n"
    and hyp3: "\<And>n. \<lbrakk> currentTerm s n < termBound; electionWon s n \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s n) (lastCommittedConfiguration s n)"
    and hyp4: "\<And>n. \<lbrakk> currentTerm s n < termBound; electionWon s n \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s n) (lastAcceptedConfiguration s n)"
    and hyp5: "\<And>n. finite (joinVotes s n)"
    and hyp6: "\<And>n. electionWon s n \<Longrightarrow> startedJoinSinceLastReboot s n"
    unfolding PublishVotesAreResponsesBelow_def PublishVotesOnlyCollectedByLeadersBelow_def ElectionWonQuorumBelow_def JoinVotesFinite_def
      ElectionWonImpliesStartedJoin_def
    by auto

  {
    fix n
    assume prem: "currentTerm t n < termBound"

    from Next hyp1 [of n] prem have "publishVotes t n \<subseteq> source ` { mprs \<in> sentPublishResponses t. msgTermVersion mprs = termVersion n t }"
    proof (cases rule: square_Next_cases)
      case (HandleJoinRequest nf nm laTerm_m laVersion_m)
      consider (ne) "nm \<noteq> n" | (noVotes) "nm = n" "publishVotes t n = {}" | (votes) "nm = n" "publishVotes t n \<noteq> {}" by auto
      thus ?thesis
      proof cases
        case ne with hyp1 [of n] prem show ?thesis by (auto simp add: HandleJoinRequest termVersion_def)
      next
        case noVotes thus ?thesis by simp
      next
        case votes

        note termVersion_def

        from HandleJoinRequest prem hyp2 votes have electionWon: "electionWon s n"
          and termBound: "currentTerm s n < termBound"
          and joinVotes_increasing: "joinVotes s n \<subseteq> joinVotes t n" by auto

        from HandleJoinRequest hyp5 [of n] have joinVotes_finite: "finite (joinVotes t n)" by auto

        have q1: "IsQuorum (joinVotes t n) (lastCommittedConfiguration s n)"
          by (intro IsQuorum_mono [OF hyp3] electionWon termBound joinVotes_increasing joinVotes_finite)
        have q2: "IsQuorum (joinVotes t n) (lastAcceptedConfiguration s n)"
          by (intro IsQuorum_mono [OF hyp4] electionWon termBound joinVotes_increasing joinVotes_finite)

        from q1 q2 have electionWon': "electionWon t n" by (simp add: HandleJoinRequest votes)

        from HandleJoinRequest have startedJoinSinceLastReboot: "startedJoinSinceLastReboot s nm" "startedJoinSinceLastReboot t nm" by simp_all

        from startedJoinSinceLastReboot electionWon' electionWon have tv_eq: "termVersion n t = termVersion n s"
          by (simp add: termVersion_def votes HandleJoinRequest)

        from prem show ?thesis by (simp add: HandleJoinRequest tv_eq, intro hyp1)
      qed
    next
      case (HandlePublishResponse_NoQuorum nf nm)
      show ?thesis 
      proof (cases "nm = n")
        case False with hyp1 [of n] prem show ?thesis
          by (auto simp add: HandlePublishResponse_NoQuorum termVersion_def)
      next
        case True

        have termVersion_simp: "termVersion n t = termVersion n s"
          unfolding termVersion_def HandlePublishResponse_NoQuorum by simp

        have "publishVotes t n = insert nf (publishVotes s n)" by (simp add: HandlePublishResponse_NoQuorum True)
        also have "... \<subseteq> source ` { mprs \<in> sentPublishResponses s. msgTermVersion mprs = termVersion n s }"
        proof (intro subsetI, elim insertE)
          fix nf' assume "nf' \<in> publishVotes s n"
          also from prem have "publishVotes s n \<subseteq> source ` { mprs \<in> sentPublishResponses s. msgTermVersion mprs = termVersion n s }"
            by (intro hyp1, simp add: HandlePublishResponse_NoQuorum)
          finally show "nf' \<in> ..." .
        next
          fix nf' assume "nf' = nf"
          with HandlePublishResponse_NoQuorum hyp6 show "nf' \<in> source ` { mprs \<in> sentPublishResponses s. msgTermVersion mprs = termVersion n s }"
            by (intro image_eqI [where x = "\<lparr>source = nf, dest = nm, term = currentTerm s nm, payload = PublishResponse \<lparr>prs_version = lastPublishedVersion s nm\<rparr>\<rparr>"],
                auto simp add: termVersion_def True msgTermVersion_def)
        qed
        also have "... = source ` { mprs \<in> sentPublishResponses t. msgTermVersion mprs = termVersion n t }"
          unfolding termVersion_def HandlePublishResponse_NoQuorum by simp
        finally show ?thesis .
      qed
    next
      case (HandlePublishResponse_Quorum nf nm)
      show ?thesis 
      proof (cases "nm = n")
        case False with hyp1 [of n] prem show ?thesis
          by (auto simp add: HandlePublishResponse_Quorum termVersion_def)
      next
        case True

        have termVersion_simp: "termVersion n t = termVersion n s"
          unfolding termVersion_def HandlePublishResponse_Quorum by simp

        have "publishVotes t n = insert nf (publishVotes s n)" by (simp add: HandlePublishResponse_Quorum True)
        also have "... \<subseteq> source ` { mprs \<in> sentPublishResponses s. msgTermVersion mprs = termVersion n s }"
        proof (intro subsetI, elim insertE)
          fix nf' assume "nf' \<in> publishVotes s n"
          also from prem have "publishVotes s n \<subseteq> source ` { mprs \<in> sentPublishResponses s. msgTermVersion mprs = termVersion n s }"
            by (intro hyp1, simp add: HandlePublishResponse_Quorum)
          finally show "nf' \<in> ..." .
        next
          fix nf' assume "nf' = nf"
          with HandlePublishResponse_Quorum hyp6 show "nf' \<in> source ` { mprs \<in> sentPublishResponses s. msgTermVersion mprs = termVersion n s }"
            by (intro image_eqI [where x = "\<lparr>source = nf, dest = nm, term = currentTerm s nm, payload = PublishResponse \<lparr>prs_version = lastPublishedVersion s nm\<rparr>\<rparr>"],
                auto simp add: termVersion_def True msgTermVersion_def)
        qed
        also have "... = source ` { mprs \<in> sentPublishResponses t. msgTermVersion mprs = termVersion n t }"
          unfolding termVersion_def HandlePublishResponse_Quorum by simp
        finally show ?thesis .
      qed
    qed (auto simp add: termVersion_def)
  }
  thus ?thesis unfolding PublishVotesAreResponsesBelow_def by auto
qed

lemma FinitePublishResponses_step:
  assumes "s \<Turnstile> FinitePublishResponses"
  shows "(s,t) \<Turnstile> FinitePublishResponses$"
  using Next assms
  unfolding FinitePublishResponses_def
  by (cases rule: square_Next_cases, auto)

lemma CommitMeansQuorumBelow_step:
  assumes "s \<Turnstile> CommitMeansQuorumBelow termBound"
  assumes "s \<Turnstile> FinitePublishResponses"
  assumes "s \<Turnstile> PublishVotesAreResponsesBelow termBound"
  assumes "s \<Turnstile> PublishResponseMeansPublishRequest"
  assumes "s \<Turnstile> ElectionWonImpliesStartedJoin"
  assumes "s \<Turnstile> LastPublishedVersionImpliesLastPublishedConfigurationBelow termBound"
  assumes "s \<Turnstile> LastPublishedVersionImpliesLastCommittedConfigurationBelow termBound"
  shows "(s,t) \<Turnstile> CommitMeansQuorumBelow termBound$"
proof -
  from assms
  have   hyp1: "\<And>mc. \<lbrakk> mc \<in> sentCommits s; term mc < termBound \<rbrakk> \<Longrightarrow> \<exists> mprq \<in> sentPublishRequests s.
      msgTermVersion mprq = msgTermVersion mc
    \<and> IsQuorum (source ` { mprs \<in> sentPublishResponses s. msgTermVersion mprs = msgTermVersion mc }) (config mprq)
    \<and> IsQuorum (source ` { mprs \<in> sentPublishResponses s. msgTermVersion mprs = msgTermVersion mc }) (commConf mprq)"
    and hyp2: "finite (sentPublishResponses s)"
    and hyp3: "\<And>n. currentTerm s n < termBound \<Longrightarrow> publishVotes s n \<subseteq> source ` {mprs \<in> sentPublishResponses s. msgTermVersion mprs = termVersion n s}"
    and hyp4: "\<And>mprs. mprs \<in> sentPublishResponses s \<Longrightarrow> \<exists>mprq\<in>sentPublishRequests s. msgTermVersion mprs = msgTermVersion mprq \<and> dest mprs = source mprq"
    and hyp5: "\<And>n. electionWon s n \<Longrightarrow> startedJoinSinceLastReboot s n"
    and hyp6: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound; term m = currentTerm s (source m); electionWon s (source m); version m = lastPublishedVersion s (source m) \<rbrakk> \<Longrightarrow> config m = lastPublishedConfiguration s (source m)"
    and hyp7: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound; term m = currentTerm s (source m); electionWon s (source m); version m = lastPublishedVersion s (source m); msgTermVersion m \<notin> msgTermVersion ` sentCommits s \<rbrakk> \<Longrightarrow> commConf m = lastCommittedConfiguration s (source m)"
    unfolding CommitMeansQuorumBelow_def FinitePublishResponses_def PublishVotesAreResponsesBelow_def
      PublishResponseMeansPublishRequest_def ElectionWonImpliesStartedJoin_def
      LastPublishedVersionImpliesLastPublishedConfigurationBelow_def
      LastPublishedVersionImpliesLastCommittedConfigurationBelow_def
    by auto

  {
    fix mc
    assume prem: "mc \<in> sentCommits t" "term mc < termBound"

    have "\<exists> mprq \<in> sentPublishRequests t.
      msgTermVersion mprq = msgTermVersion mc
    \<and> IsQuorum (source ` { mprs \<in> sentPublishResponses t. msgTermVersion mprs = msgTermVersion mc }) (config mprq)
    \<and> IsQuorum (source ` { mprs \<in> sentPublishResponses t. msgTermVersion mprs = msgTermVersion mc }) (commConf mprq)"
    proof (cases "msgTermVersion mc \<in> msgTermVersion ` sentCommits s")
      case True
      then obtain mc' where mc': "msgTermVersion mc = msgTermVersion mc'" "mc' \<in> sentCommits s" by auto

      from mc' prem have "term mc' < termBound" by (auto simp add: msgTermVersion_def)

      with prem hyp1 mc'
      obtain mprq where mprq: "mprq \<in> sentPublishRequests s"
        and tv: "msgTermVersion mprq = msgTermVersion mc"
        and q1: "IsQuorum (source ` { mprs \<in> sentPublishResponses s. msgTermVersion mprs = msgTermVersion mc }) (config mprq)"
        and q2: "IsQuorum (source ` { mprs \<in> sentPublishResponses s. msgTermVersion mprs = msgTermVersion mc }) (commConf mprq)"
        by auto

      have IsQuorum_step: "\<And>cf. IsQuorum (source ` {mprs \<in> sentPublishResponses s. msgTermVersion mprs = msgTermVersion mc}) cf
             \<Longrightarrow> IsQuorum (source ` {mprs \<in> sentPublishResponses t. msgTermVersion mprs = msgTermVersion mc}) cf"
      proof (rule IsQuorum_mono [OF _ image_mono finite_imageI])
        from sentPublishResponses_increasing show "{mprs \<in> sentPublishResponses s. msgTermVersion mprs = msgTermVersion mc} \<subseteq> {mprs \<in> sentPublishResponses t. msgTermVersion mprs = msgTermVersion mc}" by auto
        from Next hyp2 show "finite {mprs \<in> sentPublishResponses t. msgTermVersion mprs = msgTermVersion mc}" by (cases rule: square_Next_cases, auto)
      qed

      show ?thesis
      proof (intro bexI [where x = mprq] conjI tv IsQuorum_step q1 q2)
        from mprq sentPublishRequests_increasing show "mprq \<in> sentPublishRequests t" by auto
      qed
    next
      case isUncommitted: False
      from Next hyp1 prem isUncommitted
      show ?thesis
      proof (cases rule: square_Next_cases)
        case (HandlePublishResponse_Quorum nf nm)

        from isUncommitted have isNewCommit: "mc \<notin> sentCommits s" by auto

        from prem isNewCommit
        obtain nd where mc_eq: "mc = \<lparr>source = nm, dest = nd, term = currentTerm s nm, payload = Commit \<lparr>c_version = lastPublishedVersion s nm\<rparr>\<rparr>"
          unfolding HandlePublishResponse_Quorum
          by auto

        from HandlePublishResponse_Quorum 
        have "\<lparr>source = nf, dest = nm, term = currentTerm s nm, payload = PublishResponse \<lparr>prs_version = lastPublishedVersion s nm\<rparr>\<rparr> \<in> sentPublishResponses s" by simp
        from hyp4 [OF this] obtain mprq where mprq: "mprq \<in> sentPublishRequests s" "term mprq = currentTerm s nm" "version mprq = lastPublishedVersion s nm" "nm = source mprq"
          by (auto simp add: msgTermVersion_def)

        have tv_eq: "msgTermVersion mc = termVersion nm s"
          using hyp5 HandlePublishResponse_Quorum
          by (auto simp add: msgTermVersion_def termVersion_def mc_eq)

        have IsQuorum_step: "\<And>cf. IsQuorum (publishVotes t nm) cf
             \<Longrightarrow> IsQuorum (source ` {mprs \<in> sentPublishResponses t. msgTermVersion mprs = msgTermVersion mc}) cf"
        proof (rule IsQuorum_mono [OF _ _ finite_imageI])
          have "publishVotes t nm = insert nf (publishVotes s nm)" by (simp add: HandlePublishResponse_Quorum)
          also have "... \<subseteq> source ` {mprs \<in> sentPublishResponses t. msgTermVersion mprs = msgTermVersion mc}"
            unfolding HandlePublishResponse_Quorum tv_eq
          proof (intro insert_subsetI hyp3)
            from prem show "currentTerm s nm < termBound" by (simp add: mc_eq)
            from HandlePublishResponse_Quorum 
            have "\<lparr>source = nf, dest = nm, term = currentTerm s nm, payload = PublishResponse \<lparr>prs_version = lastPublishedVersion s nm\<rparr>\<rparr> \<in> sentPublishResponses s" by simp
            thus "nf \<in> source ` {mprs \<in> sentPublishResponses s. msgTermVersion mprs = termVersion nm s}"
              using hyp5 HandlePublishResponse_Quorum
              by (intro image_eqI [where x = "\<lparr>source = nf, dest = nm, term = currentTerm s nm, payload = PublishResponse \<lparr>prs_version = lastPublishedVersion s nm\<rparr>\<rparr>"], auto simp add: msgTermVersion_def termVersion_def)
          qed
          finally show "publishVotes t nm \<subseteq> ..." .
          from Next hyp2 show "finite {mprs \<in> sentPublishResponses t. msgTermVersion mprs = msgTermVersion mc}" by (cases rule: square_Next_cases, auto)
        qed

        show ?thesis
        proof (intro bexI conjI IsQuorum_step)
          from mprq sentPublishRequests_increasing show "mprq \<in> sentPublishRequests t" by auto
          show "msgTermVersion mprq = msgTermVersion mc" by (simp add: mprq msgTermVersion_def mc_eq)

          from mprq have nm_source: "nm = source mprq" by simp

          from mprq have config_prems: "mprq \<in> sentPublishRequests s" "term mprq < termBound"
            "term mprq = currentTerm s (source mprq)" "electionWon s (source mprq)"
            "version mprq = lastPublishedVersion s (source mprq)"
          proof -
            from HandlePublishResponse_Quorum
            show "term mprq = currentTerm s (source mprq)" "version mprq = lastPublishedVersion s (source mprq)"
              by (auto simp add: msgTermVersion_def termVersion_def mprq)
            from prem mprq show "term mprq < termBound" by (simp add: mc_eq)
            from HandlePublishResponse_Quorum show "electionWon s (source mprq)" by (simp add: nm_source)
          qed

          have config_eq: "config mprq = lastPublishedConfiguration s nm"
            unfolding nm_source by (intro hyp6 config_prems)

          from config_eq HandlePublishResponse_Quorum
          show IsQuorum1: "IsQuorum (publishVotes t nm) (config mprq)" 
            unfolding nm_source by simp

          have commConfig_eq: "commConf mprq = lastCommittedConfiguration s nm"
            unfolding nm_source
          proof (intro hyp7 config_prems)
            have "msgTermVersion mprq = msgTermVersion mc"
              by (auto simp add: mc_eq msgTermVersion_def mprq)
            with isUncommitted
            show "msgTermVersion mprq \<notin> msgTermVersion ` sentCommits s" by simp
          qed

          from config_eq commConfig_eq HandlePublishResponse_Quorum
          show "IsQuorum (publishVotes t nm) (commConf mprq)" by simp_all
        qed
      qed auto
    qed
  }
  thus ?thesis by (auto simp add: CommitMeansQuorumBelow_def)
qed

lemma JoinTermNewerThanLastAccepted_step:
  assumes "s \<Turnstile> JoinTermNewerThanLastAccepted"
  assumes "s \<Turnstile> LastAcceptedTermInPast"
  shows "(s,t) \<Turnstile> JoinTermNewerThanLastAccepted$"
proof -
  from assms
  have  hyp1: "\<And>mj. mj \<in> sentJoins s \<Longrightarrow> laTerm mj < term mj"
    and hyp2: "\<And>n. lastAcceptedTerm s n \<le> currentTerm s n"
    unfolding JoinTermNewerThanLastAccepted_def LastAcceptedTermInPast_def
    by metis+

  {
    fix mj
    assume prem: "mj \<in> sentJoins t"
    from Next hyp1 prem
    have "laTerm mj < term mj"
    proof (cases rule: square_Next_cases)
      case (HandleStartJoin nf nm tm newJoinRequest)
      from HandleStartJoin prem have "mj \<in> sentJoins s \<or> mj = newJoinRequest" by auto
      with prem hyp1 show ?thesis
      proof (elim disjE)
        assume mj: "mj = newJoinRequest"
        with HandleStartJoin have "laTerm mj = lastAcceptedTerm s nf" by simp
        also have "... \<le> currentTerm s nf" by (intro hyp2)
        also have "... < term mj" by (simp add: mj HandleStartJoin)
        finally show ?thesis .
      qed metis
    qed auto
  }
  thus ?thesis by (auto simp add: JoinTermNewerThanLastAccepted_def)
qed

lemma JoinLimitsPublishResponses_step:
  assumes "s \<Turnstile> JoinLimitsPublishResponses"
  assumes "s \<Turnstile> PublishResponseBeforeLastAccepted"
  assumes "s \<Turnstile> JoinRequestsAtMostCurrentTerm"
  shows "(s,t) \<Turnstile> JoinLimitsPublishResponses$"
proof -
  from assms
  have  hyp1: "\<And>mj mprs. \<lbrakk> mj \<in> sentJoins s; mprs \<in> sentPublishResponses s; source mj = source mprs; term mprs < term mj \<rbrakk> \<Longrightarrow> msgTermVersion mprs \<le> TermVersion (laTerm mj) (laVersion mj)"
    and hyp2: "\<And>m. m \<in> sentPublishResponses s \<Longrightarrow> msgTermVersion m \<le> laTermVersion s (source m)"
    and hyp3: "\<And>m. \<lbrakk> m \<in> sentJoins s \<rbrakk> \<Longrightarrow> term m \<le> currentTerm s (source m)"
    unfolding JoinLimitsPublishResponses_def PublishResponseBeforeLastAccepted_def
      JoinRequestsAtMostCurrentTerm_def
    by metis+

  {
    fix mj mprs
    assume prem: "mj \<in> sentJoins t" "mprs \<in> sentPublishResponses t" "source mj = source mprs" "term mprs < term mj"
    from Next hyp1 prem
    have "msgTermVersion mprs \<le> TermVersion (laTerm mj) (laVersion mj)"
    proof (cases rule: square_Next_cases)
      case (HandleStartJoin nf nm tm newJoinRequest)
      from prem have mprs: "mprs \<in> sentPublishResponses s" by (auto simp add: HandleStartJoin)
      from HandleStartJoin prem have "mj \<in> sentJoins s \<or> mj = newJoinRequest" by auto
      with mprs prem hyp1 show ?thesis
      proof (elim disjE)
        have "msgTermVersion mprs \<le> laTermVersion s (source mprs)" by (intro hyp2 mprs prem)
        also assume "mj = newJoinRequest"
        with HandleStartJoin prem
        have "laTermVersion s (source mprs) = TermVersion (laTerm mj) (laVersion mj)"
          by (auto simp add: laTermVersion_def)
        finally show ?thesis .
      qed metis
    next
      case (HandlePublishRequest nf nm newVersion newValue newConfig commConfig)
      from prem have mj: "mj \<in> sentJoins s" by (auto simp add: HandlePublishRequest)
      from HandlePublishRequest prem have "mprs \<in> sentPublishResponses s \<or> mprs = \<lparr>source = nf, dest = nm, term = currentTerm s nf, payload = PublishResponse \<lparr>prs_version = newVersion\<rparr>\<rparr>" by auto
      with mj prem hyp1 show ?thesis
      proof (elim disjE)
        assume mprs: "mprs = \<lparr>source = nf, dest = nm, term = currentTerm s nf, payload = PublishResponse \<lparr>prs_version = newVersion\<rparr>\<rparr>"
        from mj prem have "term mj \<le> currentTerm s (source mj)" by (intro hyp3, simp_all)
        also have "... = currentTerm s (source mprs)" by (simp add: prem)
        also have "... = term mprs" by (simp add: mprs)
        also from prem have "... < term mj" by simp
        finally show ?thesis by simp
      qed metis
    qed auto
  }
  thus ?thesis by (auto simp add: JoinLimitsPublishResponses_def)
qed

lemma FiniteJoins_step:
  assumes "s \<Turnstile> FiniteJoins"
  shows "(s,t) \<Turnstile> FiniteJoins$"
proof -
  from assms
  have  hyp1: "finite (sentJoins s)"
    unfolding FiniteJoins_def
    by metis+

  from Next hyp1 have "finite (sentJoins t)"
    by (cases rule: square_Next_cases, simp_all)
  thus ?thesis by (simp add: FiniteJoins_def)
qed

lemma FiniteTermVersions_step:
  assumes "s \<Turnstile> FiniteTermVersions"
  shows "(s,t) \<Turnstile> FiniteTermVersions$"
proof -
  from assms
  have  hyp1: "finite (msgTermVersion ` messages s)"
    unfolding FiniteTermVersions_def
    by metis+

  from Next hyp1
  have "finite (msgTermVersion ` messages t)"
  proof (cases rule: square_Next_cases)
    case (ClientRequest nm v vs newPublishVersion newPublishRequests newEntry matchingElems newTransitiveElems)
    have "msgTermVersion ` messages t \<subseteq> insert (TermVersion (currentTerm s nm) newPublishVersion) (msgTermVersion ` messages s)"
      unfolding ClientRequest by (auto simp add: msgTermVersion_def)
    with hyp1 show ?thesis by (meson finite.insertI finite_subset)
  next
    case (HandlePublishResponse_Quorum nf nm)
    have "msgTermVersion ` messages t \<subseteq> insert (TermVersion (currentTerm s nm) (lastPublishedVersion s nm)) (msgTermVersion ` messages s)"
      unfolding HandlePublishResponse_Quorum by (auto simp add: msgTermVersion_def)
    with hyp1 show ?thesis by (meson finite.insertI finite_subset)
  qed auto
  thus ?thesis by (auto simp add: FiniteTermVersions_def)
qed

lemma termWinningConfiguration_fixed:
  assumes termWon:   "tm \<in> fst ` leaderHistory s"
  assumes termBound: "tm < termBound"
  assumes "t \<Turnstile> OneMasterPerTermBelow termBound" (* DANGER needs OneMasterPerTermBelow first *)
  assumes "s \<Turnstile> FiniteTermVersions"
  assumes "s \<Turnstile> PublishResponseMeansPublishRequest"
  assumes "s \<Turnstile> PublishRequestVersionAtMostSenderBelow termBound"
  assumes "s \<Turnstile> PublishRequestSentByMasterBelow termBound"
  assumes "s \<Turnstile> ElectionWonImpliesStartedJoin"
  assumes "s \<Turnstile> LeaderHistoryBounded"
  assumes "s \<Turnstile> MessagePositiveTerm"
  shows "termWinningConfiguration tm t = termWinningConfiguration tm s"
proof -

  from assms
  have  hyp1: "\<And>n1 n2 tm. \<lbrakk> tm < termBound; (tm, n1) \<in> leaderHistory t; (tm, n2) \<in> leaderHistory t \<rbrakk> \<Longrightarrow> n1 = n2"
    and hyp2: "finite (msgTermVersion ` messages s)"
    and hyp3: "\<And>mprs. mprs \<in> sentPublishResponses s \<Longrightarrow> \<exists>mprq\<in>sentPublishRequests s. msgTermVersion mprs = msgTermVersion mprq \<and> dest mprs = source mprq"
    and hyp4: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound \<rbrakk> \<Longrightarrow> msgTermVersion m \<le> termVersion (source m) s"
    and hyp5: "\<And>m n. \<lbrakk> m \<in> sentPublishRequests s; term m = currentTerm s n; term m < termBound; electionWon s n \<rbrakk> \<Longrightarrow> n = source m"
    and hyp6: "\<And>n. electionWon s n \<Longrightarrow> startedJoinSinceLastReboot s n"
    and hyp7: "\<And>n tm. (tm, n) \<in> leaderHistory s \<Longrightarrow> tm \<le> currentTerm s n"
    and hyp8: "\<And>m. m \<in> messages s \<Longrightarrow> 0 < term m"
    unfolding OneMasterPerTermBelow_def FiniteTermVersions_def PublishResponseMeansPublishRequest_def
      PublishRequestVersionAtMostSenderBelow_def PublishRequestSentByMasterBelow_def
      ElectionWonImpliesStartedJoin_def LeaderHistoryBounded_def MessagePositiveTerm_def
    by metis+

  from Next show ?thesis
  proof (cases rule: square_Next_cases)
    case unchanged
    thus ?thesis by (auto simp add: termWinningConfiguration_def lastAcceptedTermVersionBelow_def publishResponsesBelow_def Let_def)
  next
    case (HandleStartJoin nf nm tm' newJoinRequest)
    hence simps: "leaderHistory t = leaderHistory s"
      "initialConfiguration t = initialConfiguration s"
      "sentPublishRequests t = sentPublishRequests s"
      "\<And>n. publishResponsesBelow n tm t = publishResponsesBelow n tm s"
      by (auto simp add: publishResponsesBelow_def)
    show ?thesis unfolding termWinningConfiguration_def lastAcceptedTermVersionBelow_def simps by simp
  next
    case (HandleJoinRequest nf nm laTerm_m laVersion_m)
    have "\<And>n. ((tm, n) \<in> leaderHistory t) = ((tm, n) \<in> leaderHistory s)"
    proof (intro iffI)
      fix n
      show "(tm, n) \<in> leaderHistory s \<Longrightarrow> (tm, n) \<in> leaderHistory t" by (auto simp add: HandleJoinRequest)
      assume n: "(tm, n) \<in> leaderHistory t"
      from termWon obtain n' where n'_s: "(tm, n') \<in> leaderHistory s" by auto
      hence n': "(tm, n') \<in> leaderHistory t" by (auto simp add: HandleJoinRequest)
      have "n' = n" by (intro hyp1 [where tm = tm] termBound n n')
      with n'_s show "(tm, n) \<in> leaderHistory s" by simp
    qed
    with HandleJoinRequest show ?thesis by (auto simp add: termWinningConfiguration_def lastAcceptedTermVersionBelow_def publishResponsesBelow_def Let_def)
  next
    case (HandlePublishResponse_NoQuorum nf nm)
    thus ?thesis by (auto simp add: termWinningConfiguration_def publishResponsesBelow_def lastAcceptedTermVersionBelow_def Let_def)
  next
    case (HandlePublishResponse_Quorum nf nm)
    hence simps: "leaderHistory t = leaderHistory s"
      "initialConfiguration t = initialConfiguration s"
      "sentPublishRequests t = sentPublishRequests s"
      "\<And>n. publishResponsesBelow n tm t = publishResponsesBelow n tm s"
      by (auto simp add: publishResponsesBelow_def)
    show ?thesis unfolding termWinningConfiguration_def lastAcceptedTermVersionBelow_def simps by simp
  next
    case (HandleCommitRequest nf nm)
    thus ?thesis by (auto simp add: termWinningConfiguration_def publishResponsesBelow_def lastAcceptedTermVersionBelow_def Let_def)
  next
    case (RestartNode nr)
    thus ?thesis by (auto simp add: termWinningConfiguration_def publishResponsesBelow_def lastAcceptedTermVersionBelow_def Let_def)
  next
    case (ClientRequest nm v vs newPublishVersion newPublishRequests newEntry matchingElems newTransitiveElems)
    hence simps: "leaderHistory t = leaderHistory s"
      "initialConfiguration t = initialConfiguration s"
      "\<And>n. publishResponsesBelow n tm t = publishResponsesBelow n tm s"
      by (auto simp add: publishResponsesBelow_def)

    define n where "n \<equiv> SOME n. (tm, n) \<in> leaderHistory s"
    define publishResponses where "publishResponses \<equiv> publishResponsesBelow n tm s"
    define tv where "tv \<equiv> Max (msgTermVersion ` publishResponses)"
    define mprq_s where "mprq_s \<equiv> SOME mprq. mprq \<in> sentPublishRequests s \<and> msgTermVersion mprq = tv"
    define mprq_t where "mprq_t \<equiv> SOME mprq. mprq \<in> sentPublishRequests t \<and> msgTermVersion mprq = tv"

    show ?thesis
    proof (cases "publishResponses = {}")
      case True thus ?thesis by (simp add: termWinningConfiguration_def Let_def n_def publishResponses_def lastAcceptedTermVersionBelow_def simps)
    next
      case havePublishResponse: False

      have mprq_eq: "mprq_t = mprq_s"
        unfolding mprq_s_def mprq_t_def
      proof (intro cong [OF refl, where f = Eps] ext iffI)
        fix mprq
        show "mprq \<in> sentPublishRequests s \<and> msgTermVersion mprq = tv \<Longrightarrow> mprq \<in> sentPublishRequests t \<and> msgTermVersion mprq = tv"
          by (auto simp add: ClientRequest)
        assume "mprq \<in> sentPublishRequests t \<and> msgTermVersion mprq = tv"
        hence disj: "mprq \<in> sentPublishRequests s \<or> mprq \<in> newPublishRequests" and mprq: "tv = msgTermVersion mprq" by (auto simp add: ClientRequest)
        from disj show "mprq \<in> sentPublishRequests s \<and> msgTermVersion mprq = tv"
        proof (elim disjE)
          assume "mprq \<in> sentPublishRequests s" with mprq show ?thesis by simp
        next
          assume "mprq \<in> newPublishRequests"
          hence msgTermVersion_mprq: "msgTermVersion mprq = TermVersion (currentTerm s nm) (Suc (lastAcceptedVersion s nm))"
            by (auto simp add: ClientRequest msgTermVersion_def)

          have tv: "tv \<in> msgTermVersion ` publishResponses" and tv_max: "\<And>tv'. tv' \<in> msgTermVersion ` publishResponses \<Longrightarrow> tv' \<le> tv"
          proof -
            have fin: "finite (msgTermVersion ` publishResponses)"
              by (intro finite_subset [OF image_mono, OF _ hyp2], auto simp add: publishResponses_def publishResponsesBelow_def sentPublishResponses_def)
            from fin havePublishResponse show "tv \<in> msgTermVersion ` publishResponses" unfolding tv_def by (intro Max_in, auto)
            fix tv' assume "tv' \<in> msgTermVersion ` publishResponses"
            with fin show "tv' \<le> tv" unfolding tv_def by (intro Max_ge, auto)
          qed

          then obtain mprs where mprs: "mprs \<in> publishResponses" "tv = msgTermVersion mprs" by auto
          hence mprs_properties: "mprs \<in> sentPublishResponses s" "source mprs = n" "term mprs < tm"
            unfolding publishResponses_def publishResponsesBelow_def by auto

          have "msgTermVersion mprs = TermVersion (currentTerm s nm) (Suc (lastAcceptedVersion s nm))"
            using mprq mprs msgTermVersion_mprq by simp

          with hyp3 [of mprs] mprs_properties
          obtain mprq' where mprq': "mprq' \<in> sentPublishRequests s"
            "term mprq' = currentTerm s nm" "version mprq' = Suc (lastPublishedVersion s nm)"
            "msgTermVersion mprq' = TermVersion (currentTerm s nm) (Suc (lastAcceptedVersion s nm))"
            by (auto simp add: msgTermVersion_def ClientRequest)

          from mprq' msgTermVersion_mprq have "msgTermVersion mprq' = msgTermVersion mprq" by simp
          also from mprq mprs have "... = msgTermVersion mprs" by simp
          finally have term_mprq'_termBound: "term mprq' < termBound"
            using mprs_properties termBound by (auto simp add: msgTermVersion_def)

          from mprq' term_mprq'_termBound
          have msgTermVersion_mprq'_le: "msgTermVersion mprq' \<le> termVersion (source mprq') s" by (intro hyp4)

          from mprq' term_mprq'_termBound ClientRequest
          have nm_source: "nm = source mprq'" by (intro hyp5)

          from mprq'
          have "TermVersion (currentTerm s nm) (Suc (lastPublishedVersion s nm)) = msgTermVersion mprq'"
            by (simp add: ClientRequest)
          also note msgTermVersion_mprq'_le
          also from nm_source have "termVersion (source mprq') s = termVersion nm s" by simp
          also from ClientRequest hyp6 have "... = TermVersion (currentTerm s nm) (lastPublishedVersion s nm)"
            by (simp add: termVersion_def)
          finally show ?thesis by (simp add: less_eq_TermVersion_def)
        qed
      qed

      have max_not_zero: "Max (msgTermVersion ` publishResponses) \<noteq> TermVersion 0 0"
      proof (intro notI)
        assume "Max (msgTermVersion ` publishResponses) = TermVersion 0 0"
        moreover have "Max (msgTermVersion ` publishResponses) \<in> msgTermVersion ` publishResponses"
        proof (intro Max_in finite_subset [OF _ hyp2] image_mono)
          from havePublishResponse show "msgTermVersion ` publishResponses \<noteq> {}" by simp
          show "publishResponses \<subseteq> messages s"
            by (auto simp add: publishResponses_def publishResponsesBelow_def sentPublishResponses_def)
        qed
        ultimately obtain mprs' where "mprs' \<in> publishResponses" "msgTermVersion mprs' = TermVersion 0 0" by auto
        hence "mprs' \<in> messages s" "term mprs' = 0" by (auto simp add: msgTermVersion_def publishResponses_def publishResponsesBelow_def sentPublishResponses_def)
        with hyp8 [of mprs'] show False by simp
      qed

      from havePublishResponse max_not_zero have
        "termWinningConfiguration tm s = config mprq_s"
        "termWinningConfiguration tm t = config mprq_t"
        unfolding termWinningConfiguration_def simps lastAcceptedTermVersionBelow_def
        by (simp_all add: Let_def mprq_t_def mprq_s_def tv_def publishResponses_def n_def)
      thus ?thesis by (simp add: mprq_eq)
    qed
  next
    case (HandlePublishRequest nf nm newVersion newValue newConfig commConfig)
    hence simps: "leaderHistory t = leaderHistory s"
      "initialConfiguration t = initialConfiguration s"
      "sentPublishRequests t = sentPublishRequests s" by auto

    define n where "n \<equiv> SOME n. (tm, n) \<in> leaderHistory s"

    have "publishResponsesBelow n tm t = publishResponsesBelow n tm s"
    proof (intro equalityI subsetI)
      fix mprs
      assume "mprs \<in> publishResponsesBelow n tm s" thus "mprs \<in> publishResponsesBelow n tm t"
        by (auto simp add: publishResponsesBelow_def HandlePublishRequest)
    next
      fix mprs
      assume "mprs \<in> publishResponsesBelow n tm t"
      hence disj: "mprs \<in> sentPublishResponses s \<or> mprs = \<lparr>source = nf, dest = nm, term = currentTerm s nf, payload = PublishResponse \<lparr>prs_version = newVersion\<rparr>\<rparr>"
        and mprs: "source mprs = n" "term mprs < tm"
        by (auto simp add: publishResponsesBelow_def HandlePublishRequest)
      from disj show "mprs \<in> publishResponsesBelow n tm s"
      proof (elim disjE)
        assume "mprs \<in> sentPublishResponses s" with mprs show ?thesis by (auto simp add: publishResponsesBelow_def)
      next
        assume mprs_eq: "mprs = \<lparr>source = nf, dest = nm, term = currentTerm s nf, payload = PublishResponse \<lparr>prs_version = newVersion\<rparr>\<rparr>"
        with mprs have "currentTerm s n < tm" by simp
        also from termWon have "tm \<le> currentTerm s n"
          by (intro hyp7, unfold n_def, auto, meson someI_ex)
        finally show ?thesis by simp
      qed
    qed

    thus ?thesis
      unfolding termWinningConfiguration_def simps Let_def n_def lastAcceptedTermVersionBelow_def by simp
  qed
qed

lemma TermWinningConfigurationHasQuorumBelow_step:
  assumes "s \<Turnstile> TermWinningConfigurationHasQuorumBelow termBound"
  assumes "t \<Turnstile> OneMasterPerTermBelow termBound" (* DANGER needs OneMasterPerTermBelow first *)
  assumes "s \<Turnstile> FiniteTermVersions"
  assumes "s \<Turnstile> PublishResponseMeansPublishRequest"
  assumes "s \<Turnstile> PublishRequestVersionAtMostSenderBelow termBound"
  assumes "s \<Turnstile> PublishRequestSentByMasterBelow termBound"
  assumes "s \<Turnstile> ElectionWonImpliesStartedJoin"
  assumes "s \<Turnstile> LeaderHistoryBounded"
  assumes "s \<Turnstile> LeaderHistoryFaithful"
  assumes "s \<Turnstile> JoinVotesFaithful"
  assumes "s \<Turnstile> FiniteJoins"
  assumes "s \<Turnstile> LastAcceptedDataSource"
  assumes "s \<Turnstile> MessagePositiveTerm"
  assumes "s \<Turnstile> PublishResponseBeforeLastAccepted"
  assumes "s \<Turnstile> PublishResponseForLastAccepted"
  assumes "s \<Turnstile> PublishRequestsUniquePerTermVersionBelow termBound"
  assumes "s \<Turnstile> LastAcceptedTermInPast"
  assumes "s \<Turnstile> EndOfTermIsPermanentBelow termBound"
  assumes "s \<Turnstile> PublishRequestFromHistoricalLeader"
  assumes "s \<Turnstile> MessagePositiveTerm"
  shows "(s,t) \<Turnstile> TermWinningConfigurationHasQuorumBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>tm n. \<lbrakk> tm < termBound; (tm, n) \<in> leaderHistory s \<rbrakk>
    \<Longrightarrow> IsQuorum (source ` {j \<in> sentJoins s. dest j = n \<and> term j = tm \<and> TermVersion (laTerm j) (laVersion j) \<le> lastAcceptedTermVersionBelow n tm s }) (termWinningConfiguration tm s)"
    unfolding TermWinningConfigurationHasQuorumBelow_def
    by auto

  from assms 
  have  hyp2: "\<And>n1 n2 tm. \<lbrakk> tm < termBound; (tm, n1) \<in> leaderHistory t; (tm, n2) \<in> leaderHistory t \<rbrakk> \<Longrightarrow> n1 = n2"
    and hyp3: "finite (msgTermVersion ` messages s)"
    and hyp4: "\<And>mprs. mprs \<in> sentPublishResponses s \<Longrightarrow> \<exists>mprq\<in>sentPublishRequests s. msgTermVersion mprs = msgTermVersion mprq \<and> dest mprs = source mprq"
    and hyp5: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound \<rbrakk> \<Longrightarrow> msgTermVersion m \<le> termVersion (source m) s"
    and hyp6: "\<And>m n. \<lbrakk> m \<in> sentPublishRequests s; term m = currentTerm s n; term m < termBound; electionWon s n \<rbrakk> \<Longrightarrow> n = source m"
    and hyp7: "\<And>n. electionWon s n \<Longrightarrow> startedJoinSinceLastReboot s n"
    and hyp8: "\<And>n tm. (tm, n) \<in> leaderHistory s \<Longrightarrow> tm \<le> currentTerm s n"
    and hyp9: "\<And>n. electionWon s n \<Longrightarrow> (currentTerm s n, n) \<in> leaderHistory s"
    and hyp10: "\<And>nm nf. nf \<in> joinVotes s nm \<Longrightarrow> \<exists>joinPayload. \<lparr>source = nf, dest = nm, term = currentTerm s nm, payload = Join joinPayload\<rparr> \<in> sentJoins s \<and> TermVersion (jp_laTerm joinPayload) (jp_laVersion joinPayload) \<le> laTermVersion s nm"
    and hyp11: "finite (sentJoins s)"
    and hyp12: "\<And>n. if lastAcceptedTerm s n = 0 then lastAcceptedVersion s n = 0 \<and> lastAcceptedValue s n = initialValue s \<and> lastAcceptedConfiguration s n = initialConfiguration s
        else \<exists>m\<in>sentPublishRequests s. lastAcceptedTerm s n = term m \<and> lastAcceptedVersion s n = version m \<and> lastAcceptedValue s n = value m \<and> lastAcceptedConfiguration s n = config m"
    and hyp13: "\<And>m. m \<in> messages s \<Longrightarrow> 0 < term m"
    and hyp14: "\<And>m. m \<in> sentPublishResponses s \<Longrightarrow> msgTermVersion m \<le> laTermVersion s (source m)"
    and hyp15: "\<And>n. 0 < lastAcceptedTerm s n \<Longrightarrow> \<exists>m\<in>sentPublishResponses s. source m = n \<and> msgTermVersion m = laTermVersion s n"
    and hyp16: "\<And>m1 m2. \<lbrakk> m1 \<in> sentPublishRequests s; m2 \<in> sentPublishRequests s; term m1 < termBound; term m1 = term m2; version m1 = version m2 \<rbrakk> \<Longrightarrow> payload m1 = payload m2"
    and hyp17: "\<And>n. lastAcceptedTerm s n \<le> currentTerm s n"
    and hyp18: "\<And>n. \<lbrakk> (currentTerm s n, n) \<in> leaderHistory s; currentTerm s n < termBound; startedJoinSinceLastReboot s n \<rbrakk> \<Longrightarrow> electionWon s n"
    and hyp19: "\<And>m. m \<in> sentPublishRequests s \<Longrightarrow> (term m, source m) \<in> leaderHistory s"
    and hyp20: "\<And>m. m \<in> messages s \<Longrightarrow> 0 < term m"
    unfolding PublishRequestsUniquePerTermVersionBelow_def LastAcceptedTermInPast_def EndOfTermIsPermanentBelow_def
      PublishRequestFromHistoricalLeader_def OneMasterPerTermBelow_def FiniteTermVersions_def PublishResponseMeansPublishRequest_def
      PublishRequestVersionAtMostSenderBelow_def PublishRequestSentByMasterBelow_def
      ElectionWonImpliesStartedJoin_def LeaderHistoryBounded_def 
      LeaderHistoryFaithful_def JoinVotesFaithful_def FiniteJoins_def LastAcceptedDataSource_def
      MessagePositiveTerm_def PublishResponseBeforeLastAccepted_def PublishResponseForLastAccepted_def
      MessagePositiveTerm_def
    by metis+

  {
    fix tm n
    assume prem: "tm < termBound" "(tm, n) \<in> leaderHistory t"

    {
      assume leaderHistory_eq: "leaderHistory t = leaderHistory s"
      have "publishResponsesBelow n tm t = publishResponsesBelow n tm s"
        "lastAcceptedTermVersionBelow n tm t = lastAcceptedTermVersionBelow n tm s"
        "termWinningConfiguration tm t = termWinningConfiguration tm s"
      proof -
        from leaderHistory_eq prem have "tm \<in> fst ` leaderHistory s" by (auto simp add: rev_image_eqI)
        with prem show "termWinningConfiguration tm t = termWinningConfiguration tm s"
          by (intro termWinningConfiguration_fixed [where termBound = termBound] assms, auto)

        from Next
        show publishResponsesBelow_eq: "publishResponsesBelow n tm t = publishResponsesBelow n tm s"
        proof (cases rule: square_Next_cases)
          case (HandlePublishRequest nf nm newVersion newValue newConfig commConfig)
          show ?thesis
          proof (intro subsetI equalityI)
            fix mprq assume "mprq \<in> publishResponsesBelow n tm s"
            with HandlePublishRequest show "mprq \<in> publishResponsesBelow n tm t" by (auto simp add: publishResponsesBelow_def)
          next
            fix mprq assume "mprq \<in> publishResponsesBelow n tm t"

            with HandlePublishRequest have mprq: "term mprq < tm" "source mprq = n"
              and disj: "mprq \<in> sentPublishResponses s \<or> mprq = \<lparr>source = nf, dest = nm, term = currentTerm s nf, payload = PublishResponse \<lparr>prs_version = newVersion\<rparr>\<rparr>"
              by (auto simp add: publishResponsesBelow_def)
            from disj show "mprq \<in> publishResponsesBelow n tm s"
            proof (elim disjE)
              assume "mprq \<in> sentPublishResponses s" with mprq show ?thesis by (auto simp add: publishResponsesBelow_def)
            next
              assume "mprq = \<lparr>source = nf, dest = nm, term = currentTerm s nf, payload = PublishResponse \<lparr>prs_version = newVersion\<rparr>\<rparr>"
              with mprq have "currentTerm s n < tm" by simp
              also from prem have "tm \<le> currentTerm s n" by (intro hyp8, simp add: leaderHistory_eq)
              finally show ?thesis by simp
            qed
          qed
        qed (auto simp add: publishResponsesBelow_def)
        thus lastAcceptedTermVersionBelow_eq: "lastAcceptedTermVersionBelow n tm t = lastAcceptedTermVersionBelow n tm s"
          by (simp add: lastAcceptedTermVersionBelow_def)

      qed
    }
    note termWinningConfiguration[simp] = this

    from Next hyp1 prem have "IsQuorum (source ` {j \<in> sentJoins t. dest j = n \<and> term j = tm \<and> TermVersion (laTerm j) (laVersion j) \<le> lastAcceptedTermVersionBelow n tm t}) (termWinningConfiguration tm t)"
    proof (cases rule: square_Next_cases)
      case (HandleStartJoin nf nm tm' newJoinRequest)
      hence simps1: "leaderHistory t = leaderHistory s" "termWinningConfiguration tm t = termWinningConfiguration tm s" by simp_all
      show ?thesis
      proof (cases "newJoinRequest \<in> {j \<in> sentJoins t. dest j = n \<and> term j = tm \<and> TermVersion (laTerm j) (laVersion j) \<le> lastAcceptedTermVersionBelow n tm t}")
        case False
        hence simps2: "{j \<in> sentJoins t. dest j = n \<and> term j = tm \<and> TermVersion (laTerm j) (laVersion j) \<le> lastAcceptedTermVersionBelow n tm t} = {j \<in> sentJoins s. dest j = n \<and> term j = tm \<and> TermVersion (laTerm j) (laVersion j) \<le> lastAcceptedTermVersionBelow n tm s}"
          by (auto simp add: HandleStartJoin)
        from prem show ?thesis unfolding simps1 simps2 by (intro hyp1, simp_all)
      next
        case True
        hence simps2: "{j \<in> sentJoins t. dest j = n \<and> term j = tm \<and> TermVersion (laTerm j) (laVersion j) \<le> lastAcceptedTermVersionBelow n tm t} = insert newJoinRequest {j \<in> sentJoins s. dest j = n \<and> term j = tm \<and> TermVersion (laTerm j) (laVersion j) \<le> lastAcceptedTermVersionBelow n tm s}"
          by (auto simp add: HandleStartJoin)
        from prem show ?thesis unfolding simps1 simps2 image_insert by (intro IsQuorum_insert hyp1, simp_all)
      qed
    next
      case (HandleJoinRequest nf nm laTerm_m laVersion_m)

      have lastAcceptedTermVersionBelow_eq: "lastAcceptedTermVersionBelow n tm t = lastAcceptedTermVersionBelow n tm s"
        by (simp add: lastAcceptedTermVersionBelow_def Let_def publishResponsesBelow_def HandleJoinRequest)

      have publishResponsesBelow_eq: "publishResponsesBelow nm tm t = publishResponsesBelow nm tm s"
        by (auto simp add: publishResponsesBelow_def HandleJoinRequest)

      have simp1: "{j \<in> sentJoins t. dest j = n \<and> term j = tm \<and> TermVersion (laTerm j) (laVersion j) \<le> lastAcceptedTermVersionBelow n tm t} = {j \<in> sentJoins s. dest j = n \<and> term j = tm \<and> TermVersion (laTerm j) (laVersion j) \<le> lastAcceptedTermVersionBelow n tm s}"
        by (auto simp add: HandleJoinRequest lastAcceptedTermVersionBelow_eq)

      from HandleJoinRequest
      have "leaderHistory t = (if electionWon t nm then insert (currentTerm s nm, nm) (leaderHistory s) else leaderHistory s)" by simp
      with prem hyp9 consider (old) "(tm, n) \<in> leaderHistory s" | (new) "tm = currentTerm s nm" "nm = n" "electionWon t nm" "\<not> electionWon s nm"
        by (cases "electionWon t nm", auto)

      thus ?thesis
      proof cases
        case old
        hence simp2: "termWinningConfiguration tm t = termWinningConfiguration tm s"
          by (intro termWinningConfiguration_fixed [where termBound = termBound] assms prem, auto simp add: rev_image_eqI)
        show ?thesis unfolding simp1 simp2 by (intro hyp1 prem old)
      next
        case new

        from new have IsQuorum: "IsQuorum (joinVotes t nm) (lastAcceptedConfiguration s nm)"
          by (auto simp add: HandleJoinRequest)

        have termWinningConfiguration_eq: "termWinningConfiguration tm t = lastAcceptedConfiguration s nm"
        proof -
          have leader_simp: "(SOME n. (tm, n) \<in> leaderHistory t) = nm"
          proof (intro hyp2 [where tm = tm] prem)
            from new show "(tm, nm) \<in> leaderHistory t" by (auto simp add: HandleJoinRequest)
            thus "(tm, SOME n. (tm, n) \<in> leaderHistory t) \<in> leaderHistory t" by (intro someI)
          qed

          show ?thesis
          proof (cases "lastAcceptedTerm s nm = 0")
            case True
            with hyp12 [of nm] have "lastAcceptedConfiguration s nm = initialConfiguration s" by simp

            moreover have "publishResponsesBelow nm tm t = {}"
            proof (rule ccontr)
              assume "\<not>?thesis"
              then obtain mprs where mprs: "mprs \<in> sentPublishResponses s" "source mprs = nm" "term mprs < tm"
                unfolding publishResponsesBelow_def HandleJoinRequest by auto

              from mprs have mprs_positive: "0 < term mprs" by (intro hyp13, simp add: sentPublishResponses_def)
              from mprs have "msgTermVersion mprs \<le> laTermVersion s (source mprs)" by (intro hyp14)
              with mprs_positive True show False by (auto simp add: laTermVersion_def msgTermVersion_def mprs less_eq_TermVersion_def)
            qed

            ultimately show ?thesis unfolding termWinningConfiguration_def Let_def lastAcceptedTermVersionBelow_def leader_simp by (simp add: HandleJoinRequest)
          next
            case False
            hence positive: "0 < lastAcceptedTerm s nm" by simp
            from hyp15 [OF positive]
            obtain mprs where mprs: "mprs \<in> sentPublishResponses s" "source mprs = nm" "msgTermVersion mprs = laTermVersion s nm" by auto

            from mprs hyp4 [of mprs]
            obtain mprq where mprq: "mprq \<in> sentPublishRequests s" "term mprs = term mprq" "version mprs = version mprq" "msgTermVersion mprq = laTermVersion s nm"
              by (auto simp add: msgTermVersion_def)

            define mprq' where "mprq' \<equiv> SOME mprq. mprq \<in> sentPublishRequests t \<and> msgTermVersion mprq = lastAcceptedTermVersionBelow nm tm s"
            have mprq'_fold: "(SOME mprq. mprq \<in> sentPublishRequests t \<and> msgTermVersion mprq = lastAcceptedTermVersionBelow nm tm s) = mprq'"
              by (simp add: mprq'_def)

            from hyp12 [of nm] False 
            obtain mprq'' where mprq'': "mprq'' \<in> sentPublishRequests s" "lastAcceptedTerm s nm = term mprq''"
              "lastAcceptedVersion s nm = version mprq''" "lastAcceptedValue s nm = value mprq''" "lastAcceptedConfiguration s nm = config mprq''"
              by auto

            have payload_eq'': "payload mprq'' = payload mprq"
            proof (intro hyp16 mprq mprq'')
              from mprq mprq'' show "version mprq'' = version mprq" "term mprq'' = term mprq" by (auto simp add: msgTermVersion_def laTermVersion_def)
              from mprq'' have "term mprq'' = lastAcceptedTerm s nm" by simp
              also have "... \<le> currentTerm s nm" by (intro hyp17)
              also from new have "... = tm" by simp
              also from prem have "... < termBound" by simp
              finally show "term mprq'' < termBound" .
            qed

            have mprq_publishResponsesBelow: "mprs \<in> publishResponsesBelow nm tm t"
              unfolding publishResponsesBelow_def
            proof (intro CollectI conjI)
              from mprs show "mprs \<in> sentPublishResponses t" "source mprs = nm" by (simp_all add: HandleJoinRequest)
              show "term mprs < tm"
              proof (cases "term mprs = currentTerm s nm")
                case False
                from mprs have "term mprs = lastAcceptedTerm s nm" by (simp add: laTermVersion_def msgTermVersion_def)
                also have "... \<le> currentTerm s nm" by (intro hyp17)
                finally have "term mprs \<le> currentTerm s nm" .
                with False new show ?thesis by auto
              next
                case True
                have "electionWon s nm"
                proof (intro hyp18)
                  from HandleJoinRequest show "startedJoinSinceLastReboot s nm" by simp
                  from prem new show "currentTerm s nm < termBound" by simp

                  from mprq have "(term mprq, source mprq) \<in> leaderHistory s" by (intro hyp19)
                  with mprq True have 1: "(currentTerm s nm, source mprq) \<in> leaderHistory s" by simp

                  from 1 new have "source mprq = nm"
                    by (intro hyp2 [where tm = tm] prem, simp_all add: HandleJoinRequest)
                  with 1 show "(currentTerm s nm, nm) \<in> leaderHistory s" by simp
                qed
                with new show ?thesis by simp
              qed
            qed

            hence havePublishResponse: "(publishResponsesBelow nm tm t = {}) = False" by auto

            have termVersion_mprs: "msgTermVersion mprs = Max (msgTermVersion ` publishResponsesBelow nm tm t)"
            proof (intro order_antisym Max_ge)
              show 1: "finite (msgTermVersion ` publishResponsesBelow nm tm t)"
                by (intro finite_subset [OF _ hyp3] image_mono, auto simp add: publishResponsesBelow_def HandleJoinRequest sentPublishResponses_def)
              from mprq_publishResponsesBelow
              show "msgTermVersion mprs \<in> msgTermVersion ` publishResponsesBelow nm tm t" by simp

              from havePublishResponse
              have "Max (msgTermVersion ` publishResponsesBelow nm tm t) \<in> msgTermVersion ` publishResponsesBelow nm tm t"
                by (intro Max_in 1, auto)
              then obtain mprs' where mprs': "mprs' \<in> sentPublishResponses s" "source mprs' = nm"
                "term mprs' < tm" "msgTermVersion mprs' = Max (msgTermVersion ` publishResponsesBelow nm tm t)"
                by (auto simp add: HandleJoinRequest publishResponsesBelow_def)

              have "Max (msgTermVersion ` publishResponsesBelow nm tm t) = msgTermVersion mprs'" by (simp add: mprs')
              also have "... \<le> laTermVersion s (source mprs')" by (intro hyp14 mprs')
              also have "... = msgTermVersion mprs" by (simp add: mprs mprs')
              finally show "Max (msgTermVersion ` publishResponsesBelow nm tm t) \<le> msgTermVersion mprs" .
            qed

            with mprq have termVersion_mprq: "msgTermVersion mprq = Max (msgTermVersion ` publishResponsesBelow nm tm t)"
              by (simp add: msgTermVersion_def)

            have mprq': "mprq' \<in> sentPublishRequests t \<and> msgTermVersion mprq' = lastAcceptedTermVersionBelow nm tm s"
              unfolding mprq'_def
            proof (intro someI conjI)
              from mprq show "mprq \<in> sentPublishRequests t" by (auto simp add: HandleJoinRequest)
              from termVersion_mprq havePublishResponse
              show "msgTermVersion mprq = lastAcceptedTermVersionBelow nm tm s"
                by (simp add: lastAcceptedTermVersionBelow_def Let_def publishResponsesBelow_eq)
            qed

            have payload_eq': "payload mprq' = payload mprq"
            proof (intro hyp16)
              from mprq  show "mprq  \<in> sentPublishRequests s" by simp
              from mprq' show "mprq' \<in> sentPublishRequests s" by (auto simp add: HandleJoinRequest)

              from termVersion_mprq havePublishResponse mprq' publishResponsesBelow_eq
              have msgTermVersion_eq: "msgTermVersion mprq' = msgTermVersion mprq"
                by (auto simp add: lastAcceptedTermVersionBelow_def)

              thus "term mprq' = term mprq" "version mprq' = version mprq" by (auto simp add: msgTermVersion_def)

              from msgTermVersion_eq have "term mprq' = term mprq" by (auto simp add: msgTermVersion_def)
              also from mprq have "... = term mprs" by simp
              also from mprq_publishResponsesBelow have "... < tm" by (auto simp add: publishResponsesBelow_def)
              also from prem have "tm < termBound" by simp
              finally show "term mprq' < termBound" .
            qed

            from payload_eq' payload_eq'' mprq'' have config_eq: "config mprq' = lastAcceptedConfiguration s nm" by (simp add: config_def)

            from lastAcceptedTermVersionBelow_eq new
            have lastAcceptedTermVersionBelow_eq2: "lastAcceptedTermVersionBelow nm tm t = lastAcceptedTermVersionBelow nm tm s" by simp

            have lastAcceptedTermVersionBelow_nonzero: "(lastAcceptedTermVersionBelow nm tm t = TermVersion 0 0) = False"
            proof (intro iffI)
              assume "lastAcceptedTermVersionBelow nm tm t = TermVersion 0 0"
              hence "TermVersion 0 0 = Max (msgTermVersion ` publishResponsesBelow nm tm t)"
                unfolding lastAcceptedTermVersionBelow_def havePublishResponse Let_def if_False by simp
              also from havePublishResponse have "... \<in> msgTermVersion ` publishResponsesBelow nm tm t"
                by (intro Max_in finite_subset [OF _ hyp3] image_mono, auto simp add: publishResponsesBelow_eq, auto simp add: publishResponsesBelow_def sentPublishResponses_def)
              finally obtain mprs' where mrps': "mprs' \<in> messages s" "term mprs' = 0"
                by (auto simp add: publishResponsesBelow_def HandleJoinRequest msgTermVersion_def sentPublishResponses_def)
              with hyp20 [of mprs'] show False by simp
            qed simp

            show ?thesis
              unfolding termWinningConfiguration_def Let_def leader_simp lastAcceptedTermVersionBelow_nonzero if_False
              unfolding mprq'_fold lastAcceptedTermVersionBelow_eq2 config_eq by simp
          qed
        qed

        have laTermVersion_eq: "lastAcceptedTermVersionBelow n tm s = laTermVersion s nm"
        proof (intro order_antisym)
          show "lastAcceptedTermVersionBelow n tm s \<le> laTermVersion s nm"
          proof (cases "publishResponsesBelow n tm s = {}")
            case True thus ?thesis by (cases "laTermVersion s nm", auto simp add: lastAcceptedTermVersionBelow_def less_eq_TermVersion_def)
          next
            case False 

            from False have "lastAcceptedTermVersionBelow n tm s = Max (msgTermVersion ` publishResponsesBelow n tm s)"
              by (auto simp add: lastAcceptedTermVersionBelow_def)
            also from False have "... \<in> msgTermVersion ` publishResponsesBelow n tm s"
              by (intro Max_in finite_subset [OF _ hyp3] image_mono, auto simp add: publishResponsesBelow_def sentPublishResponses_def)
            finally obtain mprs where mprs: "mprs \<in> publishResponsesBelow n tm s" "lastAcceptedTermVersionBelow n tm s = msgTermVersion mprs" by auto

            from mprs have "msgTermVersion mprs \<le> laTermVersion s (source mprs)"
              by (intro hyp14, auto simp add: publishResponsesBelow_def)
            with mprs show ?thesis by (auto simp add: publishResponsesBelow_def new)
          qed

          show "laTermVersion s nm \<le> lastAcceptedTermVersionBelow n tm s"
          proof (cases "lastAcceptedTerm s nm = 0")
            case True with hyp12 [of nm] show ?thesis
              by (cases "lastAcceptedTermVersionBelow n tm s", auto simp add: laTermVersion_def less_eq_TermVersion_def)
          next
            case False
            with hyp15 [of nm]
            obtain mprs where mprs: "mprs \<in> sentPublishResponses s" "source mprs = nm" "msgTermVersion mprs = laTermVersion s nm" by auto

            have "lastAcceptedTerm s nm < currentTerm s nm"
            proof (cases "lastAcceptedTerm s nm = currentTerm s nm")
              case False with hyp17 [of nm] show ?thesis by auto
            next
              case True
              with mprs hyp4 [of mprs]
              obtain mprq where mprq: "mprq \<in> sentPublishRequests s" "term mprq = currentTerm s nm" by (auto simp add: msgTermVersion_def laTermVersion_def)

              have "electionWon s nm"
              proof (intro hyp18 HandleJoinRequest)
                from prem new show currentTerm_termBound: "currentTerm s nm < termBound" by simp

                have term_mprq_history: "(term mprq, source mprq) \<in> leaderHistory s" by (intro hyp19 mprq)

                have "source mprq = nm"
                proof (intro hyp2 [OF currentTerm_termBound])
                  from term_mprq_history show "(currentTerm s nm, source mprq) \<in> leaderHistory t" by (simp add: mprq HandleJoinRequest)
                  from HandleJoinRequest new show "(currentTerm s nm, nm) \<in> leaderHistory t" by auto
                qed
                with term_mprq_history mprq show "(currentTerm s nm, nm) \<in> leaderHistory s" by simp
              qed
              with new show ?thesis by simp
            qed

            with mprs have mprs_publishResponsesBelow: "mprs \<in> publishResponsesBelow n tm s"
              by (auto simp add: publishResponsesBelow_def new laTermVersion_def msgTermVersion_def)

            hence eq_Max: "lastAcceptedTermVersionBelow n tm s = Max (msgTermVersion ` publishResponsesBelow n tm s)"
              by (auto simp add: lastAcceptedTermVersionBelow_def Let_def)

            from mprs have laTermVersion_eq: "laTermVersion s nm = msgTermVersion mprs" by simp

            show ?thesis unfolding eq_Max laTermVersion_eq
              by (intro Max_ge finite_subset [OF _ hyp3] image_mono imageI mprs_publishResponsesBelow, auto simp add: publishResponsesBelow_def sentPublishResponses_def)
          qed
        qed

        from HandleJoinRequest
        have j_laTermVersion_max: "TermVersion laTerm_m laVersion_m \<le> laTermVersion s nm"
          by (auto simp add: laTermVersion_def less_eq_TermVersion_def)

        show ?thesis
          unfolding termWinningConfiguration_eq HandleJoinRequest
        proof (intro IsQuorum_mono [OF IsQuorum] finite_imageI finite_subset [OF _ hyp11] subsetI)
          show "\<And>m. m \<in> {j \<in> sentJoins s. dest j = n \<and> term j = tm \<and> TermVersion (laTerm j) (laVersion j) \<le> lastAcceptedTermVersionBelow n tm t} \<Longrightarrow> m \<in> sentJoins s"
            by (auto simp add: HandleJoinRequest)
          fix nv assume "nv \<in> joinVotes t nm" hence "nv = nf \<or> nv \<in> joinVotes s nm" by (simp add: HandleJoinRequest)
          thus "nv \<in> source ` {j \<in> sentJoins s. dest j = n \<and> term j = tm \<and> TermVersion (laTerm j) (laVersion j) \<le> lastAcceptedTermVersionBelow n tm t}"
          proof (elim disjE)
            assume "nv = nf"
            thus ?thesis
            proof (intro image_eqI)
              from HandleJoinRequest new j_laTermVersion_max laTermVersion_eq lastAcceptedTermVersionBelow_eq
              show "\<lparr>source = nf, dest = nm, term = currentTerm s nm, payload = Join \<lparr>jp_laTerm = laTerm_m, jp_laVersion = laVersion_m\<rparr>\<rparr>
                            \<in> {j \<in> sentJoins s. dest j = n \<and> term j = tm \<and> TermVersion (laTerm j) (laVersion j) \<le> lastAcceptedTermVersionBelow n tm t}"
                by auto
            qed simp
          next
            assume "nv \<in> joinVotes s nm"
            from hyp10 [OF this]
            obtain joinPayload
              where join_sent: "\<lparr>source = nv, dest = nm, term = currentTerm s nm, payload = Join joinPayload\<rparr> \<in> sentJoins s"
                and join_termVersion: "TermVersion (jp_laTerm joinPayload) (jp_laVersion joinPayload) \<le> laTermVersion s nm" by auto

            with new laTermVersion_eq lastAcceptedTermVersionBelow_eq show ?thesis
              by (intro image_eqI [where x = "\<lparr>source = nv, dest = nm, term = currentTerm s nm, payload = Join joinPayload\<rparr>"], auto simp add: laTerm_def laVersion_def)
          qed
        qed
      qed
    qed auto
  }
  thus ?thesis by (auto simp add: TermWinningConfigurationHasQuorumBelow_def)
qed

lemma PublishResponseBeforeLastAccepted_step:
  assumes "s \<Turnstile> PublishResponseBeforeLastAccepted"
  assumes "s \<Turnstile> LastAcceptedTermInPast"
  shows "(s,t) \<Turnstile> PublishResponseBeforeLastAccepted$"
proof -
  from assms
  have  hyp1: "\<And>m. m \<in> sentPublishResponses s \<Longrightarrow> msgTermVersion m \<le> laTermVersion s (source m)"
    and hyp2: "\<And>n. lastAcceptedTerm s n \<le> currentTerm s n"
    unfolding PublishResponseBeforeLastAccepted_def LastAcceptedTermInPast_def
    by metis+

  {
    fix m assume prem: "m \<in> sentPublishResponses t"
    from Next hyp1 prem have "msgTermVersion m \<le> laTermVersion t (source m)"
    proof (cases rule: square_Next_cases)
      case (HandlePublishRequest nf nm newVersion newValue newConfig commConfig)
      from prem have "m = \<lparr>source = nf, dest = nm, term = currentTerm s nf, payload = PublishResponse \<lparr>prs_version = newVersion\<rparr>\<rparr> \<or> m \<in> sentPublishResponses s" by (auto simp add: HandlePublishRequest)
      thus ?thesis
      proof (elim disjE)
        assume "m \<in> sentPublishResponses s"
        with HandlePublishRequest hyp1 prem have "msgTermVersion m \<le> laTermVersion s (source m)" by simp
        also from HandlePublishRequest hyp2 [of "source m"] have "... \<le> laTermVersion t (source m)"
          by (auto simp add: laTermVersion_def less_eq_TermVersion_def)
        finally show ?thesis by simp
      next
        assume m: "m = \<lparr>source = nf, dest = nm, term = currentTerm s nf, payload = PublishResponse \<lparr>prs_version = newVersion\<rparr>\<rparr>"
        hence "msgTermVersion m = TermVersion (currentTerm s (source m)) newVersion" by (simp add: msgTermVersion_def)
        also have "... \<le> laTermVersion t (source m)" by (simp add: laTermVersion_def HandlePublishRequest m)
        finally show ?thesis by simp
      qed
    qed (auto simp add: laTermVersion_def)
  }
  thus ?thesis by (auto simp add: PublishResponseBeforeLastAccepted_def)
qed

lemma PublishResponseForLastAccepted_step:
  assumes "s \<Turnstile> PublishResponseForLastAccepted"
  shows "(s,t) \<Turnstile> PublishResponseForLastAccepted$"
proof -
  from assms
  have hyp1: "\<And>n. 0 < lastAcceptedTerm s n \<Longrightarrow> \<exists> m \<in> sentPublishResponses s. source m = n \<and> msgTermVersion m = laTermVersion s n"
    unfolding PublishResponseForLastAccepted_def
    by metis+

  {
    fix n
    assume prem: "0 < lastAcceptedTerm t n"
    from Next hyp1 prem have "\<exists> m \<in> sentPublishResponses t. source m = n \<and> msgTermVersion m = laTermVersion t n"
    proof (cases rule: square_Next_cases)
      case (ClientRequest nm v vs newPublishVersion newPublishRequests newEntry matchingElems newTransitiveElems)
      with hyp1 prem have "\<exists> m \<in> sentPublishResponses s. source m = n \<and> msgTermVersion m = laTermVersion s n" by auto
      thus ?thesis by (auto simp add: laTermVersion_def ClientRequest)
    next
      case (HandlePublishRequest nf nm newVersion newValue newConfig commConfig)
      show ?thesis
      proof (cases "n = nf")
        case False
        with HandlePublishRequest hyp1 prem show ?thesis by (auto simp add: laTermVersion_def)
      next
        case True
        show ?thesis
          by (intro bexI [where x = "\<lparr>source = nf, dest = nm, term = currentTerm s nf, payload = PublishResponse \<lparr>prs_version = newVersion\<rparr>\<rparr>"],
              auto simp add: True msgTermVersion_def laTermVersion_def HandlePublishRequest)
      qed
    qed (auto simp add: laTermVersion_def)
  }
  thus ?thesis by (auto simp add: PublishResponseForLastAccepted_def)
qed

lemma CommittedVersionsUniqueBelow_step:
  assumes "s \<Turnstile> CommittedVersionsUniqueBelow termBound"
  assumes "t \<Turnstile> CommitMeansLaterPublicationsBelow termBound" (* DANGER need to show CommitMeansLaterPublicationsBelow holds first *)
  assumes "s \<Turnstile> PublishResponseMeansPublishRequest"
  assumes "s \<Turnstile> CommitMeansPublishResponse"
  shows "(s,t) \<Turnstile> CommittedVersionsUniqueBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>mc1 mc2. \<lbrakk> mc1 \<in> sentCommits s; mc2 \<in> sentCommits s; term mc1 < termBound; term mc2 < termBound; version mc1 = version mc2 \<rbrakk> \<Longrightarrow> term mc1 = term mc2"
    and hyp2: "\<And>mc mp. \<lbrakk> mc \<in> sentCommits t; mp \<in> sentPublishRequests t; term mc < term mp; term mp < termBound \<rbrakk> \<Longrightarrow> version mc < version mp"
    and hyp3: "\<And>mprs. mprs \<in> sentPublishResponses s \<Longrightarrow> \<exists> mprq \<in> sentPublishRequests s. msgTermVersion mprs = msgTermVersion mprq \<and> dest mprs = source mprq"
    and hyp4: "\<And>mc. mc \<in> sentCommits s \<Longrightarrow> \<exists>mprs\<in>sentPublishResponses s. msgTermVersion mc = msgTermVersion mprs \<and> source mc = dest mprs"
    unfolding CommittedVersionsUniqueBelow_def CommitMeansLaterPublicationsBelow_def PublishResponseMeansPublishRequest_def
      CommitMeansPublishResponse_def
    by metis+

  from hyp1 have hyp1': "\<And>mc1 mc2. \<lbrakk> mc1 \<in> sentCommits s; mc2 \<in> sentCommits s; term mc1 < termBound; term mc2 < termBound; version mc1 = version mc2; term mc1 < term mc2 \<rbrakk> \<Longrightarrow> False"
    using nat_neq_iff by blast

  {
    fix mc1 mc2
    assume prem: "mc1 \<in> sentCommits t" "mc2 \<in> sentCommits t" "term mc1 < termBound" "term mc2 < termBound" "version mc1 = version mc2" "term mc1 < term mc2"
    from Next prem prem hyp1' have False
    proof (cases rule: square_Next_cases)
      case (HandlePublishResponse_Quorum nf nm)

      have messageE: "\<And>m P. m \<in> sentCommits t \<Longrightarrow> (m \<in> sentCommits s \<Longrightarrow> P) \<Longrightarrow> (\<And>nd. m = \<lparr>source = nm, dest = nd, term = currentTerm s nm, payload = Commit \<lparr>c_version = lastPublishedVersion s nm\<rparr>\<rparr> \<Longrightarrow> P) \<Longrightarrow> P"
        unfolding HandlePublishResponse_Quorum by auto

      from `mc2 \<in> sentCommits t` obtain mprs where mprs: "mprs \<in> sentPublishResponses s" "term mprs = term mc2" "version mprs = version mc2"
      proof (elim messageE)
        assume mc2: "mc2 \<in> sentCommits s"
        with prem have "\<exists>mprs\<in>sentPublishResponses s. msgTermVersion mc2 = msgTermVersion mprs \<and> source mc2 = dest mprs" by (intro hyp4, simp_all)
        thus thesis by (elim bexE, intro that, auto simp add: msgTermVersion_def)
      next
        fix nd2
        assume mc2: "mc2 = \<lparr>source = nm, dest = nd2, term = currentTerm s nm, payload = Commit \<lparr>c_version = lastPublishedVersion s nm\<rparr>\<rparr>"
        from HandlePublishResponse_Quorum show thesis
          by (intro that [of "\<lparr>source = nf, dest = nm, term = currentTerm s nm, payload = PublishResponse \<lparr>prs_version = lastPublishedVersion s nm\<rparr>\<rparr>"],
              auto simp add: mc2)
      qed

      hence "\<exists> mprq \<in> sentPublishRequests s. msgTermVersion mprs = msgTermVersion mprq \<and> dest mprs = source mprq"
        by (intro hyp3, simp_all)
      then obtain mprq where mprq: "mprq \<in> sentPublishRequests s" "term mprq = term mprs" "version mprq = version mprs"
        by (auto simp add: msgTermVersion_def)

      have "version mc1 < version mprq"
        by (intro hyp2 prem mprq, auto simp add: mprq mprs prem HandlePublishResponse_Quorum)
      also have "... = version mc1" by (simp add: mprq mprs prem)
      finally show ?thesis by simp
    qed auto
  }
  note not_lt = this
  {
    fix mc1 mc2 :: Message
    assume prem: "mc1 \<in> sentCommits t" "mc2 \<in> sentCommits t" "term mc1 < termBound" "term mc2 < termBound" "version mc1 = version mc2"
    consider (lt) "term mc1 < term mc2" | (eq) "term mc1 = term mc2" | (gt) "term mc2 < term mc1" using nat_neq_iff by blast
    hence "term mc1 = term mc2"
    proof cases
      case eq thus ?thesis by simp
    next
      case lt with prem have False by (intro not_lt [of mc1 mc2], simp_all)
      thus ?thesis by simp
    next
      case gt with prem have False by (intro not_lt [of mc2 mc1], simp_all)
      thus ?thesis by simp
    qed
  }
  thus ?thesis using nat_neq_iff by (auto simp add: CommittedVersionsUniqueBelow_def)
qed


lemma PublishResponseMeansPublishRequest_step:
  assumes "s \<Turnstile> PublishResponseMeansPublishRequest"
  shows "(s,t) \<Turnstile> PublishResponseMeansPublishRequest$"
proof -
  from assms
  have hyp1: "\<And>mprs. mprs \<in> sentPublishResponses s \<Longrightarrow> \<exists> mprq \<in> sentPublishRequests s. msgTermVersion mprs = msgTermVersion mprq \<and> dest mprs = source mprq"
    unfolding PublishResponseMeansPublishRequest_def
    by metis+

  {
    fix mprs
    assume prem: "mprs \<in> sentPublishResponses t"
    from Next prem hyp1 have "\<exists> mprq \<in> sentPublishRequests t. msgTermVersion mprs = msgTermVersion mprq \<and> dest mprs = source mprq"
    proof (cases rule: square_Next_cases)
      case (ClientRequest nm v vs newPublishVersion newPublishRequests newEntry matchingElems newTransitiveElems)
      with prem hyp1 
      have "\<exists> mprq \<in> sentPublishRequests s. msgTermVersion mprs = msgTermVersion mprq \<and> dest mprs = source mprq" by auto
      thus ?thesis by (auto simp add: ClientRequest)
    next
      case (HandlePublishResponse_Quorum nf nm)
      with prem hyp1 
      have "\<exists> mprq \<in> sentPublishRequests s. msgTermVersion mprs = msgTermVersion mprq \<and> dest mprs = source mprq" by auto
      thus ?thesis by (auto simp add: HandlePublishResponse_Quorum)
    next
      case (HandlePublishRequest nf nm newVersion newValue newConfig commConfig)
      let ?mprq = "\<lparr>source = nm, dest = nf, term = currentTerm s nf, payload = PublishRequest \<lparr>prq_version = newVersion, prq_value = newValue, prq_config = newConfig, prq_commConf = commConfig\<rparr>\<rparr>"
      from HandlePublishRequest have prq: "?mprq \<in> sentPublishRequests s" by simp

      with prem hyp1 show ?thesis
        unfolding HandlePublishRequest
        by (elim insertE, intro bexI [where x = "?mprq"], simp add: msgTermVersion_def)
    qed auto
  }
  thus ?thesis by (simp add: PublishResponseMeansPublishRequest_def)
qed

lemma CommitMeansPublishResponse_step:
  assumes "s \<Turnstile> CommitMeansPublishResponse"
  shows "(s,t) \<Turnstile> CommitMeansPublishResponse$"
proof -
  from assms
  have  hyp1: "\<And>mc. mc \<in> sentCommits s \<Longrightarrow> \<exists>mprs\<in>sentPublishResponses s. msgTermVersion mc = msgTermVersion mprs \<and> source mc = dest mprs"
    unfolding CommitMeansPublishResponse_def
    by metis+

  {
    fix mc
    assume prem: "mc \<in> sentCommits t"
    from Next prem hyp1 have "\<exists>mprs\<in>sentPublishResponses t. msgTermVersion mc = msgTermVersion mprs \<and> source mc = dest mprs"
    proof (cases rule: square_Next_cases)
      case (ClientRequest nm v vs newPublishVersion newPublishRequests newEntry matchingElems newTransitiveElems)
      from prem have "mc \<in> sentCommits s" by (auto simp add: ClientRequest)
      with hyp1 prem show ?thesis by (auto simp add: ClientRequest)
    next
      case (HandlePublishResponse_Quorum nf nm)
      let ?mprs = "\<lparr>source = nf, dest = nm, term = currentTerm s nm, payload = PublishResponse \<lparr>prs_version = lastPublishedVersion s nm\<rparr>\<rparr>"
      from HandlePublishResponse_Quorum have pr: "?mprs \<in> sentPublishResponses s" by simp
      from prem hyp1 have "\<exists>mprs\<in>sentPublishResponses s. msgTermVersion mc = msgTermVersion mprs \<and> source mc = dest mprs"
      proof (unfold HandlePublishResponse_Quorum, elim UnE UnionE rangeE, simp_all add: msgTermVersion_def)
        fix n
        from pr show "\<exists>mprs\<in>sentPublishResponses s. currentTerm s nm = term mprs \<and> lastPublishedVersion s nm = version mprs \<and> nm = dest mprs"
          by (intro bexI [where x = "?mprs"], auto)
      qed
      thus ?thesis by (auto simp add: HandlePublishResponse_Quorum)
    qed auto
  }
  thus ?thesis by (simp add: CommitMeansPublishResponse_def)
qed

lemma psubset_element_I: "\<And>x A B. \<lbrakk> A \<subseteq> B; x \<in> B; x \<notin> A \<rbrakk> \<Longrightarrow> A \<subset> B" by auto

lemma CommitMeansLaterPublicationsBelow_TODO:
  assumes "s \<Turnstile> TermWinningConfigurationHasQuorumBelow termBound"
  assumes "s \<Turnstile> PublishRequestFromHistoricalLeader"
  assumes "s \<Turnstile> CommitMeansQuorumBelow termBound"
  assumes "s \<Turnstile> OneMasterPerTermBelow termBound"
  assumes "s \<Turnstile> FiniteTermVersions"
  assumes "s \<Turnstile> CommitMeansPublishResponse"
  assumes "s \<Turnstile> PublishResponseMeansPublishRequest"
  shows "s \<Turnstile> CommitMeansLaterPublicationsBelow termBound"
proof -
  from assms
  have  hyp2: "\<And>tm n. \<lbrakk> tm < termBound; (tm, n) \<in> leaderHistory s \<rbrakk> \<Longrightarrow> IsQuorum (source ` {j \<in> sentJoins s. dest j = n \<and> term j = tm \<and> TermVersion (laTerm j) (laVersion j) \<le> lastAcceptedTermVersionBelow n tm s}) (termWinningConfiguration tm s)"
    and hyp3: "\<And>m. m \<in> sentPublishRequests s \<Longrightarrow> (term m, source m) \<in> leaderHistory s"
    and hyp4: "\<And>mc. \<lbrakk> mc \<in> sentCommits s; term mc < termBound \<rbrakk> \<Longrightarrow> \<exists>mprq\<in>sentPublishRequests s. msgTermVersion mprq = msgTermVersion mc \<and> IsQuorum (source ` {mprs \<in> sentPublishResponses s. msgTermVersion mprs = msgTermVersion mc}) (config mprq) \<and> IsQuorum (source ` {mprs \<in> sentPublishResponses s. msgTermVersion mprs = msgTermVersion mc}) (commConf mprq)"
    and hyp5: "\<And>n1 n2 tm. \<lbrakk> tm < termBound; (tm, n1) \<in> leaderHistory s; (tm, n2) \<in> leaderHistory s \<rbrakk> \<Longrightarrow> n1 = n2"
    and hyp6: "finite (msgTermVersion ` messages s)"
    and hyp7: "\<And>mc. mc\<in>sentCommits s \<Longrightarrow> \<exists>mprs\<in>sentPublishResponses s. msgTermVersion mc = msgTermVersion mprs \<and> source mc = dest mprs"
    and hyp8: "\<And>mprs. mprs \<in> sentPublishResponses s \<Longrightarrow> \<exists>mprq\<in>sentPublishRequests s. msgTermVersion mprs = msgTermVersion mprq \<and> dest mprs = source mprq"
    unfolding TermWinningConfigurationHasQuorumBelow_def PublishRequestFromHistoricalLeader_def CommitMeansQuorumBelow_def OneMasterPerTermBelow_def
      FiniteTermVersions_def CommitMeansPublishResponse_def PublishResponseMeansPublishRequest_def
    by auto

  have wf_termVersion: "wf {(tv1, tv2). tv1 < (tv2 :: TermVersion)}" (is "wf ?r")
  proof -
    have p: "?r \<subseteq> map_prod (%(t,v). TermVersion t v) (%(t,v). TermVersion t v) ` ({(t1,t2). t1 < t2} <*lex*> {(v1,v2). v1 < v2})"
      by (auto simp add: map_prod_def lex_prod_def image_def elim: less_TermVersion.elims)
    show ?thesis by (intro wf_subset [OF _ p] wf_map_prod_image wf_lex_prod wf_less, auto simp add: inj_def)
  qed

  {
    fix mc mprq
    assume prem: "mc \<in> sentCommits s" "mprq \<in> sentPublishRequests s" "term mc < term mprq" "term mprq < termBound"

    define inductor where "inductor = (msgTermVersion mprq, msgTermVersion ` {mc' \<in> sentCommits s. msgTermVersion mc < msgTermVersion mc' \<and> term mc' < term mprq})"
    from wf_lex_prod [OF wf_termVersion wf_finite_psubset] inductor_def prem have "version mc < version mprq"
    proof (induct inductor arbitrary: mc mprq rule: wf_induct_rule)
      case (less inductor)

      consider (notFirstInTerm) "\<exists> mprq' \<in> sentPublishRequests s. term mprq' = term mprq \<and> version mprq' < version mprq"
        | (laterCommit) "\<exists> mc' \<in> sentCommits s. msgTermVersion mc < msgTermVersion mc' \<and> term mc' < term mprq"
        | (hardCase) "\<not> (\<exists> mprq' \<in> sentPublishRequests s. term mprq' = term mprq \<and> version mprq' < version mprq)"
          "\<not> (\<exists> mc' \<in> sentCommits s. msgTermVersion mc < msgTermVersion mc' \<and> term mc' < term mprq)" by auto

      thus ?case
      proof cases
        case notFirstInTerm
        then obtain mprq' where mprq': "mprq' \<in> sentPublishRequests s" "term mprq' = term mprq" "version mprq' < version mprq" by auto
        have "version mc < version mprq'"
        proof (intro less mprq')
          from mprq' have "msgTermVersion mprq' < msgTermVersion mprq" by (simp add: msgTermVersion_def)

          with less
          show "((msgTermVersion mprq', msgTermVersion ` {mc' \<in> sentCommits s. msgTermVersion mc < msgTermVersion mc' \<and> term mc' < term mprq'}), inductor) \<in> {(tv1, tv2). tv1 < tv2} <*lex*> finite_psubset" by simp
          from less mprq' show "term mc < term mprq'" "term mprq' < termBound" by auto
        qed simp
        also from mprq' have "... < version mprq" by simp
        finally show ?thesis .
      next
        case laterCommit
        then obtain mc' where mc': "mc' \<in> sentCommits s" "msgTermVersion mc < msgTermVersion mc'" "term mc' < term mprq" by auto

        have "version mc < version mc'"
        proof (cases "term mc = term mc'")
          case True
          with mc' show ?thesis by (auto simp add: msgTermVersion_def)
        next
          case False

          from mc' hyp7 [of mc'] obtain mprs' where mprs': "mprs' \<in> sentPublishResponses s" "msgTermVersion mc' = msgTermVersion mprs'" by auto
          from this hyp8 [of mprs'] obtain mprq' where mprq': "mprq' \<in> sentPublishRequests s" "msgTermVersion mprs' = msgTermVersion mprq'" by auto

          have "version mc < version mprq'"
          proof (intro less(1) [OF _ refl] less mprq')
            from mc' False mprs' mprq' show "term mc < term mprq'" by (auto simp add: msgTermVersion_def)

            from mprq' mprs' have "term mprq' = term mc'" by (auto simp add: msgTermVersion_def)
            also from mc' have "... < term mprq" by simp
            finally have term_mprq'_mprq: "term mprq' < term mprq" .
            also from less have "... < termBound" by simp
            finally show "term mprq' < termBound" .

            show "((msgTermVersion mprq', msgTermVersion ` {mc' \<in> sentCommits s. msgTermVersion mc < msgTermVersion mc' \<and> term mc' < term mprq'}), inductor) \<in> {(tv1, tv2). tv1 < tv2} <*lex*> finite_psubset"
              unfolding less using term_mprq'_mprq by (auto simp add: msgTermVersion_def)
          qed
          also from mprs' mprq' have "... = version mc'" by (auto simp add: msgTermVersion_def)
          finally show ?thesis by simp
        qed

        also have "version mc' < version mprq"
        proof (intro less(1) [OF _ refl] less mc')
          from mc' show "((msgTermVersion mprq, msgTermVersion ` {mc'' \<in> sentCommits s. msgTermVersion mc' < msgTermVersion mc'' \<and> term mc'' < term mprq}), inductor) \<in> {(tv1, tv2). tv1 < tv2} <*lex*> finite_psubset"
            unfolding less in_lex_prod
            by (intro disjI2 conjI refl iffD2 [OF in_finite_psubset] psubset_element_I [where x = "msgTermVersion mc'"] image_mono imageI finite_subset [OF _ hyp6], auto simp add: sentCommits_def)
        qed

        finally show ?thesis .
      next
        case hardCase
          (* mprq is first publication in this term, and mc is the latest commit in any earlier term *)

        have leaderHistory: "(term mprq, source mprq) \<in> leaderHistory s" by (intro hyp3 less)

        have "IsQuorum (source ` {j \<in> sentJoins s. dest j = source mprq \<and> term j = term mprq \<and> TermVersion (laTerm j) (laVersion j) \<le> lastAcceptedTermVersionBelow (source mprq) (term mprq) s}) (termWinningConfiguration (term mprq) s)"
          by (intro hyp2 leaderHistory less)

        from `term mprq < termBound` leaderHistory
        have leader_simp: "(SOME n. (term mprq, n) \<in> leaderHistory s) = source mprq" by (intro some_equality less hyp5)

        note termWinningConfiguration_def [where tm = "term mprq" and s = s]

        from less have "mc \<in> sentCommits s" "term mc < termBound" by auto
        from hyp4 [OF this]
        obtain mprqc where mprqc: "mprqc \<in> sentPublishRequests s" "msgTermVersion mprqc = msgTermVersion mc"
          "IsQuorum (source ` {mprs \<in> sentPublishResponses s. msgTermVersion mprs = msgTermVersion mc}) (config mprqc)"
          "IsQuorum (source ` {mprs \<in> sentPublishResponses s. msgTermVersion mprs = msgTermVersion mc}) (commConf mprqc)" by auto

        show ?thesis sorry
      qed
    qed
  }
  thus ?thesis by (auto simp add: CommitMeansLaterPublicationsBelow_def)
qed

lemma CommitMeansLaterPublicationsBelow_step:
  assumes "s \<Turnstile> CommitMeansLaterPublicationsBelow termBound"
  assumes "s \<Turnstile> LastAcceptedDataSource"
  assumes "s \<Turnstile> LastAcceptedTermInPast"
  shows "(s,t) \<Turnstile> CommitMeansLaterPublicationsBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>mc mp. \<lbrakk> mc \<in> sentCommits s; mp \<in> sentPublishRequests s;
                         term mc < term mp; term mp < termBound \<rbrakk> \<Longrightarrow> version mc < version mp"
    and hyp2: "\<And>n. if lastAcceptedTerm s n = 0 then lastAcceptedVersion s n = 0 \<and> lastAcceptedValue s n = initialValue s \<and> lastAcceptedConfiguration s n = initialConfiguration s
        else \<exists>m\<in>sentPublishRequests s. lastAcceptedTerm s n = term m \<and> lastAcceptedVersion s n = version m \<and> lastAcceptedValue s n = value m \<and> lastAcceptedConfiguration s n = config m"
    and hyp3: "\<And>n. lastAcceptedTerm s n \<le> currentTerm s n"
    unfolding CommitMeansLaterPublicationsBelow_def LastAcceptedDataSource_def LastAcceptedTermInPast_def
    by metis+

  {
    fix mc mp
    assume prem: "mc \<in> sentCommits t" "mp \<in> sentPublishRequests t" "term mc < term mp" "term mp < termBound"
    from Next prem hyp1 have "version mc < version mp"
    proof (cases rule: square_Next_cases)
      case (ClientRequest nm v vs newPublishVersion newPublishRequests newEntry matchingElems newTransitiveElems)
      from prem have mc_messages: "mc \<in> sentCommits s" by (auto simp add: ClientRequest)
      from prem have "mp \<in> sentPublishRequests s \<or> mp \<in> newPublishRequests" by (auto simp add: ClientRequest)
      thus ?thesis
      proof (elim disjE)
        assume "mp \<in> sentPublishRequests s" with prem hyp1 show ?thesis by (auto simp add: ClientRequest)
      next
        assume mp: "mp \<in> newPublishRequests"
        hence mp_simps: "source mp = nm" "term mp = currentTerm s nm" "version mp = newPublishVersion" "newPublishVersion = Suc (lastAcceptedVersion s nm)" "config mp = vs" "commConf mp = lastCommittedConfiguration s nm"
          by (auto simp add: ClientRequest)

        consider (gt) "term mc < lastAcceptedTerm s nm"
          | (le) "lastAcceptedTerm s nm \<le> term mc"
          using leI by auto

        thus ?thesis
        proof cases
          case gt
          with hyp2 [of nm]
          obtain mp' where mp': "mp' \<in> sentPublishRequests s" "lastAcceptedTerm s nm = term mp'"
            "lastAcceptedVersion s nm = version mp'" "lastAcceptedValue s nm = value mp'" "lastAcceptedConfiguration s nm = config mp'"
            by auto
          have "version mc < version mp'"
          proof (intro hyp1 prem mp' mc_messages)
            from gt mp' show "term mc < term mp'" by simp
            have "term mp' = lastAcceptedTerm s nm" by (simp add: mp')
            also have "... \<le> currentTerm s nm" by (intro hyp3)
            also from mp have "... = term mp" by (simp add: mp_simps)
            also from prem have "... < termBound" by simp
            finally show "term mp' < termBound".
          qed
          also have "version mp' < version mp" using mp' mp_simps by simp
          finally show ?thesis by simp
        next
          case le (* lastAcceptedTerm s nm \<le> term mc < term mp = currentTerm s nm *)

          note termWinningConfiguration_def

(* idea: look at last-accepted term/version vs last-committed. last-committed _was_ committed, and last-accepted is \<ge>,
so must have \<ge> version: either == term (so \<ge> termversion \<Rightarrow> \<ge> version) or else > term (so induction) *)

(* if mc \<le> last-committed-on-nm then either equal term (hence versions OK) or lesser term (hence induction works) *)

(* if mc > last-committed-on-nm then ... nm couldn't have become master? why? *)




          show ?thesis sorry

(* making a new publish request in a brand-new term *)
(* 

 do know that IsQuorum (joinVotes s nm) vs and electionWon s nm
 and this \<longrightarrow> IsQuorum (joinVotes s nm) (lastCommittedConfiguration s nm)
         and  IsQuorum (joinVotes s nm) (lastAcceptedConfiguration  s nm)

Look at payloads of joinVotes. All have laTermVersion sender \<le> laTermVersion nm

Does this mean no commits can occur between laTermVersion nm and termVersion nm? All those joinVotes mean
the senders won't be voting for a PublishRequest P with termVersion P \<ge> laTermVersion and term P < term nm.
Also no publications in term nm yet, so nothing to vote for there, so all PublishResponses R either have
termVersion R \<le> laTermVersion nm or term R > term nm.

Any intervening commit would need to get a quorum of votes vs the last committed config.

Any intervening commit comes from a PublishRequest and therefore has a yet-higher version.
Therefore "wlog" may assume that mc is the TermVersion-last commit before mp.

Also have  (source ` { j \<in> sentJoins s. dest j = n \<and> term j = tm }) (termWinningConfiguration tm s)


*)
        qed
      qed
    next
      case (HandlePublishResponse_Quorum nf nm)
        (* making a new commit *)

(* know that IsQuorum (publishVotes t nm) (lastCommittedConfiguration s nm)
                 and IsQuorum (publishVotes t nm) (lastPublishedConfiguration s nm) 
                 and electionWon s nm
                 and this \<longrightarrow> lastAcceptedConfiguration s nm \<in> { lastCommittedConfiguration s nm, lastPublishedConfiguration s nm }
                  so IsQuorum (publishVotes t nm) (lastAcceptedConfiguration s nm) too *)

(* do we need lastAcceptedConfiguration? *)

      then show ?thesis sorry
    qed auto
  }
  thus ?thesis by (auto simp add: CommitMeansLaterPublicationsBelow_def)
qed



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
      from hyp have "finite (insert \<lparr>source = nm, dest = n, term = currentTerm s nm, payload = PublishRequest \<lparr>prq_version  = newPublishVersion, prq_value = v, prq_config = vs, prq_commConf = lastCommittedConfiguration s nm\<rparr> \<rparr> (messagesTo s n))" by simp
      moreover have "\<And>n. messagesTo t n \<subseteq> insert \<lparr>source = nm, dest = n, term = currentTerm s nm, payload = PublishRequest \<lparr>prq_version  = newPublishVersion, prq_value = v, prq_config = vs, prq_commConf = lastCommittedConfiguration s nm\<rparr> \<rparr> (messagesTo s n)"
        unfolding messagesTo_def ClientRequest by auto
      ultimately show "finite (messagesTo t n)" by (metis finite_subset)
    next
      case (HandlePublishRequest nf nm newVersion  newValue newConfig commConfig)
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
  from assms have hyp: "\<And>m. m \<in> sentJoins s \<Longrightarrow> term m \<le> currentTerm s (source m)"
    by (auto simp add: JoinRequestsAtMostCurrentTerm_def)
  {
    fix m
    assume prem: "m \<in> sentJoins t"

    from Next hyp prem have "term m \<le> currentTerm t (source m)"
    proof (cases rule: square_Next_cases)
      case (HandleStartJoin nf nm tm newJoinRequest)
      from prem have "m = newJoinRequest \<or> m \<in> sentJoins s" by (simp add: HandleStartJoin)
      thus ?thesis
      proof (elim disjE)
        assume "m \<in> sentJoins s"
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
  have prem: "\<And>m. m \<in> sentJoins s \<Longrightarrow> term m \<le> currentTerm s (source m)"
    and hyp: "\<And>m1 m2. m1 \<in> sentJoins s \<Longrightarrow> m2 \<in> sentJoins s \<Longrightarrow> source m1 = source m2 \<Longrightarrow> term m1 = term m2 \<Longrightarrow> m1 = m2"
    by (auto simp add: JoinRequestsAtMostCurrentTerm_def JoinRequestsUniquePerTerm_def)

  {
    fix m1 m2
    assume msgs: "m1 \<in> sentJoins t" "m2 \<in> sentJoins t"
    assume source_eq: "source m1 = source m2" and term_eq: "term m1 = term m2"

    from Next hyp msgs source_eq term_eq have "m1 = m2"
    proof (cases rule: square_Next_cases)
      case (HandleStartJoin nf nm tm newJoinRequest)
      from msgs have "m1 = newJoinRequest \<or> m1 \<in> sentJoins s" "m2 = newJoinRequest \<or> m2 \<in> sentJoins s" by (simp_all add: HandleStartJoin)
      thus ?thesis
      proof (elim disjE)
        assume "m1 \<in> sentJoins s" "m2 \<in> sentJoins s" with hyp source_eq term_eq show ?thesis by metis
      next
        assume "m1 = newJoinRequest" "m2 = newJoinRequest" thus ?thesis by simp
      next
        assume m1: "m1 \<in> sentJoins s" and m2: "m2 = newJoinRequest"
        from m1 prem have "term m1 \<le> currentTerm s (source m1)" by metis
        also from m2 source_eq have "source m1 = nf" by (simp add: HandleStartJoin)
        hence "currentTerm s (source m1) < tm" by (simp add: HandleStartJoin)
        also from m2 have "tm = term m2" by (simp add: HandleStartJoin)
        also note term_eq
        finally show ?thesis by simp
      next
        assume m1: "m1 = newJoinRequest" and m2: "m2 \<in> sentJoins s"
        from m2 prem have "term m2 \<le> currentTerm s (source m2)" by metis
        also from m1 source_eq have "source m2 = nf" by (simp add: HandleStartJoin)
        hence "currentTerm s (source m2) < tm" by (simp add: HandleStartJoin)
        also from m1 have "tm = term m1" by (simp add: HandleStartJoin)
        also note term_eq
        finally show ?thesis by simp
      qed
    qed auto
  }
  thus ?thesis by (simp add: JoinRequestsUniquePerTerm_def)
qed


lemma JoinVotesFaithful_step:
  assumes "s \<Turnstile> JoinVotesFaithful"
  assumes "s \<Turnstile> LastAcceptedTermInPast"
  shows "(s,t) \<Turnstile> JoinVotesFaithful$"
proof -
  from assms have hyp: "\<And>nm nf. nf \<in> joinVotes s nm \<Longrightarrow> \<exists> joinPayload. \<lparr> source = nf, dest = nm, term = currentTerm s nm, payload = Join joinPayload \<rparr> \<in> sentJoins s \<and> TermVersion (jp_laTerm joinPayload) (jp_laVersion joinPayload) \<le> laTermVersion s nm"
    by (auto simp add: JoinVotesFaithful_def)

  from assms
  have  hyp2: "\<And>n. lastAcceptedTerm s n \<le> currentTerm s n"
    unfolding LastAcceptedTermInPast_def
    by auto

  {
    fix nm0 nf0
    assume prem: "nf0 \<in> joinVotes t nm0"

    from Next have laTermVersion_increasing: "laTermVersion s nm0 \<le> laTermVersion t nm0"
    proof (cases rule: square_Next_cases)
      case (HandlePublishRequest nf nm newVersion newValue newConfig commConfig)
      with hyp2 [of nm0] show ?thesis
        by (cases "nf = nm0", auto simp add: laTermVersion_def less_eq_TermVersion_def)
    qed (auto simp add: laTermVersion_def)

    from Next hyp prem have "\<exists> joinPayload. \<lparr> source = nf0, dest = nm0, term = currentTerm t nm0, payload = Join joinPayload \<rparr> \<in> sentJoins s \<and> TermVersion (jp_laTerm joinPayload) (jp_laVersion joinPayload) \<le> laTermVersion s nm0"
    proof (cases rule: square_Next_cases)
      case (HandleStartJoin nf nm tm newJoinRequest)
      with hyp prem show ?thesis by (cases "nm0 = nf", auto simp add: laTermVersion_def)
    next
      case (RestartNode nr)
      with hyp prem show ?thesis by (cases "nm0 = nr", auto simp add: laTermVersion_def)
    next
      case (HandleJoinRequest nf nm laTerm_m laVersion_m)
      thus ?thesis
      proof (cases "nm0 = nm \<and> nf0 = nf")
        case False
        with prem have "nf0 \<in> joinVotes s nm0" by (cases "nm0 = nm", auto simp add: HandleJoinRequest)
        with hyp show ?thesis by (auto simp add: HandleJoinRequest simp add: laTermVersion_def)
      qed (auto simp add: laTermVersion_def less_eq_TermVersion_def)
    qed (auto simp add: laTermVersion_def)
    with sentJoins_increasing laTermVersion_increasing 
    have "\<exists>joinPayload. \<lparr>source = nf0, dest = nm0, term = currentTerm t nm0, payload = Join joinPayload\<rparr> \<in> sentJoins t \<and> TermVersion (jp_laTerm joinPayload) (jp_laVersion joinPayload) \<le> laTermVersion t nm0" by auto
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

lemma ElectionWonImpliesStartedJoin_step:
  assumes "s \<Turnstile> ElectionWonImpliesStartedJoin"
  shows "(s,t) \<Turnstile> ElectionWonImpliesStartedJoin$"
proof -
  from assms have hyp: "\<And>n. electionWon s n \<Longrightarrow> startedJoinSinceLastReboot s n"
    by (auto simp add: ElectionWonImpliesStartedJoin_def)

  {
    fix n
    assume prem: "electionWon t n"

    from Next hyp prem have "startedJoinSinceLastReboot t n"
    proof (cases rule: square_Next_cases)
      case (HandleJoinRequest nf nm laTerm_m laVersion_m)
      with hyp prem show ?thesis by (cases "nm = n", auto)
    qed auto
  }
  thus ?thesis by (auto simp add: ElectionWonImpliesStartedJoin_def)
qed

lemma MessagePositiveTerm_step:
  assumes "s \<Turnstile> MessagePositiveTerm"
  assumes "s \<Turnstile> JoinVotesFaithful"
  shows "(s,t) \<Turnstile> MessagePositiveTerm$"
proof -
  from assms
  have  hyp1: "\<And>m. m \<in> messages s \<Longrightarrow> term m > 0"
    and hyp2: "\<And> nm nf. nf \<in> joinVotes s nm \<Longrightarrow> \<exists> joinPayload. \<lparr> source = nf, dest = nm, term = currentTerm s nm, payload = Join joinPayload \<rparr> \<in> sentJoins s \<and> TermVersion (jp_laTerm joinPayload) (jp_laVersion joinPayload) \<le> laTermVersion s nm"
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
      with hyp2 obtain joinPayload where "\<lparr> source = voter, dest = nm, term = currentTerm s nm, payload = Join joinPayload \<rparr> \<in> messages s" by (auto simp add: sentJoins_def)
      from hyp1 [OF this] have "0 < currentTerm s nm" by simp
      with hyp1 prem show ?thesis by (auto simp add: ClientRequest)
    next
      case (HandlePublishRequest nf nm newVersion  newValue newConfig commConfig)
      with hyp1 [of "\<lparr>source = nm, dest = nf, term = currentTerm s nf, payload = PublishRequest \<lparr>prq_version  = newVersion, prq_value = newValue, prq_config = newConfig, prq_commConf = commConfig\<rparr>\<rparr>"]
      have "0 < currentTerm s nf" by (auto simp add: sentPublishRequests_def)
      with hyp1 prem show ?thesis by (auto simp add: HandlePublishRequest)
    next
      case (HandlePublishResponse_Quorum nf nm)
      with hyp1 [of "\<lparr>source = nf, dest = nm, term = currentTerm s nm, payload = PublishResponse \<lparr>prs_version  = lastPublishedVersion  s nm\<rparr>\<rparr>"]
      have "0 < currentTerm s nm" by (auto simp add: sentPublishResponses_def)
      with hyp1 prem show ?thesis by (auto simp add: HandlePublishResponse_Quorum)
    qed simp_all
  }
  thus ?thesis by (auto simp add: MessagePositiveTerm_def)
qed

lemma TermIncreasedByJoin_step:
  assumes "s \<Turnstile> TermIncreasedByJoin"
  shows "(s,t) \<Turnstile> TermIncreasedByJoin$"
proof -
  from assms have hyp: "\<And>n. currentTerm s n > 0 \<Longrightarrow> \<exists> m \<in> sentJoins s. currentTerm s n = term m"
    by (auto simp add: TermIncreasedByJoin_def)

  {
    fix n
    assume prem: "currentTerm t n > 0"
    from Next hyp prem have "\<exists> m \<in> sentJoins t. currentTerm t n = term m"
      by (cases rule: square_Next_cases, auto)
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
        else (\<exists> m \<in> sentPublishRequests s. lastAcceptedTerm          s n = term     m
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
        case (HandlePublishRequest nf nm newVersion  newValue newConfig commConfig)
        with hyp2 [of "\<lparr>source = nm, dest = nf, term = currentTerm s nf, payload = PublishRequest \<lparr>prq_version  = newVersion, prq_value = newValue, prq_config = newConfig, prq_commConf = commConfig\<rparr>\<rparr>"]
        have "0 < currentTerm s nf" by (simp add: sentPublishRequests_def)
        with term'0 show ?thesis by (auto simp add: HandlePublishRequest lastAcceptedData)
      qed (simp_all add: lastAcceptedData)
      thus ?thesis by (simp add: term'0 P_def)
    next
      case term'Pos: False
      from Next term'Pos hyp1 have "\<exists> m \<in> sentPublishRequests t.
                                          lastAcceptedTerm          t n = term     m
                                        \<and> lastAcceptedVersion       t n = version  m
                                        \<and> lastAcceptedValue         t n = value    m
                                        \<and> lastAcceptedConfiguration t n = config   m"
      proof (cases rule: square_Next_cases)
        case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
        with term'Pos hyp1 have "\<exists> m \<in> sentPublishRequests s.
                                          lastAcceptedTerm          s n = term     m
                                        \<and> lastAcceptedVersion       s n = version  m
                                        \<and> lastAcceptedValue         s n = value    m
                                        \<and> lastAcceptedConfiguration s n = config   m"
          by (auto simp add: P_def)
        thus ?thesis by (auto simp add: P_def ClientRequest)
      next
        case (HandlePublishRequest nf nm newVersion  newValue newConfig commConfig)
        show ?thesis
        proof (cases "n = nf")
          case False
          with term'Pos hyp1 HandlePublishRequest show ?thesis by (auto simp add: P_def)
        next
          case True
          with term'Pos hyp1 HandlePublishRequest show ?thesis
            by (intro bexI [where x = "\<lparr>source = nm, dest = nf, term = currentTerm s nf, payload = PublishRequest \<lparr>prq_version  = newVersion, prq_value = newValue, prq_config = newConfig, prq_commConf = commConfig\<rparr>\<rparr>"],
                auto)
        qed
      next
        case (HandlePublishResponse_Quorum nf nm)
        with term'Pos hyp1 have "\<exists> m \<in> sentPublishRequests s.
                                          lastAcceptedTerm          s n = term     m
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
    unfolding CommittedConfigurations_def using sentCommits_increasing sentPublishRequests_increasing
    by (auto simp add: CommittedConfigurations_def sentPublishRequests_def)
qed

lemma AcceptedConfigurationSource_step:
  assumes "s \<Turnstile> AcceptedConfigurationSource"
  shows "(s,t) \<Turnstile> AcceptedConfigurationSource$"
proof -
  from assms
  have  hyp1: "\<And>n. lastAcceptedConfiguration s n \<in> PublishedConfigurations s"
    unfolding AcceptedConfigurationSource_def
    by metis

  {
    fix n
    from Next hyp1 have "lastAcceptedConfiguration t n \<in> PublishedConfigurations s \<union> PublishedConfigurations t"
    proof (cases rule: square_Next_cases)
      case (ClientRequest nm v vs newPublishVersion newPublishRequests newEntry matchingElems newTransitiveElems)
      from hyp1 have "lastAcceptedConfiguration t n \<in> PublishedConfigurations s"
        by (auto simp add: PublishedConfigurations_def ClientRequest)
      thus ?thesis by simp
    next
      case (HandlePublishRequest nf nm newVersion newValue newConfig commConfig)
      show ?thesis
      proof (cases "nf = n")
        case True
        have "lastAcceptedConfiguration t n = newConfig"
          by (simp add: HandlePublishRequest True)
        also from HandlePublishRequest have "newConfig \<in> config ` sentPublishRequests s"
        proof (intro image_eqI)
          show "newConfig = config \<lparr>source = nm, dest = nf, term = currentTerm s nf, payload = PublishRequest \<lparr>prq_version = newVersion, prq_value = newValue, prq_config = newConfig, prq_commConf = commConfig\<rparr>\<rparr>"
            by simp
        qed simp
        also have "... \<subseteq> PublishedConfigurations s"
          by (auto simp add: PublishedConfigurations_def sentPublishRequests_def)
        finally show ?thesis by simp
      next
        case False with HandlePublishRequest hyp1 show ?thesis by simp
      qed
    qed (auto simp add: PublishedConfigurations_def)
    also from Next have "... \<subseteq> PublishedConfigurations t"
      by (cases rule: square_Next_cases, auto simp add: PublishedConfigurations_def)
    finally have "lastAcceptedConfiguration t n \<in> ..." .
  }
  thus ?thesis by (simp add: AcceptedConfigurationSource_def)
qed

lemma PublishedConfigurationSource_step:
  assumes "s \<Turnstile> PublishedConfigurationSource"
  assumes "s \<Turnstile> AcceptedConfigurationSource"
  shows "(s,t) \<Turnstile> PublishedConfigurationSource$"
proof -
  from assms
  have  hyp1: "\<And>n. electionWon s n \<Longrightarrow> lastPublishedConfiguration s n \<in> PublishedConfigurations s"
    and hyp2: "\<And>n. lastAcceptedConfiguration s n \<in> PublishedConfigurations s"
    unfolding PublishedConfigurationSource_def AcceptedConfigurationSource_def
    by metis+

  {
    fix n
    assume prem: "electionWon t n"

    from Next prem hyp1 have "lastPublishedConfiguration t n \<in> PublishedConfigurations s \<union> PublishedConfigurations t"
    proof (cases rule: square_Next_cases)
      case unchanged
      with prem hyp1 show ?thesis by (auto simp add: PublishedConfigurations_def)
    next
      case (HandleStartJoin nf nm tm newJoinRequest)
      with prem hyp1 hyp2 show ?thesis by (cases "nf = n", auto)
    next
      case (HandleJoinRequest nf nm laTerm_m laVersion_m)
      with prem hyp1 hyp2 show ?thesis by auto
    next
      case (ClientRequest nm v vs newPublishVersion newPublishRequests newEntry matchingElems newTransitiveElems)
      show ?thesis
      proof (cases "nm = n")
        case False
        with prem hyp1 hyp2 ClientRequest show ?thesis by auto
      next
        case True
        define prq where "\<And>nf. prq nf \<equiv> \<lparr>source = nm, dest = nf, term = currentTerm s nm, payload = PublishRequest \<lparr>prq_version = newPublishVersion, prq_value = v, prq_config = vs, prq_commConf = lastCommittedConfiguration s nm\<rparr>\<rparr>"
        have "vs \<in> config ` sentPublishRequests t"
        proof (intro image_eqI)
          show "vs = config (prq nm)"
            by (auto simp add: prq_def)
          have "prq nm \<in> newPublishRequests" by (auto simp add: prq_def ClientRequest)
          also have "... \<subseteq> sentPublishRequests t"
            by (auto simp add: ClientRequest)
          finally show "prq nm \<in> sentPublishRequests t" .
        qed
        also have "... \<subseteq> PublishedConfigurations t"
          unfolding PublishedConfigurations_def by (auto simp add: sentPublishRequests_def)
        finally show ?thesis by (auto simp add: ClientRequest True)
      qed
    next
      case (RestartNode nr)
      with prem hyp1 show ?thesis by (cases "nr = n", auto simp add: PublishedConfigurations_def)
    qed auto
    also from Next have "... \<subseteq> PublishedConfigurations t"
      by (cases rule: square_Next_cases, auto simp add: PublishedConfigurations_def)
    finally have "lastPublishedConfiguration t n \<in> ..." .
  }
  thus ?thesis by (simp add: PublishedConfigurationSource_def)
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
      else \<exists>m\<in>sentPublishRequests s. lastAcceptedTerm s n = term m \<and> lastAcceptedVersion  s n = version  m \<and> lastAcceptedValue s n = value m \<and> lastAcceptedConfiguration s n = config m"
    and hyp3: "\<And>m. m \<in> sentPublishRequests s \<Longrightarrow> commConf m \<in> CommittedConfigurations s"
    and hyp4: "\<And>m. m \<in> messages s \<Longrightarrow> term m > 0"
    by (auto simp add: CurrentConfigurationSource_def CurrentConfigurationMsgSource_def LastAcceptedDataSource_def MessagePositiveTerm_def)

  {
    fix n
    from Next have "lastCommittedConfiguration t n \<in> insert (lastCommittedConfiguration s n) (CommittedConfigurations t)"
    proof (cases rule: square_Next_cases)
      case (HandlePublishRequest nf nm newVersion  newValue newConfig commConfig)
      show ?thesis
      proof (cases "nf = n")
        case True
        hence "lastCommittedConfiguration t n = commConf \<lparr>source = nm, dest = nf,
              term = currentTerm s nf, payload = PublishRequest \<lparr>prq_version  = newVersion, prq_value = newValue, prq_config = newConfig, prq_commConf = commConfig\<rparr>\<rparr>"
          by (simp add: HandlePublishRequest)
        also from HandlePublishRequest have "... \<in> CommittedConfigurations s"
          by (intro hyp3, auto)
        also note CommittedConfigurations_increasing
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
        have "0 < lastAcceptedTerm s nf" by (simp add: sentCommits_def)
        with hyp2 [of n]
        obtain mPub where mPub: "mPub \<in> sentPublishRequests s" "lastAcceptedTerm s n = term mPub"
          "lastAcceptedVersion  s n = version  mPub" "lastAcceptedValue s n = value mPub" "lastAcceptedConfiguration s n = config mPub"
          unfolding nf_eq_n by auto

        have "lastAcceptedConfiguration s n \<in> CommittedConfigurations t"
          unfolding CommittedConfigurations_def
        proof (intro insertI2 CollectI bexI conjI)
          from mPub show "config mPub = lastAcceptedConfiguration s n" by simp
          from mPub show "mPub \<in> sentPublishRequests t" by (simp add: HandleCommitRequest)
          from HandleCommitRequest mPub show "msgTermVersion \<lparr>source = nm, dest = n, term = currentTerm s n, payload = Commit \<lparr>c_version  = lastAcceptedVersion s n\<rparr>\<rparr> = msgTermVersion mPub"
            "\<lparr>source = nm, dest = n, term = currentTerm s n, payload = Commit \<lparr>c_version  = lastAcceptedVersion  s n\<rparr>\<rparr> \<in> sentCommits t"
            by (simp_all add: nf_eq_n msgTermVersion_def)
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
    and hyp2: "\<And>m. m \<in> sentPublishRequests s \<Longrightarrow> commConf m \<in> CommittedConfigurations s"
    by (auto simp add: CurrentConfigurationSource_def CurrentConfigurationMsgSource_def)

  {
    fix m
    assume prem: "m \<in> sentPublishRequests t"
    with Next hyp2 have "commConf m \<in> CommittedConfigurations s"
    proof (cases rule: square_Next_cases)
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
      with prem have "m \<in> sentPublishRequests s \<or> m \<in> newPublishRequests" by auto
      thus ?thesis
      proof (elim disjE)
        assume "m : sentPublishRequests s"
        with hyp2 prem show "commConf m \<in> CommittedConfigurations s" by simp
      next
        assume "m \<in> newPublishRequests"
        hence "commConf m = lastCommittedConfiguration s nm"
          by (auto simp add: ClientRequest)
        also note hyp1
        finally show ?thesis .
      qed
    qed (auto simp add: CommittedConfigurations_def)
    also note CommittedConfigurations_increasing
    finally have "commConf m \<in> CommittedConfigurations t" .
  }
  thus ?thesis by (auto simp add: CurrentConfigurationMsgSource_def)
qed

lemma PublishedConfigurationsValid_step:
  assumes "s \<Turnstile> PublishedConfigurationsValid"
  shows "(s,t) \<Turnstile> PublishedConfigurationsValid$"
proof -
  from assms have hyp: "\<And>m. m \<in> sentPublishRequests s \<Longrightarrow> config m \<in> ValidConfigs"
    and init: "initialConfiguration s \<in> ValidConfigs"
    by (auto simp add: PublishedConfigurationsValid_def PublishedConfigurations_def)

  from Next init have "initialConfiguration t \<in> ValidConfigs"
    by (cases rule: square_Next_cases, simp_all)
  moreover
  {
    fix m
    assume prem: "m \<in> sentPublishRequests t"
    from Next hyp prem have "config m \<in> ValidConfigs"
    proof (cases rule: square_Next_cases)
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
      with prem have "m \<in> sentPublishRequests s \<or> m \<in> newPublishRequests" by auto
      thus ?thesis
      proof (elim disjE)
        assume "m \<in> sentPublishRequests s" with prem hyp show ?thesis by simp
      next
        assume "m \<in> newPublishRequests"
        hence "config m = vs" by (auto simp add: ClientRequest)
        with ClientRequest show ?thesis by simp
      qed
    qed auto
  }
  ultimately show ?thesis by (auto simp add: PublishedConfigurationsValid_def PublishedConfigurations_def)
qed

lemma PublicationsInPastTerm_step:
  assumes "s \<Turnstile> PublicationsInPastTerm"
  shows "(s,t) \<Turnstile> PublicationsInPastTerm$"
proof -
  from assms have hyp: "\<And>m. m \<in> sentPublishRequests s \<Longrightarrow> term m \<le> currentTerm s (source m)"
    by (auto simp add: PublicationsInPastTerm_def)

  {
    fix m
    assume prem: "m \<in> sentPublishRequests t"
    from Next hyp prem have "term m \<le> currentTerm s (source m)"
      by (cases rule: square_Next_cases, auto)
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
  from assms have hyp: "\<And>m. m \<in> sentPublishRequests s \<Longrightarrow> 0 < version  m"
    by (auto simp add: PublishRequestVersionPositive_def)

  {
    fix m
    assume prem: "m \<in> sentPublishRequests t"
    from Next hyp prem have "0 < version  m"
      by (cases rule: square_Next_cases, auto)
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
  have  hyp1: "\<And>m. m \<in> sentPublishRequests s \<Longrightarrow> (term m, source m) \<in> leaderHistory s"
    and hyp2: "\<And>n. electionWon s n \<Longrightarrow> (currentTerm s n, n) \<in> leaderHistory s"
    by (auto simp add: PublishRequestFromHistoricalLeader_def LeaderHistoryFaithful_def)

  {
    fix m
    assume prem: "m \<in> sentPublishRequests t"
    from Next hyp1 prem have "(term m, source m) \<in> leaderHistory t"
    proof (cases rule: square_Next_cases)
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
      with prem have "m \<in> sentPublishRequests s \<or> m \<in> newPublishRequests" by auto
      thus ?thesis
      proof (elim disjE)
        assume "m \<in> sentPublishRequests s"
        with ClientRequest hyp1 prem show ?thesis by auto
      next
        assume "m \<in> newPublishRequests"
        thus ?thesis by (auto simp add: ClientRequest hyp2)
      qed
    next
    qed auto
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
    qed auto
  }
  thus ?thesis by (auto simp add: BasedOnIncreasing_def)
qed

lemma PublishRequestBasedOn_step:
  assumes "s \<Turnstile> PublishRequestBasedOn"
  shows "(s,t) \<Turnstile> PublishRequestBasedOn$"
proof -
  from assms
  have  hyp1: "\<And>m. m \<in> sentPublishRequests s \<Longrightarrow> \<exists> tiPrev. (TermVersion  (term m) (version  m), tiPrev) \<in> basedOn s"
    by (auto simp add: PublishRequestBasedOn_def)

  {
    fix m assume prem: "m \<in> sentPublishRequests t"
    from Next hyp1 prem
    have "\<exists> tiPrev. (TermVersion  (term m) (version  m), tiPrev) \<in> basedOn t"
    proof (cases rule: square_Next_cases)
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
      with prem have "m \<in> sentPublishRequests s \<or> m \<in> newPublishRequests" by auto
      thus ?thesis
      proof (elim disjE)
        assume "m \<in> sentPublishRequests s" with prem hyp1 obtain tiPrev where "(TermVersion  (term m) (version  m), tiPrev) \<in> basedOn s" by auto
        also from ClientRequest have "basedOn s \<subseteq> basedOn t" by auto
        finally show ?thesis by auto
      next
        assume "m \<in> newPublishRequests"
        thus ?thesis unfolding ClientRequest by (elim UN_E insertE, auto)
      qed
    qed auto
  }
  thus ?thesis by (auto simp add: PublishRequestBasedOn_def)
qed

lemma BasedOnPublishRequest_step:
  assumes "s \<Turnstile> BasedOnPublishRequest"
  shows "(s,t) \<Turnstile> BasedOnPublishRequest$"
proof -
  from assms
  have  hyp1: "\<And> tiPrev tCurr iCurr. (TermVersion  tCurr iCurr, tiPrev) \<in> basedOn s
    \<Longrightarrow> \<exists> m \<in> sentPublishRequests s. term m = tCurr \<and> version  m = iCurr"
    by (auto simp add: BasedOnPublishRequest_def)

  {
    fix tiPrev tCurr iCurr assume prem: "(TermVersion  tCurr iCurr, tiPrev) \<in> basedOn t"
    from Next hyp1 prem
    have "\<exists> m \<in> sentPublishRequests t. term m = tCurr \<and> version  m = iCurr"
    proof (cases rule: square_Next_cases)
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
      from prem consider
        (s) "(TermVersion  tCurr iCurr, tiPrev) \<in> basedOn s"
        | (new) "tiPrev = TermVersion (lastAcceptedTerm s nm) (lastAcceptedVersion s nm)" "tCurr = currentTerm s nm" "iCurr = Suc (lastAcceptedVersion s nm)"
        unfolding ClientRequest by auto
      thus ?thesis
      proof cases
        case s with hyp1 have "\<exists>m\<in>sentPublishRequests s. term m = tCurr \<and> version  m = iCurr" by simp
        thus ?thesis unfolding ClientRequest by auto
      next
        case new
        have "\<exists>m\<in>newPublishRequests. term m = tCurr \<and> version m = iCurr"
          by (auto simp add: ClientRequest new)
        thus ?thesis unfolding ClientRequest by (elim bexE, auto)
      qed
    qed auto
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
    and hyp2: "\<And>m. m \<in> sentPublishRequests s \<Longrightarrow> \<exists> tiPrev. (TermVersion  (term m) (version  m), tiPrev) \<in> basedOn s"
    and hyp3: "\<And>n. if lastAcceptedTerm s n = 0
        then lastAcceptedVersion       s n = 0
           \<and> lastAcceptedValue         s n = initialValue s
           \<and> lastAcceptedConfiguration s n = initialConfiguration s
        else (\<exists> m \<in> sentPublishRequests s. lastAcceptedTerm          s n = term     m
                                         \<and> lastAcceptedVersion       s n = version  m
                                         \<and> lastAcceptedValue         s n = value    m
                                         \<and> lastAcceptedConfiguration s n = config   m)"
    unfolding BasedOnBasedOn_def PublishRequestBasedOn_def LastAcceptedDataSource_def
    by metis+

  {
    fix tiCurr tPrev iPrev
    assume prem: "(tiCurr, TermVersion tPrev iPrev) \<in> basedOn t" "0 < iPrev"
    from Next hyp1 prem
    have "\<exists> tiPrevPrev. (TermVersion tPrev iPrev, tiPrevPrev) \<in> basedOn t"
    proof (cases rule: square_Next_cases)
      case (ClientRequest nm v vs newPublishVersion newPublishRequests newEntry matchingElems newTransitiveElems)
      from prem consider
        (s) "(tiCurr, TermVersion tPrev iPrev) \<in> basedOn s"
        | (new) "tPrev = lastAcceptedTerm s nm" "iPrev = lastAcceptedVersion  s nm"
          "tiCurr = TermVersion (currentTerm s nm) (Suc (lastAcceptedVersion  s nm))"
        unfolding ClientRequest by auto
      thus ?thesis
      proof cases
        case s
        with prem have "\<exists> tiPrevPrev. (TermVersion tPrev iPrev, tiPrevPrev) \<in> basedOn s" by (intro hyp1)
        thus ?thesis by (auto simp add: ClientRequest)
      next
        case new with hyp3 [of nm] prem
        obtain m where m: "m \<in> sentPublishRequests s" "term m = tPrev" "version  m = iPrev"
          by (cases "lastAcceptedTerm s nm = 0", auto)
        with hyp2 obtain tiPrevPrev where "(TermVersion tPrev iPrev, tiPrevPrev) \<in> basedOn s" unfolding sentPublishRequests_def by auto
        thus ?thesis unfolding ClientRequest by auto
      qed
    qed auto
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
  have  hyp1: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound; currentTerm s (source m) = term m; startedJoinSinceLastReboot s (source m) \<rbrakk> \<Longrightarrow> electionWon s (source m)"
    and hyp2: "\<And>m. m \<in> sentPublishRequests s \<Longrightarrow> term m \<le> currentTerm s (source m)"
    and hyp3: "\<And>n. \<lbrakk> currentTerm s n < termBound; electionWon s n \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s n) (lastCommittedConfiguration s n)"
    and hyp4: "\<And>n. \<lbrakk> currentTerm s n < termBound; electionWon s n \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s n) (lastAcceptedConfiguration s n)"
    by (auto simp add: PublishRequestImpliesElectionWonBelow_def PublicationsInPastTerm_def ElectionWonQuorumBelow_def)

  {
    fix m
    assume prem: "m \<in> sentPublishRequests t" "term m < termBound" "currentTerm t (source m) = term m" "startedJoinSinceLastReboot t (source m)"
    from Next hyp1 prem have "electionWon t (source m)"
    proof (cases rule: square_Next_cases)
      case (HandleStartJoin nf nm tm newJoinRequest)
      show ?thesis
      proof (cases "source m = nf")
        case False
        hence "electionWon t (source m) = electionWon s (source m)" by (simp add: HandleStartJoin)
        also from prem have "electionWon s (source m)"
          by (intro hyp1, auto simp add: HandleStartJoin False)
        finally show ?thesis .
      next
        case True
        from prem have "term m \<le> currentTerm s (source m)"
          by (intro hyp2, auto simp add: HandleStartJoin)
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
    qed auto
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
  have  hyp1: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound; currentTerm s (source m) = term m;
                     electionWon s (source m) \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s (source m)) (config m)"
    and hyp2: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound; currentTerm s (source m) = term m;
                     electionWon s (source m) \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s (source m)) (commConf m)"
    and hyp3: "\<And>n. \<lbrakk> currentTerm s n < termBound; electionWon s n \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s n) (lastCommittedConfiguration      s n)"
    and hyp4: "\<And>n. \<lbrakk> currentTerm s n < termBound; electionWon s n \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s n) (lastAcceptedConfiguration s n)"
    and hyp5: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound; currentTerm s (source m) = term m; startedJoinSinceLastReboot s (source m) \<rbrakk> \<Longrightarrow> electionWon s (source m)"
    by (auto simp add: ElectionWonQuorumBelow_def PublishRequestImpliesQuorumBelow_def PublishRequestImpliesElectionWonBelow_def)

  {
    fix m assume prem: "m \<in> sentPublishRequests t" "term m < termBound" "currentTerm t (source m) = term m" "electionWon t (source m)"
    from Next hyp1 hyp2 prem have "IsQuorum (joinVotes t (source m)) (config m) \<and> IsQuorum (joinVotes t (source m)) (commConf m)"
    proof (cases rule: square_Next_cases)
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
        from prem electionWon have "IsQuorum (joinVotes s (source m)) (config m) \<and> IsQuorum (joinVotes s (source m)) (commConf m)"
          by (intro conjI hyp1 hyp2, simp_all add: HandleJoinRequest True)
        with joinVotes_increase
        have "IsQuorum (joinVotes t (source m)) (config m) \<and> IsQuorum (joinVotes t (source m)) (commConf m)"
          unfolding IsQuorum_def using less_le_trans mult_le_mono1 by blast
        thus ?thesis by (simp add: HandleJoinRequest True)
      qed
    next
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
      with prem have "m \<in> sentPublishRequests s \<or> m \<in> newPublishRequests" by auto
      thus ?thesis
      proof (elim disjE)
        assume "m \<in> sentPublishRequests s" with ClientRequest prem hyp1 hyp2 show ?thesis by auto
      next
        assume m_new: "m \<in> newPublishRequests"
        hence config_m: "config m = vs"
          and commConf_m: "commConf m = lastCommittedConfiguration s (source m)"
          and source_m: "source m = nm" 
          by (auto simp add: ClientRequest)

        from ClientRequest have joinVotes_eq: "joinVotes t = joinVotes s" by simp

        from prem have "IsQuorum (joinVotes t (source m)) (commConf m)"
          unfolding commConf_m joinVotes_eq by (intro hyp3, auto simp add: ClientRequest)
        moreover from ClientRequest have "IsQuorum (joinVotes t (source m)) (config m)"
          unfolding config_m source_m by simp
        ultimately show ?thesis by simp
      qed
    qed auto
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
  have  hyp1: "\<And>n. \<lbrakk> currentTerm s n < termBound; electionWon s n \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s n) (lastCommittedConfiguration s n)"
    and hyp2: "\<And>n. \<lbrakk> currentTerm s n < termBound; electionWon s n \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s n) (lastAcceptedConfiguration  s n)"
    and hyp3: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound; currentTerm s (source m) = term m;
                     electionWon s (source m) \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s (source m)) (config m)"
    and hyp4: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound; currentTerm s (source m) = term m;
                     electionWon s (source m) \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s (source m)) (commConf m)"
    and hyp5: "\<And>m n. \<lbrakk> m \<in> sentPublishRequests s; term m = currentTerm s n; term m < termBound; electionWon s n \<rbrakk>
                    \<Longrightarrow> n = source m"
    unfolding ElectionWonQuorumBelow_def PublishRequestImpliesQuorumBelow_def PublishRequestSentByMasterBelow_def
    by metis+

  {
    fix n
    assume prem: "currentTerm t n < termBound" "electionWon t n"
    from Next hyp1 hyp2 prem
    have "IsQuorum (joinVotes t n) (lastCommittedConfiguration t n) \<and> IsQuorum (joinVotes t n) (lastAcceptedConfiguration t n)"
    proof (cases rule: square_Next_cases)
      case (HandlePublishRequest nf nm newVersion  newValue newConfig commConfig)

      define publishRequest where "publishRequest \<equiv> \<lparr>source = nm, dest = nf, term = currentTerm s nf, payload = PublishRequest \<lparr>prq_version  = newVersion, prq_value = newValue, prq_config = newConfig, prq_commConf = commConfig\<rparr>\<rparr>"

      show ?thesis
      proof (cases "nf = n")
        case False with HandlePublishRequest hyp1 hyp2 prem show ?thesis by auto
      next
        case nf_eq_n: True

        have config_eqs: "joinVotes t = joinVotes s"
          "lastCommittedConfiguration t n = commConf publishRequest"
          "lastAcceptedConfiguration t n = config publishRequest"
          by (simp_all add: HandlePublishRequest nf_eq_n publishRequest_def)

        from HandlePublishRequest prem
        have n_source: "n = source publishRequest"
          by (intro hyp5, auto simp add: publishRequest_def nf_eq_n)
        hence nm_eq_n: "nm = n" by (simp add: nf_eq_n publishRequest_def)

        from nf_eq_n n_source nm_eq_n
        show ?thesis unfolding config_eqs unfolding n_source
          apply (intro conjI hyp3 hyp4)
          using prem HandlePublishRequest
          by (auto simp add: publishRequest_def nf_eq_n nm_eq_n)
      qed
    qed auto
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
  have  hyp1: "\<And>m n. \<lbrakk> m \<in> sentPublishRequests s; term m = currentTerm s n; term m < termBound; electionWon s n \<rbrakk>
                    \<Longrightarrow> n = source m"
    and hyp2: "\<And>n1 n2 tm. \<lbrakk> tm < termBound; (tm, n1) \<in> leaderHistory t; (tm, n2) \<in> leaderHistory t \<rbrakk> \<Longrightarrow> n1 = n2"
    and hyp3: "\<And>n. electionWon s n \<Longrightarrow> (currentTerm s n, n) \<in> leaderHistory s"
    and hyp4: "\<And>m. m \<in> sentPublishRequests s \<Longrightarrow> (term m, source m) \<in> leaderHistory s"
    unfolding OneMasterPerTermBelow_def PublishRequestSentByMasterBelow_def
        LeaderHistoryFaithful_def PublishRequestFromHistoricalLeader_def
    by metis+

  {
    fix m n
    assume prem: "m \<in> sentPublishRequests t" "term m = currentTerm t n" "term m < termBound" "electionWon t n"
    from Next hyp1 prem
    have "n = source m"
    proof (cases rule: square_Next_cases)
      case (HandleStartJoin nf nm tm newJoinRequest)
      from prem have "n \<noteq> nf" by (auto simp add: HandleStartJoin)
      with prem have "m \<in> sentPublishRequests s" "term m = currentTerm s n" "currentTerm s n < termBound" "electionWon s n" 
        by (auto simp add: HandleStartJoin)
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
      with prem have "m \<in> sentPublishRequests s \<or> m \<in> newPublishRequests" by auto
      thus ?thesis
      proof (elim disjE)
        assume "m \<in> sentPublishRequests s" with ClientRequest hyp1 hyp2 prem show ?thesis by auto
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
      case (RestartNode nr)
      show ?thesis
      proof (cases "n = nr")
        case False with RestartNode hyp1 hyp2 prem show ?thesis by auto
      next
        case True with prem RestartNode show ?thesis by auto
      qed
    qed auto
  }
  thus ?thesis by (auto simp add: PublishRequestSentByMasterBelow_def)
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
    qed auto
  }
  thus ?thesis by (auto simp add: EndOfTermIsPermanentBelow_def)
qed

lemma termVersion_nondecreasing:
  assumes "currentTerm s n < termBound"
  assumes "s \<Turnstile> ElectionWonQuorumBelow termBound"
  shows "termVersion n s \<le> termVersion n t"
proof -
  from assms
  have  hyp1: "\<And>n. \<lbrakk> currentTerm s n < termBound; electionWon s n \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s n) (lastCommittedConfiguration s n)"
    and hyp2: "\<And>n. \<lbrakk> currentTerm s n < termBound; electionWon s n \<rbrakk> \<Longrightarrow> IsQuorum (joinVotes s n) (lastAcceptedConfiguration  s n)"
    by (auto simp add: ElectionWonQuorumBelow_def)

  from Next show ?thesis
  proof (cases rule: square_Next_cases)
    case (HandleJoinRequest nf nm laTerm_m laVersion_m)
    show ?thesis
    proof (cases "nm = n")
      case False
      with HandleJoinRequest show ?thesis by (auto simp add: termVersion_def less_eq_TermVersion_def)
    next
      case nm_eq_n: True
      show ?thesis
      proof (cases "electionWon s nm")
        case False
        with HandleJoinRequest show ?thesis
          by (auto simp add: termVersion_def less_eq_TermVersion_def)
      next
        case electionWon_s: True
        have "IsQuorum (joinVotes s nm) (lastCommittedConfiguration s nm)" using assms electionWon_s unfolding nm_eq_n by (metis hyp1)
        moreover
        have "IsQuorum (joinVotes s nm) (lastAcceptedConfiguration  s nm)" using assms electionWon_s unfolding nm_eq_n by (metis hyp2)
        ultimately
        have electionWon_t: "electionWon t nm" by (auto simp add: HandleJoinRequest IsQuorum_insert)

        from electionWon_s electionWon_t HandleJoinRequest
        show ?thesis by (simp add: termVersion_def nm_eq_n)
      qed
    qed
  qed (auto simp add: termVersion_def less_eq_TermVersion_def)
qed


lemma PublishRequestVersionAtMostSenderBelow_step:
  assumes "s \<Turnstile> PublishRequestVersionAtMostSenderBelow termBound"
  assumes "s \<Turnstile> ElectionWonQuorumBelow termBound"
  assumes "s \<Turnstile> ElectionWonImpliesStartedJoin"
  shows "(s,t) \<Turnstile> PublishRequestVersionAtMostSenderBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound \<rbrakk> \<Longrightarrow> msgTermVersion m \<le> termVersion (source m) s"
    and hyp2: "\<And>n. electionWon s n \<Longrightarrow> startedJoinSinceLastReboot s n"
    by (auto simp add: PublishRequestVersionAtMostSenderBelow_def ElectionWonImpliesStartedJoin_def)

  {
    fix m
    assume prem: "m \<in> sentPublishRequests t" "term m < termBound"
    with hyp1 have hyp1: "m \<in> sentPublishRequests s \<Longrightarrow> msgTermVersion m \<le> termVersion (source m) s" by simp

    have "msgTermVersion m \<le> termVersion (source m) t"
    proof (cases "currentTerm s (source m) < termBound")
      case False
      with prem have "term m < currentTerm s (source m)" by auto
      also note terms_increasing
      finally show ?thesis by (auto simp add: msgTermVersion_def termVersion_def less_eq_TermVersion_def)
    next
      case True
      have termVersion_source_nondecreasing: "termVersion (source m) s \<le> termVersion (source m) t"
        by (intro termVersion_nondecreasing [where termBound = termBound] assms True)

      from Next hyp1 prem have "msgTermVersion m \<le> termVersion (source m) t \<or> msgTermVersion m \<le> termVersion (source m) s"
      proof (cases rule: square_Next_cases)
        case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)
        from prem have "m \<in> sentPublishRequests s \<or> m \<in> newPublishRequests" by (auto simp add: ClientRequest)
        thus ?thesis
        proof (elim disjE)
          assume "m \<in> sentPublishRequests s"
          with hyp1 prem ClientRequest show ?thesis by (auto simp add: msgTermVersion_def termVersion_def)
        next
          assume m_new: "m \<in> newPublishRequests"
          hence source_eq: "source m = nm" by (auto simp add: ClientRequest)

          from m_new have 1: "msgTermVersion  m = TermVersion  (currentTerm s nm) (Suc (lastAcceptedVersion  s nm))"
            by (auto simp add: msgTermVersion_def ClientRequest)

          from ClientRequest have "electionWon s nm" by simp
          hence "startedJoinSinceLastReboot s nm" by (intro hyp2, auto simp add: IsQuorum_def)
          with ClientRequest have 2: "termVersion  (source m) t = TermVersion  (currentTerm s nm) (Suc (lastAcceptedVersion  s nm))"
            by (auto simp add: termVersion_def source_eq)

          show ?thesis by (simp add: 1 2)
        qed
      qed (auto simp add: msgTermVersion_def termVersion_def)
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
  assumes "s \<Turnstile> ElectionWonImpliesStartedJoin"
  shows "(s,t) \<Turnstile> PublishRequestsUniquePerTermVersionBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>m1 m2. \<lbrakk> m1 \<in> sentPublishRequests s; m2 \<in> sentPublishRequests s;
     term m1 < termBound; term m1 = term m2; version  m1 = version  m2 \<rbrakk> \<Longrightarrow> payload m1 = payload m2"
    unfolding PublishRequestsUniquePerTermVersionBelow_def by metis
  from assms
  have  hyp2: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound \<rbrakk> \<Longrightarrow> msgTermVersion  m \<le> termVersion  (source m) s"
    and hyp3: "\<And>n1 n2 tm. \<lbrakk> tm < termBound; (tm, n1) \<in> leaderHistory s; (tm, n2) \<in> leaderHistory s \<rbrakk> \<Longrightarrow> n1 = n2"
    and hyp4: "\<And>m. m \<in> sentPublishRequests s \<Longrightarrow> (term m, source m) \<in> leaderHistory s"
    and hyp5: "\<And>n. electionWon s n \<Longrightarrow> (currentTerm s n, n) \<in> leaderHistory s"
    and hyp6: "\<And>n. electionWon s n \<Longrightarrow> startedJoinSinceLastReboot s n"
    by (auto simp add: PublishRequestVersionAtMostSenderBelow_def OneMasterPerTermBelow_def
        PublishRequestFromHistoricalLeader_def LeaderHistoryFaithful_def ElectionWonImpliesStartedJoin_def)

  {
    fix m1 m2
    assume prem: "m1 \<in> sentPublishRequests t" "m2 \<in> sentPublishRequests t"
      "term m1 < termBound" "term m1 = term m2" "version  m1 = version  m2"

    with hyp1 have hyp1: "m1 \<in> sentPublishRequests s \<Longrightarrow> m2 \<in> sentPublishRequests s \<Longrightarrow> payload m1 = payload m2" by metis

    from Next prem hyp1 have "payload m1 = payload m2"
    proof (cases rule: square_Next_cases)
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)

      from ClientRequest
      have startedJoinSinceLastReboot_nm: "startedJoinSinceLastReboot s nm"
        by (intro hyp6)

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
        from prem have "m1 \<in> sentPublishRequests s \<or> m1 \<in> newPublishRequests" by (auto simp add: ClientRequest)
        with prem show "(term m1, source m1) \<in> leaderHistory s"
          by (metis hyp4 newMsg_leaderHistory)
        from prem have "m2 \<in> sentPublishRequests s \<or> m2 \<in> newPublishRequests" by (auto simp add: ClientRequest)
        with prem have "(term m2, source m2) \<in> leaderHistory s"
          by (metis hyp4 newMsg_leaderHistory)
        with prem show "(term m1, source m2) \<in> leaderHistory s" by simp
      qed

      from prem consider
        (old_old) "m1 \<in> sentPublishRequests s" "m2 \<in> sentPublishRequests s"
        | (old_new) "m1 \<in> sentPublishRequests s" "m2 \<in> newPublishRequests"
        | (new_old) "m1 \<in> newPublishRequests" "m2 \<in> sentPublishRequests s"
        | (new_new) "m1 \<in> newPublishRequests" "m2 \<in> newPublishRequests"
        unfolding ClientRequest by auto
      thus ?thesis
      proof cases
        case old_old with hyp1 show ?thesis by simp
      next
        case new_new with ClientRequest show ?thesis by auto
      next
        case old_new
        with prem have "msgTermVersion m1 \<le> termVersion (source m1) s" by (intro hyp2)
        also have "... = termVersion (source m2) s" by (simp add: source_eq)
        also from old_new have "... = termVersion nm s" by (auto simp add: ClientRequest)
        also from ClientRequest startedJoinSinceLastReboot_nm have "... < termVersion nm t" by (auto simp add: termVersion_def)
        also from ClientRequest old_new startedJoinSinceLastReboot_nm have "... = msgTermVersion m2" by (auto simp add: msgTermVersion_def termVersion_def)
        also from prem have "... = msgTermVersion  m1" by (simp add: msgTermVersion_def)
        finally show ?thesis by simp
      next
        case new_old
        with prem have "msgTermVersion m2 \<le> termVersion (source m2) s" by (intro hyp2, auto)
        also have "... = termVersion (source m1) s" by (simp add: source_eq)
        also from new_old have "... = termVersion nm s" by (auto simp add: ClientRequest)
        also from ClientRequest startedJoinSinceLastReboot_nm have "... < termVersion nm t" by (auto simp add: termVersion_def)
        also from ClientRequest new_old startedJoinSinceLastReboot_nm have "... = msgTermVersion m1" by (auto simp add: msgTermVersion_def termVersion_def)
        also from prem have "... = msgTermVersion m2" by (simp add: msgTermVersion_def)
        finally show ?thesis by simp
      qed
    qed auto
  }
  thus ?thesis unfolding PublishRequestsUniquePerTermVersionBelow_def by (simp only: unl_after, metis)
qed

lemma BasedOnUniqueBelow_step:
  assumes "s \<Turnstile> BasedOnUniqueBelow termBound"
  assumes "s \<Turnstile> PublishRequestVersionAtMostSenderBelow termBound"
  assumes "s \<Turnstile> BasedOnPublishRequest"
  assumes "s \<Turnstile> PublishRequestSentByMasterBelow termBound"
  assumes "s \<Turnstile> ElectionWonImpliesStartedJoin"
  shows "(s,t) \<Turnstile> BasedOnUniqueBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>tiPrev1 tiPrev2 tCurr iCurr. \<lbrakk> tCurr < termBound;
        (TermVersion tCurr iCurr, tiPrev1) \<in> basedOn s; (TermVersion tCurr iCurr, tiPrev2) \<in> basedOn s \<rbrakk>
      \<Longrightarrow> tiPrev1 = tiPrev2"
    and hyp2: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound \<rbrakk> \<Longrightarrow> msgTermVersion m \<le> termVersion (source m) s"
    and hyp3: "\<And>tiPrev tCurr iCurr. (TermVersion  tCurr iCurr, tiPrev) \<in> basedOn s
      \<Longrightarrow> \<exists> m \<in> sentPublishRequests s. term m = tCurr \<and> version  m = iCurr"
    and hyp4: "\<And>m n. \<lbrakk> m \<in> sentPublishRequests s; term m = currentTerm s n; term m < termBound; electionWon s n \<rbrakk>
      \<Longrightarrow> n = source m"
    and hyp5: "\<And>n. electionWon s n \<Longrightarrow> startedJoinSinceLastReboot s n"
    by (auto simp add: BasedOnUniqueBelow_def PublishRequestVersionAtMostSenderBelow_def
        BasedOnPublishRequest_def PublishRequestSentByMasterBelow_def ElectionWonImpliesStartedJoin_def)

  {
    fix tiPrev1 tiPrev2 tCurr iCurr
    assume prem: "tCurr < termBound"
      "(TermVersion tCurr iCurr, tiPrev1) \<in> basedOn t"
      "(TermVersion tCurr iCurr, tiPrev2) \<in> basedOn t"

    from Next prem hyp1 have "tiPrev1 = tiPrev2"
    proof (cases rule: square_Next_cases)
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)

      from ClientRequest
      have startedJoinSinceLastReboot: "startedJoinSinceLastReboot s nm" by (intro hyp5)

      from prem consider
        (old_old) "(TermVersion tCurr iCurr, tiPrev1) \<in> basedOn s" "(TermVersion  tCurr iCurr, tiPrev2) \<in> basedOn s"
        | (old_new) "(TermVersion tCurr iCurr, tiPrev1) \<in> basedOn s"
          "tCurr = currentTerm s nm" "iCurr = Suc (lastAcceptedVersion  s nm)"
          "tiPrev2 = TermVersion (lastAcceptedTerm s nm) (lastAcceptedVersion  s nm)"
        | (new_old) "(TermVersion tCurr iCurr, tiPrev2) \<in> basedOn s"
          "tCurr = currentTerm s nm" "iCurr = Suc (lastAcceptedVersion  s nm)"
          "tiPrev1 = TermVersion (lastAcceptedTerm s nm) (lastAcceptedVersion  s nm)"
        | (new_new) "tiPrev1 = tiPrev2"
        by (auto simp add: ClientRequest)
      thus ?thesis
      proof cases
        case new_new thus ?thesis by simp
      next
        case old_old with hyp1 prem show ?thesis by simp
      next
        case old_new
        with hyp3 obtain m where m: "m \<in> sentPublishRequests s" "term m = tCurr" "version  m = iCurr" by metis
        from m prem old_new have nm_eq: "nm = source m" by (intro hyp4, auto simp add: ClientRequest)
        from m prem have "msgTermVersion  m \<le> termVersion  nm s" unfolding nm_eq by (intro hyp2, auto)
        thus ?thesis
          by (simp add: msgTermVersion_def m old_new termVersion_def startedJoinSinceLastReboot ClientRequest less_eq_TermVersion_def)
      next
        case new_old
        with hyp3 obtain m where m: "m \<in> sentPublishRequests s" "term m = tCurr" "version  m = iCurr" by metis
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
  have  hyp1: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; lastAcceptedVersion s (source m) = lastPublishedVersion s (source m);
                     term m = currentTerm s (source m); term m < termBound; electionWon s (source m) \<rbrakk>
      \<Longrightarrow> lastAcceptedTerm s (source m) = currentTerm s (source m)"
    and hyp2: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound; currentTerm s (source m) = term m;
                     startedJoinSinceLastReboot s (source m) \<rbrakk> \<Longrightarrow> electionWon s (source m)"
    unfolding LeaderMustAcceptItsPublishRequestsBelow_def PublishRequestImpliesElectionWonBelow_def
    by metis+

  {
    fix m
    assume prem: "m \<in> sentPublishRequests t" "lastAcceptedVersion t (source m) = lastPublishedVersion t (source m)"
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
          from prem show "m \<in> sentPublishRequests s" "term m = currentTerm s (source m)" "term m < termBound"
            unfolding HandleJoinRequest by simp_all
          show "electionWon s (source m)"
          proof (intro hyp2)
            from prem show "m \<in> sentPublishRequests s"
              "currentTerm s (source m) = term m" "term m < termBound"
              unfolding HandleJoinRequest by simp_all
            from HandleJoinRequest show "startedJoinSinceLastReboot s (source m)" by (simp add: nm_eq)
          qed
          with prem show "lastAcceptedVersion  s (source m) = lastPublishedVersion  s (source m)"
            by (auto simp add: HandleJoinRequest)
        qed
      qed
    next
      case (ClientRequest nm v vs newPublishVersion newPublishRequests newEntry matchingElems newTransitiveElems)
      show ?thesis
      proof (cases "source m = nm")
        case False with ClientRequest hyp1 prem show ?thesis by auto
      next
        case nm_eq: True
        from prem have "m \<in> sentPublishRequests s \<or> m \<in> newPublishRequests" unfolding ClientRequest by auto
        thus ?thesis
        proof (elim disjE)
          assume old: "m \<in> sentPublishRequests s"
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
      with prem hyp1 show ?thesis by (cases "source m = nr", auto)
    qed auto
  }
  thus ?thesis unfolding LeaderMustAcceptItsPublishRequestsBelow_def by auto
qed

lemma PublishRequestsContiguousWithinTermBelow_step:
  assumes "s \<Turnstile> PublishRequestsContiguousWithinTermBelow termBound"
  assumes "s \<Turnstile> PublishRequestVersionAtMostSenderBelow termBound"
  assumes "s \<Turnstile> ElectionWonImpliesStartedJoin"
  assumes "s \<Turnstile> PublishRequestSentByMasterBelow termBound"
  assumes "s \<Turnstile> LastAcceptedTermInPast"
  assumes "s \<Turnstile> LeaderMustAcceptItsPublishRequestsBelow termBound"
  shows "(s,t) \<Turnstile> PublishRequestsContiguousWithinTermBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>m1 m2. \<lbrakk> m1 \<in> sentPublishRequests s; m2 \<in> sentPublishRequests s; term m1 = term m2; term m1 < termBound; version m1 < version m2 \<rbrakk>
      \<Longrightarrow> (TermVersion (term m2) (version m2), TermVersion (term m2) (version m2 - 1)) \<in> basedOn s"
    and hyp2: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound \<rbrakk> \<Longrightarrow> msgTermVersion m \<le> termVersion (source m) s"
    and hyp3: "\<And>n. electionWon s n \<Longrightarrow> startedJoinSinceLastReboot s n"
    and hyp4: "\<And>m n. \<lbrakk> m \<in> sentPublishRequests s; term m = currentTerm s n; term m < termBound; electionWon s n \<rbrakk>
      \<Longrightarrow> n = source m"
    and hyp5: "\<And>n. lastAcceptedTerm s n \<le> currentTerm s n"
    and hyp6: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; lastAcceptedVersion s (source m) = lastPublishedVersion s (source m);
                     term m = currentTerm s (source m); term m < termBound; electionWon s (source m) \<rbrakk>
      \<Longrightarrow> lastAcceptedTerm s (source m) = currentTerm s (source m)"
    unfolding PublishRequestsContiguousWithinTermBelow_def PublishRequestVersionAtMostSenderBelow_def
      ElectionWonImpliesStartedJoin_def PublishRequestSentByMasterBelow_def LastAcceptedTermInPast_def
      LeaderMustAcceptItsPublishRequestsBelow_def
    by metis+

  {
    fix m1 m2
    assume prem: "m1 \<in> sentPublishRequests t" "m2 \<in> sentPublishRequests t" "term m1 = term m2" "term m1 < termBound" "version m1 < version m2"

    from Next prem hyp1 have "(TermVersion (term m2) (version m2), TermVersion (term m2) (version m2 - 1)) \<in> basedOn t"
    proof (cases rule: square_Next_cases)
      case (ClientRequest nm v vs newPublishVersion  newPublishRequests newEntry matchingElems newTransitiveElems)

      from ClientRequest have startedJoinSinceLastReboot: "startedJoinSinceLastReboot s nm" by (intro hyp3)

      from prem consider
        (old_old) "m1 \<in> sentPublishRequests s" "m2 \<in> sentPublishRequests s"
        | (old_new) "m1 \<in> sentPublishRequests s" "m2 \<in> newPublishRequests"
        | (new_old) "m1 \<in> newPublishRequests" "m2 \<in> sentPublishRequests s"
        | (new_new) "m1 \<in> newPublishRequests" "m2 \<in> newPublishRequests"
        unfolding ClientRequest by auto
      thus ?thesis
      proof cases
        case old_old with prem hyp1 have "(TermVersion (term m2) (version m2), TermVersion (term m2) (version m2 - 1)) \<in> basedOn s" by simp
        with ClientRequest show ?thesis by auto
      next
        case new_new with prem show ?thesis by (auto simp add: ClientRequest)
      next
        case new_old
        from new_old prem have nm_eq: "nm = source m2" by (intro hyp4, auto simp add: ClientRequest)
        from new_old prem have "msgTermVersion  m2 \<le> termVersion  nm s" unfolding nm_eq by (intro hyp2, auto)
        with new_old prem show ?thesis
          by (auto simp add: msgTermVersion_def termVersion_def startedJoinSinceLastReboot less_eq_TermVersion_def ClientRequest)
      next
        case old_new
        from old_new prem have nm_eq: "nm = source m1" "nm = source m2" by (intro hyp4, auto simp add: ClientRequest)

        have "lastAcceptedTerm s nm = currentTerm s nm"
          unfolding nm_eq
        proof (intro hyp6)
          from old_new show "m1 \<in> sentPublishRequests s" by simp
          from prem show "term m1 < termBound" by simp
          from ClientRequest show "electionWon s (source m1)" by (simp add: nm_eq)
          from prem have "term m1 = term m2" by simp
          also from ClientRequest old_new have "term m2 = currentTerm s nm" by auto
          finally show "term m1 = currentTerm s (source m1)" by (simp add: nm_eq)
          from ClientRequest show "lastAcceptedVersion s (source m1) = lastPublishedVersion s (source m1)" by (simp add: nm_eq)
        qed

        moreover from old_new prem have "(TermVersion (term m2) (version m2), TermVersion (lastAcceptedTerm s nm) (version m2 - 1)) \<in> basedOn t"
          by (auto simp add: ClientRequest)

        moreover from old_new have "term m2 = currentTerm s nm" by (auto simp add: ClientRequest)

        ultimately show ?thesis by simp
      qed
    qed auto
  }
  thus ?thesis unfolding PublishRequestsContiguousWithinTermBelow_def by auto
qed

lemma NewLeaderHasExpectedLastPublishedVersion_step:
  assumes "s \<Turnstile> NewLeaderHasExpectedLastPublishedVersion"
  shows "(s,t) \<Turnstile> NewLeaderHasExpectedLastPublishedVersion$"
proof -
  from assms
  have  hyp1: "\<And>n. \<lbrakk> electionWon s n; lastAcceptedTerm s n \<noteq> currentTerm s n \<rbrakk>
        \<Longrightarrow> lastPublishedVersion s n \<in> { lastAcceptedVersion s n, Suc (lastAcceptedVersion s n) }"
    unfolding NewLeaderHasExpectedLastPublishedVersion_def
    by metis+

  {
    fix n
    assume prem: "electionWon t n" "lastAcceptedTerm t n \<noteq> currentTerm t n"
    from Next hyp1 prem have "lastPublishedVersion t n \<in> { lastAcceptedVersion t n, Suc (lastAcceptedVersion t n) }"
    proof (cases rule: square_Next_cases)
      case (HandleStartJoin nf nm tm newJoinRequest)
      with hyp1 prem show ?thesis by (cases "nf = n", auto)
    next
      case (RestartNode nr)
      with hyp1 prem show ?thesis by (cases "nr = n", auto)
    next
      case (HandlePublishRequest nf nm newVersion newValue newConfig commConfig)
      with hyp1 prem show ?thesis by (cases "nf = n", auto)
    qed auto
  }
  thus ?thesis by (auto simp add: NewLeaderHasExpectedLastPublishedVersion_def)
qed

lemma NewLeaderSentNoMessagesYetBelow_step:
  assumes "s \<Turnstile> NewLeaderSentNoMessagesYetBelow termBound"
  assumes "s \<Turnstile> PublishRequestImpliesElectionWonBelow termBound"
  assumes "t \<Turnstile> OneMasterPerTermBelow termBound" (* DANGER - need to show this for the after state first *)
  assumes "s \<Turnstile> PublishRequestFromHistoricalLeader"
  assumes "s \<Turnstile> ElectionWonImpliesStartedJoin"
  assumes "s \<Turnstile> LeaderHistoryFaithful"
  shows "(s,t) \<Turnstile> NewLeaderSentNoMessagesYetBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>n m. \<lbrakk> electionWon s n; lastAcceptedTerm s n \<noteq> currentTerm s n;
                       lastAcceptedVersion s n = lastPublishedVersion s n;
                       currentTerm s n < termBound;
                       m \<in> sentPublishRequests s \<rbrakk> \<Longrightarrow> term m \<noteq> currentTerm s n"
    and hyp2: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound; currentTerm s (source m) = term m;
                     startedJoinSinceLastReboot s (source m) \<rbrakk> \<Longrightarrow> electionWon s (source m)"
    and hyp3: "\<And>n1 n2 tm. \<lbrakk> tm < termBound; (tm, n1) \<in> leaderHistory t; (tm, n2) \<in> leaderHistory t \<rbrakk> \<Longrightarrow> n1 = n2"
    and hyp4: "\<And>m. m \<in> sentPublishRequests s \<Longrightarrow> (term m, source m) \<in> leaderHistory s"
    and hyp5: "\<And>n. electionWon s n \<Longrightarrow> startedJoinSinceLastReboot s n"
    and hyp6: "\<And>n. electionWon s n \<Longrightarrow> (currentTerm s n, n) \<in> leaderHistory s"
    unfolding NewLeaderSentNoMessagesYetBelow_def PublishRequestImpliesElectionWonBelow_def OneMasterPerTermBelow_def
      PublishRequestFromHistoricalLeader_def ElectionWonImpliesStartedJoin_def LeaderHistoryFaithful_def
    by metis+

  {
    fix n m
    assume prem: "electionWon t n" "lastAcceptedTerm t n \<noteq> currentTerm t n"
      "lastAcceptedVersion t n = lastPublishedVersion t n"
      "currentTerm t n < termBound"
      "m \<in> sentPublishRequests t"
    from Next hyp1 prem
    have "term m \<noteq> currentTerm t n"
    proof (cases rule: square_Next_cases)
      case (HandleJoinRequest nf nm laTerm_m laVersion_m)
      show ?thesis
      proof (cases "nm = n")
        case False
        with prem have "term m \<noteq> currentTerm s n" by (intro hyp1, auto simp add: HandleJoinRequest)
        thus ?thesis by (simp add: HandleJoinRequest)
      next
        case nm_eq_n: True

        have "term m \<noteq> currentTerm s n"
        proof (cases "electionWon s n")
          case True
          with prem show ?thesis
            by (intro hyp1, simp_all add: HandleJoinRequest nm_eq_n)
        next
          case False
          show "term m \<noteq> currentTerm s n"
          proof (intro notI)
            assume term_eq: "term m = currentTerm s n"
            have n_eq_source: "n = source m"
            proof (intro hyp3)
              from prem show "currentTerm t n < termBound" by simp
              from prem show "(currentTerm t n, n) \<in> leaderHistory t" by (auto simp add: HandleJoinRequest nm_eq_n)
              from prem have "(term m, source m) \<in> leaderHistory s"
                by (intro hyp4, auto simp add: HandleJoinRequest)
              with term_eq show "(currentTerm t n, source m) \<in> leaderHistory t" by (auto simp add: HandleJoinRequest)
            qed
            have "electionWon s (source m)"
            proof (intro hyp2)
              from prem show "m \<in> sentPublishRequests s" by (auto simp add: HandleJoinRequest)
              from prem show "term m < termBound" by (simp add: term_eq HandleJoinRequest)
              from prem n_eq_source show "currentTerm s (source m) = term m" by (simp add: term_eq HandleJoinRequest)
              from HandleJoinRequest show "startedJoinSinceLastReboot s (source m)"
                by (simp add: nm_eq_n n_eq_source)
            qed
            with False show False by (simp add: n_eq_source)
          qed
        qed
        thus ?thesis by (simp add: HandleJoinRequest)
      qed
    next
      case (ClientRequest nm v vs newPublishVersion newPublishRequests newEntry matchingElems newTransitiveElems)

      with prem consider
        (1) "nm = n" (* contradicts lastAcceptedVersion t n = lastPublishedVersion t n *)
        | (2) "nm \<noteq> n" "m \<in> sentPublishRequests s" (* reduces to previous case *)
        | (3) "nm \<noteq> n" "m \<in> newPublishRequests" (* ? *) 
        by auto
      hence "term m \<noteq> currentTerm s n"
      proof cases
        case 1
        with ClientRequest have "lastAcceptedVersion t n \<noteq> lastPublishedVersion t n" by auto
        with prem show ?thesis by simp
      next
        case 2
        show ?thesis using prem unfolding ClientRequest by (intro hyp1, auto simp add: 2)
      next
        case 3
        show ?thesis
        proof (intro notI)
          assume term_eq: "term m = currentTerm s n"
          have "n = nm"
          proof (intro hyp3)
            from prem show "currentTerm t n < termBound" by simp
            from prem have "(currentTerm s n, n) \<in> leaderHistory s" by (intro hyp6, simp add: ClientRequest)
            thus "(currentTerm t n, n) \<in> leaderHistory t" by (simp add: ClientRequest)
            from ClientRequest have "(currentTerm s nm, nm) \<in> leaderHistory s" by (intro hyp6, simp add: ClientRequest)
            with term_eq 3 show "(currentTerm t n, nm) \<in> leaderHistory t" by (auto simp add: ClientRequest)
          qed
          with 3 show False by simp
        qed
      qed
      thus ?thesis by (simp add: ClientRequest)
    next
      case (HandlePublishRequest nf nm newVersion newValue newConfig commConfig)
      show ?thesis
      proof (cases "nf = n")
        case False
        with HandlePublishRequest prem have "term m \<noteq> currentTerm s n"
          by (intro hyp1, auto)
        thus ?thesis by (simp add: HandlePublishRequest)
      next
        case True
        have "lastAcceptedTerm t n = currentTerm t n"
          by (simp add: HandlePublishRequest True)
        with prem show ?thesis by simp
      qed
    next
      case (RestartNode nr)
      with hyp1 prem show ?thesis by (cases "n = nr", auto)
    qed auto
  }
  thus ?thesis unfolding NewLeaderSentNoMessagesYetBelow_def by simp
qed

lemma NewLeaderCanOnlySendOneMessageBelow_step:
  assumes "s \<Turnstile> NewLeaderCanOnlySendOneMessageBelow termBound"
  assumes "s \<Turnstile> NewLeaderSentNoMessagesYetBelow termBound"
  assumes "s \<Turnstile> PublishRequestImpliesElectionWonBelow termBound"
  shows "(s,t) \<Turnstile> NewLeaderCanOnlySendOneMessageBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound;
                     term m = currentTerm s (source m);
                     electionWon s (source m);
                     currentTerm s (source m) \<noteq> lastAcceptedTerm s (source m) \<rbrakk>
      \<Longrightarrow> version m = lastPublishedVersion s (source m)"
    and hyp2: "\<And>n m. \<lbrakk> electionWon s n; lastAcceptedTerm s n \<noteq> currentTerm s n;
                       lastAcceptedVersion s n = lastPublishedVersion s n;
                       currentTerm s n < termBound;
                       m \<in> sentPublishRequests s \<rbrakk> \<Longrightarrow> term m \<noteq> currentTerm s n"
    and hyp3: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound; currentTerm s (source m) = term m;
                     startedJoinSinceLastReboot s (source m) \<rbrakk> \<Longrightarrow> electionWon s (source m)"
    unfolding NewLeaderCanOnlySendOneMessageBelow_def NewLeaderSentNoMessagesYetBelow_def
      PublishRequestImpliesElectionWonBelow_def
    by metis+

  {
    fix m
    assume prem: "m \<in> sentPublishRequests t" "term m < termBound"
      "term m = currentTerm t (source m)"
      "electionWon t (source m)"
      "currentTerm t (source m) \<noteq> lastAcceptedTerm t (source m)"
    from Next hyp1 prem have "version m = lastPublishedVersion t (source m)"
    proof (cases rule: square_Next_cases)
      case (HandleStartJoin nf nm tm newJoinRequest)
      with hyp1 prem show ?thesis by (cases "nf = source m", clarify, auto)
    next
      case (HandleJoinRequest nf nm laTerm_m laVersion_m)
      show ?thesis
      proof (cases "nm = source m")
        case False with HandleJoinRequest hyp1 prem show ?thesis by auto
      next
        case True
        have "electionWon s (source m)"
        proof (intro hyp3)
          from prem show "term m < termBound" "currentTerm s (source m) = term m" "m \<in> sentPublishRequests s"
            by (auto simp add: HandleJoinRequest)
          from HandleJoinRequest show "startedJoinSinceLastReboot s (source m)" by (simp add: True)
        qed
        with HandleJoinRequest hyp1 prem show ?thesis by auto
      qed
    next
      case (ClientRequest nm v vs newPublishVersion newPublishRequests newEntry matchingElems newTransitiveElems)
      show ?thesis
      proof (cases "nm = source m")
        case False
        with ClientRequest hyp1 prem show ?thesis by auto
      next
        case True
        from ClientRequest prem have "m \<in> sentPublishRequests s \<or> m \<in> newPublishRequests" by auto
        thus ?thesis
        proof (elim disjE)
          assume m_msg: "m \<in> sentPublishRequests s"
          have "term m \<noteq> currentTerm s (source m)"
          proof (intro hyp2 m_msg prem)
            from prem show "currentTerm s (source m) < termBound"
              "lastAcceptedTerm s (source m) \<noteq> currentTerm s (source m)"
              "electionWon s (source m)"
              by (auto simp add: ClientRequest)
            from ClientRequest show "lastAcceptedVersion s (source m) = lastPublishedVersion s (source m)" by (simp add: True)
          qed
          with prem show ?thesis by (simp add: ClientRequest)
        next
          assume m_new: "m \<in> newPublishRequests"
          thus ?thesis by (auto simp add: ClientRequest)
        qed
      qed
    next
      case (HandlePublishRequest nf nm newVersion newValue newConfig commConfig)
      show ?thesis apply (cases "nf = source m") using hyp1 prem HandlePublishRequest by simp_all
    next
      case (RestartNode nr)
      with hyp1 prem show ?thesis by (cases "nr = source m", clarify, simp)
    qed auto
  }
  thus ?thesis unfolding NewLeaderCanOnlySendOneMessageBelow_def by simp
qed

lemma LeaderCannotPublishWithoutAcceptingPreviousRequestBelow_step:
  assumes "s \<Turnstile> LeaderCannotPublishWithoutAcceptingPreviousRequestBelow termBound"
  assumes "s \<Turnstile> PublishRequestSentByMasterBelow termBound"
  assumes "s \<Turnstile> PublishRequestVersionAtMostSenderBelow termBound"
  assumes "s \<Turnstile> ElectionWonImpliesStartedJoin"
  assumes "s \<Turnstile> NewLeaderCanOnlySendOneMessageBelow termBound"
  shows "(s,t) \<Turnstile> LeaderCannotPublishWithoutAcceptingPreviousRequestBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>n. \<lbrakk> electionWon s n; currentTerm s n < termBound \<rbrakk>
    \<Longrightarrow> lastPublishedVersion s n \<in> {lastAcceptedVersion s n, Suc (lastAcceptedVersion s n)}"
    and hyp2: "\<And>m n. \<lbrakk> m \<in> sentPublishRequests s; term m = currentTerm s n; term m < termBound; electionWon s n \<rbrakk>
    \<Longrightarrow> n = source m"
    and hyp3: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound \<rbrakk>
    \<Longrightarrow> msgTermVersion m \<le> termVersion (source m) s"
    and hyp4: "\<And>n. electionWon s n \<Longrightarrow> startedJoinSinceLastReboot s n"
    and hyp5: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound;
                     term m = currentTerm s (source m);
                     electionWon s (source m);
                     currentTerm s (source m) \<noteq> lastAcceptedTerm s (source m) \<rbrakk>
      \<Longrightarrow> version m = lastPublishedVersion s (source m)"
    unfolding LeaderCannotPublishWithoutAcceptingPreviousRequestBelow_def PublishRequestSentByMasterBelow_def
      ElectionWonImpliesStartedJoin_def PublishRequestVersionAtMostSenderBelow_def
      NewLeaderCanOnlySendOneMessageBelow_def
    by metis+

  {
    fix n
    assume prem: "electionWon t n" "currentTerm t n < termBound"
    from Next hyp1 prem
    have "lastPublishedVersion t n \<in> {lastAcceptedVersion t n, Suc (lastAcceptedVersion t n)}"
    proof (cases rule: square_Next_cases)
      case (HandleStartJoin nf nm tm newJoinRequest)
      with hyp1 prem show ?thesis by (cases "nf = n", auto)
    next
      case (RestartNode nr)
      with hyp1 prem show ?thesis by (cases "nr = n", auto)
    next
      case (HandlePublishRequest nf nm newVersion newValue newConfig commConfig)
      show ?thesis
      proof (cases "nf = n")
        case False with hyp1 prem HandlePublishRequest show ?thesis by simp
      next
        case nf_eq_n: True
        define msg where "msg \<equiv> \<lparr>source = nm, dest = nf, term = currentTerm s nf
          , payload = PublishRequest \<lparr>prq_version = newVersion, prq_value = newValue, prq_config = newConfig, prq_commConf = commConfig\<rparr>\<rparr>"
        from HandlePublishRequest prem
        have n_source: "n = source msg" by (intro hyp2, simp_all add: msg_def nf_eq_n)
        hence nm_eq_n: "nm = n" by (simp add: msg_def)

        from prem have n_properties: "startedJoinSinceLastReboot s n" "electionWon s n"
          using hyp4 unfolding HandlePublishRequest by simp_all 

        from HandlePublishRequest prem
        have "msgTermVersion msg \<le> termVersion (source msg) s"
          by (intro hyp3, simp_all add: msg_def nf_eq_n)
        hence "newVersion \<le> lastPublishedVersion s n"
          by (auto simp add: msgTermVersion_def msg_def termVersion_def n_properties nf_eq_n nm_eq_n less_eq_TermVersion_def)

        show ?thesis
        proof (cases "currentTerm s nf = lastAcceptedTerm s nf")
          case False
          have "version msg = lastPublishedVersion s (source msg)"
          proof (intro hyp5)
            from HandlePublishRequest show "msg \<in> sentPublishRequests s" by (auto simp add: msg_def)
            from prem show "term msg < termBound" "electionWon s (source msg)" "term msg = currentTerm s (source msg)" 
              by (simp_all add: msg_def nf_eq_n nm_eq_n HandlePublishRequest)
            from False show "currentTerm s (source msg) \<noteq> lastAcceptedTerm s (source msg)"
              by (simp add: msg_def nm_eq_n nf_eq_n)
          qed
          thus ?thesis
            by (simp add: msg_def nm_eq_n HandlePublishRequest nf_eq_n)
        next
          case True
          with HandlePublishRequest have "lastAcceptedVersion s nf < newVersion" by simp
          also note `newVersion \<le> lastPublishedVersion s n`
          finally have "lastAcceptedVersion s n \<noteq> lastPublishedVersion s n" by (simp add: nf_eq_n)

          moreover from prem
          have "lastPublishedVersion s n \<in> {lastAcceptedVersion s n, Suc (lastAcceptedVersion s n)}"
            by (intro hyp1, simp_all add: HandlePublishRequest)
          ultimately have "lastPublishedVersion s n = Suc (lastAcceptedVersion s n)" by simp

          with `lastAcceptedVersion s nf < newVersion`
          have "lastPublishedVersion s n \<le> newVersion" by (simp add: nf_eq_n)
          with `newVersion \<le> lastPublishedVersion s n`
          have "lastPublishedVersion s n = newVersion" by simp
          thus ?thesis by (simp add: HandlePublishRequest nf_eq_n)
        qed
      qed

    qed auto
  }
  thus ?thesis by (auto simp add: LeaderCannotPublishWithoutAcceptingPreviousRequestBelow_def)
qed

lemma LastPublishedVersionImpliesLastPublishedConfigurationBelow_step:
  assumes "s \<Turnstile> LastPublishedVersionImpliesLastPublishedConfigurationBelow termBound"
  assumes "s \<Turnstile> PublishRequestImpliesElectionWonBelow termBound"
  assumes "s \<Turnstile> PublishRequestVersionAtMostSenderBelow termBound"
  assumes "s \<Turnstile> ElectionWonImpliesStartedJoin"
  shows "(s,t) \<Turnstile> LastPublishedVersionImpliesLastPublishedConfigurationBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound;
                     term m = currentTerm s (source m);
                     electionWon s (source m);
                     version m = lastPublishedVersion s (source m) \<rbrakk>
      \<Longrightarrow> config m = lastPublishedConfiguration s (source m)"
    and hyp2: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound; currentTerm s (source m) = term m;
                     startedJoinSinceLastReboot s (source m) \<rbrakk> \<Longrightarrow> electionWon s (source m)"
    and hyp3: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound \<rbrakk>
    \<Longrightarrow> msgTermVersion m \<le> termVersion (source m) s"
    and hyp4: "\<And>n. electionWon s n \<Longrightarrow> startedJoinSinceLastReboot s n"
    unfolding LastPublishedVersionImpliesLastPublishedConfigurationBelow_def
      PublishRequestImpliesElectionWonBelow_def PublishRequestVersionAtMostSenderBelow_def
      ElectionWonImpliesStartedJoin_def
    by metis+

  {
    fix m
    assume prem: "m \<in> sentPublishRequests t" "term m < termBound"
      "term m = currentTerm t (source m)"
      "electionWon t (source m)"
      "version m = lastPublishedVersion t (source m)"
    from Next hyp1 prem have "config m = lastPublishedConfiguration t (source m)"
    proof (cases rule: square_Next_cases)
      case (HandleStartJoin nf nm tm newJoinRequest)
      show ?thesis apply (cases "nf = source m") using hyp1 prem HandleStartJoin by simp_all
    next
      case (RestartNode nr)
      show ?thesis
      proof (cases "nr = source m")
        case False
        with prem hyp1 RestartNode show ?thesis by simp
      next
        case True
        with prem show ?thesis by (simp add: RestartNode)
      qed
    next
      case (HandleJoinRequest nf nm laTerm_m laVersion_m)
      show ?thesis
      proof (cases "nm = source m")
        case False with HandleJoinRequest hyp1 prem show ?thesis by auto
      next
        case True
        have "electionWon s (source m)"
        proof (intro hyp2)
          from prem show "term m < termBound" "currentTerm s (source m) = term m" "m \<in> sentPublishRequests s"
            by (auto simp add: HandleJoinRequest)
          from HandleJoinRequest show "startedJoinSinceLastReboot s (source m)" by (simp add: True)
        qed
        with HandleJoinRequest hyp1 prem show ?thesis by auto
      qed   
    next
      case (ClientRequest nm v vs newPublishVersion newPublishRequests newEntry matchingElems newTransitiveElems)
      from prem have "m \<in> sentPublishRequests s \<or> m \<in> newPublishRequests" by (auto simp add: ClientRequest)
      thus ?thesis
      proof (elim disjE)
        assume "m \<in> newPublishRequests"
        thus ?thesis by (auto simp add: ClientRequest)
      next
        assume m_msg: "m \<in> sentPublishRequests s"
        show ?thesis
        proof (cases "source m = nm")
          case False
          with prem have "config m = lastPublishedConfiguration s (source m)"
            by (intro hyp1, auto simp add: ClientRequest)
          thus ?thesis by (simp add: ClientRequest False)
        next
          case True
          from ClientRequest hyp4 have startedJoinSinceLastReboot_nm: "startedJoinSinceLastReboot s nm" by simp_all
          have "msgTermVersion m \<le> termVersion (source m) s" by (intro hyp3 m_msg prem)
          thus ?thesis
            by (simp add: msgTermVersion_def termVersion_def True startedJoinSinceLastReboot_nm prem less_eq_TermVersion_def ClientRequest)
        qed
      qed
    qed auto
  }
  thus ?thesis by (auto simp add: LastPublishedVersionImpliesLastPublishedConfigurationBelow_def)
qed

lemma LastAcceptedConfigurationEitherCommittedOrPublishedBelow_step:
  assumes "s \<Turnstile> LastAcceptedConfigurationEitherCommittedOrPublishedBelow termBound"
  assumes "s \<Turnstile> PublishRequestSentByMasterBelow termBound"
  assumes "s \<Turnstile> PublishRequestVersionAtMostSenderBelow termBound"
  assumes "s \<Turnstile> ElectionWonImpliesStartedJoin"
  assumes "s \<Turnstile> NewLeaderCanOnlySendOneMessageBelow termBound"
  assumes "s \<Turnstile> LeaderCannotPublishWithoutAcceptingPreviousRequestBelow termBound"
  assumes "s \<Turnstile> LastPublishedVersionImpliesLastPublishedConfigurationBelow termBound"
  shows "(s,t) \<Turnstile> LastAcceptedConfigurationEitherCommittedOrPublishedBelow termBound$"
proof -
  from assms
  have  hyp1: "\<And>n. \<lbrakk> electionWon s n; currentTerm s n < termBound \<rbrakk>
      \<Longrightarrow> lastAcceptedConfiguration s n \<in> { lastCommittedConfiguration s n, lastPublishedConfiguration s n }"
    and hyp2: "\<And>m n. \<lbrakk> m \<in> sentPublishRequests s; term m = currentTerm s n; term m < termBound; electionWon s n \<rbrakk>
    \<Longrightarrow> n = source m"
    and hyp3: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound \<rbrakk>
    \<Longrightarrow> msgTermVersion m \<le> termVersion (source m) s"
    and hyp4: "\<And>n. electionWon s n \<Longrightarrow> startedJoinSinceLastReboot s n"
    and hyp5: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound;
                     term m = currentTerm s (source m);
                     electionWon s (source m);
                     currentTerm s (source m) \<noteq> lastAcceptedTerm s (source m) \<rbrakk>
      \<Longrightarrow> version m = lastPublishedVersion s (source m)"
    and hyp6: "\<And>n. \<lbrakk> electionWon s n; currentTerm s n < termBound \<rbrakk>
    \<Longrightarrow> lastPublishedVersion s n \<in> {lastAcceptedVersion s n, Suc (lastAcceptedVersion s n)}"
    and hyp7: "\<And>m. \<lbrakk> m \<in> sentPublishRequests s; term m < termBound;
                     term m = currentTerm s (source m);
                     electionWon s (source m);
                     version m = lastPublishedVersion s (source m) \<rbrakk>
      \<Longrightarrow> config m = lastPublishedConfiguration s (source m)"
    unfolding LastAcceptedConfigurationEitherCommittedOrPublishedBelow_def PublishRequestSentByMasterBelow_def
      PublishRequestVersionAtMostSenderBelow_def ElectionWonImpliesStartedJoin_def
      NewLeaderCanOnlySendOneMessageBelow_def LeaderCannotPublishWithoutAcceptingPreviousRequestBelow_def
      LastPublishedVersionImpliesLastPublishedConfigurationBelow_def
    by metis+

  {
    fix n
    assume prem: "electionWon t n" "currentTerm t n < termBound"
    from Next hyp1 prem have "lastAcceptedConfiguration t n \<in> { lastCommittedConfiguration t n, lastPublishedConfiguration t n }"
    proof (cases rule: square_Next_cases)
      case (HandleStartJoin nf nm tm newJoinRequest)
      show ?thesis
      proof (cases "nf = n")
        case False with hyp1 prem HandleStartJoin show ?thesis by simp
      next
        case True with prem HandleStartJoin show ?thesis by simp
      qed
    next
      case (HandlePublishRequest nf nm newVersion newValue newConfig commConfig)
      show ?thesis
      proof (cases "nf = n")
        case False with hyp1 prem HandlePublishRequest show ?thesis by simp
      next
        case nf_eq_n: True
        define msg where "msg \<equiv> \<lparr>source = nm, dest = nf, term = currentTerm s nf
          , payload = PublishRequest \<lparr>prq_version = newVersion, prq_value = newValue, prq_config = newConfig, prq_commConf = commConfig\<rparr>\<rparr>"
        from HandlePublishRequest prem
        have n_source: "n = source msg" by (intro hyp2, simp_all add: msg_def nf_eq_n)
        hence nm_eq_n: "nm = n" by (simp add: msg_def)

        from prem have n_properties: "startedJoinSinceLastReboot s n" "electionWon s n"
          using hyp4 unfolding HandlePublishRequest by simp_all

        from HandlePublishRequest prem
        have "msgTermVersion msg \<le> termVersion (source msg) s"
          by (intro hyp3, simp_all add: msg_def nf_eq_n)
        hence "newVersion \<le> lastPublishedVersion s n"
          by (auto simp add: msgTermVersion_def msg_def termVersion_def n_properties nm_eq_n nf_eq_n less_eq_TermVersion_def)

        have "lastPublishedVersion s n = newVersion" 
        proof (cases "currentTerm s nf = lastAcceptedTerm s nf")
          case False
          have "version msg = lastPublishedVersion s (source msg)"
          proof (intro hyp5)
            from HandlePublishRequest show "msg \<in> sentPublishRequests s" by (auto simp add: msg_def)
            from prem show "term msg < termBound" "electionWon s (source msg)" "term msg = currentTerm s (source msg)"
              by (auto simp add: msg_def HandlePublishRequest nf_eq_n nm_eq_n)
            from False show "currentTerm s (source msg) \<noteq> lastAcceptedTerm s (source msg)"
              by (simp add: msg_def nm_eq_n nf_eq_n)
          qed
          thus "lastPublishedVersion s n = newVersion" by (simp add: msg_def nm_eq_n)
        next
          case True
          with HandlePublishRequest have "lastAcceptedVersion s nf < newVersion" by simp
          with `newVersion \<le> lastPublishedVersion s n`
          have "lastAcceptedVersion s n \<noteq> lastPublishedVersion s n" by (simp add: nf_eq_n)

          moreover from prem have "lastPublishedVersion s n \<in> {lastAcceptedVersion s n, Suc (lastAcceptedVersion s n)}"
            by (intro hyp6, auto simp add: HandlePublishRequest)
          ultimately have "lastPublishedVersion s n = Suc (lastAcceptedVersion s n)" by auto
          with `newVersion \<le> lastPublishedVersion s n` `lastAcceptedVersion s nf < newVersion`
          show "lastPublishedVersion s n = newVersion" by (auto simp add: nf_eq_n)
        qed

        have "newConfig = config msg" by (simp add: msg_def)
        also have "config msg = lastPublishedConfiguration s (source msg)"
        proof (intro hyp7)
          from HandlePublishRequest show "msg \<in> sentPublishRequests s" by (auto simp add: msg_def)
          from prem show "term msg < termBound" "electionWon s (source msg)" "term msg = currentTerm s (source msg)"
            by (auto simp add: msg_def HandlePublishRequest nf_eq_n nm_eq_n)
          from `lastPublishedVersion s n = newVersion`
          show "version msg = lastPublishedVersion s (source msg)"
            by (simp add: msg_def nm_eq_n nf_eq_n)
        qed
        finally have "newConfig = lastPublishedConfiguration s n" by (simp add: msg_def nm_eq_n)
        thus ?thesis by (simp add: HandlePublishRequest nf_eq_n)
      qed
    next
      case (RestartNode nr)
      with hyp1 prem show ?thesis by (cases "nr = n", auto)
    qed auto
  }
  thus ?thesis by (auto simp add: LastAcceptedConfigurationEitherCommittedOrPublishedBelow_def)
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
    by (auto simp add: Spec_def Initial_def Init_def JoinRequestsAtMostCurrentTerm_def sentJoins_def)

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
    by (auto simp add: Spec_def Initial_def Init_def JoinRequestsUniquePerTerm_def sentJoins_def)

  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> stable JoinRequestsUniquePerTerm"
  proof (intro Stable actionI temp_impI)
    from imp_box_before_afterI [OF JoinRequestsAtMostCurrentTerm_INV]
    show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> \<box>([Next]_vars \<and> $JoinRequestsAtMostCurrentTerm)"
      by (auto simp add: Spec_def Valid_def more_temp_simps)

    fix s t assume "(s,t) \<Turnstile> $JoinRequestsUniquePerTerm \<and> [Next]_vars \<and> $JoinRequestsAtMostCurrentTerm"
    thus "(s,t) \<Turnstile> JoinRequestsUniquePerTerm$" by (intro JoinRequestsUniquePerTerm_step, auto)
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

lemma JoinVotesFaithful_INV: "\<turnstile> Spec \<longrightarrow> \<box>JoinVotesFaithful"
proof invariant
  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> Init JoinVotesFaithful"
    by (auto simp add: Spec_def Initial_def Init_def JoinVotesFaithful_def)

  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> stable JoinVotesFaithful"
  proof (intro Stable actionI temp_impI)
    from imp_box_before_afterI [OF LastAcceptedTermInPast_INV]
    show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> \<box>([Next]_vars \<and> $LastAcceptedTermInPast)"
      by (auto simp add: Spec_def Valid_def more_temp_simps)

    fix s t assume "(s,t) \<Turnstile> $JoinVotesFaithful \<and> [Next]_vars \<and> $LastAcceptedTermInPast"
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

      with s obtain joinPayload where msg: "\<lparr>source = nf, dest = nm, term = currentTerm s nm, payload = Join joinPayload\<rparr> \<in> sentJoins s"
        by (auto simp add: JoinVotesFaithful_def)

      define P where "P \<equiv> \<lambda>m. source m = nf \<and> dest m = nm \<and> term m = currentTerm s nm \<and> m \<in> sentJoins s"

      have 1: "TheJoin nf nm s = The P" by (simp add: P_def TheJoin_def)
      have "P (TheJoin nf nm s)"
        unfolding 1 
      proof (intro theI [where P = P])
        from msg show "P \<lparr>source = nf, dest = nm, term = currentTerm s nm, payload = Join joinPayload\<rparr>" by (simp add: P_def)
        fix m' assume m': "P m'"

        from s have eqI: "\<And>m1 m2. \<lbrakk> m1 \<in> sentJoins s; m2 \<in> sentJoins s; source m1 = source m2; term m1 = term m2 \<rbrakk> \<Longrightarrow> m1 = m2"
          by (auto simp add: JoinRequestsUniquePerTerm_def)

        from m' msg show "m' = \<lparr>source = nf, dest = nm, term = currentTerm s nm, payload = Join joinPayload\<rparr>"
          by (intro eqI, auto simp add: P_def)
      qed
      thus "source (TheJoin nf nm s) = nf \<and> dest (TheJoin nf nm s) = nm
          \<and> term (TheJoin nf nm s) = currentTerm s nm \<and> TheJoin nf nm s \<in> sentJoins s"
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
          CurrentConfigurationSource_def CurrentConfigurationMsgSource_def CommittedConfigurations_def sentPublishRequests_def)

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

lemma PublishedConfigurationsValid_INV: "\<turnstile> Spec \<longrightarrow> \<box>PublishedConfigurationsValid"
proof invariant
  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> Init PublishedConfigurationsValid"
    by (auto simp add: Spec_def Initial_def Init_def PublishedConfigurationsValid_def PublishedConfigurations_def sentPublishRequests_def)

  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> stable PublishedConfigurationsValid"
  proof (intro Stable actionI temp_impI)
    show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> \<box>[Next]_vars"
      by (auto simp add: Spec_def Valid_def more_temp_simps)

    fix s t assume "(s,t) \<Turnstile> $PublishedConfigurationsValid \<and> [Next]_vars"
    thus "(s,t) \<Turnstile> PublishedConfigurationsValid$" by (intro PublishedConfigurationsValid_step, auto)
  qed
qed

lemma PublicationsInPastTerm_INV: "\<turnstile> Spec \<longrightarrow> \<box>PublicationsInPastTerm"
proof invariant
  show "\<And>sigma. sigma \<Turnstile> Spec \<Longrightarrow> sigma \<Turnstile> Init PublicationsInPastTerm"
    by (auto simp add: Spec_def Initial_def Init_def PublicationsInPastTerm_def sentPublishRequests_def)

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
    by (auto simp add: Spec_def Initial_def Init_def PublishRequestFromHistoricalLeader_def sentPublishRequests_def)

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

end

end
