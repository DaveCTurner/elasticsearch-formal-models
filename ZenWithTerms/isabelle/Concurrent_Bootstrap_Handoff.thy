theory Concurrent_Bootstrap_Handoff
  imports Bootstrap_First_Commit
begin

section \<open>Interleaved rounds and the common-seed handoff\<close>

text \<open>
  An interleaved bootstrap trace starts with configured local captures and
  no publications. Its startup step may use a different seed when the
  lineage is empty. This overapproximates the choice in CoordinationState:
  the default election strategy checks the candidate's local committed and
  accepted configurations, and the first publication carries its local
  committed configuration. A nonempty publication's configuration is in
  the request, regardless of the receiver's initial capture. The model
  admits delayed votes and receipts, term changes, and reboot. It does not
  assume that the first election commits, or that only one round runs.
\<close>

abbreviation interleaved_bootstrap_step where
  "interleaved_bootstrap_step s s' \<equiv> \<exists>D. transition D s s'"

definition compatible_bootstrap_evidence where
  "compatible_bootstrap_evidence C s \<longleftrightarrow>
    (\<forall>c t e. certificate s (c,t) = Some e \<and> elected_from e = [] \<longrightarrow> elected_committed e = C) \<and>
    (\<forall>p. [p] \<in> publications s \<longrightarrow> pub_previous p = C)"

lemma compatible_bootstrap_evidenceD:
  assumes "compatible_bootstrap_evidence C s"
  shows "certificate s (c,t) = Some e \<Longrightarrow> elected_from e = [] \<Longrightarrow> elected_committed e = C"
    "[p] \<in> publications s \<Longrightarrow> pub_previous p = C"
  using assms unfolding compatible_bootstrap_evidence_def by blast+

definition bootstrap_seed_view where
  "bootstrap_seed_view C s = s\<lparr>committed_config :=
     (\<lambda>n. if durable_history s n = [] then C else committed_config s n)\<rparr>"

lemma tip_seed_irrelevant:
  assumes "h \<noteq> []"
  shows "at_tip C f h = at_tip D f h"
  using assms by (induction h) auto

lemma empty_bootstrap_history_has_capture:
  assumes "rtranclp interleaved_bootstrap_step (installed_bootstrap F) s"
  shows "[] \<notin> publications s" "quorum_commits s \<subseteq> publications s"
    "\<And>n. durable_history s n = [] \<Longrightarrow> committed_config s n = F n"
proof -
  have "[] \<notin> publications s \<and> quorum_commits s \<subseteq> publications s \<and>
    (\<forall>n. durable_history s n = [] \<longrightarrow> committed_config s n = F n)"
    using assms
  proof (induction rule: rtranclp_induct)
    case base
    show ?case by (simp add: installed_bootstrap_def bootstrapped_def)
  next
    case (step s s')
    from step.hyps(2) obtain D where move: "transition D s s'" by blast
    show ?case using move step.IH by cases (auto simp: fun_upd_apply)
  qed
  then show "[] \<notin> publications s" "quorum_commits s \<subseteq> publications s"
    "\<And>n. durable_history s n = [] \<Longrightarrow> committed_config s n = F n" by auto
qed

lemma bootstrap_evidence_survives:
  assumes "transition D s s'"
  shows "publications s \<subseteq> publications s'"
    "certificate s k = Some e \<Longrightarrow> certificate s' k = Some e"
  using assms by (cases; auto simp: fun_upd_apply)+

lemma bootstrap_evidence_backwards:
  assumes "transition D s s'" "compatible_bootstrap_evidence C s'"
  shows "compatible_bootstrap_evidence C s"
proof -
  have pubs: "[p] \<in> publications s'" if "[p] \<in> publications s" for p
    using bootstrap_evidence_survives(1)[OF assms(1)] that by blast
  have cert: "certificate s' (c,t) = Some e" if "certificate s (c,t) = Some e" for c t e
    by (rule bootstrap_evidence_survives(2)[OF assms(1) that])
  show ?thesis using assms(2) pubs cert unfolding compatible_bootstrap_evidence_def by blast
qed

lemma bootstrap_seed_receive:
  assumes nonempty: "h \<noteq> []"
  shows "bootstrap_seed_view C
    (s\<lparr>durable_history := (durable_history s)(n := h),
      committed_config := (committed_config s)(n := carried D h),
      acknowledgements := insert (n,h) (acknowledgements s)\<rparr>) =
    (bootstrap_seed_view C s)\<lparr>durable_history := (durable_history s)(n := h),
      committed_config := (committed_config (bootstrap_seed_view C s))(n := carried C h),
      acknowledgements := insert (n,h) (acknowledgements s)\<rparr>"
proof -
  have "(\<lambda>m. if ((durable_history s)(n := h)) m = [] then C else
      ((committed_config s)(n := carried D h)) m) =
      (\<lambda>m. if durable_history s m = [] then C else committed_config s m)(n := carried C h)"
    by (rule ext) (simp add: fun_upd_apply nonempty tip_seed_irrelevant[OF nonempty, of D pub_previous C])
  then show ?thesis by (simp add: bootstrap_seed_view_def cong: if_cong)
qed

lemma bootstrap_seed_apply:
  assumes nonempty: "durable_history s n \<noteq> []"
  shows "bootstrap_seed_view C
    (s\<lparr>committed_config := (committed_config s)(n := config_of D (durable_history s n))\<rparr>) =
    (bootstrap_seed_view C s)\<lparr>committed_config :=
      (committed_config (bootstrap_seed_view C s))(n := config_of C (durable_history s n))\<rparr>"
proof -
  have "(\<lambda>m. if durable_history s m = [] then C else
      ((committed_config s)(n := config_of D (durable_history s n))) m) =
      (\<lambda>m. if durable_history s m = [] then C else committed_config s m)
        (n := config_of C (durable_history s n))"
    by (rule ext) (simp add: fun_upd_apply nonempty tip_seed_irrelevant[OF nonempty, of D pub_config C])
  then show ?thesis by (simp add: bootstrap_seed_view_def cong: if_cong)
qed

lemma interleaved_bootstrap_projects:
  assumes move: "transition D s s'"
    and evidence: "compatible_bootstrap_evidence C s'"
    and proper: "[] \<notin> publications s" "quorum_commits s \<subseteq> publications s"
  shows "transition C (bootstrap_seed_view C s) (bootstrap_seed_view C s')"
  using move
proof cases
  case (start_join n t c)
  let ?x = "bootstrap_seed_view C s"
  let ?y = "?x\<lparr>node_term := (node_term ?x)(n := t),
    sent_joins := insert (n,c,t,position (durable_history ?x n)) (sent_joins ?x),
    joined_since_restart := insert n (joined_since_restart ?x)\<rparr>"
  have eq: "?y = bootstrap_seed_view C s'" unfolding start_join(1)
    by (rule dynamic_state.equality) (simp_all add: bootstrap_seed_view_def cong: if_cong)
  have lower: "node_term ?x n < t" using start_join(2) by (simp add: bootstrap_seed_view_def)
  from transition.start_join[where c=c and C=C, OF lower] show ?thesis unfolding eq .
next
  case (win c Q)
  let ?e = "\<lparr>elected_from = durable_history s c, elected_committed = committed_config s c, elected_votes = Q\<rparr>"
  have new: "certificate s' (c,node_term s c) = Some ?e" unfolding win(1) by simp
  have root: "committed_config s c = C" if "durable_history s c = []"
  proof -
    have "elected_from ?e = []" using that by simp
    then have "elected_committed ?e = C" by (rule compatible_bootstrap_evidenceD(1)[OF evidence new])
    then show ?thesis by simp
  qed
  have config: "committed_config (bootstrap_seed_view C s) c = committed_config s c"
    using root by (auto simp: bootstrap_seed_view_def)
  have quorum: "quorum (config_of C (durable_history s c)) Q"
  proof (cases "durable_history s c = []")
    case True
    with root[OF True] win(4) show ?thesis by simp
  next
    case False
    with tip_seed_irrelevant[OF False, of C pub_config D] win(5) show ?thesis by simp
  qed
  let ?x = "bootstrap_seed_view C s"
  have joined: "c \<in> joined_since_restart ?x" and no_cert: "certificate ?x (c,node_term ?x c) = None"
    using win(2,3) by (simp_all add: bootstrap_seed_view_def)
  have old_quorum: "quorum (committed_config ?x c) Q" using win(4) by (simp only: config)
  have new_quorum: "quorum (config_of C (durable_history ?x c)) Q"
    using quorum by (simp add: bootstrap_seed_view_def)
  have fresh: "fresh_votes ?x c (node_term ?x c) (durable_history ?x c) Q"
    using win(6) by (simp add: fresh_votes_def bootstrap_seed_view_def)
  let ?y = "?x\<lparr>certificate := (certificate ?x)((c,node_term ?x c) :=
      Some \<lparr>elected_from = durable_history ?x c, elected_committed = committed_config ?x c,
        elected_votes = Q\<rparr>), publication_tip := (publication_tip ?x)((c,node_term ?x c) := durable_history ?x c)\<rparr>"
  have eq: "?y = bootstrap_seed_view C s'" unfolding win(1)
    by (rule dynamic_state.equality) (simp_all add: root bootstrap_seed_view_def cong: if_cong)
  have "transition C ?x ?y" by (rule transition.win[OF joined no_cert old_quorum new_quorum fresh])
  then show ?thesis unfolding eq .
next
  case (publish c v cfg Q h payload)
  have root: "committed_config s c = C" if empty: "durable_history s c = []"
  proof -
    let ?p = "\<lparr>pub_term = node_term s c, pub_version = v, pub_payload = payload,
        pub_owner = c, pub_config = cfg, pub_previous = committed_config s c\<rparr>"
    from publish(1) have "h \<in> publications s'" by simp
    then have "[?p] \<in> publications s'" unfolding publish(8) empty by simp
    then have "pub_previous ?p = C" by (rule compatible_bootstrap_evidenceD(2)[OF evidence])
    then show ?thesis by simp
  qed
  have guard: "cfg \<noteq> config_of C (durable_history s c) \<longrightarrow>
    committed_config s c = config_of C (durable_history s c)"
  proof (cases "durable_history s c = []")
    case True
    from True root[OF True] show ?thesis by simp
  next
    case False
    then have "config_of C (durable_history s c) = config_of D (durable_history s c)"
      by (rule tip_seed_irrelevant)
    then show ?thesis using publish(5) by simp
  qed
  let ?x = "bootstrap_seed_view C s"
  let ?y = "?x\<lparr>publication_tip := (publication_tip ?x)((c,node_term ?x c) := h),
      publications := insert h (publications ?x)\<rparr>"
  have eq: "?y = bootstrap_seed_view C s'" unfolding publish(1)
    by (rule dynamic_state.equality) (simp_all add: bootstrap_seed_view_def cong: if_cong)
  have "transition C ?x ?y"
    by (rule transition.publish[where D=cfg and v=v and Q=Q and payload=payload],
        use guard publish(2-8) in \<open>simp_all add: root active_leader_def fresh_votes_def bootstrap_seed_view_def\<close>)
  then show ?thesis unfolding eq .
next
  case (receive h n)
  have proper_h: "h \<noteq> []" using receive(2) proper(1) by blast
  let ?x = "bootstrap_seed_view C s"
  have "transition C ?x (?x\<lparr>durable_history := (durable_history ?x)(n := h),
       committed_config := (committed_config ?x)(n := carried C h),
       acknowledgements := insert (n,h) (acknowledgements ?x)\<rparr>)"
    by (rule transition.receive, use receive(2-4) in \<open>simp_all add: bootstrap_seed_view_def\<close>)
  then show ?thesis unfolding receive(1) bootstrap_seed_receive[OF proper_h]
    by (simp add: bootstrap_seed_view_def)
next
  case (certify c h)
  have proper_h: "h \<noteq> []" using certify(4) proper(1) by blast
  have tips: "carried C h = carried D h" "config_of C h = config_of D h"
    by (rule tip_seed_irrelevant[OF proper_h])+
  have receipts: "joint_receipts C s h"
    using certify(7) by (simp add: joint_receipts_def tips)
  let ?x = "bootstrap_seed_view C s"
  let ?y = "?x\<lparr>quorum_commits := insert h (quorum_commits ?x)\<rparr>"
  have eq: "?y = bootstrap_seed_view C s'" unfolding certify(1)
    by (rule dynamic_state.equality) (simp_all add: bootstrap_seed_view_def cong: if_cong)
  have "transition C ?x ?y"
    by (rule transition.certify[where c=c], use certify(2-6) receipts in
        \<open>simp_all add: active_leader_def joint_receipts_def bootstrap_seed_view_def\<close>)
  then show ?thesis unfolding eq .
next
  case (apply_commit n)
  from proper(2) apply_commit(2) have "durable_history s n \<in> publications s" by (rule subsetD)
  with proper(1) have proper_h: "durable_history s n \<noteq> []" by auto
  let ?x = "bootstrap_seed_view C s"
  let ?y = "?x\<lparr>committed_config := (committed_config ?x)(n := config_of C (durable_history ?x n))\<rparr>"
  have eq: "?y = bootstrap_seed_view C s'"
    unfolding apply_commit(1) bootstrap_seed_apply[OF proper_h, where C=C and D=D]
    by (simp add: bootstrap_seed_view_def)
  have committed: "durable_history ?x n \<in> quorum_commits ?x"
    and current_term_eq: "term_of (durable_history ?x n) = node_term ?x n"
    and when_active: "active_leader ?x n \<longrightarrow> durable_history ?x n = publication_tip ?x (n,node_term ?x n)"
    using apply_commit(2-4) by (simp_all add: active_leader_def bootstrap_seed_view_def)
  from transition.apply_commit[where C=C, OF committed current_term_eq when_active] show ?thesis unfolding eq .
next
  case (reboot n)
  let ?x = "bootstrap_seed_view C s"
  have eq: "?x\<lparr>joined_since_restart := joined_since_restart ?x - {n}\<rparr> = bootstrap_seed_view C s'"
    unfolding reboot by (rule dynamic_state.equality) (simp_all add: bootstrap_seed_view_def cong: if_cong)
  from transition.reboot[where C=C and s="?x" and n=n] show ?thesis unfolding eq .
qed

theorem interleaved_bootstrap_seed_replay:
  assumes seed: "finite C" "C \<noteq> {}"
    and trace: "rtranclp interleaved_bootstrap_step (installed_bootstrap F) s"
    and evidence: "compatible_bootstrap_evidence C s"
  shows "dynamic_reachable C (bootstrap_seed_view C s)"
  using trace evidence
proof (induction rule: rtranclp_induct)
  case base
  have "bootstrap_seed_view C (installed_bootstrap F) = bootstrapped C"
    by (simp add: bootstrap_seed_view_def installed_bootstrap_def bootstrapped_def cong: if_cong)
  then show ?case using dynamic_reachable.boot[OF seed] by simp
next
  case (step s s')
  from step.hyps(2) obtain D where move: "transition D s s'" by blast
  have before: "dynamic_reachable C (bootstrap_seed_view C s)"
    by (rule step.IH, rule bootstrap_evidence_backwards[OF move step.prems])
  show ?case
    by (rule dynamic_reachable.advance[OF before interleaved_bootstrap_projects[OF move step.prems
      empty_bootstrap_history_has_capture(1,2)[OF step.hyps(1)]]])
qed

corollary compatible_interleaving_preserves_dynamic_safety:
  assumes seed: "finite C" "C \<noteq> {}"
    and trace: "rtranclp interleaved_bootstrap_step (installed_bootstrap F) s"
    and evidence: "compatible_bootstrap_evidence C s"
  shows "a \<in> quorum_commits s \<Longrightarrow> b \<in> quorum_commits s \<Longrightarrow> prefix a b \<or> prefix b a"
    "a \<in> publications s \<Longrightarrow> b \<in> publications s \<Longrightarrow> position a = position b \<Longrightarrow> a = b"
    "certificate s (c,t) = Some e \<Longrightarrow> certificate s (d,t) = Some f \<Longrightarrow> c = d"
  using dynamic_committed_states_form_chain[OF interleaved_bootstrap_seed_replay[OF seed trace evidence]]
    dynamic_unique_publication[OF interleaved_bootstrap_seed_replay[OF seed trace evidence]]
    dynamic_one_election_candidate_per_term[OF interleaved_bootstrap_seed_replay[OF seed trace evidence]]
  by (simp_all add: bootstrap_seed_view_def)

lemma common_seed_has_compatible_evidence:
  assumes reach: "dynamic_reachable C s"
  shows "compatible_bootstrap_evidence C s"
proof -
  from dynamic_invariants[OF reach] have lead: "leadership_ok C s" and pubs: "publications_ok C s" by blast+
  have cert: "elected_committed e = C" if "certificate s (c,t) = Some e" "elected_from e = []" for c t e
    using leadershipD(3)[OF lead that(1)] that(2) by (auto simp: effective_config_def)
  have root: "pub_previous p = C" if "[p] \<in> publications s" for p
  proof -
    from that have "[] @ [p] \<in> publications s" by simp
    from publicationsD(4)[OF pubs this] show ?thesis by (auto simp: valid_edge_def effective_config_def)
  qed
  show ?thesis using root cert unfolding compatible_bootstrap_evidence_def by blast
qed

theorem interleaved_bootstrap_handoff_iff:
  assumes seed: "finite C" "C \<noteq> {}"
    and trace: "rtranclp interleaved_bootstrap_step (installed_bootstrap F) s"
  shows "dynamic_reachable C s \<longleftrightarrow> compatible_bootstrap_evidence C s \<and>
    (\<forall>n. F n \<noteq> C \<longrightarrow> durable_history s n \<noteq> [])"
proof
  assume reach: "dynamic_reachable C s"
  from dynamic_invariants[OF reach] have journal: "journal_ok C s" by blast
  have "F n = C" if "durable_history s n = []" for n
    using journalD(3)[OF journal, of n] empty_bootstrap_history_has_capture(3)[OF trace that] that
    by (auto simp: effective_config_def)
  then show "compatible_bootstrap_evidence C s \<and>
    (\<forall>n. F n \<noteq> C \<longrightarrow> durable_history s n \<noteq> [])"
    using common_seed_has_compatible_evidence[OF reach] by blast
next
  assume compat: "compatible_bootstrap_evidence C s \<and>
    (\<forall>n. F n \<noteq> C \<longrightarrow> durable_history s n \<noteq> [])"
  have same: "bootstrap_seed_view C s = s"
    by (rule dynamic_state.equality)
      (use compat empty_bootstrap_history_has_capture(3)[OF trace] in
        \<open>auto simp: bootstrap_seed_view_def fun_eq_iff\<close>)
  from compat interleaved_bootstrap_seed_replay[OF seed trace] show "dynamic_reachable C s"
    by (simp add: same)
qed

corollary incompatible_bootstrap_evidence_prevents_later_handoff:
  assumes suffix: "rtranclp interleaved_bootstrap_step s s'"
    and incompatible: "\<not> compatible_bootstrap_evidence C s"
  shows "\<not> dynamic_reachable C s'"
proof
  assume reach: "dynamic_reachable C s'"
  from suffix common_seed_has_compatible_evidence[OF reach]
  have "compatible_bootstrap_evidence C s"
  proof (induction rule: converse_rtranclp_induct)
    case base
    then show ?case .
  next
    case (step a b)
    from step.hyps(1) obtain D where "transition D a b" by blast
    then show ?case by (rule bootstrap_evidence_backwards) (use step in blast)
  qed
  with incompatible show False by blast
qed

section \<open>Catching up a lagging process\<close>

text \<open>
  A delivery catch-up preserves every recorded certificate, publication,
  and quorum commit. In the abstract transition system it needs a join to
  the publication's term only if the receiver has not already entered
  that term, and the request must advance its accepted key. The request
  may therefore replace an earlier accepted, uncommitted history at this
  node. Coordinator must still supply a valid current leader, matching
  cluster identity, legitimate publication delivery, and serviced local
  persistence. The method guard below uses the receiver's actual accepted
  key, including its version. Following a reboot, the history and capture are retained;
  a reboot does not by itself repair a missed publication or erase a
  conflicting record of an earlier election.
\<close>

lemma java_bootstrap_catchup_guards:
  assumes join_term: "current_term (java_nodes j n) = term_of h"
    and old_key: "accepted_key (java_nodes j n) < position h"
  shows "java_checks j (Java_Publish n (request (owner h) (term_of h) (rank_version (position h))
           (config_of C h) (carried C h)) value)"
  using assms by (cases "position h"; cases "accepted_key (java_nodes j n)") (auto simp: request_def rank_less_iff)

definition bootstrap_catchup_join where
  "bootstrap_catchup_join s n h =
    (if node_term s n < term_of h then s\<lparr>node_term := (node_term s)(n := term_of h),
        sent_joins := insert (n,owner h,term_of h,position (durable_history s n)) (sent_joins s),
        joined_since_restart := insert n (joined_since_restart s)\<rparr> else s)"

definition bootstrap_catchup_receive where
  "bootstrap_catchup_receive C s n h =
    (bootstrap_catchup_join s n h)\<lparr>durable_history := (durable_history s)(n := h),
       committed_config := (committed_config s)(n := carried C h),
       acknowledgements := insert (n,h) (acknowledgements s)\<rparr>"

lemma bootstrap_catchup_join_legal:
  shows "rtranclp (transition C) s (bootstrap_catchup_join s n h)"
  unfolding bootstrap_catchup_join_def
  by (auto intro: rtranclp.rtrancl_into_rtrancl transition.start_join)

lemma bootstrap_catchup_receive_legal:
  assumes pub: "h \<in> publications s"
    and term_bound: "node_term s n \<le> term_of h"
    and advances: "position (durable_history s n) < position h"
  shows "transition C (bootstrap_catchup_join s n h) (bootstrap_catchup_receive C s n h)"
proof -
  let ?join = "bootstrap_catchup_join s n h"
  have same: "publications ?join = publications s" "durable_history ?join = durable_history s"
    "committed_config ?join = committed_config s" "acknowledgements ?join = acknowledgements s"
    by (simp_all add: bootstrap_catchup_join_def)
  have current: "node_term ?join n = term_of h"
    using term_bound by (auto simp: bootstrap_catchup_join_def)
  show ?thesis unfolding bootstrap_catchup_receive_def
    using transition.receive[where C=C and s="?join" and n=n and h=h] pub advances current same
    by simp
qed

theorem lagging_process_can_accept_committed_publication:
  fixes C :: config
  assumes trace: "rtranclp interleaved_bootstrap_step (installed_bootstrap F) s"
    and commit: "h \<in> quorum_commits s"
    and term_bound: "node_term s n \<le> term_of h"
    and advances: "position (durable_history s n) < position h"
  defines "s' \<equiv> bootstrap_catchup_receive C s n h"
  shows "rtranclp (transition C) s s'" "durable_history s' n = h"
    "committed_config s' n = carried C h" "(n,h) \<in> acknowledgements s'"
    "certificate s' = certificate s" "publications s' = publications s"
    "quorum_commits s' = quorum_commits s" "node_term s' n = term_of h"
proof -
  have pub: "h \<in> publications s" using empty_bootstrap_history_has_capture(2)[OF trace] commit by blast
  show "rtranclp (transition C) s s'"
    unfolding s'_def by (rule rtranclp.rtrancl_into_rtrancl[OF bootstrap_catchup_join_legal
      bootstrap_catchup_receive_legal[OF pub term_bound advances]])
  show "durable_history s' n = h" "committed_config s' n = carried C h" "(n,h) \<in> acknowledgements s'"
    "certificate s' = certificate s" "publications s' = publications s"
    "quorum_commits s' = quorum_commits s" "node_term s' n = term_of h"
    using term_bound by (auto simp: s'_def bootstrap_catchup_receive_def bootstrap_catchup_join_def)
qed

corollary caught_up_follower_can_apply:
  fixes C :: config
  assumes trace: "rtranclp interleaved_bootstrap_step (installed_bootstrap F) s"
    and commit: "h \<in> quorum_commits s"
    and term_bound: "node_term s n \<le> term_of h"
    and advances: "position (durable_history s n) < position h"
    and follower: "certificate s (n,term_of h) = None"
  defines "s' \<equiv> bootstrap_catchup_receive C s n h"
  shows "transition C s' (s'\<lparr>committed_config := (committed_config s')(n := config_of C h)\<rparr>)"
proof -
  note received = lagging_process_can_accept_committed_publication[OF trace commit term_bound advances, where C=C, folded s'_def]
  from received(2,5,7,8) commit follower have "durable_history s' n \<in> quorum_commits s'"
    "term_of (durable_history s' n) = node_term s' n"
    "\<not> active_leader s' n" by (simp_all add: active_leader_def)
  from transition.apply_commit[where C=C, OF this(1,2)] this(3) received(2)
  show ?thesis by simp
qed

lemma single_seed_bootstrap_segment:
  assumes "rtranclp (transition C) a b"
  shows "rtranclp interleaved_bootstrap_step a b"
  using assms by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl)

lemma bootstrap_catchup_leaves_other_nodes:
  assumes "m \<noteq> n"
  shows "durable_history (bootstrap_catchup_receive C s n h) m = durable_history s m"
    "node_term (bootstrap_catchup_receive C s n h) m = node_term s m"
  using assms by (simp_all add: bootstrap_catchup_receive_def bootstrap_catchup_join_def)

lemma finite_bootstrap_catchup:
  assumes finite: "finite A"
    and trace: "rtranclp interleaved_bootstrap_step (installed_bootstrap F) s"
    and commit: "h \<in> quorum_commits s"
    and eligible: "\<And>n. n \<in> A \<Longrightarrow>
      node_term s n \<le> term_of h \<and> position (durable_history s n) < position h"
  shows "\<exists>s'. rtranclp (transition C) s s' \<and>
    (\<forall>n\<in>A. durable_history s' n = h) \<and>
    (\<forall>n. n \<notin> A \<longrightarrow> durable_history s' n = durable_history s n \<and> node_term s' n = node_term s n) \<and>
    certificate s' = certificate s \<and> publications s' = publications s \<and> quorum_commits s' = quorum_commits s"
  using finite eligible
proof (induction A rule: finite_induct)
  case empty
  show ?case by auto
next
  case (insert n A)
  from insert.IH obtain u where
    path: "rtranclp (transition C) s u" and
    received: "\<And>m. m \<in> A \<Longrightarrow> durable_history u m = h" and
    unchanged: "\<And>m. m \<notin> A \<Longrightarrow> durable_history u m = durable_history s m \<and> node_term u m = node_term s m" and
    keeps: "certificate u = certificate s" "publications u = publications s" "quorum_commits u = quorum_commits s"
    using insert.prems by blast
  have prefix: "rtranclp interleaved_bootstrap_step (installed_bootstrap F) u"
    by (rule rtranclp_trans[OF trace single_seed_bootstrap_segment[OF path]])
  have committed: "h \<in> quorum_commits u" using commit by (simp add: keeps)
  have term_bound: "node_term u n \<le> term_of h" and key: "position (durable_history u n) < position h"
    using unchanged[OF insert.hyps(2)] insert.prems[of n] by simp_all
  let ?u' = "bootstrap_catchup_receive C u n h"
  note result = lagging_process_can_accept_committed_publication[OF prefix committed term_bound key, where C=C]
  have "rtranclp (transition C) s ?u'" by (rule rtranclp_trans[OF path result(1)])
  moreover have "durable_history ?u' m = h" if "m \<in> insert n A" for m
  proof (cases "m = n")
    case True
    with result(2) show ?thesis by simp
  next
    case False
    with that have "m \<in> A" by simp
    from bootstrap_catchup_leaves_other_nodes(1)[OF False, where C=C and s=u and h=h]
      received[OF this] show ?thesis by simp
  qed
  moreover have "durable_history ?u' m = durable_history s m \<and> node_term ?u' m = node_term s m"
    if "m \<notin> insert n A" for m
  proof -
    from that have different: "m \<noteq> n" and outside: "m \<notin> A" by auto
    from bootstrap_catchup_leaves_other_nodes[OF different, where C=C and s=u and h=h]
      unchanged[OF outside] show ?thesis by simp
  qed
  moreover have "certificate ?u' = certificate s" "publications ?u' = publications s" "quorum_commits ?u' = quorum_commits s"
    using result(5-7) keeps by simp_all
  ultimately show ?case by blast
qed

theorem finite_compatible_catchup_hands_off:
  fixes F :: "node \<Rightarrow> config" and C :: config and s :: dynamic_state
  defines "lagging \<equiv> {n. F n \<noteq> C \<and> durable_history s n = []}"
  assumes seed: "finite C" "C \<noteq> {}"
    and trace: "rtranclp interleaved_bootstrap_step (installed_bootstrap F) s"
    and compatible: "compatible_bootstrap_evidence C s"
    and finite: "finite lagging"
    and commit: "h \<in> quorum_commits s" "position [] < position h"
    and eligible: "\<And>n. n \<in> lagging \<Longrightarrow> node_term s n \<le> term_of h"
  obtains s' where "rtranclp (transition C) s s'" "dynamic_reachable C s'"
    "certificate s' = certificate s" "publications s' = publications s" "quorum_commits s' = quorum_commits s"
proof -
  have ready: "node_term s n \<le> term_of h \<and> position (durable_history s n) < position h"
    if "n \<in> lagging" for n
    using that eligible[OF that] commit(2) by (auto simp: lagging_def)
  from finite_bootstrap_catchup[OF finite trace commit(1) ready, where C=C] obtain s' where
    path: "rtranclp (transition C) s s'" and
    acquires: "\<And>n. n \<in> lagging \<Longrightarrow> durable_history s' n = h" and
    remains: "\<And>n. n \<notin> lagging \<Longrightarrow> durable_history s' n = durable_history s n" and
    keeps: "certificate s' = certificate s" "publications s' = publications s" "quorum_commits s' = quorum_commits s"
    by blast
  have full_trace: "rtranclp interleaved_bootstrap_step (installed_bootstrap F) s'"
    by (rule rtranclp_trans[OF trace single_seed_bootstrap_segment[OF path]])
  have nonempty: "h \<noteq> []" using commit(2) by auto
  have evidence: "compatible_bootstrap_evidence C s'" using compatible
    by (simp only: compatible_bootstrap_evidence_def keeps)
  have covers: "durable_history s' n \<noteq> []" if "F n \<noteq> C" for n
  proof (cases "n \<in> lagging")
    case True
    with acquires nonempty show ?thesis by simp
  next
    case False
    with that have "durable_history s n \<noteq> []" by (simp add: lagging_def)
    then show ?thesis by (simp add: remains[OF False])
  qed
  have "dynamic_reachable C s'"
    by (rule interleaved_bootstrap_handoff_iff[OF seed full_trace, THEN iffD2]) (use evidence covers in blast)
  then show thesis by (rule that[OF path _ keeps])
qed

end
