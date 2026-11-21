theory Bootstrap_First_Commit
  imports Bootstrap_Placeholder_Liveness Coordination_State_Refinement
begin

section \<open>Real voters in differing initial configurations\<close>

lemma encoded_initial_quorum_iff:
  assumes injective: "inj_on encode C"
    and real: "\<And>n. encode (Discovered_ID n) = n"
    and inert: "\<And>r. Bootstrap_Placeholder r \<in> C \<Longrightarrow> encode (Bootstrap_Placeholder r) \<notin> Q"
  shows "quorum (encode ` C) Q \<longleftrightarrow> initial_quorum C Q"
proof -
  have intersection: "encode ` C \<inter> Q = encode ` (C \<inter> Discovered_ID ` Q)"
  proof (rule equalityI)
    show "encode ` C \<inter> Q \<subseteq> encode ` (C \<inter> Discovered_ID ` Q)"
    proof
      fix n
      assume "n \<in> encode ` C \<inter> Q"
      then obtain x where "x \<in> C" "encode x = n" "n \<in> Q" by blast
      then show "n \<in> encode ` (C \<inter> Discovered_ID ` Q)"
        by (cases x) (auto simp: real dest: inert intro!: image_eqI[of _ _ "Discovered_ID n"])
    qed
    show "encode ` (C \<inter> Discovered_ID ` Q) \<subseteq> encode ` C \<inter> Q"
      by (auto simp: real)
  qed
  have "inj_on encode (C \<inter> Discovered_ID ` Q)"
    by (rule inj_on_subset[OF injective]) blast
  moreover have "finite (encode ` C) \<longleftrightarrow> finite C"
    using injective by (auto dest: finite_imageD)
  ultimately show ?thesis
    by (simp add: quorum_def majority_def initial_quorum_def intersection card_image[OF injective] card_image image_mono)
qed

text \<open>
  The method-boundary checks use the candidate's local initial voting
  configuration, even if every join was cast at a node with a different
  configuration. A receiver admits the publication by term and accepted
  key alone at the CoordinationState boundary. Before emitting a commit the leader
  needs both a quorum of its own committed configuration and a quorum of
  the proposed configuration.

  The fresh-round trace below starts with installed term-zero states and
  empty publication histories. The Java joins additionally require the
  selected joiners' actual initial versions to be at most the candidate's
  initial version, and the first publication must exceed that version.
  Coordinator-side delivery includes join validation, current leadership
  for self-delivery, and compatibility with any committed cluster UUID.
  A freshly installed bootstrap state has no committed cluster UUID.
  The stock Reconfigurator's election hook leaves the supplied state
  unchanged, so the ordinary initial publication can use D = C.
\<close>

lemma first_java_election:
  assumes "local_committed x = C" "accepted_config x = C"
    "finite N" "card N < 1073741824" "C \<subseteq> N"
  shows "java_election x Q \<longleftrightarrow> quorum C Q"
  by (simp add: java_election_def assms java_quorum_eq[OF assms(3-5)])

lemma first_java_fresh_join:
  assumes "current_term (java_nodes j n) < t"
    "current_term (java_nodes candidate c) = t" "started_join (java_nodes candidate c)"
    "accepted_key (java_nodes j n) \<le> accepted_key (java_nodes candidate c)"
    "accepted_config (java_nodes candidate c) \<noteq> {}"
  shows "java_checks j (Java_Start_Join n c t)"
    "Join_Msg n c t (accepted_key (java_nodes j n)) \<in>
      java_journal (java_execute N E j (Java_Start_Join n c t))"
    "java_checks candidate (Java_Join n c t (accepted_key (java_nodes j n)))"
  using assms by (simp_all add: java_put_def Let_def)

lemma first_java_client_and_receive:
  assumes "local_committed (java_nodes j c) = C" "accepted_config (java_nodes j c) = C"
    "election_won (java_nodes j c)" "published_version (java_nodes j c) = rank_version (accepted_key (java_nodes j c))"
    "current_term (java_nodes j c) = t" "rank_version (accepted_key (java_nodes j c)) < v"
    "finite N" "card N < 1073741824" "D \<subseteq> N"
    "quorum D (join_votes (java_nodes j c))"
    "current_term (java_nodes j n) = t" "rank_term (accepted_key (java_nodes j n)) < t"
  shows "java_checks j (Java_Client c t v value D C)"
    "java_checks j (Java_Publish n (request c t v D C) value)"
    "accepted_config (java_nodes (java_execute N E j (Java_Publish n (request c t v D C) value)) n) = D"
    "local_committed (java_nodes (java_execute N E j (Java_Publish n (request c t v D C) value)) n) = C"
  using assms by (simp_all add: request_def java_put_def java_quorum_eq[OF assms(7-9)])

lemma first_java_commit_boundary:
  assumes "local_committed x = C" "published_config x = D"
    "finite N" "card N < 1073741824" "C \<subseteq> N" "D \<subseteq> N"
  shows "java_publication x A \<longleftrightarrow> quorum C A \<and> quorum D A"
  by (simp add: java_publication_def assms java_quorum_eq[OF assms(3-5)] java_quorum_eq[OF assms(3,4,6)])

lemma first_java_response_emits_commit:
  assumes "election_won (java_nodes j c)" "published_key (java_nodes j c) = k"
    "local_committed (java_nodes j c) = C" "published_config (java_nodes j c) = D"
    "finite N" "card N < 1073741824" "C \<subseteq> N" "D \<subseteq> N"
    "quorum C (add_vote E n (publish_votes (java_nodes j c)))"
    "quorum D (add_vote E n (publish_votes (java_nodes j c)))"
    "d \<in> N"
  shows "java_checks j (Java_Response n c k)"
    "Commit_Msg c d k \<in> java_journal (java_execute N E j (Java_Response n c k))"
  using assms(1,2,9-11) by (auto simp: first_java_commit_boundary[OF assms(3-8)] Let_def java_put_def)

lemma first_java_apply_boundary:
  assumes "current_term (java_nodes j n) = t" "accepted_key (java_nodes j n) = \<lparr>rank_term = t, rank_version = v\<rparr>"
  shows "java_checks j (Java_Commit n c \<lparr>rank_term = t, rank_version = v\<rparr>)"
    "local_committed (java_nodes (java_execute N E j (Java_Commit n c \<lparr>rank_term = t, rank_version = v\<rparr>)) n) =
      accepted_config (java_nodes j n)"
  using assms by (simp_all add: java_put_def)

section \<open>Durable votes at the initial configuration boundary\<close>

definition bootstrap_vote_fence :: "dynamic_state \<Rightarrow> bool" where
  "bootstrap_vote_fence s \<longleftrightarrow>
    (\<forall>n c t r. (n,c,t,r) \<in> sent_joins s \<longrightarrow> t \<le> node_term s n \<and>
       (\<forall>h. (n,h) \<in> acknowledgements s \<and> term_of h < t \<longrightarrow> position h \<le> r)) \<and>
    (\<forall>n c d t r u. (n,c,t,r) \<in> sent_joins s \<and> (n,d,t,u) \<in> sent_joins s \<longrightarrow> c = d) \<and>
    (\<forall>n h. (n,h) \<in> acknowledgements s \<longrightarrow> position h \<le> position (durable_history s n))"

definition installed_bootstrap where
  "installed_bootstrap F = (bootstrapped {})\<lparr>committed_config := F\<rparr>"

lemma installed_bootstrap_fence[simp]: "bootstrap_vote_fence (installed_bootstrap F)"
  by (simp add: bootstrap_vote_fence_def installed_bootstrap_def bootstrapped_def)

lemma bootstrap_vote_fence_transition:
  assumes "bootstrap_vote_fence s" "transition C s s'"
  shows "bootstrap_vote_fence s'"
  using assms(2)
proof cases
  case (start_join n t c)
  have old: "u \<le> node_term s m" if "(m,d,u,r) \<in> sent_joins s" for m d u r
    using assms(1) that unfolding bootstrap_vote_fence_def by blast
  have bound: "node_term s m \<le> ((node_term s)(n := t)) m" for m
    using start_join by simp
  have no_prior_vote: "(n,d,t,r) \<notin> sent_joins s" for d r
    using old[of n d t r] start_join by auto
  have unique: "(m,d,u,r) \<in> sent_joins s \<Longrightarrow> (m,e,u,k) \<in> sent_joins s \<Longrightarrow> d = e"
    for m d u r e k using assms(1) unfolding bootstrap_vote_fence_def by blast
  have accepted: "(m,h) \<in> acknowledgements s \<Longrightarrow> position h \<le> position (durable_history s m)"
    for m h using assms(1) unfolding bootstrap_vote_fence_def by blast
  show ?thesis
    using assms(1) start_join order_trans[OF old bound] no_prior_vote unique accepted
    unfolding bootstrap_vote_fence_def by (auto simp: fun_upd_same simp del: fun_upd_apply)
next
  case (receive h n)
  have receipt: "position p \<le> position h" if "(n,p) \<in> acknowledgements s" for p
  proof -
    have "position p \<le> position (durable_history s n)"
      using assms(1) that unfolding bootstrap_vote_fence_def by blast
    with receive show ?thesis by order
  qed
  have new: "\<not> term_of h < t" if "(n,c,t,r) \<in> sent_joins s" for c t r
  proof -
    have "t \<le> node_term s n" using assms(1) that unfolding bootstrap_vote_fence_def by blast
    moreover have "term_of h = node_term s n" using receive by simp
    ultimately show ?thesis by simp
  qed
  show ?thesis using assms(1) receive receipt new unfolding bootstrap_vote_fence_def by auto
qed (use assms(1) in \<open>simp_all add: bootstrap_vote_fence_def\<close>)

lemma bootstrap_vote_fence_path:
  assumes "rtranclp (transition C) (installed_bootstrap F) s"
  shows "bootstrap_vote_fence s"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step s s')
  show ?case by (rule bootstrap_vote_fence_transition[OF step.IH step.hyps(2)])
qed

lemma bootstrap_vote_fence_mixed_path:
  assumes "rtranclp (\<lambda>s s'. \<exists>C. transition C s s') (installed_bootstrap F) s"
  shows "bootstrap_vote_fence s"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step s s')
  from step.hyps(2) obtain C where move: "transition C s s'" by (rule exE)
  show ?case by (rule bootstrap_vote_fence_transition[OF step.IH move])
qed

theorem differing_bootstrap_elections_unique_in_term:
  assumes stable: "stable_requirements R matches bind"
    and captures: "configured_bootstrap R V matches c C" "configured_bootstrap R W matches d D"
    and quorums: "initial_quorum C Q" "initial_quorum D A"
    and votes: "voted s c t Q" "voted s d t A"
    and fence: "bootstrap_vote_fence s"
  shows "c = d"
proof -
  obtain n where "n \<in> Q" "n \<in> A"
    using configured_quorums_intersect[OF stable captures quorums] by blast
  with votes obtain r u where "(n,c,t,r) \<in> sent_joins s" "(n,d,t,u) \<in> sent_joins s"
    unfolding voted_def by blast
  with fence show ?thesis unfolding bootstrap_vote_fence_def by blast
qed

theorem first_receipts_block_later_empty_base:
  assumes stable: "stable_requirements R matches bind"
    and captures: "configured_bootstrap R V matches c C" "configured_bootstrap R W matches d D"
    and quorums: "initial_quorum C A" "initial_quorum D Q"
    and receipts: "\<And>n. n \<in> A \<Longrightarrow> (n,h) \<in> acknowledgements s"
    and fence: "bootstrap_vote_fence s"
    and later: "0 < term_of h" "term_of h < t"
  shows "\<not> fresh_votes s d t [] Q"
proof
  assume fresh: "fresh_votes s d t [] Q"
  obtain n where "n \<in> A" "n \<in> Q"
    using configured_quorums_intersect[OF stable captures quorums] by blast
  then obtain r where recorded: "(n,h) \<in> acknowledgements s" "(n,d,t,r) \<in> sent_joins s" "r \<le> position []"
    using fresh receipts unfolding fresh_votes_def by blast
  have "position h \<le> r"
    using recorded(1,2) fence later(2) unfolding bootstrap_vote_fence_def by blast
  then have "position h \<le> position []" using recorded(3) by (rule order_trans)
  moreover have "position [] < position h"
    using later(1) by (simp add: rank_less_iff)
  ultimately show False by simp
qed

section \<open>A first-publication trace and a common-seed handoff\<close>

definition bootstrap_join_group where
  "bootstrap_join_group s B c t = s\<lparr>node_term := (\<lambda>n. if n \<in> B then t else node_term s n),
    sent_joins := sent_joins s \<union> {(n,c,t,position (durable_history s n)) |n. n \<in> B},
    joined_since_restart := joined_since_restart s \<union> B\<rparr>"

lemma bootstrap_join_group_trace:
  assumes "finite B" "\<And>n. n \<in> B \<Longrightarrow> node_term s n < t"
  shows "rtranclp (transition C) s (bootstrap_join_group s B c t)"
  using assms
proof (induction B rule: finite_induct)
  case empty
  then show ?case by (simp add: bootstrap_join_group_def)
next
  case (insert n B)
  let ?s = "bootstrap_join_group s B c t"
  have path: "rtranclp (transition C) s ?s" using insert by blast
  have newer: "node_term ?s n < t" using insert by (simp add: bootstrap_join_group_def)
  have move: "transition C ?s (bootstrap_join_group s (insert n B) c t)"
  proof -
    have eq: "bootstrap_join_group s (insert n B) c t =
        ?s\<lparr>node_term := (node_term ?s)(n := t),
          sent_joins := insert (n,c,t,position (durable_history ?s n)) (sent_joins ?s),
          joined_since_restart := insert n (joined_since_restart ?s)\<rparr>"
      by (cases s) (auto simp: bootstrap_join_group_def fun_eq_iff)
    show ?thesis unfolding eq by (rule transition.start_join[OF newer])
  qed
  show ?case by (rule rtranclp.rtrancl_into_rtrancl[OF path move])
qed

definition bootstrap_receive_group where
  "bootstrap_receive_group s A h C = s\<lparr>
    durable_history := (\<lambda>n. if n \<in> A then h else durable_history s n),
    committed_config := (\<lambda>n. if n \<in> A then carried C h else committed_config s n),
    acknowledgements := acknowledgements s \<union> {(n,h) |n. n \<in> A}\<rparr>"

lemma bootstrap_receive_group_trace:
  assumes "finite A" "h \<in> publications s"
    "\<And>n. n \<in> A \<Longrightarrow> term_of h = node_term s n"
    "\<And>n. n \<in> A \<Longrightarrow> position (durable_history s n) < position h"
  shows "rtranclp (transition C) s (bootstrap_receive_group s A h C)"
  using assms
proof (induction A rule: finite_induct)
  case empty
  then show ?case by (simp add: bootstrap_receive_group_def)
next
  case (insert n A)
  let ?s = "bootstrap_receive_group s A h C"
  have path: "rtranclp (transition C) s ?s" using insert by blast
  have guards: "h \<in> publications ?s" "term_of h = node_term ?s n"
    "position (durable_history ?s n) < position h"
    using insert by (simp_all add: bootstrap_receive_group_def)
  have move: "transition C ?s (bootstrap_receive_group s (insert n A) h C)"
  proof -
    have eq: "bootstrap_receive_group s (insert n A) h C =
      ?s\<lparr>durable_history := (durable_history ?s)(n := h),
        committed_config := (committed_config ?s)(n := carried C h),
        acknowledgements := insert (n,h) (acknowledgements ?s)\<rparr>"
      by (cases s) (auto simp: bootstrap_receive_group_def fun_eq_iff)
    show ?thesis unfolding eq by (rule transition.receive[OF guards])
  qed
  show ?case by (rule rtranclp.rtrancl_into_rtrancl[OF path move])
qed

definition bootstrap_apply_group where
  "bootstrap_apply_group s B C = s\<lparr>committed_config :=
    (\<lambda>n. if n \<in> B then config_of C (durable_history s n) else committed_config s n)\<rparr>"

lemma bootstrap_apply_group_trace:
  assumes "finite B"
    "\<And>n. n \<in> B \<Longrightarrow> durable_history s n \<in> quorum_commits s"
    "\<And>n. n \<in> B \<Longrightarrow> term_of (durable_history s n) = node_term s n"
    "\<And>n. n \<in> B \<Longrightarrow> active_leader s n \<Longrightarrow>
      durable_history s n = publication_tip s (n,node_term s n)"
  shows "rtranclp (transition C) s (bootstrap_apply_group s B C)"
  using assms
proof (induction B rule: finite_induct)
  case empty
  then show ?case by (simp add: bootstrap_apply_group_def)
next
  case (insert n B)
  let ?s = "bootstrap_apply_group s B C"
  have path: "rtranclp (transition C) s ?s" using insert by blast
  have guards: "durable_history ?s n \<in> quorum_commits ?s"
    "term_of (durable_history ?s n) = node_term ?s n"
    "active_leader ?s n \<longrightarrow> durable_history ?s n = publication_tip ?s (n,node_term ?s n)"
    using insert by (auto simp: bootstrap_apply_group_def active_leader_def)
  have move: "transition C ?s (bootstrap_apply_group s (insert n B) C)"
  proof -
    have eq: "bootstrap_apply_group s (insert n B) C =
      ?s\<lparr>committed_config := (committed_config ?s)(n := config_of C (durable_history ?s n))\<rparr>"
      by (cases s) (auto simp: bootstrap_apply_group_def fun_eq_iff)
    show ?thesis unfolding eq by (rule transition.apply_commit[OF guards])
  qed
  show ?case by (rule rtranclp.rtrancl_into_rtrancl[OF path move])
qed

locale isolated_bootstrap_publication =
  fixes C D :: config and c :: node and t v payload :: nat
    and H Q A K B :: "node set"
  assumes finite_H: "finite H"
    and send: "insert c (Q \<union> A) \<subseteq> H"
    and receive: "K \<subseteq> A"
    and apply_subset: "B \<subseteq> A"
    and first_key: "0 < t" "0 < v"
    and joins: "quorum C Q" "quorum D Q"
    and acks: "quorum C K" "quorum D K"
begin

definition first_lineage where
  "first_lineage = [\<lparr>pub_term = t, pub_version = v, pub_payload = payload,
    pub_owner = c, pub_config = D, pub_previous = C\<rparr>]"

definition first_joined where
  "first_joined F = bootstrap_join_group (installed_bootstrap F) H c t"

definition first_elected where
  "first_elected F = (first_joined F)\<lparr>certificate := (\<lambda>k. if k = (c,t) then
    Some \<lparr>elected_from = [], elected_committed = C, elected_votes = Q\<rparr> else None)\<rparr>"

definition first_published where
  "first_published F = (first_elected F)\<lparr>publication_tip := (\<lambda>k. if k = (c,t) then first_lineage else []),
    publications := {first_lineage}\<rparr>"

definition first_received where
  "first_received F = bootstrap_receive_group (first_published F) A first_lineage C"

definition first_certified where
  "first_certified F = (first_received F)\<lparr>quorum_commits := {first_lineage}\<rparr>"

definition first_applied where
  "first_applied F = bootstrap_apply_group (first_certified F) B C"

lemma first_joined_fields[simp]:
  "node_term (first_joined F) n = (if n \<in> H then t else 0)"
  "durable_history (first_joined F) n = []"
  "committed_config (first_joined F) n = F n"
  "certificate (first_joined F) k = None"
  "publication_tip (first_joined F) k = []"
  "publications (first_joined F) = {}"
  "acknowledgements (first_joined F) = {}"
  "joined_since_restart (first_joined F) = H"
  "sent_joins (first_joined F) = {(n,c,t,position []) | n. n \<in> H}"
  by (simp_all add: first_joined_def bootstrap_join_group_def installed_bootstrap_def bootstrapped_def)

lemma first_joined_fresh: "fresh_votes (first_joined F) c t [] Q"
  using send unfolding fresh_votes_def by auto

lemma first_election_legal:
  assumes winner: "F c = C"
  shows "transition C (first_joined F) (first_elected F)"
proof -
  have c: "c \<in> H" using send by blast
  have initial:
    "c \<in> joined_since_restart (first_joined F)"
    "certificate (first_joined F) (c,node_term (first_joined F) c) = None"
    "quorum (committed_config (first_joined F) c) Q"
    "quorum (config_of C (durable_history (first_joined F) c)) Q"
    "fresh_votes (first_joined F) c (node_term (first_joined F) c) (durable_history (first_joined F) c) Q"
    by (simp_all add: c winner joins first_joined_fresh)
  have eq: "first_elected F = (first_joined F)\<lparr>certificate := (certificate (first_joined F))((c,t) :=
      Some \<lparr>elected_from = [], elected_committed = C, elected_votes = Q\<rparr>),
    publication_tip := (publication_tip (first_joined F))((c,t) := [])\<rparr>"
    by (rule dynamic_state.equality) (simp_all add: first_elected_def fun_eq_iff)
  from transition.win[OF initial] show ?thesis
    by (simp add: eq c winner)
qed

lemma first_elected_active[simp]: "active_leader (first_elected F) n \<longleftrightarrow> n = c"
  using send by (auto simp: first_elected_def active_leader_def)

lemma first_publish_legal:
  assumes winner: "F c = C"
  shows "transition C (first_elected F) (first_published F)"
proof -
  have c: "c \<in> H" using send by blast
  have voters: "\<forall>n\<in>Q. n \<in> H" using send by blast
  have guards:
    "active_leader (first_elected F) c"
    "publication_tip (first_elected F) (c,node_term (first_elected F) c) = durable_history (first_elected F) c"
    "rank_version (position (durable_history (first_elected F) c)) < v"
    "D \<noteq> config_of C (durable_history (first_elected F) c) \<longrightarrow>
      committed_config (first_elected F) c = config_of C (durable_history (first_elected F) c)"
    "quorum D Q"
    "fresh_votes (first_elected F) c (node_term (first_elected F) c) (durable_history (first_elected F) c) Q"
    "first_lineage = durable_history (first_elected F) c @ [\<lparr>
      pub_term = node_term (first_elected F) c, pub_version = v, pub_payload = payload,
      pub_owner = c, pub_config = D, pub_previous = committed_config (first_elected F) c\<rparr>]"
    by (simp_all add: first_elected_def c winner first_key joins voters active_leader_def fresh_votes_def first_lineage_def)
  have eq: "first_published F = (first_elected F)\<lparr>publication_tip :=
    (publication_tip (first_elected F))((c,t) := first_lineage),
    publications := insert first_lineage (publications (first_elected F))\<rparr>"
    by (rule dynamic_state.equality) (simp_all add: first_published_def first_elected_def fun_eq_iff)
  from transition.publish[OF guards] show ?thesis
    by (simp add: eq first_elected_def c)
qed

lemma first_published_fields[simp]:
  "node_term (first_published F) n = (if n \<in> H then t else 0)"
  "durable_history (first_published F) n = []"
  "committed_config (first_published F) n = F n"
  "publications (first_published F) = {first_lineage}"
  "acknowledgements (first_published F) = {}"
  "publication_tip (first_published F) k = (if k = (c,t) then first_lineage else [])"
  "active_leader (first_published F) n \<longleftrightarrow> n = c"
  using send by (auto simp: first_published_def first_elected_def active_leader_def)

lemma first_receive_legal:
  "rtranclp (transition C) (first_published F) (first_received F)"
  unfolding first_received_def
proof (rule bootstrap_receive_group_trace)
  show "finite A" using finite_H send by (blast intro: finite_subset)
  show "first_lineage \<in> publications (first_published F)" by simp
  fix n
  assume "n \<in> A"
  with send show "term_of first_lineage = node_term (first_published F) n"
    by (auto simp: first_lineage_def)
  show "position (durable_history (first_published F) n) < position first_lineage"
    using first_key by (simp add: first_lineage_def rank_less_iff)
qed

lemma first_certify_legal:
  "transition C (first_received F) (first_certified F)"
proof -
  have c: "c \<in> H" using send by blast
  have receipts: "(n,first_lineage) \<in> acknowledgements (first_received F)" if "n \<in> K" for n
    using receive that by (auto simp: first_received_def bootstrap_receive_group_def)
  have joint: "joint_receipts C (first_received F) first_lineage"
    unfolding joint_receipts_def
  proof (intro exI[of _ K] conjI ballI)
    show "quorum (carried C first_lineage) K" "quorum (config_of C first_lineage) K"
      using acks by (simp_all add: first_lineage_def)
    show "(n, first_lineage) \<in> acknowledgements (first_received F)" if "n \<in> K" for n
      by (rule receipts[OF that])
  qed
  have guards:
    "active_leader (first_received F) c"
    "first_lineage = publication_tip (first_received F) (c,node_term (first_received F) c)"
    "first_lineage \<in> publications (first_received F)"
    "term_of first_lineage = node_term (first_received F) c"
    "owner first_lineage = c"
    by (simp_all add: first_received_def bootstrap_receive_group_def active_leader_def first_published_def
      first_elected_def c first_lineage_def)
  from transition.certify[OF guards joint] show ?thesis
    by (simp add: first_certified_def first_received_def bootstrap_receive_group_def
      first_published_def first_elected_def first_joined_def bootstrap_join_group_def
      installed_bootstrap_def bootstrapped_def)
qed

lemma first_apply_legal:
  "rtranclp (transition C) (first_certified F) (first_applied F)"
  unfolding first_applied_def
proof (rule bootstrap_apply_group_trace)
  show "finite B" using finite_H send apply_subset by (blast intro: finite_subset)
  fix n
  assume "n \<in> B"
  with send apply_subset have members: "n \<in> A" "n \<in> H" by blast+
  show "durable_history (first_certified F) n \<in> quorum_commits (first_certified F)"
    "term_of (durable_history (first_certified F) n) = node_term (first_certified F) n"
    using members by (simp_all add: first_certified_def first_received_def bootstrap_receive_group_def first_lineage_def)
  assume "active_leader (first_certified F) n"
  with members show "durable_history (first_certified F) n =
      publication_tip (first_certified F) (n,node_term (first_certified F) n)"
    by (auto simp: first_certified_def first_received_def bootstrap_receive_group_def
      active_leader_def first_published_def first_elected_def)
qed

lemma first_commit_trace:
  assumes "F c = C"
  shows "rtranclp (transition C) (installed_bootstrap F) (first_applied F)"
proof -
  have "rtranclp (transition C) (installed_bootstrap F) (first_joined F)"
    unfolding first_joined_def
    using finite_H first_key by (intro bootstrap_join_group_trace) (simp_all add: installed_bootstrap_def bootstrapped_def)
  then have "rtranclp (transition C) (installed_bootstrap F) (first_elected F)"
    using first_election_legal[of F, OF assms] by (rule rtranclp.rtrancl_into_rtrancl)
  then have "rtranclp (transition C) (installed_bootstrap F) (first_published F)"
    using first_publish_legal[of F, OF assms] by (rule rtranclp.rtrancl_into_rtrancl)
  then have "rtranclp (transition C) (installed_bootstrap F) (first_received F)"
    using first_receive_legal by (rule rtranclp_trans)
  then have "rtranclp (transition C) (installed_bootstrap F) (first_certified F)"
    using first_certify_legal by (rule rtranclp.rtrancl_into_rtrancl)
  then show ?thesis using first_apply_legal by (rule rtranclp_trans)
qed

lemma first_commit_result:
  "quorum_commits (first_applied F) = {first_lineage}"
  "durable_history (first_applied F) n = (if n \<in> A then first_lineage else [])"
  "committed_config (first_applied F) n = (if n \<in> B then D else if n \<in> A then C else F n)"
  "(n,first_lineage) \<in> acknowledgements (first_applied F) \<longleftrightarrow> n \<in> A"
  "certificate (first_applied F) (c,t) =
    Some \<lparr>elected_from = [], elected_committed = C, elected_votes = Q\<rparr>"
  using apply_subset
  by (auto simp: first_applied_def first_certified_def first_received_def
    bootstrap_apply_group_def bootstrap_receive_group_def first_published_def first_elected_def first_lineage_def)

text \<open>
  A successful quorum commit can leave a previously installed configuration
  at a node that missed the publication. In the isolated round, the precise
  sufficient handoff condition is that every initial disagreement with the
  winner has accepted its publication. Applying the commit additionally
  changes the committed configuration to the proposed one. Thus the endpoint
  can be identical to a reachable common-seed endpoint even when some nodes
  have accepted but not yet applied, as permitted by the dynamic rules.
\<close>

lemma first_endpoint_agreement:
  "first_applied F = first_applied (\<lambda>_. C) \<longleftrightarrow>
    (\<forall>n. n \<notin> A \<longrightarrow> F n = C)"
proof
  assume eq: "first_applied F = first_applied (\<lambda>_. C)"
  show "\<forall>n. n \<notin> A \<longrightarrow> F n = C"
  proof (intro allI impI)
    fix n
    assume "n \<notin> A"
    then have outside: "n \<notin> A" "n \<notin> B" using apply_subset by auto
    from arg_cong[OF eq, where f="\<lambda>s. committed_config s n"] outside
    show "F n = C" by (simp add: first_commit_result)
  qed
next
  assume agree: "\<forall>n. n \<notin> A \<longrightarrow> F n = C"
  show "first_applied F = first_applied (\<lambda>_. C)"
    using agree apply_subset
    by (auto simp: first_applied_def first_certified_def first_received_def first_published_def
      first_elected_def first_joined_def bootstrap_apply_group_def bootstrap_receive_group_def
      bootstrap_join_group_def installed_bootstrap_def bootstrapped_def fun_eq_iff)
qed

theorem first_commit_handoff:
  assumes coverage: "\<And>n. n \<notin> A \<Longrightarrow> F n = C"
  shows "dynamic_reachable C (first_applied F)"
proof -
  have seed: "finite C" "C \<noteq> {}" using joins(1) unfolding quorum_def majority_def by auto
  have path: "rtranclp (transition C) (bootstrapped C) (first_applied (\<lambda>_. C))"
    using first_commit_trace[of "\<lambda>_. C"] by (simp add: installed_bootstrap_def bootstrapped_def)
  have reach: "dynamic_reachable C (first_applied (\<lambda>_. C))"
    using path dynamic_reachable.boot[OF seed]
    by (induction rule: rtranclp_induct) (auto intro: dynamic_reachable.advance)
  have "first_applied F = first_applied (\<lambda>_. C)"
    using coverage first_endpoint_agreement[of F] by blast
  then show ?thesis using reach by simp
qed

lemma missed_disagreement_prevents_handoff:
  assumes "n \<notin> A" "F n \<noteq> C"
  shows "\<not> dynamic_reachable C (first_applied F)"
proof
  assume reach: "dynamic_reachable C (first_applied F)"
  then have "journal_ok C (first_applied F)" using dynamic_invariants by blast
  then have effective: "effective_config C (quorum_commits (first_applied F))
    (durable_history (first_applied F) n) (committed_config (first_applied F) n)"
    by (rule journalD(3))
  have "n \<notin> B" using assms(1) apply_subset by blast
  with effective assms show False by (simp add: first_commit_result effective_config_def)
qed

corollary first_commit_handoff_iff:
  "dynamic_reachable C (first_applied F) \<longleftrightarrow> (\<forall>n. n \<notin> A \<longrightarrow> F n = C)"
  using first_commit_handoff[where F=F] missed_disagreement_prevents_handoff[where F=F] by blast

end

theorem differing_configured_views_first_commit:
  fixes captured :: "node \<Rightarrow> 'r initial_member set"
  assumes stable: "stable_requirements R matches bind"
    and installed: "\<And>n. n \<in> U \<Longrightarrow> configured_bootstrap R (view n) matches n (captured n)"
    and universe: "finite U" "bind ` R \<subseteq> U"
    and healthy: "H \<subseteq> U" "insert c (Q \<union> A) \<subseteq> H"
    and delivery: "K \<subseteq> A" "B \<subseteq> A"
    and first_key: "0 < t" "0 < v"
    and election: "initial_quorum (captured c) Q" "quorum D Q"
    and commit: "initial_quorum (captured c) K" "quorum D K"
  obtains encode s h where
    "encode = bootstrap_member_encoding U bind"
    "rtranclp (transition (encode ` captured c))
      (installed_bootstrap (\<lambda>n. if n \<in> U then encode ` captured n else encode ` captured c)) s"
    "majority (bind ` R) (bind ` R \<inter> Q)"
    "majority (bind ` R) (bind ` R \<inter> K)"
    "bootstrap_vote_fence s"
    "certificate s (c,t) =
      Some \<lparr>elected_from = [], elected_committed = encode ` captured c, elected_votes = Q\<rparr>"
    "quorum_commits s = {h}" "position h = \<lparr>rank_term = t, rank_version = v\<rparr>" "at_tip 0 pub_payload h = payload"
    "\<And>n. n \<in> A \<Longrightarrow> durable_history s n = h"
    "\<And>n. n \<in> K \<Longrightarrow> (n,h) \<in> acknowledgements s"
    "\<And>n. n \<in> B \<Longrightarrow> committed_config s n = D"
    "dynamic_reachable (encode ` captured c) s \<longleftrightarrow>
      (\<forall>n\<in>U - A. captured n = captured c)"
proof -
  let ?encode = "bootstrap_member_encoding U bind"
  let ?C = "?encode ` captured c"
  let ?F = "\<lambda>n. if n \<in> U then ?encode ` captured n else ?C"
  let ?captures = "\<Union>n\<in>U. captured n"
  have c: "c \<in> U" using healthy by blast
  have roster: "Bootstrap_Placeholder r \<in> captured n \<Longrightarrow> r \<in> R" if "n \<in> U" for r n
    unfolding configured_view_form[OF stable installed[OF that]] by simp
  have actual: "actual_bootstrap_members ?captures \<subseteq> U"
  proof
    fix n
    assume "n \<in> actual_bootstrap_members ?captures"
    then obtain p where "p \<in> U" "Discovered_ID n \<in> captured p" by auto
    with captured_real_members[OF stable installed[OF this(1)]] universe(2) show "n \<in> U" by blast
  qed
  have placeholders: "Bootstrap_Placeholder r \<in> ?captures \<Longrightarrow> r \<in> R" for r
    using roster by blast
  have bind_inj: "inj_on bind R" using stable by (simp add: stable_requirements_def)
  have real: "?encode (Discovered_ID n) = n" for n by (simp add: bootstrap_member_encoding_def)
  have injective: "inj_on ?encode ?captures"
  proof (rule finite_bootstrap_member_encoding(2)[where R=R])
    show "finite U" by (rule universe(1))
    show "inj_on bind R" by (rule bind_inj)
    show "Bootstrap_Placeholder r \<in> ?captures \<Longrightarrow> r \<in> R" for r by (rule placeholders)
    show "actual_bootstrap_members ?captures \<subseteq> U" by (rule actual)
  qed
  have inert: "?encode (Bootstrap_Placeholder r) \<notin> U" for r
    using Max_ge[OF universe(1), of "Suc (Max U) + bind r"] by (auto simp: bootstrap_member_encoding_def)
  have winner_inj: "inj_on ?encode (captured c)"
    by (rule inj_on_subset[OF injective]) (use c in blast)
  have projected: "majority (bind ` R) (bind ` R \<inter> Q)" "majority (bind ` R) (bind ` R \<inter> K)"
    by (rule configured_quorum_projects[OF stable installed[OF c] election(1)],
        rule configured_quorum_projects[OF stable installed[OF c] commit(1)])
  have inert_Q: "\<And>r. Bootstrap_Placeholder r \<in> captured c \<Longrightarrow> ?encode (Bootstrap_Placeholder r) \<notin> Q"
    using inert healthy c by blast
  have inert_K: "\<And>r. Bootstrap_Placeholder r \<in> captured c \<Longrightarrow> ?encode (Bootstrap_Placeholder r) \<notin> K"
    using inert healthy delivery c by blast
  have elect: "quorum ?C Q" by (simp add: encoded_initial_quorum_iff[OF winner_inj real inert_Q] election(1))
  have certify: "quorum ?C K" by (simp add: encoded_initial_quorum_iff[OF winner_inj real inert_K] commit(1))
  have finite_H: "finite H" by (rule finite_subset[OF healthy(1) universe(1)])
  interpret round: isolated_bootstrap_publication ?C D c t v payload H Q A K B
    by (unfold_locales; rule finite_H healthy(2) delivery first_key elect election(2) certify commit(2))
  have path: "rtranclp (transition ?C) (installed_bootstrap ?F) (round.first_applied ?F)"
    by (rule round.first_commit_trace) (simp add: c)
  have equivalent: "?encode ` captured n = ?C \<longleftrightarrow> captured n = captured c" if "n \<in> U" for n
    by (rule inj_on_image_eq_iff[OF injective]) (use c that in blast)+
  have later:
    "dynamic_reachable ?C (round.first_applied ?F) \<longleftrightarrow>
      (\<forall>n\<in>U - A. captured n = captured c)"
    using round.first_commit_handoff_iff[of ?F] equivalent by auto
  show thesis
  proof (rule that[of ?encode "round.first_applied ?F" round.first_lineage])
    show "?encode = bootstrap_member_encoding U bind" by (rule refl)
    show "rtranclp (transition ?C) (installed_bootstrap ?F) (round.first_applied ?F)" by (rule path)
    show "majority (bind ` R) (bind ` R \<inter> Q)" "majority (bind ` R) (bind ` R \<inter> K)"
      by (fact projected)+
    show "bootstrap_vote_fence (round.first_applied ?F)" by (rule bootstrap_vote_fence_path[OF path])
    show "certificate (round.first_applied ?F) (c,t) =
      Some \<lparr>elected_from = [], elected_committed = ?C, elected_votes = Q\<rparr>"
      by (rule round.first_commit_result(5))
    show "quorum_commits (round.first_applied ?F) = {round.first_lineage}" by (rule round.first_commit_result(1))
    show "position round.first_lineage = \<lparr>rank_term = t, rank_version = v\<rparr>" "at_tip 0 pub_payload round.first_lineage = payload"
      by (simp_all add: round.first_lineage_def)
    show "durable_history (round.first_applied ?F) n = round.first_lineage" if "n \<in> A" for n
      using that by (simp add: round.first_commit_result)
    show "(n,round.first_lineage) \<in> acknowledgements (round.first_applied ?F)" if "n \<in> K" for n
      using that delivery(1) by (auto simp: round.first_commit_result)
    show "committed_config (round.first_applied ?F) n = D" if "n \<in> B" for n
      using that by (simp add: round.first_commit_result)
    show "dynamic_reachable ?C (round.first_applied ?F) \<longleftrightarrow>
      (\<forall>n\<in>U - A. captured n = captured c)" by (rule later)
  qed
qed

end
