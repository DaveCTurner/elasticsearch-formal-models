theory Coordination_State_Refinement
  imports Coordination_State_Java
begin

section \<open>Representation and default-strategy quorum checks\<close>

definition mask_votes :: "node set \<Rightarrow> 'v local_node \<Rightarrow> 'v local_node" where
  "mask_votes E x = x\<lparr>join_votes := join_votes x \<inter> E, publish_votes := publish_votes x \<inter> E\<rparr>"

lemma mask_vote_selectors[simp]:
  "join_votes (mask_votes E x) = join_votes x \<inter> E"
  "publish_votes (mask_votes E x) = publish_votes x \<inter> E"
  by (simp_all add: mask_votes_def)

definition project_java :: "node set \<Rightarrow> 'v tla_state \<Rightarrow> 'v java_state" where
  "project_java E s = \<lparr>java_nodes = (\<lambda>n. mask_votes E (nodes_at s n)), java_journal = messages s\<rparr>"

definition configurations_ok :: "node set \<Rightarrow> 'v tla_state \<Rightarrow> bool" where
  "configurations_ok E s \<longleftrightarrow>
    (\<forall>n. accepted_config (nodes_at s n) \<subseteq> E \<and> local_committed (nodes_at s n) \<subseteq> E \<and>
      published_config (nodes_at s n) \<subseteq> E)"

lemma configurations_okD:
  assumes "configurations_ok E s"
  shows "accepted_config (nodes_at s n) \<subseteq> E" "local_committed (nodes_at s n) \<subseteq> E"
    "published_config (nodes_at s n) \<subseteq> E"
  using assms unfolding configurations_ok_def by auto

lemma project_java_select[simp]:
  "java_nodes (project_java E s) n = mask_votes E (nodes_at s n)"
  "java_journal (project_java E s) = messages s"
  by (simp_all add: project_java_def)

lemma project_java_put[simp]:
  "project_java E (put_node s n x) = java_put (project_java E s) n (mask_votes E x)"
  by (simp add: project_java_def java_put_def put_node_def fun_eq_iff)

lemma project_java_messages[simp]:
  "project_java E (s\<lparr>messages := M\<rparr>) = (project_java E s)\<lparr>java_journal := M\<rparr>"
  "project_java E (s\<lparr>descendant := G\<rparr>) = project_java E s"
  by (simp_all add: project_java_def)

lemma eligible_insert:
  "add_vote E n (Q \<inter> E) = insert n Q \<inter> E"
  by (auto simp: add_vote_def)

lemma reset_commutes:
  "java_reset (mask_votes E x) = mask_votes E (reset_transient x)"
  by (simp add: java_reset_def reset_transient_def mask_votes_def)

lemma commit_configuration_unchanged:
  assumes "local_committed (java_nodes j n) = accepted_config (java_nodes j n)"
  shows "java_execute N E j (Java_Commit n c k) = j"
proof -
  let ?x = "java_nodes j n"
  have "?x\<lparr>local_committed := accepted_config ?x\<rparr> = ?x"
    by (subst assms[symmetric]) simp
  then show ?thesis by (simp add: java_put_def)
qed

lemma signed_int_small:
  assumes "0 \<le> x" "x < 2147483648"
  shows "signed_int x = x"
proof -
  have "0 \<le> x + 2147483648" "x + 2147483648 < 4294967296" using assms by linarith+
  then show ?thesis by (simp add: signed_int_def)
qed

lemma java_quorum_eq:
  assumes finite: "finite N" and bound: "card N < 1073741824" and sub: "D \<subseteq> N"
  shows "java_has_quorum D Q = quorum D Q"
proof -
  have fd: "finite D" by (rule finite_subset[OF sub finite])
  have size: "card D \<le> card N" by (rule card_mono[OF finite sub])
  have votes: "card (D \<inter> Q) \<le> card D" by (rule card_mono[OF fd]) simp
  have d: "int (card D) \<le> int (card N)" using size by simp
  have q: "int (card (D \<inter> Q)) \<le> int (card D)" using votes by simp
  have n: "int (card N) < 1073741824" using bound by simp
  have fits: "int (card D) < 2147483648" "2 * int (card (D \<inter> Q)) < 2147483648"
    using d q n by linarith+
  have nonnegative: "0 \<le> int (card D)" "0 \<le> 2 * int (card (D \<inter> Q))" by simp_all
  have normal: "signed_int (int (card D)) = int (card D)"
    "signed_int (2 * int (card (D \<inter> Q))) = 2 * int (card (D \<inter> Q))"
    by (rule signed_int_small[OF nonnegative(1) fits(1)], rule signed_int_small[OF nonnegative(2) fits(2)])
  have cast: "2 * int (card (D \<inter> Q)) = int (2 * card (D \<inter> Q))" by simp
  have comparison: "(int (card D) < 2 * int (card (D \<inter> Q))) = (card D < 2 * card (D \<inter> Q))"
    by (subst cast) (rule of_nat_less_iff)
  show ?thesis unfolding java_has_quorum_def quorum_def majority_def normal comparison
    using fd by simp
qed

lemma empty_votes_before_bootstrap:
  assumes "tla_reachable N V C initial_value versions s"
  shows "accepted_config (nodes_at s n) = {} \<Longrightarrow>
    join_votes (nodes_at s n) = {} \<and> publish_votes (nodes_at s n) = {}"
  using assms
proof (induction arbitrary: n rule: tla_reachable.induct)
  case init
  show ?case by (simp add: tla_initial_def)
next
  case (advance s a)
  obtain d where "linked C s d" using tla_dynamic_refinement[OF advance.hyps(1)] by blast
  then have pub: "Publish_Msg i p v \<in> messages s \<Longrightarrow> pub_config p \<noteq> {}" for i p v
    using linkedD(3)[of C s d "Publish_Msg i p v"] by simp
  have won: "election_won (nodes_at s i) \<Longrightarrow> accepted_config (nodes_at s i) \<noteq> {}" for i
    using node_linkD(9)[OF linkedD(1)[OF \<open>linked C s d\<close>, of i]]
    unfolding election_quorum_def by (auto dest: quorum_nonempty)
  from advance.hyps(2) advance.IH advance.prems pub won show ?case
    by (cases a) (auto simp: Let_def put_node_def reset_transient_def)
qed

locale default_strategy =
  fixes N E :: "node set" and C :: config
  assumes finite_nodes: "finite N" and elig: "E \<subseteq> N"
    and int_bound: "card N < 1073741824"
    and initial_config: "C \<subseteq> E" "C \<noteq> {}"
begin

declare [[record_sort_updates = true]]

lemma quorum_mask:
  assumes sub: "D \<subseteq> E"
  shows "java_has_quorum D (Q \<inter> E) = quorum D Q"
proof -
  have "D \<subseteq> N" using sub elig by blast
  moreover have "D \<inter> (Q \<inter> E) = D \<inter> Q" using sub by blast
  ultimately show ?thesis using java_quorum_eq[OF finite_nodes int_bound]
    by (simp add: quorum_def majority_def)
qed

lemma election_mask:
  assumes "local_committed x \<subseteq> E" "accepted_config x \<subseteq> E"
  shows "java_election (mask_votes E x) (Q \<inter> E) = election_quorum x Q"
  by (simp add: java_election_def election_quorum_def mask_votes_def quorum_mask assms)

lemma response_mask:
  assumes "local_committed x \<subseteq> E" "published_config x \<subseteq> E"
  shows "java_publication (mask_votes E x) (Q \<inter> E) = response_quorum x Q"
  by (simp add: java_publication_def response_quorum_def mask_votes_def quorum_mask assms)

section \<open>Simulation of each successful method call\<close>

theorem successful_call_simulates:
  assumes reach: "tla_reachable N V C initial_value versions s"
    and ok: "configurations_ok E s"
    and checks: "java_checks (project_java E s) a"
    and caller: "caller_contract N E V C initial_value (project_java E s) a"
  shows "(enabled N V s (abstract_action a) \<and>
      java_execute N E (project_java E s) a = project_java E (execute N C initial_value s (abstract_action a)) \<and>
      configurations_ok E (execute N C initial_value s (abstract_action a))) \<or>
    java_execute N E (project_java E s) a = project_java E s"
proof (cases a)
  case (Java_Bootstrap n k v D F)
  let ?x = "nodes_at s n"
  from checks Java_Bootstrap have empty: "accepted_config ?x = {}" by (simp add: mask_votes_def)
  from checks caller Java_Bootstrap have e: "enabled N V s (Bootstrap n)"
    and args: "k = accepted_key ?x" "v = initial_value" "D = C" "F = C"
    using empty_votes_before_bootstrap[OF reach empty] by (auto simp: Let_def mask_votes_def)
  have updated: "configurations_ok E (execute N C initial_value s (Bootstrap n))"
    using ok initial_config(1) by (auto simp: configurations_ok_def put_node_def)
  have commutes: "java_execute N E (project_java E s) a = project_java E (execute N C initial_value s (Bootstrap n))"
    by (simp add: Java_Bootstrap args mask_votes_def)
  show ?thesis using Java_Bootstrap e updated commutes by simp
next
  case (Java_Start_Join n c t)
  from checks caller Java_Start_Join have e: "enabled N V s (Start_Join n c t)" by (simp add: mask_votes_def)
  have updated: "configurations_ok E (execute N C initial_value s (Start_Join n c t))"
    using ok by (auto simp: configurations_ok_def put_node_def reset_transient_def Let_def)
  have commutes: "java_execute N E (project_java E s) a = project_java E (execute N C initial_value s (Start_Join n c t))"
    by (simp add: Java_Start_Join java_reset_def reset_transient_def Let_def mask_votes_def)
  show ?thesis using Java_Start_Join e updated commutes by simp
next
  case (Java_Join n c t k)
  from checks caller Java_Join have e: "enabled N V s (Handle_Join n c t k)"
    by (simp add: mask_votes_def Let_def)
  have updated: "configurations_ok E (execute N C initial_value s (Handle_Join n c t k))"
    using ok by (auto simp: configurations_ok_def put_node_def Let_def)
  have outcomes: "java_election (mask_votes E (nodes_at s c)) (insert n (join_votes (nodes_at s c)) \<inter> E) =
      election_quorum (nodes_at s c) (insert n (join_votes (nodes_at s c)))"
    by (rule election_mask[OF configurations_okD(2,1)[OF ok]])
  have commutes: "java_execute N E (project_java E s) a = project_java E (execute N C initial_value s (Handle_Join n c t k))"
    by (simp add: Java_Join Let_def eligible_insert outcomes conj_commute; simp add: mask_votes_def)
  show ?thesis using Java_Join e updated commutes by simp
next
  case (Java_Client n t v x D F)
  let ?n = "nodes_at s n"
  from caller Java_Client have sub: "D \<subseteq> E" and F: "F = local_committed ?n"
    by (auto simp: mask_votes_def)
  have "quorum D (join_votes ?n)" using checks Java_Client
    by (simp add: Let_def mask_votes_def quorum_mask[OF sub])
  then have "D \<noteq> {}" by (rule quorum_nonempty)
  with checks caller Java_Client sub elig have e: "enabled N V s (Client_Value n t v x D)"
    by (auto simp: Let_def mask_votes_def quorum_mask[OF sub])
  have updated: "configurations_ok E (execute N C initial_value s (Client_Value n t v x D))"
    using ok sub by (auto simp: configurations_ok_def put_node_def Let_def)
  have commutes: "java_execute N E (project_java E s) a = project_java E (execute N C initial_value s (Client_Value n t v x D))"
    by (simp add: Java_Client F Let_def mask_votes_def)
  show ?thesis using Java_Client e updated commutes by simp
next
  case (Java_Publish n p x)
  from checks caller Java_Publish have e: "enabled N V s (Handle_Publish n p x)"
    and cfg: "pub_config p \<subseteq> E" "pub_previous p \<subseteq> E"
    by (auto simp: mask_votes_def Let_def)
  have updated: "configurations_ok E (execute N C initial_value s (Handle_Publish n p x))"
    using ok cfg by (auto simp: configurations_ok_def put_node_def)
  have commutes: "java_execute N E (project_java E s) a = project_java E (execute N C initial_value s (Handle_Publish n p x))"
    by (simp add: Java_Publish mask_votes_def)
  show ?thesis using Java_Publish e updated commutes by simp
next
  case (Java_Response n c k)
  from checks caller Java_Response have e: "enabled N V s (Handle_Response n c k)"
    by (simp add: mask_votes_def Let_def)
  have updated: "configurations_ok E (execute N C initial_value s (Handle_Response n c k))"
    using ok by (auto simp: configurations_ok_def put_node_def Let_def)
  have outcomes: "java_publication (mask_votes E (nodes_at s c)) (insert n (publish_votes (nodes_at s c)) \<inter> E) =
      response_quorum (nodes_at s c) (insert n (publish_votes (nodes_at s c)))"
    by (rule response_mask[OF configurations_okD(2,3)[OF ok]])
  have commutes: "java_execute N E (project_java E s) a = project_java E (execute N C initial_value s (Handle_Response n c k))"
    by (simp add: Java_Response Let_def eligible_insert outcomes; simp add: mask_votes_def)
  show ?thesis using Java_Response e updated commutes by simp
next
  case (Java_Commit n c k)
  let ?x = "nodes_at s n"
  show ?thesis
  proof (cases "election_won ?x \<and> rank_version k \<noteq> published_version ?x")
    case True
    with caller Java_Commit have local: "local_committed (java_nodes (project_java E s) n) =
      accepted_config (java_nodes (project_java E s) n)" by (simp add: mask_votes_def Let_def)
    from commit_configuration_unchanged[OF local] show ?thesis by (simp add: Java_Commit)
  next
    case False
    with checks caller Java_Commit have e: "enabled N V s (Handle_Commit c n k)" by (auto simp: mask_votes_def Let_def)
    have updated: "configurations_ok E (execute N C initial_value s (Handle_Commit c n k))"
      using ok by (auto simp: configurations_ok_def put_node_def Let_def)
    have commutes: "java_execute N E (project_java E s) a = project_java E (execute N C initial_value s (Handle_Commit c n k))"
      by (simp add: Java_Commit Let_def mask_votes_def)
    show ?thesis using Java_Commit e updated commutes by simp
  qed
next
  case (Java_Restart n)
  with caller have e: "enabled N V s (Restart n)" by simp
  have updated: "configurations_ok E (execute N C initial_value s (Restart n))"
    using ok by (auto simp: configurations_ok_def put_node_def reset_transient_def)
  have commutes: "java_execute N E (project_java E s) a = project_java E (execute N C initial_value s (Restart n))"
    by (simp add: Java_Restart reset_commutes)
  show ?thesis using Java_Restart e updated commutes by simp
qed

end

theorem coordination_state_refines_tla:
  assumes reach: "java_reachable N E V C initial_value versions j"
  shows "\<exists>s. tla_reachable N V C initial_value versions s \<and> configurations_ok E s \<and> j = project_java E s"
  using reach
proof (induction rule: java_reachable.induct)
  case init
  have "C \<subseteq> N" using init.hyps by blast
  have "tla_reachable N V C initial_value versions (tla_initial initial_value versions)"
    by (rule tla_reachable.init[OF init.hyps(1) \<open>C \<subseteq> N\<close> init.hyps(5,6)])
  then show ?case by (intro exI[of _ "tla_initial initial_value versions"])
    (simp add: configurations_ok_def tla_initial_def java_initial_def mask_votes_def project_java_def)
next
  case (advance j a)
  from advance.IH obtain s where s: "tla_reachable N V C initial_value versions s"
    "configurations_ok E s" "j = project_java E s" by blast
  have "default_strategy N E C" using advance.hyps(1)
    by (induction rule: java_reachable.induct) (auto simp: default_strategy_def)
  then interpret default_strategy N E C .
  show ?case
  proof (cases "java_checks j a")
    case False
    with s show ?thesis by (intro exI[of _ s]) (simp add: java_call_def)
  next
    case True
    then have checks: "java_checks (project_java E s) a" and good: "caller_contract N E V C initial_value (project_java E s) a"
      using advance.hyps(2) s(3) by auto
    from successful_call_simulates[OF s(1,2) checks good] show ?thesis
    proof
      let ?s' = "execute N C initial_value s (abstract_action a)"
      assume "enabled N V s (abstract_action a) \<and>
        java_execute N E (project_java E s) a = project_java E ?s' \<and> configurations_ok E ?s'"
      then show ?thesis using s True by (intro exI[of _ ?s']) (auto simp: java_call_def intro: tla_reachable.advance)
    next
      assume "java_execute N E (project_java E s) a = project_java E s"
      with s True show ?thesis by (intro exI[of _ s]) (simp add: java_call_def)
    qed
  qed
qed

section \<open>A caller condition that the class cannot enforce by itself\<close>

theorem late_commit_has_no_matching_step:
  assumes elected: "election_won (nodes_at s n)"
    and late: "rank_version k \<noteq> published_version (nodes_at s n)"
    and key: "accepted_key (nodes_at s n) = k" "rank_term k = current_term (nodes_at s n)"
    and changes: "local_committed (nodes_at s n) \<noteq> accepted_config (nodes_at s n)" "accepted_config (nodes_at s n) \<noteq> {}"
  shows "\<not> (\<exists>s'. (s' = s \<or> tla_next N V C initial_value s s') \<and>
    java_call N E (project_java E s) (Java_Commit n c k) = project_java E s')"
proof
  assume "\<exists>s'. (s' = s \<or> tla_next N V C initial_value s s') \<and>
    java_call N E (project_java E s) (Java_Commit n c k) = project_java E s'"
  then obtain s' where step: "s' = s \<or> tla_next N V C initial_value s s'"
    and projection: "java_call N E (project_java E s) (Java_Commit n c k) = project_java E s'" by blast
  have post: "local_committed (nodes_at s' n) = accepted_config (nodes_at s n)"
    using arg_cong[OF projection, of "\<lambda>j. local_committed (java_nodes j n)"] key
    by (simp add: java_call_def java_put_def Let_def mask_votes_def)
  have key_after: "accepted_key (nodes_at s' n) = k"
    using arg_cong[OF projection, of "\<lambda>j. accepted_key (java_nodes j n)"] key
    by (simp add: java_call_def java_put_def Let_def mask_votes_def)
  from step have "tla_next N V C initial_value s s'" using post changes(1) by auto
  then obtain a where enabled: "enabled N V s a" and result: "s' = execute N C initial_value s a"
    unfolding tla_next_def by blast
  show False
  proof (cases a)
    case (Bootstrap i)
    have "i \<noteq> n" using enabled Bootstrap changes(2) by (auto simp: Let_def)
    with post changes(1) show False by (simp add: result Bootstrap put_node_def)
  next
    case (Start_Join i d t)
    with post changes(1) show False by (simp add: result put_node_def Let_def reset_transient_def split: if_splits)
  next
    case (Handle_Join i d t r)
    with post changes(1) show False by (simp add: result put_node_def Let_def split: if_splits)
  next
    case (Client_Value i t v payload D)
    with post changes(1) show False by (simp add: result put_node_def Let_def split: if_splits)
  next
    case (Handle_Publish i p payload)
    have np: "i = n"
      by (rule ccontr) (use post changes(1) in \<open>simp add: result Handle_Publish put_node_def\<close>)
    have "request_key p = accepted_key (nodes_at s n)"
      using key_after key(1) by (simp add: result Handle_Publish np put_node_def)
    then show False using enabled Handle_Publish np by (cases "accepted_key (nodes_at s n)") (auto simp: Let_def)
  next
    case (Handle_Response i d r)
    with post changes(1) show False by (simp add: result put_node_def Let_def split: if_splits)
  next
    case (Handle_Commit d i r)
    have n: "i = n"
      by (rule ccontr) (use post changes(1) in \<open>simp add: result Handle_Commit put_node_def Let_def\<close>)
    have "r = k" using enabled Handle_Commit n key(1) by (simp add: Let_def)
    with enabled Handle_Commit n elected late show False by (simp add: Let_def)
  next
    case (Restart i)
    with post changes(1) show False by (simp add: result put_node_def reset_transient_def split: if_splits)
  qed
qed

end
