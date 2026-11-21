theory Coordinator_Lifecycle
  imports Coordination_State_Refinement
begin

section \<open>Coordinator publication lifecycle at mutex boundaries\<close>

record publication_lifecycle =
  leading :: bool
  current_publication :: "rank option"
  registered_publications :: "rank set"
  applied_self_commits :: "rank set"

record 'v coordinator_state =
  coordination :: "'v java_state"
  lifecycle_at :: "node \<Rightarrow> publication_lifecycle"

definition coordinator_initial :: "'v \<Rightarrow> (node \<Rightarrow> nat) \<Rightarrow> 'v coordinator_state" where
  "coordinator_initial v versions = \<lparr>coordination = java_initial v versions,
    lifecycle_at = (\<lambda>_. \<lparr>leading = False, current_publication = None, registered_publications = {},
      applied_self_commits = {}\<rparr>)\<rparr>"

datatype 'v coordinator_event =
    Dispatch "'v java_action" bool
  | Begin_Publication node nat nat 'v config config bool
  | Leave_Leader node
  | Finish_Success node rank
  | Finish_Failure node rank

fun receiver :: "'v java_action \<Rightarrow> node" where
  "receiver (Java_Bootstrap n k v D F) = n"
| "receiver (Java_Start_Join n c t) = n"
| "receiver (Java_Join n c t k) = c"
| "receiver (Java_Client n t v payload_value D F) = n"
| "receiver (Java_Publish n p v) = n"
| "receiver (Java_Response n c k) = c"
| "receiver (Java_Commit n c k) = n"
| "receiver (Java_Restart n) = n"

fun direct_dispatch :: "'v java_action \<Rightarrow> bool" where
  "direct_dispatch (Java_Client n t v payload_value D F) = False"
| "direct_dispatch _ = True"

fun leader_entry ::
  "node set \<Rightarrow> node set \<Rightarrow> 'v java_state \<Rightarrow> 'v java_action \<Rightarrow> bool" where
  "leader_entry N E j (Java_Join n c t k) =
    (\<not> election_won (java_nodes j c) \<and> election_won (java_nodes (java_execute N E j (Java_Join n c t k)) c))"
| "leader_entry N E j _ = False"

text \<open>
  Dispatch represents a successful CoordinationState call. A processJoinRequest
  that enters LEADER is a dispatch with leader entry. A preceding successful
  ensureTermAtLeast call is represented separately by Java_Start_Join, which
  increases the term and leaves LEADER. Failed protocol checks have no core
  effect. A caller may independently leave LEADER or cancel a publication.

  Begin_Publication covers both installation of currentPublication and the
  exception path before installation. Only a registered publication can
  supply an authentic commit. Successful removal requires local acknowledgement,
  which is downstream of handling the matching self-commit. Failed removal
  fences the current term's LEADER before another publication can start.
  An old-term publication can remain in the slot until its callback runs.
\<close>

fun dispatch_input ::
  "node set \<Rightarrow> node set \<Rightarrow> 'v set \<Rightarrow> config \<Rightarrow> 'v \<Rightarrow>
    'v coordinator_state \<Rightarrow> 'v java_action \<Rightarrow> bool" where
  "dispatch_input N E V C v s (Java_Commit n c k) =
    (Commit_Msg c n k \<in> java_journal (coordination s) \<and> k \<in> registered_publications (lifecycle_at s c))"
| "dispatch_input N E V C v s a = caller_contract N E V C v (coordination s) a"

fun lifecycle_after_dispatch ::
  "'v java_action \<Rightarrow> bool \<Rightarrow> publication_lifecycle \<Rightarrow> publication_lifecycle" where
  "lifecycle_after_dispatch (Java_Start_Join n c t) enter g = g\<lparr>leading := False\<rparr>"
| "lifecycle_after_dispatch (Java_Restart n) enter g = g\<lparr>leading := False, current_publication := None\<rparr>"
| "lifecycle_after_dispatch (Java_Commit n c k) enter g =
    (if c = n then g\<lparr>applied_self_commits := insert k (applied_self_commits g)\<rparr> else g)"
| "lifecycle_after_dispatch (Java_Join n c t k) enter g = g\<lparr>leading := leading g \<or> enter\<rparr>"
| "lifecycle_after_dispatch _ enter g = g"

fun coordinator_enabled ::
  "node set \<Rightarrow> node set \<Rightarrow> 'v set \<Rightarrow> config \<Rightarrow> 'v \<Rightarrow>
    'v coordinator_state \<Rightarrow> 'v coordinator_event \<Rightarrow> bool" where
  "coordinator_enabled N E V C v s (Dispatch a enter) =
    (direct_dispatch a \<and> java_checks (coordination s) a \<and> dispatch_input N E V C v s a \<and>
      (enter \<longrightarrow> leader_entry N E (coordination s) a))"
| "coordinator_enabled N E V C v s (Begin_Publication n t w payload_value D F registered) =
    (leading (lifecycle_at s n) \<and> current_publication (lifecycle_at s n) = None \<and>
      java_checks (coordination s) (Java_Client n t w payload_value D F) \<and>
      caller_contract N E V C v (coordination s) (Java_Client n t w payload_value D F))"
| "coordinator_enabled N E V C v s (Leave_Leader n) = (n \<in> N)"
| "coordinator_enabled N E V C v s (Finish_Success n k) =
    (current_publication (lifecycle_at s n) = Some k \<and> k \<in> applied_self_commits (lifecycle_at s n))"
| "coordinator_enabled N E V C v s (Finish_Failure n k) = (current_publication (lifecycle_at s n) = Some k)"

definition put_lifecycle ::
  "'v coordinator_state \<Rightarrow> node \<Rightarrow> publication_lifecycle \<Rightarrow> 'v coordinator_state" where
  "put_lifecycle s n g = s\<lparr>lifecycle_at := (lifecycle_at s)(n := g)\<rparr>"

fun coordinator_execute ::
  "node set \<Rightarrow> node set \<Rightarrow> 'v coordinator_state \<Rightarrow> 'v coordinator_event \<Rightarrow> 'v coordinator_state" where
  "coordinator_execute N E s (Dispatch a enter) =
    (put_lifecycle (s\<lparr>coordination := java_execute N E (coordination s) a\<rparr>) (receiver a)
      (lifecycle_after_dispatch a enter (lifecycle_at s (receiver a))))"
| "coordinator_execute N E s (Begin_Publication n t w payload_value D F registered) =
    (let j = java_execute N E (coordination s) (Java_Client n t w payload_value D F);
         g = lifecycle_at s n
     in put_lifecycle (s\<lparr>coordination := j\<rparr>) n
       (if registered then g\<lparr>current_publication := Some \<lparr>rank_term = t, rank_version = w\<rparr>,
          registered_publications := insert \<lparr>rank_term = t, rank_version = w\<rparr> (registered_publications g)\<rparr> else g))"
| "coordinator_execute N E s (Leave_Leader n) = put_lifecycle s n ((lifecycle_at s n)\<lparr>leading := False\<rparr>)"
| "coordinator_execute N E s (Finish_Success n k) =
    put_lifecycle s n ((lifecycle_at s n)\<lparr>current_publication := None\<rparr>)"
| "coordinator_execute N E s (Finish_Failure n k) =
    put_lifecycle s n ((lifecycle_at s n)\<lparr>current_publication := None,
      leading := (leading (lifecycle_at s n) \<and> rank_term k \<noteq> current_term (java_nodes (coordination s) n))\<rparr>)"

inductive coordinator_reachable ::
  "node set \<Rightarrow> node set \<Rightarrow> 'v set \<Rightarrow> config \<Rightarrow> 'v \<Rightarrow>
    (node \<Rightarrow> nat) \<Rightarrow> 'v coordinator_state \<Rightarrow> bool"
  for N E V C v versions where
  init: "default_strategy N E C \<Longrightarrow> v \<in> V \<Longrightarrow>
    coordinator_reachable N E V C v versions (coordinator_initial v versions)"
| advance: "coordinator_reachable N E V C v versions s \<Longrightarrow> coordinator_enabled N E V C v s event \<Longrightarrow>
    coordinator_reachable N E V C v versions (coordinator_execute N E s event)"

section \<open>Local lifecycle invariants\<close>

definition lifecycle_ok :: "'v local_node \<Rightarrow> publication_lifecycle \<Rightarrow> bool" where
  "lifecycle_ok x g \<longleftrightarrow>
    (leading g \<longrightarrow> election_won x) \<and>
    (\<forall>k\<in>registered_publications g. rank_term k \<le> current_term x \<and>
      (rank_term k = current_term x \<longrightarrow>
        (started_join x \<longrightarrow> election_won x) \<and>
        (leading g \<and> k \<notin> applied_self_commits g \<longrightarrow> current_publication g = Some k) \<and>
        (election_won x \<and> rank_version k \<noteq> published_version x \<longrightarrow> k \<in> applied_self_commits g))) \<and>
    (\<forall>k\<in>applied_self_commits g. k \<le> accepted_key x \<and>
      (k = accepted_key x \<longrightarrow> accepted_config x \<noteq> {} \<and> local_committed x = accepted_config x))"

lemma lifecycleD:
  assumes "lifecycle_ok x g"
  shows
    "leading g \<Longrightarrow> election_won x"
    "k \<in> registered_publications g \<Longrightarrow> rank_term k \<le> current_term x"
    "k \<in> registered_publications g \<Longrightarrow> rank_term k = current_term x \<Longrightarrow> started_join x \<Longrightarrow> election_won x"
    "k \<in> registered_publications g \<Longrightarrow> rank_term k = current_term x \<Longrightarrow> leading g \<Longrightarrow>
      k \<notin> applied_self_commits g \<Longrightarrow> current_publication g = Some k"
    "k \<in> registered_publications g \<Longrightarrow> rank_term k = current_term x \<Longrightarrow> election_won x \<Longrightarrow>
      rank_version k \<noteq> published_version x \<Longrightarrow> k \<in> applied_self_commits g"
    "k \<in> applied_self_commits g \<Longrightarrow> k \<le> accepted_key x"
    "k \<in> applied_self_commits g \<Longrightarrow> k = accepted_key x \<Longrightarrow> accepted_config x \<noteq> {}"
    "k \<in> applied_self_commits g \<Longrightarrow> k = accepted_key x \<Longrightarrow> local_committed x = accepted_config x"
  using assms unfolding lifecycle_ok_def
  by (auto simp del: split_paired_All)

lemma lifecycle_step_down:
  "lifecycle_ok x g \<Longrightarrow> lifecycle_ok x (g\<lparr>leading := False\<rparr>)"
  unfolding lifecycle_ok_def by simp

lemma lifecycle_finish_success:
  assumes "lifecycle_ok x g" "current_publication g = Some p" "p \<in> applied_self_commits g"
  shows "lifecycle_ok x (g\<lparr>current_publication := None\<rparr>)"
  using assms lifecycleD(4)[OF assms(1)]
  unfolding lifecycle_ok_def by auto

lemma lifecycle_finish_failure:
  assumes "lifecycle_ok x g" "current_publication g = Some p"
  shows "lifecycle_ok x (g\<lparr>current_publication := None, leading := (leading g \<and> rank_term p \<noteq> current_term x)\<rparr>)"
  using assms lifecycleD(4)[OF assms(1)]
  unfolding lifecycle_ok_def by auto

lemma lifecycle_begin:
  assumes ok: "lifecycle_ok x g" and leader: "leading g" and free: "current_publication g = None"
    and t: "t = current_term x"
  shows "lifecycle_ok (x\<lparr>published_version := w, published_config := D, publish_votes := {}\<rparr>)
    (if registered then g\<lparr>current_publication := Some \<lparr>rank_term = t, rank_version = w\<rparr>,
      registered_publications := insert \<lparr>rank_term = t, rank_version = w\<rparr> (registered_publications g)\<rparr> else g)"
proof -
  have old: "k \<in> applied_self_commits g" if "k \<in> registered_publications g" "rank_term k = current_term x" for k
    using lifecycleD(4)[OF ok that leader] free by auto
  show ?thesis
    using ok old lifecycleD(1)[OF ok leader] t unfolding lifecycle_ok_def by auto
qed

lemma lifecycle_start_join:
  assumes ok: "lifecycle_ok x g" and inc: "current_term x < t"
  shows "lifecycle_ok ((java_reset x)\<lparr>current_term := t, started_join := True\<rparr>) (g\<lparr>leading := False\<rparr>)"
proof -
  have "rank_term k < t" if "k \<in> registered_publications g" for k
    by (rule le_less_trans[OF lifecycleD(2)[OF ok that] inc])
  then show ?thesis using ok unfolding lifecycle_ok_def java_reset_def by (auto intro: less_imp_le)
qed

lemma lifecycle_restart:
  "lifecycle_ok x g \<Longrightarrow> lifecycle_ok (java_reset x) (g\<lparr>leading := False, current_publication := None\<rparr>)"
  unfolding lifecycle_ok_def java_reset_def by simp

lemma lifecycle_join:
  assumes ok: "lifecycle_ok x g" and start: "started_join x" and keep: "election_won x \<Longrightarrow> won"
    and enter: "enter \<Longrightarrow> \<not> election_won x \<and> won"
  shows "lifecycle_ok (x\<lparr>join_votes := Q, election_won := won,
      published_version := (if won \<and> \<not> election_won x then rank_version (accepted_key x) else published_version x)\<rparr>)
    (g\<lparr>leading := leading g \<or> enter\<rparr>)"
proof (cases "election_won x")
  case True
  with keep enter have "won" "\<not> enter" by auto
  with True ok show ?thesis unfolding lifecycle_ok_def by simp
next
  case False
  have "rank_term k \<noteq> current_term x" if "k \<in> registered_publications g" for k
    using lifecycleD(3)[OF ok that _ start] False by blast
  moreover have "\<not> leading g" using lifecycleD(1)[OF ok] False by blast
  ultimately show ?thesis using ok enter unfolding lifecycle_ok_def by auto
qed

lemma lifecycle_bootstrap:
  assumes ok: "lifecycle_ok x g" and empty: "accepted_config x = {}"
    and k: "k = accepted_key x"
  shows "lifecycle_ok (x\<lparr>accepted_key := k, accepted_value := v, accepted_config := D, local_committed := F\<rparr>) g"
proof -
  have "p \<noteq> k" if "p \<in> applied_self_commits g" for p
    using lifecycleD(7)[OF ok that] empty k by auto
  with ok k show ?thesis unfolding lifecycle_ok_def by auto
qed

lemma lifecycle_receive:
  assumes ok: "lifecycle_ok x g" and newer: "accepted_key x < k"
  shows "lifecycle_ok (x\<lparr>accepted_key := k, accepted_value := v, accepted_config := D, local_committed := F\<rparr>) g"
proof -
  have "\<forall>p\<in>applied_self_commits g. p \<le> k \<and> (p = k \<longrightarrow> D \<noteq> {} \<and> F = D)"
  proof (intro ballI)
    fix p
    assume "p \<in> applied_self_commits g"
    from le_less_trans[OF lifecycleD(6)[OF ok this] newer] have low: "p < k" .
    have "p \<noteq> k" using low by (rule less_imp_neq)
    with less_imp_le[OF low] show "p \<le> k \<and> (p = k \<longrightarrow> D \<noteq> {} \<and> F = D)" by simp
  qed
  then show ?thesis using ok unfolding lifecycle_ok_def by simp
qed

lemma lifecycle_apply:
  assumes ok: "lifecycle_ok x g" and k: "k = accepted_key x" and nonempty: "accepted_config x \<noteq> {}"
  shows "lifecycle_ok (x\<lparr>local_committed := accepted_config x\<rparr>)
    (if self then g\<lparr>applied_self_commits := insert k (applied_self_commits g)\<rparr> else g)"
  using assms unfolding lifecycle_ok_def by auto

section \<open>Facts from the already refined execution prefix\<close>

lemma java_reachable_default_strategy:
  "java_reachable N E V C v versions j \<Longrightarrow> default_strategy N E C"
  by (induction rule: java_reachable.induct) (auto simp: default_strategy_def)

lemma successful_java_call_reachable:
  assumes "java_reachable N E V C v versions j" "java_checks j a" "caller_contract N E V C v j a"
  shows "java_reachable N E V C v versions (java_execute N E j a)"
proof -
  have "java_reachable N E V C v versions (java_call N E j a)"
    by (rule java_reachable.advance[OF assms(1)]) (simp add: assms(3))
  then show ?thesis by (simp add: java_call_def assms(2))
qed

lemma accepted_term_bound:
  assumes "tla_reachable N V C v versions s"
  shows "rank_term (accepted_key (nodes_at s n)) \<le> current_term (nodes_at s n)"
proof -
  obtain a where a: "dynamic_reachable C a" "linked C s a"
    using tla_dynamic_refinement[OF assms] by blast
  have j: "journal_ok C a" using dynamic_invariants[OF a(1)] by auto
  have x: "node_link C a n (nodes_at s n)" by (rule linkedD(1)[OF a(2)])
  from journalD(2)[OF j, of n] node_linkD(1,4)[OF x]
  show ?thesis by (metis key_term)
qed

lemma checked_publish_is_newer:
  assumes reach: "java_reachable N E V C v versions j"
    and checks: "java_checks j (Java_Publish n p payload_value)"
  shows "accepted_key (java_nodes j n) < request_key p"
proof -
  obtain s where s: "tla_reachable N V C v versions s" "j = project_java E s"
    using coordination_state_refines_tla[OF reach] by blast
  let ?k = "accepted_key (java_nodes j n)"
  have "rank_term ?k \<le> current_term (java_nodes j n)"
    using accepted_term_bound[OF s(1), of n] by (simp add: s(2) mask_votes_def)
  then have bound: "rank_term ?k \<le> pub_term p" using checks by (simp add: Let_def)
  have inc: "rank_term ?k = pub_term p \<Longrightarrow> rank_version ?k < pub_version p"
    using checks by (auto simp: Let_def)
  show ?thesis
  proof (cases "rank_term ?k = pub_term p")
    case True
    from bound inc[OF True] True show ?thesis unfolding rank_less_iff by simp
  next
    case False
    with bound have "rank_term ?k < pub_term p" by linarith
    then show ?thesis unfolding rank_less_iff by simp
  qed
qed

lemma matching_commit_facts:
  assumes reach: "java_reachable N E V C v versions j"
    and auth: "Commit_Msg c n k \<in> java_journal j" and checks: "java_checks j (Java_Commit n c k)"
  shows "accepted_config (java_nodes j n) \<noteq> {}"
    "election_won (java_nodes j n) \<Longrightarrow> c = n"
proof -
  obtain s where s: "tla_reachable N V C v versions s" "j = project_java E s"
    using coordination_state_refines_tla[OF reach] by blast
  obtain a where a: "dynamic_reachable C a" "linked C s a"
    using tla_dynamic_refinement[OF s(1)] by blast
  have msg: "Commit_Msg c n k \<in> messages s" using auth by (simp add: s(2))
  from linkedD(3)[OF a(2) msg] obtain h where h: "h \<in> quorum_commits a" "owner h = c" "position h = k" by auto
  have p: "publications_ok C a" and l: "leadership_ok C a" using dynamic_invariants[OF a(1)] by auto
  have pub: "h \<in> publications a" by (rule publicationsD(5)[OF p h(1)])
  have local: "node_link C a n (nodes_at s n)" by (rule linkedD(1)[OF a(2)])
  have cur: "rank_term k = node_term a n" and key: "accepted_key (nodes_at s n) = k"
    using checks node_linkD(1)[OF local] by (auto simp: s(2) Let_def mask_votes_def)
  have pos: "0 < rank_term k" using publication_positive[OF p pub] h(3) by simp
  have accepted: "term_of (durable_history a n) = rank_term k"
    using node_linkD(4)[OF local] key by (metis key_term)
  have "accepted_config (nodes_at s n) \<noteq> {}"
    using node_linkD(5)[OF local] accepted pos by auto
  then show "accepted_config (java_nodes j n) \<noteq> {}" by (simp add: s(2) mask_votes_def)
  assume won: "election_won (java_nodes j n)"
  then have "active_leader a n" using node_linkD(3)[OF local] by (simp add: s(2) mask_votes_def)
  then obtain e where e: "certificate a (n,rank_term k) = Some e" using cur unfolding active_leader_def by auto
  obtain f where "certificate a (c,rank_term k) = Some f" using leadershipD(8)[OF l pub] h(2,3) by auto
  then show "c = n" by (rule dynamic_one_election_candidate_per_term[OF a(1) _ e])
qed

lemma join_keeps_election:
  assumes reach: "java_reachable N E V C v versions j"
    and won: "election_won (java_nodes j c)"
  shows "election_won (java_nodes (java_execute N E j (Java_Join i c t k)) c)"
proof -
  interpret default_strategy N E C by (rule java_reachable_default_strategy[OF reach])
  obtain s where s: "tla_reachable N V C v versions s" "configurations_ok E s" "j = project_java E s"
    using coordination_state_refines_tla[OF reach] by blast
  obtain a where "linked C s a" using tla_dynamic_refinement[OF s(1)] by blast
  then have x: "node_link C a c (nodes_at s c)" by (rule linkedD(1))
  have "election_quorum (nodes_at s c) (join_votes (nodes_at s c))"
    using node_linkD(9)[OF x] won by (simp add: s(3) mask_votes_def)
  from election_quorum_insert[OF this, of i]
  have q: "election_quorum (nodes_at s c) (insert i (join_votes (nodes_at s c)))" .
  have "java_election (mask_votes E (nodes_at s c)) (insert i (join_votes (nodes_at s c)) \<inter> E)"
    using election_mask[OF configurations_okD(2,1)[OF s(2), of c], of "insert i (join_votes (nodes_at s c))"] q by simp
  then show ?thesis by (simp add: s(3) java_put_def Let_def eligible_insert)
qed

lemma java_execute_other_node:
  "i \<noteq> receiver a \<Longrightarrow> java_nodes (java_execute N E j a) i = java_nodes j i"
  by (cases a) (simp_all add: java_put_def Let_def)

lemma dispatch_preserves_lifecycle:
  assumes reach: "java_reachable N E V C v versions j"
    and ok: "lifecycle_ok (java_nodes j (receiver a)) g"
    and direct: "direct_dispatch a" and checks: "java_checks j a"
    and caller: "caller_contract N E V C v j a"
    and entry: "enter \<Longrightarrow> leader_entry N E j a"
  shows "lifecycle_ok (java_nodes (java_execute N E j a) (receiver a)) (lifecycle_after_dispatch a enter g)"
proof (cases a)
  case (Java_Bootstrap n k payload_value D F)
  let ?x = "java_nodes j n"
  have empty: "accepted_config ?x = {}" using checks Java_Bootstrap by simp
  have key: "k = accepted_key ?x" using caller Java_Bootstrap by (simp add: Let_def)
  have "lifecycle_ok ?x g" using ok Java_Bootstrap by simp
  then have "lifecycle_ok (?x\<lparr>accepted_key := k, accepted_value := payload_value, accepted_config := D,
    local_committed := F\<rparr>) g" by (rule lifecycle_bootstrap[OF _ empty key])
  then show ?thesis by (simp add: Java_Bootstrap java_put_def)
next
  case (Java_Start_Join n c t)
  then have "current_term (java_nodes j n) < t" using checks by simp
  with ok Java_Start_Join show ?thesis by (simp add: java_put_def lifecycle_start_join Let_def)
next
  case (Java_Join n c t k)
  let ?x = "java_nodes j c"
  let ?q = "add_vote E n (join_votes ?x)"
  let ?won = "java_election ?x ?q"
  have starter: "started_join ?x" using checks Java_Join by (simp add: Let_def)
  have retain: "election_won ?x \<Longrightarrow> ?won"
    using join_keeps_election[OF reach, of c n t k] by (simp add: java_put_def Let_def)
  have entered: "enter \<Longrightarrow> \<not> election_won ?x \<and> ?won"
    using entry Java_Join by (simp add: java_put_def Let_def)
  have "lifecycle_ok ?x g" using ok Java_Join by simp
  from lifecycle_join[OF this starter retain entered] show ?thesis
    by (simp add: Java_Join java_put_def Let_def)
next
  case (Java_Client n t w payload_value D F)
  with direct show ?thesis by simp
next
  case (Java_Publish n p payload_value)
  have newer: "accepted_key (java_nodes j n) < request_key p"
    by (rule checked_publish_is_newer[OF reach]) (use Java_Publish checks in simp)
  with ok Java_Publish show ?thesis by (simp add: java_put_def lifecycle_receive)
next
  case (Java_Response n c k)
  with ok show ?thesis by (simp add: java_put_def Let_def lifecycle_ok_def)
next
  case (Java_Commit n c k)
  then have "Commit_Msg c n k \<in> java_journal j" using caller by (simp add: Let_def)
  then have nonempty: "accepted_config (java_nodes j n) \<noteq> {}"
    by (rule matching_commit_facts(1)[OF reach]) (use checks Java_Commit in simp)
  have "k = accepted_key (java_nodes j n)" using checks Java_Commit by (simp add: Let_def)
  with ok Java_Commit nonempty show ?thesis by (simp add: java_put_def lifecycle_apply)
next
  case (Java_Restart n)
  with ok show ?thesis by (simp add: java_put_def lifecycle_restart)
qed

section \<open>The coordinator discharges the ordering clause\<close>

lemma coordinator_dispatch_contract:
  assumes reach: "java_reachable N E V C v versions (coordination s)"
    and inv: "\<forall>i. lifecycle_ok (java_nodes (coordination s) i) (lifecycle_at s i)"
    and enabled: "coordinator_enabled N E V C v s (Dispatch a enter)"
  shows "caller_contract N E V C v (coordination s) a"
proof (cases a)
  case (Java_Commit n c k)
  let ?x = "java_nodes (coordination s) n"
  let ?g = "lifecycle_at s n"
  have ok: "lifecycle_ok ?x ?g" using inv by blast
  have auth: "Commit_Msg c n k \<in> java_journal (coordination s)"
    and reg: "k \<in> registered_publications (lifecycle_at s c)"
    and checks: "java_checks (coordination s) (Java_Commit n c k)"
    using Java_Commit enabled by simp_all
  from checks have t: "rank_term k = current_term ?x" and key: "k = accepted_key ?x"
    by (auto simp: Let_def)
  have "local_committed ?x = accepted_config ?x"
    if won: "election_won ?x" and late: "rank_version k \<noteq> published_version ?x"
  proof -
    have "c = n" by (rule matching_commit_facts(2)[OF reach auth checks won])
    with reg have "k \<in> registered_publications ?g" by simp
    from lifecycleD(5)[OF ok this t won late] show ?thesis by (rule lifecycleD(8)[OF ok _ key])
  qed
  with auth show ?thesis using Java_Commit by (simp add: Let_def)
qed (use enabled in simp_all)

lemma coordinator_invariants:
  assumes reach: "coordinator_reachable N E V C v versions s"
  shows "java_reachable N E V C v versions (coordination s) \<and>
    (\<forall>i. lifecycle_ok (java_nodes (coordination s) i) (lifecycle_at s i))"
  using reach
proof (induction rule: coordinator_reachable.induct)
  case init
  have "java_reachable N E V C v versions (java_initial v versions)"
    using init.hyps unfolding default_strategy_def by (auto intro: java_reachable.init)
  then show ?case by (simp add: coordinator_initial_def lifecycle_ok_def)
next
  case (advance s event)
  then have reach: "java_reachable N E V C v versions (coordination s)"
    and inv: "\<forall>i. lifecycle_ok (java_nodes (coordination s) i) (lifecycle_at s i)" by auto
  from advance.hyps(2) show ?case
  proof (cases event)
    case (Dispatch a enter)
    have en: "coordinator_enabled N E V C v s (Dispatch a enter)" using advance.hyps(2) Dispatch by simp
    have contract: "caller_contract N E V C v (coordination s) a" by (rule coordinator_dispatch_contract[OF reach inv en])
    have checks: "java_checks (coordination s) a" using en by simp
    have core: "java_reachable N E V C v versions (java_execute N E (coordination s) a)"
      by (rule successful_java_call_reachable[OF reach checks contract])
    have at_node: "lifecycle_ok (java_nodes (java_execute N E (coordination s) a) (receiver a))
        (lifecycle_after_dispatch a enter (lifecycle_at s (receiver a)))"
      by (rule dispatch_preserves_lifecycle[OF reach _ _ checks contract]) (use en inv in auto)
    with core inv Dispatch show ?thesis
      by (auto simp: put_lifecycle_def java_execute_other_node)
  next
    case (Begin_Publication n t w payload_value D F registered)
    let ?a = "Java_Client n t w payload_value D F"
    have checks: "java_checks (coordination s) ?a"
      and contract: "caller_contract N E V C v (coordination s) ?a"
      and lead: "leading (lifecycle_at s n)" and empty: "current_publication (lifecycle_at s n) = None"
      using advance.hyps(2) Begin_Publication by simp_all
    have t: "t = current_term (java_nodes (coordination s) n)" using checks by (simp add: Let_def)
    have core: "java_reachable N E V C v versions (java_execute N E (coordination s) ?a)"
      by (rule successful_java_call_reachable[OF reach checks contract])
    have "lifecycle_ok (java_nodes (coordination s) n) (lifecycle_at s n)" using inv by blast
    from lifecycle_begin[OF this lead empty t, where w=w and D=D and registered=registered] core inv Begin_Publication
    show ?thesis by (auto simp: put_lifecycle_def java_put_def Let_def)
  next
    case (Leave_Leader n)
    with reach inv show ?thesis by (auto simp: put_lifecycle_def intro: lifecycle_step_down)
  next
    case (Finish_Success n k)
    with reach inv advance.hyps(2) show ?thesis by (auto simp: put_lifecycle_def intro: lifecycle_finish_success)
  next
    case (Finish_Failure n k)
    with reach inv advance.hyps(2) show ?thesis by (auto simp: put_lifecycle_def intro: lifecycle_finish_failure)
  qed
qed

theorem coordinator_commit_ordering:
  assumes "coordinator_reachable N E V C v versions s"
    "coordinator_enabled N E V C v s (Dispatch (Java_Commit n c k) enter)"
  shows "caller_contract N E V C v (coordination s) (Java_Commit n c k)"
  using coordinator_invariants[OF assms(1)] assms(2) by (blast intro: coordinator_dispatch_contract)

theorem late_self_commit_is_replay:
  assumes reach: "coordinator_reachable N E V C v versions s"
    and enabled: "coordinator_enabled N E V C v s (Dispatch (Java_Commit n n k) enter)"
    and won: "election_won (java_nodes (coordination s) n)"
    and late: "rank_version k \<noteq> published_version (java_nodes (coordination s) n)"
  shows "k \<in> applied_self_commits (lifecycle_at s n) \<and>
    java_call N E (coordination s) (Java_Commit n n k) = coordination s"
proof -
  let ?x = "java_nodes (coordination s) n"
  let ?g = "lifecycle_at s n"
  have inv: "lifecycle_ok ?x ?g" using coordinator_invariants[OF reach] by blast
  from enabled have checks: "java_checks (coordination s) (Java_Commit n n k)"
    and reg: "k \<in> registered_publications ?g" by simp_all
  from checks have t: "rank_term k = current_term ?x" and key: "k = accepted_key ?x" by (auto simp: Let_def)
  have applied: "k \<in> applied_self_commits ?g" by (rule lifecycleD(5)[OF inv reg t won late])
  have same_config: "local_committed ?x = accepted_config ?x" by (rule lifecycleD(8)[OF inv applied key])
  from applied commit_configuration_unchanged[OF same_config, of N E n k] checks
  show ?thesis by (simp add: java_call_def)
qed

theorem coordinator_refines_tla:
  assumes "coordinator_reachable N E V C v versions s"
  shows "\<exists>t. tla_reachable N V C v versions t \<and> configurations_ok E t \<and> coordination s = project_java E t"
  using coordinator_invariants[OF assms] by (blast intro: coordination_state_refines_tla)

end
