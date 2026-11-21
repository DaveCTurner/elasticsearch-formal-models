theory Publication_Ancestry
  imports Coordination_Transport
begin

section \<open>Accepted state during a MasterService batch\<close>

abbreviation batch_node where "batch_node s n \<equiv> java_nodes (coordination s) n"
abbreviation batch_slot where "batch_slot s n \<equiv> current_publication (lifecycle_at s n)"
abbreviation batch_leading where "batch_leading s n \<equiv> leading (lifecycle_at s n)"

definition accepted_base where
  "accepted_base x = (accepted_key x, accepted_value x, accepted_config x, local_committed x)"

text \<open>
  This projection omits the masterless view's node and block edits. In
  particular it retains the committed configuration, which can change
  without an increase of the accepted key. We reason at Coordinator
  mutex boundaries, with a single MasterService batch outstanding at its
  node. A process restart discards the outstanding computation.
\<close>

fun between_batches where
  "between_batches n s (Begin_Publication c t w u D F install) = (c \<noteq> n)"
| "between_batches n s (Dispatch (Java_Restart c) enter) = (c \<noteq> n)"
| "between_batches n s (Dispatch (Java_Publish c p u) enter) =
    (c = n \<longrightarrow> registered s (pub_owner p) (request_key p))"
| "between_batches n s _ = True"

lemma registered_publish_delivery:
  assumes "transport_reachable N E V C v versions s H"
    "Publish_RPC c i n p u \<in> H" "decode_publication p u wire = Some decoded"
    "compatible_publication p u wire"
  shows "between_batches n s (Dispatch (Java_Publish n decoded u) enter)"
proof -
  have "supported N E s (Publish_RPC c i n p u)"
    using transport_invariants[OF assms(1)] assms(2) by blast
  with decode_publication_correct[OF assms(4,3)] show ?thesis
    by (auto simp: publish_from_def)
qed

definition batch_step where
  "batch_step N E V C v n s s' \<longleftrightarrow>
    (\<exists>event. coordinator_enabled N E V C v s event \<and> between_batches n s event \<and>
      s' = coordinator_execute N E s event)"

lemma batch_step_reachable:
  "coordinator_reachable N E V C v versions s \<Longrightarrow> batch_step N E V C v n s s' \<Longrightarrow>
    coordinator_reachable N E V C v versions s'"
  unfolding batch_step_def by (blast intro: coordinator_reachable.advance)

lemma batch_step_raises_term:
  assumes "batch_step N E V C v n s s'"
  shows "current_term (batch_node s n) \<le> current_term (batch_node s' n)"
proof -
  obtain event where en: "coordinator_enabled N E V C v s event"
    and result: "s' = coordinator_execute N E s event" using assms unfolding batch_step_def by blast
  show ?thesis
  proof (cases event)
    case (Dispatch a enter)
    then show ?thesis using en result
      by (cases a) (auto simp: java_put_def put_lifecycle_def Let_def java_reset_def intro: less_imp_le)
  qed (use result in \<open>auto simp: java_put_def put_lifecycle_def Let_def\<close>)
qed

lemma batch_step_keeps_slot_empty:
  assumes "batch_step N E V C v n s s'" "batch_slot s n = None"
  shows "batch_slot s' n = None"
proof -
  obtain event where event: "between_batches n s event" "s' = coordinator_execute N E s event"
    using assms(1) unfolding batch_step_def by blast
  show ?thesis
  proof (cases event)
    case (Dispatch a enter)
    with assms(2) event show ?thesis
      by (cases a) (auto simp: put_lifecycle_def split: if_splits)
  qed (use assms(2) event in \<open>auto simp: put_lifecycle_def Let_def split: if_splits\<close>)
qed

lemma same_term_batch_leader:
  assumes reach: "coordinator_reachable N E V C v versions s"
    and run: "batch_step N E V C v n s s'"
    and same_term: "current_term (batch_node s' n) = current_term (batch_node s n)"
    and won: "election_won (batch_node s n)"
  shows "election_won (batch_node s' n) \<and> (batch_leading s' n \<longrightarrow> batch_leading s n)"
proof -
  obtain event where event: "coordinator_enabled N E V C v s event" "between_batches n s event"
    "s' = coordinator_execute N E s event" using run unfolding batch_step_def by blast
  have java: "java_reachable N E V C v versions (coordination s)"
    using coordinator_invariants[OF reach] by blast
  show ?thesis
  proof (cases event)
    case (Dispatch a enter)
    show ?thesis using event same_term won Dispatch join_keeps_election[OF java]
      by (cases a) (auto simp: java_put_def put_lifecycle_def Let_def java_reset_def)
  qed (use event same_term won in \<open>auto simp: java_put_def put_lifecycle_def Let_def split: if_splits\<close>)
qed

lemma elected_node_has_config:
  assumes "java_reachable N E V C v versions j" "election_won (java_nodes j n)"
  shows "accepted_config (java_nodes j n) \<noteq> {}"
proof -
  obtain y where y: "tla_reachable N V C v versions y" "j = project_java E y"
    using coordination_state_refines_tla[OF assms(1)] by blast
  obtain a where "linked C y a" using tla_dynamic_refinement[OF y(1)] by blast
  then have "node_link C a n (nodes_at y n)" by (rule linkedD(1))
  from node_linkD(9)[OF this] assms(2) show ?thesis
    by (auto simp: y(2) mask_votes_def election_quorum_def dest: quorum_nonempty)
qed

lemma publish_to_current_winner:
  assumes reach: "java_reachable N E V C v versions j"
    and auth: "Publish_Msg n p u \<in> java_journal j"
    and same_term: "pub_term p = current_term (java_nodes j n)"
    and won: "election_won (java_nodes j n)"
  shows "pub_owner p = n"
proof -
  obtain y where y: "tla_reachable N V C v versions y" "j = project_java E y"
    using coordination_state_refines_tla[OF reach] by blast
  obtain a where a: "dynamic_reachable C a" "linked C y a"
    using tla_dynamic_refinement[OF y(1)] by blast
  have "Publish_Msg n p u \<in> messages y" using auth by (simp add: y(2))
  from linkedD(3)[OF a(2) this] obtain h where h: "h @ [p] \<in> publications a" by auto
  have l: "leadership_ok C a" using dynamic_invariants[OF a(1)] by auto
  from leadershipD(8)[OF l h] obtain e where e: "certificate a (pub_owner p,pub_term p) = Some e" by auto
  have node: "node_link C a n (nodes_at y n)" by (rule linkedD(1)[OF a(2)])
  have "active_leader a n" "node_term a n = pub_term p"
    using node_linkD(1,3)[OF node] same_term won by (simp_all add: y(2) mask_votes_def)
  then obtain f where f: "certificate a (n,pub_term p) = Some f" by (auto simp: active_leader_def)
  show ?thesis by (rule dynamic_one_election_candidate_per_term[OF a(1) e f])
qed

lemma quiet_winner_acceptance:
  assumes reach: "coordinator_reachable N E V C v versions s"
    and step: "batch_step N E V C v n s s'"
    and leader: "batch_leading s n"
    and free: "batch_slot s n = None"
  shows "accepted_base (batch_node s' n) = accepted_base (batch_node s n)"
proof -
  obtain event where ev: "coordinator_enabled N E V C v s event" "between_batches n s event"
    "s' = coordinator_execute N E s event" using step unfolding batch_step_def by blast
  have java: "java_reachable N E V C v versions (coordination s)" and
    life: "lifecycle_ok (batch_node s n) (lifecycle_at s n)"
    using coordinator_invariants[OF reach] by blast+
  have won: "election_won (batch_node s n)" by (rule lifecycleD(1)[OF life leader])
  have config: "accepted_config (batch_node s n) \<noteq> {}" by (rule elected_node_has_config[OF java won])
  have applied: "k \<in> applied_self_commits (lifecycle_at s n)"
    if reg: "registered s n k" and same_term: "rank_term k = current_term (batch_node s n)" for k
    using lifecycleD(4)[OF life reg same_term leader] free by auto
  have same: "accepted_base (batch_node s' n) = accepted_base (batch_node s n)"
    if "event = Dispatch a enter" and "receiver a \<noteq> n" for a enter
    using that ev(3) java_execute_other_node[of n a N E "coordination s"] by (simp add: put_lifecycle_def)
  show ?thesis
  proof (cases event)
    case (Dispatch a enter)
    have checks: "java_checks (coordination s) a" and input: "dispatch_input N E V C v s a"
      using ev(1) Dispatch by simp_all
    show ?thesis
    proof (cases "receiver a = n")
      case False
      then show ?thesis by (rule same[OF Dispatch])
    next
      case True
      show ?thesis
      proof (cases a)
        case (Java_Publish c p u)
        from Java_Publish True have c: "c = n" by simp
        have cks: "java_checks (coordination s) (Java_Publish n p u)" using checks Java_Publish c by simp
        have same_term: "pub_term p = current_term (batch_node s n)" using cks by (simp add: Let_def)
        have msg: "Publish_Msg n p u \<in> journal s" using input Java_Publish c by simp
        have own: "pub_owner p = n" by (rule publish_to_current_winner[OF java msg same_term won])
        have reg: "registered s n (request_key p)" using ev(2) Dispatch Java_Publish c own by simp
        have "request_key p \<in> applied_self_commits (lifecycle_at s n)" by (rule applied[OF reg]) (simp add: same_term)
        from lifecycleD(6)[OF life this] checked_publish_is_newer[OF java cks]
        show ?thesis by (simp add: not_less)
      next
        case (Java_Commit d c k)
        from Java_Commit True have d: "d = n" by simp
        have cks: "java_checks (coordination s) (Java_Commit n c k)" using checks Java_Commit d by simp
        have msg: "Commit_Msg c n k \<in> journal s" using input Java_Commit d by simp
        have own: "c = n" by (rule matching_commit_facts(2)[OF java msg cks won])
        have reg: "registered s n k" using input Java_Commit own by simp
        have same_t: "rank_term k = current_term (batch_node s n)" and key: "k = accepted_key (batch_node s n)"
          using cks by (auto simp: Let_def)
        from lifecycleD(8)[OF life applied[OF reg same_t] key]
        have "local_committed (batch_node s n) = accepted_config (batch_node s n)" .
        with ev(3) Dispatch Java_Commit d show ?thesis by (simp add: java_put_def put_lifecycle_def accepted_base_def)
      qed (use ev Dispatch checks True config in
        \<open>auto simp: java_put_def put_lifecycle_def Let_def java_reset_def accepted_base_def\<close>)
    qed
  qed (use ev in \<open>auto simp: java_put_def put_lifecycle_def Let_def accepted_base_def\<close>)
qed

lemma batch_trace_frame:
  assumes "rtranclp (batch_step N E V C v n) start finish"
    and initial: "coordinator_reachable N E V C v versions start"
    and free: "batch_slot start n = None"
    and winner: "election_won (batch_node start n)"
  shows "coordinator_reachable N E V C v versions finish \<and>
    current_term (batch_node start n) \<le> current_term (batch_node finish n) \<and> batch_slot finish n = None \<and>
    (current_term (batch_node start n) = current_term (batch_node finish n) \<longrightarrow>
      election_won (batch_node finish n) \<and> (batch_leading finish n \<longrightarrow>
        accepted_base (batch_node finish n) = accepted_base (batch_node start n)))"
  using assms(1)
proof induction
  case base
  then show ?case using initial free winner by simp
next
  case (step s s')
  have r: "coordinator_reachable N E V C v versions s" and slot: "batch_slot s n = None"
    and low: "current_term (batch_node start n) \<le> current_term (batch_node s n)"
    using step.IH by auto
  have up: "current_term (batch_node s n) \<le> current_term (batch_node s' n)"
    by (rule batch_step_raises_term[OF step.hyps(2)])
  have same: "election_won (batch_node s' n) \<and>
    (batch_leading s' n \<longrightarrow> accepted_base (batch_node s' n) = accepted_base (batch_node start n))"
    if endpoint: "current_term (batch_node start n) = current_term (batch_node s' n)"
  proof -
    have terms: "current_term (batch_node start n) = current_term (batch_node s n)"
      using endpoint low up by simp
    have wins: "election_won (batch_node s n)" using terms step.IH by simp
    have now: "current_term (batch_node s' n) = current_term (batch_node s n)" using terms endpoint by simp
    have frame: "election_won (batch_node s' n) \<and> (batch_leading s' n \<longrightarrow> batch_leading s n)"
      by (rule same_term_batch_leader[OF r step.hyps(2) now wins])
    have frozen: "accepted_base (batch_node s' n) = accepted_base (batch_node start n)"
      if lead: "batch_leading s' n"
    proof -
      have before: "batch_leading s n" using frame lead by simp
      have orig: "accepted_base (batch_node s n) = accepted_base (batch_node start n)"
        using step.IH terms before by simp
      from quiet_winner_acceptance[OF r step.hyps(2) before slot] orig show ?thesis by simp
    qed
    show ?thesis using frame frozen by blast
  qed
  show ?case using same up low batch_step_reachable[OF r step.hyps(2)]
    batch_step_keeps_slot_empty[OF step.hyps(2) slot] by auto
qed

section \<open>Assertion-independent admission and producer obligations\<close>

definition runtime_publication_admission where
  "runtime_publication_admission s n t w u D F \<longleftrightarrow>
    batch_leading s n \<and> batch_slot s n = None \<and>
    java_checks (coordination s) (Java_Client n t w u D F)"

theorem admitted_batch_keeps_its_accepted_base:
  assumes trace: "rtranclp (batch_step N E V C v n) start finish"
    and reach: "coordinator_reachable N E V C v versions start"
    and free: "batch_slot start n = None"
    and winner: "election_won (batch_node start n)"
    and task_term: "t \<le> current_term (batch_node start n)"
    and admission: "runtime_publication_admission finish n t w u D F"
  shows "accepted_base (batch_node finish n) = accepted_base (batch_node start n)"
proof -
  have "t = current_term (batch_node finish n)" "batch_leading finish n"
    using admission by (auto simp: runtime_publication_admission_def Let_def)
  with task_term batch_trace_frame[OF trace reach free winner] show ?thesis by auto
qed

theorem admitted_batch_refines_begin:
  assumes trace: "rtranclp (batch_step N E V C v n) start finish"
    and reach: "coordinator_reachable N E V C v versions start"
    and free: "batch_slot start n = None"
    and winner: "election_won (batch_node start n)"
    and task_term: "t \<le> current_term (batch_node start n)"
    and admission: "runtime_publication_admission finish n t w u D F"
    and producer: "parent = accepted_base (batch_node start n)"
      "F = local_committed (batch_node start n)" "result_owner = n"
    and domain: "n \<in> N" "u \<in> V" "D \<subseteq> E"
  shows "parent = accepted_base (batch_node finish n)"
    "coordinator_enabled N E V C v finish (Begin_Publication result_owner t w u D F install)"
proof -
  have same: "accepted_base (batch_node finish n) = accepted_base (batch_node start n)"
    by (rule admitted_batch_keeps_its_accepted_base[OF trace reach free winner task_term admission])
  then show "parent = accepted_base (batch_node finish n)" using producer by simp
  have "F = local_committed (batch_node finish n)" using same producer(2) unfolding accepted_base_def by simp
  with domain producer(3) admission show
    "coordinator_enabled N E V C v finish (Begin_Publication result_owner t w u D F install)"
    by (simp add: runtime_publication_admission_def)
qed

corollary admitted_batch_uses_captured_parent_in_tla:
  assumes trace: "rtranclp (batch_step N E V C v n) start finish"
    and reach: "coordinator_reachable N E V C v versions start"
    and free: "batch_slot start n = None"
    and winner: "election_won (batch_node start n)"
    and task_term: "t \<le> current_term (batch_node start n)"
    and admission: "runtime_publication_admission finish n t w u D F"
    and producer: "F = local_committed (batch_node start n)"
    and domain: "n \<in> N" "u \<in> V" "D \<subseteq> E"
  shows "\<exists>a a'. tla_reachable N V C v versions a \<and> tla_reachable N V C v versions a' \<and>
    coordination finish = project_java E a \<and>
    coordination (coordinator_execute N E finish (Begin_Publication n t w u D F install)) = project_java E a' \<and>
    (accepted_key (batch_node start n), \<lparr>rank_term = t, rank_version = w\<rparr>) \<in> descendant a'"
proof -
  let ?event = "Begin_Publication n t w u D F install"
  let ?update = "Client_Value n t w u D"
  have admissible: "coordinator_enabled N E V C v finish ?event"
    by (rule admitted_batch_refines_begin(2)[OF trace reach free winner task_term admission
      refl producer refl domain])
  have closing: "coordinator_reachable N E V C v versions finish"
    using batch_trace_frame[OF trace reach free winner] by blast
  obtain a where a: "tla_reachable N V C v versions a" "configurations_ok E a"
    "coordination finish = project_java E a" using coordinator_refines_tla[OF closing] by blast
  let ?a' = "execute N C v a ?update"
  have r: "java_reachable N E V C v versions (coordination finish)" using coordinator_invariants[OF closing] by blast
  interpret default_strategy N E C by (rule java_reachable_default_strategy[OF r])
  have checks: "java_checks (project_java E a) (Java_Client n t w u D F)"
    using admissible a(3) by simp
  have carried: "F = local_committed (nodes_at a n)"
    using admissible a(3) by (simp add: mask_votes_def)
  have Q: "quorum D (join_votes (nodes_at a n))" using checks
    by (simp add: Let_def mask_votes_def quorum_mask[OF domain(3)])
  have nonempty: "D \<noteq> {}" using quorum_nonempty[OF Q] .
  have en: "enabled N V a ?update" using Q checks domain nonempty elig
    by (auto simp: mask_votes_def Let_def)
  have a': "tla_reachable N V C v versions ?a'" by (rule tla_reachable.advance[OF a(1) en])
  have base: "accepted_key (nodes_at a n) = accepted_key (batch_node start n)"
    using admitted_batch_keeps_its_accepted_base[OF trace reach free winner task_term admission] a(3)
    by (simp add: accepted_base_def mask_votes_def)
  have edge: "(accepted_key (batch_node start n), \<lparr>rank_term = t, rank_version = w\<rparr>) \<in> descendant ?a'"
    by (simp add: base[symmetric] extend_descendant_def Let_def)
  have projection: "coordination (coordinator_execute N E finish ?event) = project_java E ?a'"
    by (simp add: a(3) carried put_lifecycle_def Let_def mask_votes_def)
  show ?thesis using a(1,3) a' projection edge by blast
qed

text \<open>
  The runtime test has no old-state argument. It also does not test the
  supplied committed configuration. A task can keep its state and metadata
  versions, return an altered committed configuration, and pass the same
  runtime coordination tests. Actual derivation from the argument supplied
  to the task remains a condition on task executors.
\<close>

lemma runtime_admission_ignores_supplied_committed_config:
  "runtime_publication_admission s n t w u D F =
    runtime_publication_admission s n t w u D F'"
  by (simp add: runtime_publication_admission_def)

lemma runtime_admission_cannot_imply_begin:
  assumes "runtime_publication_admission s n t w u D F"
    "F' \<noteq> local_committed (batch_node s n)"
  shows "runtime_publication_admission s n t w u D F' \<and>
    \<not> coordinator_enabled N E V C v s (Begin_Publication n t w u D F' install)"
  using assms by (auto simp: runtime_publication_admission_def)

text \<open>
  The admission test is satisfiable after a real model election. The
  example changes the carried committed configuration while the leader's
  accepted configuration, the supplied accepted configuration, and the
  quorum are all unchanged. It exercises the executor/API boundary.
\<close>

lemma admitted_wrong_committed_config_example:
  "\<exists>s :: unit coordinator_state.
    coordinator_reachable {0,1} {0,1} {()} {0} () (\<lambda>_. 0) s \<and>
    runtime_publication_admission s 0 1 1 () {0} {1} \<and>
    \<not> coordinator_enabled {0,1} {0,1} {()} {0} () s (Begin_Publication 0 1 1 () {0} {1} True)"
proof -
  let ?N = "{0,1}"
  let ?s = "coordinator_initial () (\<lambda>_. 0)"
  let ?e1 = "Dispatch (Java_Bootstrap 0 rank_zero () {0} {0}) False"
  let ?s1 = "coordinator_execute ?N ?N ?s ?e1"
  let ?e2 = "Dispatch (Java_Start_Join 0 0 1) False"
  let ?s2 = "coordinator_execute ?N ?N ?s1 ?e2"
  let ?e3 = "Dispatch (Java_Join 0 0 1 rank_zero) True"
  let ?s3 = "coordinator_execute ?N ?N ?s2 ?e3"
  note eval = coordinator_initial_def java_initial_def put_lifecycle_def Let_def java_put_def
    java_reset_def add_vote_def java_election_def java_has_quorum_def signed_int_def
  have initial: "coordinator_reachable ?N ?N {()} {0} () (\<lambda>_. 0) ?s"
    by (rule coordinator_reachable.init) (simp_all add: default_strategy_def)
  have e1: "coordinator_enabled ?N ?N {()} {0} () ?s ?e1" by (simp add: eval)
  have e2: "coordinator_enabled ?N ?N {()} {0} () ?s1 ?e2" by (simp add: eval)
  have e3: "coordinator_enabled ?N ?N {()} {0} () ?s2 ?e3" by (simp add: eval)
  have r: "coordinator_reachable ?N ?N {()} {0} () (\<lambda>_. 0) ?s3"
    by (rule coordinator_reachable.advance[OF coordinator_reachable.advance[OF
      coordinator_reachable.advance[OF initial e1] e2] e3])
  have admit: "runtime_publication_admission ?s3 0 1 1 () {0} {1}"
    by (simp add: runtime_publication_admission_def eval)
  have differs: "{1} \<noteq> local_committed (batch_node ?s3 0)" by (simp add: eval)
  from r runtime_admission_cannot_imply_begin[OF admit differs, where N="?N" and E="?N"]
  show ?thesis by blast
qed

end
