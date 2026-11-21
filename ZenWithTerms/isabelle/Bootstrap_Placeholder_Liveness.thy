theory Bootstrap_Placeholder_Liveness
  imports Bootstrap_Liveness
begin

section \<open>Common configured bootstrap with placeholders\<close>

abbreviation actual_bootstrap_members where
  "actual_bootstrap_members C \<equiv> {n. Discovered_ID n \<in> C}"

definition bootstrap_member_encoding where
  "bootstrap_member_encoding U index p = (case p of
     Discovered_ID n \<Rightarrow> n
   | Bootstrap_Placeholder r \<Rightarrow> Suc (Max U) + index r)"

lemma finite_bootstrap_member_encoding:
  fixes C :: "'r initial_member set" and index :: "'r \<Rightarrow> nat"
  assumes finite_u: "finite U"
    and inj: "inj_on index R"
    and roster: "\<And>r. Bootstrap_Placeholder r \<in> C \<Longrightarrow> r \<in> R"
    and real: "actual_bootstrap_members C \<subseteq> U"
  shows "\<And>n. bootstrap_member_encoding U index (Discovered_ID n) = n"
    "inj_on (bootstrap_member_encoding U index) C"
    "\<And>r. Bootstrap_Placeholder r \<in> C \<Longrightarrow> bootstrap_member_encoding U index (Bootstrap_Placeholder r) \<notin> U"
proof -
  let ?encode = "bootstrap_member_encoding U index"
  have outside: "?encode (Bootstrap_Placeholder r) \<notin> U" for r
  proof
    assume "?encode (Bootstrap_Placeholder r) \<in> U"
    from Max_ge[OF finite_u this] show False by (simp add: bootstrap_member_encoding_def)
  qed
  have real_in_universe: "Discovered_ID n \<in> C \<Longrightarrow> n \<in> U" for n using real by blast
  show "inj_on ?encode C"
  proof (rule inj_onI)
    fix x y
    assume "x \<in> C" "y \<in> C" "?encode x = ?encode y"
    then show "x = y"
      using outside inj real_in_universe roster
      by (cases x; cases y) (auto simp: bootstrap_member_encoding_def inj_on_def)
  qed
  show "\<And>n. ?encode (Discovered_ID n) = n" by (simp add: bootstrap_member_encoding_def)
  show "\<And>r. Bootstrap_Placeholder r \<in> C \<Longrightarrow> ?encode (Bootstrap_Placeholder r) \<notin> U"
    using outside by simp
qed

lemma encoded_bootstrap_quorum:
  assumes encoding: "inj_on encode C" "\<And>n. encode (Discovered_ID n) = n"
    and real: "H \<subseteq> actual_bootstrap_members C"
    and live: "initial_quorum C H"
  shows "majority (encode ` C) H"
proof -
  have finite_c: "finite C" and count: "card C < 2 * card (C \<inter> Discovered_ID ` H)"
    using live unfolding initial_quorum_def by auto
  have "Discovered_ID ` H \<subseteq> C" using real by blast
  then have full: "C \<inter> Discovered_ID ` H = Discovered_ID ` H" by blast
  have sub: "H \<subseteq> encode ` C"
  proof
    fix n
    assume "n \<in> H"
    with real have "Discovered_ID n \<in> C" by blast
    then show "n \<in> encode ` C" using imageI[of "Discovered_ID n" C encode] encoding(2)[of n] by simp
  qed
  show ?thesis using finite_c count full sub card_image[OF encoding(1)]
    by (simp add: majority_def)
qed

lemma captured_real_members:
  fixes C :: "'r initial_member set"
  assumes "stable_requirements R matches bind" "configured_bootstrap R V matches c C"
  shows "actual_bootstrap_members C = bind ` R \<inter> V"
proof -
  obtain lookup where matching: "view_matching R V matches lookup" and cfg: "C = discovered_configuration R lookup"
    using assms(2) unfolding configured_bootstrap_def by blast
  have actual: "C \<inter> Discovered_ID ` UNIV = Discovered_ID ` (bind ` R \<inter> V)"
    using configuration_actual_nodes[of R lookup UNIV] stable_matched_ids[OF assms(1) matching] by (simp add: cfg)
  show ?thesis
  proof (rule set_eqI)
    fix n
    from arg_cong[OF actual, where f="\<lambda>A. (Discovered_ID n :: 'r initial_member) \<in> A"]
    show "n \<in> actual_bootstrap_members C \<longleftrightarrow> n \<in> bind ` R \<inter> V"
      by (auto simp: image_iff)
  qed
qed

text \<open>
  The common captured configuration may resolve only part of the roster.
  The finite real universe reserves all real node IDs, including currently
  undiscovered ones. Unresolved requirements are encoded as distinct IDs
  outside that universe. The election job set admits only real voters.
  Each selected participant installs the common configuration under its
  own live quorum and service bounds. The election window starts from a
  fresh core and takes separate bounded service for pre-votes, joins and
  election processing. This is the configured startup path, before any
  previous election or accepted publication.
\<close>

theorem partial_configured_startup_to_fixed_election:
  assumes stable: "stable_requirements R matches bind"
    and universe: "finite U" "bind ` R \<subseteq> U"
    and captures: "\<And>n. n \<in> insert c H \<Longrightarrow> configured_bootstrap R (view n) matches n (C n)"
    and aligned: "\<And>n. n \<in> insert c H \<Longrightarrow> bind ` R \<inter> view n = bind ` R \<inter> view c"
    and healthy: "\<And>n. n \<in> insert c H \<Longrightarrow> eligible n \<and> candidate n"
    and live: "\<And>n. n \<in> insert c H \<Longrightarrow> initial_quorum (C n) (known n)"
    and voters: "initial_quorum (C c) H"
    and startup_service: "\<And>n. n \<in> insert c H \<Longrightarrow>
      bounded_service (bootstrap_jobs (retrying n)) (bootstrap_prerequisites (retrying n))
        (startup_sel n) startup_delay startup_horizon"
    and startup_time: "\<And>n. n \<in> insert c H \<Longrightarrow> (if retrying n then 4 else 5) * startup_delay \<le> startup_horizon"
    and new_term: "0 < t" and new_version: "0 < v"
    and election_service: "bounded_service (window_jobs True H H (insert c H) c False)
      (window_dependencies True H H (insert c H) c False) election_sel election_delay election_horizon"
    and election_time: "4 * election_delay \<le> election_horizon"
  obtains encode where
    "\<And>n. encode (Discovered_ID n) = n"
    "inj_on encode (C c)"
    "\<And>r. Bootstrap_Placeholder r \<in> C c \<Longrightarrow> encode (Bootstrap_Placeholder r) \<notin> U"
    "\<And>n. n \<in> insert c H \<Longrightarrow> C n = C c"
    "insert c H \<subseteq> U" "majority (encode ` C c) H"
    "\<And>n. n \<in> insert c H \<Longrightarrow>
      rtranclp (startup_step (configured_bootstrap R (view n) matches n) (known n) n (eligible n) (candidate n))
        (Await_View (if retrying n then Some (C n) else None)) (Startup_PreVote (C c))"
    "leader (window_state initial c t H (window_history initial c t v u)
      (completed_work (window_jobs True H H (insert c H) c False)
        (window_dependencies True H H (insert c H) c False) election_sel (4 * election_delay))) t = Some c"
proof -
  have cap: "configured_bootstrap R (view c) matches c (C c)" using captures by simp
  have equal: "C n = C c" if n: "n \<in> insert c H" for n
    using configured_exact_agreement[OF stable captures[OF n] cap] aligned[OF n] by blast
  have real: "Discovered_ID n \<in> C c" if n: "n \<in> insert c H" for n
    using configured_known_quorum(1)[OF captures[OF n]] equal[OF n] by simp
  have actual: "actual_bootstrap_members (C c) \<subseteq> U"
    using captured_real_members[OF stable cap] universe(2) by blast
  have participants: "insert c H \<subseteq> U" using actual real by blast
  have injective: "inj_on bind R" using stable unfolding stable_requirements_def by simp
  have roster: "Bootstrap_Placeholder r \<in> C c \<Longrightarrow> r \<in> R" for r
    unfolding configured_view_form[OF stable cap] discovered_configuration_def slot_member_def
    by (auto simp: image_iff split: option.splits)
  let ?encode = "bootstrap_member_encoding U bind"
  have encode_id: "?encode (Discovered_ID n) = n" for n by (simp add: bootstrap_member_encoding_def)
  have encode_inj: "inj_on ?encode (C c)"
  proof (rule finite_bootstrap_member_encoding(2)[where R=R])
    show "finite U" by (fact universe(1))
    show "inj_on bind R" by (fact injective)
    show "\<And>r. Bootstrap_Placeholder r \<in> C c \<Longrightarrow> r \<in> R" by (fact roster)
    show "actual_bootstrap_members (C c) \<subseteq> U" by (fact actual)
  qed
  have encode_ph: "?encode (Bootstrap_Placeholder r) \<notin> U" for r
    using Max_ge[OF universe(1), of "Suc (Max U) + bind r"] by (auto simp: bootstrap_member_encoding_def)
  have real_H: "H \<subseteq> actual_bootstrap_members (C c)" using real by blast
  have q: "majority (?encode ` C c) H"
    by (rule encoded_bootstrap_quorum[OF encode_inj encode_id real_H voters])
  have member: "c \<in> ?encode ` C c" using real[of c] encode_id[of c] by force
  have hfin: "finite H" using q unfolding majority_def by (auto intro: finite_subset)
  have startups:
    "rtranclp (startup_step (configured_bootstrap R (view n) matches n) (known n) n (eligible n) (candidate n))
      (Await_View (if retrying n then Some (C n) else None)) (Startup_PreVote (C c))"
    if n: "n \<in> insert c H" for n
  proof -
    have "eligible n" "candidate n" using healthy[OF n] by auto
    from configured_startup_opens_prevote(2)[OF captures[OF n] this live[OF n]
      startup_service[OF n] startup_time[OF n]]
    show ?thesis by (simp add: equal[OF n])
  qed
  have initial_reach: "reachable (?encode ` C c) initial" by (rule reachable.initial)
  interpret window: fixed_publication_window "?encode ` C c" H H "insert c H" c t v u initial True False
    using initial_reach q member hfin new_version new_term
    by unfold_locales (auto simp: initial_def version_def fresher_eq_def epoch_def)
  note won = window.fixed_candidate_wins_by_deadline(1)[OF TrueI election_service election_time]
  show thesis
  proof (rule that[of ?encode])
    show "\<And>n. ?encode (Discovered_ID n) = n" by (fact encode_id)
    show "inj_on ?encode (C c)" by (fact encode_inj)
    show "?encode (Bootstrap_Placeholder r) \<notin> U"
      if "Bootstrap_Placeholder r \<in> C c" for r by (fact encode_ph)
    show "C n = C c" if "n \<in> insert c H" for n by (rule equal[OF that])
    show "insert c H \<subseteq> U" by (fact participants)
    show "majority (?encode ` C c) H" by (fact q)
    show "rtranclp (startup_step (configured_bootstrap R (view n) matches n) (known n) n (eligible n) (candidate n))
        (Await_View (if retrying n then Some (C n) else None)) (Startup_PreVote (C c))"
      if "n \<in> insert c H" for n by (rule startups[OF that])
    show "leader (window_state initial c t H (window_history initial c t v u)
      (completed_work (window_jobs True H H (insert c H) c False)
        (window_dependencies True H H (insert c H) c False) election_sel (4 * election_delay))) t = Some c"
      by (fact won)
  qed
qed

section \<open>Unequal captures and the boundary of best-effort startup\<close>

lemma disagreeing_captures_need_different_initial_configurations:
  assumes stable: "stable_requirements R matches bind"
    and captures: "configured_bootstrap R A matches a C" "configured_bootstrap R B matches b D"
    and different: "bind ` R \<inter> A \<noteq> bind ` R \<inter> B"
    and quorums: "initial_quorum C Q" "initial_quorum D S"
  shows "C \<noteq> D" "Q \<inter> S \<noteq> {}"
  using configured_exact_agreement[OF stable captures] different configured_quorums_intersect[OF stable captures quorums]
  by auto

text \<open>
  Once the initial configuration is installed, Coordinator rejects a
  second installation. Within this startup fragment, differing installed
  configurations cannot be reconciled merely by changing discovery
  views and servicing their schedulers. A later publication or
  reconfiguration would require additional transitions.
\<close>

lemma startup_retains_installed_configuration:
  assumes start: "phase 0 = Durable_Config C"
    and steps: "\<And>i. i < k \<Longrightarrow>
      phase (Suc i) = phase i \<or> startup_step allows (known i) c eligible candidate (phase i) (phase (Suc i))"
  shows "phase k \<in> {Durable_Config C, Armed_Scheduler C, Startup_PreVote C}"
proof -
  have bound: "i \<le> k \<Longrightarrow> phase i \<in> {Durable_Config C, Armed_Scheduler C, Startup_PreVote C}" for i
  proof (induction i)
    case 0
    then show ?case using start by simp
  next
    case (Suc i)
    have less: "i < k" using Suc.prems by simp
    from Suc.IH[OF less_imp_le[OF less]] steps[OF less]
    show ?case by (auto elim: startup_step.cases)
  qed
  show ?thesis by (rule bound[OF le_refl])
qed

lemma obsolete_capture_cannot_recapture:
  assumes cap: "stable_requirements R matches bind" "configured_bootstrap R old matches c C"
    and later: "\<And>i. i < k \<Longrightarrow> 2 * card ((bind ` R \<inter> old) \<inter> known i) \<le> card R"
    and start: "phase 0 = Await_View (Some C)"
    and steps: "\<And>i. i < k \<Longrightarrow>
      phase (Suc i) = phase i \<or> startup_step allows (known i) c eligible candidate (phase i) (phase (Suc i))"
  shows "phase k = Await_View (Some C) \<or> phase k = Pending_Install C"
proof -
  have bound: "i \<le> k \<Longrightarrow> phase i = Await_View (Some C) \<or> phase i = Pending_Install C" for i
  proof (induction i)
    case 0
    then show ?case using start by simp
  next
    case (Suc i)
    have less: "i < k" using Suc.prems by simp
    have no_quorum: "\<not> initial_quorum C (known i)"
      using configured_retry_quorum_iff[OF cap, of "known i"] later[OF less] by simp
    from Suc.IH[OF less_imp_le[OF less]] steps[OF less] no_quorum
    show ?case by (auto elim: startup_step.cases simp: installation_allowed_def)
  qed
  show ?thesis by (rule bound[OF le_refl])
qed

lemma best_effort_local_first_commit:
  assumes boot: "best_effort_bootstrap V c C"
    and t: "0 < t" and v: "0 < v"
    and service: "bounded_service (window_jobs True V V V c False)
      (window_dependencies True V V V c False) sel B horizon"
    and time: "7 * B \<le> horizon"
  shows "[ (t,v,payload) ] \<in> committed (window_state initial c t V (window_history initial c t v payload)
    (completed_work (window_jobs True V V V c False)
      (window_dependencies True V V V c False) sel (7 * B)))"
proof -
  have vset: "finite V" "c \<in> V" using boot by (simp_all add: best_effort_bootstrap_def)
  then have q: "majority V V" unfolding majority_def by (auto simp: card_gt_0_iff)
  have ready: "reachable V initial" by (rule reachable.initial)
  interpret window: fixed_publication_window V V V V c t v payload initial True False
    using ready q vset t v by unfold_locales (auto simp: initial_def version_def fresher_eq_def epoch_def)
  show ?thesis using window.fixed_first_publication_commits_by_deadline(1)[OF TrueI service time]
    by (simp add: initial_def window_history_def)
qed

text \<open>
  Disjoint best-effort views can admit independent windows. The separate
  commit results belong to different fixed cluster instances and use their
  own service premises. The committed UUID check in Coordinator's publish
  handler and JoinValidationService rejects state for a different UUID.
  The binding below projects the durable committed UUID. A node whose UUID
  has not been committed yet can bind to the first UUID it commits. Restart
  preserves an existing binding under the durable recovery assumptions.
  Administrative detaching, unsafe bootstrap and data replacement are
  outside these transitions. Distinct UUID generation is a premise for
  the two-cluster observation.
\<close>

definition accepts_cluster_uuid where
  "accepts_cluster_uuid binding n uuid \<longleftrightarrow> (binding n = None \<or> binding n = Some uuid)"

inductive cluster_uuid_step :: "(node \<Rightarrow> nat option) \<Rightarrow> (node \<Rightarrow> nat option) \<Rightarrow> bool" where
  mark_committed: "accepts_cluster_uuid binding n uuid \<Longrightarrow>
    cluster_uuid_step binding (binding(n := Some uuid))"
| restart: "cluster_uuid_step binding binding"

lemma committed_uuid_persists:
  assumes "rtranclp cluster_uuid_step before after" "before n = Some uuid"
  shows "after n = Some uuid"
  using assms(1)
proof (induction rule: rtranclp_induct)
  case base
  show ?case by (rule assms(2))
next
  case (step middle after)
  from step.hyps(2) show ?case
  proof cases
    case mark_committed
    with step.IH show ?thesis by (auto simp: accepts_cluster_uuid_def)
  next
    case restart
    with step.IH show ?thesis by simp
  qed
qed

theorem best_effort_disjoint_commits_and_rejects_merge:
  assumes boots: "best_effort_bootstrap V a C" "best_effort_bootstrap W b D"
    and isolated: "V \<inter> W = {}" and pads: "0 < t" "0 < v" "p \<noteq> q"
    and first: "bounded_service (window_jobs True V V V a False)
      (window_dependencies True V V V a False) sel_A B_A horizon_A" "7 * B_A \<le> horizon_A"
    and second: "bounded_service (window_jobs True W W W b False)
      (window_dependencies True W W W b False) sel_B B_B horizon_B" "7 * B_B \<le> horizon_B"
    and bindings: "binding a = Some uuid_A" "binding b = Some uuid_B" "uuid_A \<noteq> uuid_B"
    and history: "rtranclp cluster_uuid_step binding later"
  shows "C \<inter> D = {}"
    "[(t,v,p)] \<in> committed (window_state initial a t V (window_history initial a t v p)
      (completed_work (window_jobs True V V V a False)
        (window_dependencies True V V V a False) sel_A (7 * B_A)))"
    "[(t,v,q)] \<in> committed (window_state initial b t W (window_history initial b t v q)
      (completed_work (window_jobs True W W W b False)
        (window_dependencies True W W W b False) sel_B (7 * B_B)))"
    "\<not> prefix [(t,v,p)] [(t,v,q)]" "\<not> prefix [(t,v,q)] [(t,v,p)]"
    "\<not> accepts_cluster_uuid later a uuid_B" "\<not> accepts_cluster_uuid later b uuid_A"
    "\<And>uuid. \<not> (accepts_cluster_uuid later a uuid \<and> accepts_cluster_uuid later b uuid)"
  using best_effort_disjoint_views(3)[OF boots isolated]
    best_effort_local_first_commit[OF boots(1) pads(1,2) first, of p]
    best_effort_local_first_commit[OF boots(2) pads(1,2) second, of q]
    committed_uuid_persists[OF history bindings(1)] committed_uuid_persists[OF history bindings(2)] pads(3) bindings(3)
  by (simp_all add: accepts_cluster_uuid_def prefix_def)

end
