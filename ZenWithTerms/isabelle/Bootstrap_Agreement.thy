theory Bootstrap_Agreement
  imports Fixed_Configuration
begin

section \<open>Configured bootstrap discovery\<close>

datatype 'r initial_member = Discovered_ID node | Bootstrap_Placeholder 'r

definition matched_ids where
  "matched_ids R lookup = {n. \<exists>r\<in>R. lookup r = Some n}"

definition slot_member where
  "slot_member lookup r =
    (case lookup r of Some n \<Rightarrow> Discovered_ID n | None \<Rightarrow> Bootstrap_Placeholder r)"

definition discovered_configuration where
  "discovered_configuration R lookup = slot_member lookup ` R"

definition view_matching where
  "view_matching R V matches lookup \<longleftrightarrow>
    (\<forall>r\<in>R. {n \<in> V. matches n r} = (case lookup r of Some n \<Rightarrow> {n} | None \<Rightarrow> {})) \<and>
    (\<forall>r\<in>R. \<forall>s\<in>R. \<forall>n. lookup r = Some n \<longrightarrow> lookup s = Some n \<longrightarrow> r = s)"

definition configured_bootstrap where
  "configured_bootstrap R V matches self C \<longleftrightarrow>
    finite R \<and> (\<exists>lookup. view_matching R V matches lookup \<and> self \<in> matched_ids R lookup \<and>
      card R < 2 * card (matched_ids R lookup) \<and> C = discovered_configuration R lookup)"

lemma configured_bootstrapI:
  "finite R \<Longrightarrow> view_matching R V matches lookup \<Longrightarrow> self \<in> matched_ids R lookup \<Longrightarrow>
    card R < 2 * card (matched_ids R lookup) \<Longrightarrow> C = discovered_configuration R lookup \<Longrightarrow>
    configured_bootstrap R V matches self C"
  unfolding configured_bootstrap_def by blast

definition initial_quorum where
  "initial_quorum C Q \<longleftrightarrow>
    finite C \<and> card C < 2 * card (C \<inter> Discovered_ID ` Q)"

lemma discovered_id_card[simp]: "card (Discovered_ID ` Q) = card Q"
  by (rule card_image) (simp add: inj_on_def)

definition installation_allowed where
  "installation_allowed installed master_eligible currently_known self C \<longleftrightarrow>
    \<not> installed \<and> master_eligible \<and> Discovered_ID self \<in> C \<and> initial_quorum C currently_known"

text \<open>
  A successful configured match uses one slot per requirement. Discovery
  checks that a requirement matches at most one node and that a node does
  not match two requirements in that view. The local node must be among the
  matches and the matches must form a strict majority of the requirements.
  The tagged members assume disjoint real ID and placeholder namespaces and
  represent the discovered node objects by persistent IDs. This model assumes
  distinct discovered objects have distinct persistent IDs. The configuration
  is passed to the installer, which independently checks the current peer view,
  self-membership, master eligibility, and absence of a prior configuration.
  A retry carries the same configuration into these checks.
\<close>

lemma slot_member_inj:
  assumes "view_matching R V matches lookup"
  shows "inj_on (slot_member lookup) R"
  using assms unfolding inj_on_def slot_member_def view_matching_def
  by (auto split: option.splits)

lemma configured_count:
  assumes "view_matching R V matches lookup"
  shows "card (discovered_configuration R lookup) = card R"
  unfolding discovered_configuration_def by (rule card_image[OF slot_member_inj[OF assms]])

lemma matched_in_view:
  assumes "view_matching R V matches lookup"
  shows "matched_ids R lookup \<subseteq> V"
proof
  fix n
  assume "n \<in> matched_ids R lookup"
  then obtain r where r: "r \<in> R" and lookup: "lookup r = Some n" unfolding matched_ids_def by blast
  from assms r have "{n \<in> V. matches n r} =
      (case lookup r of Some n \<Rightarrow> {n} | None \<Rightarrow> {})"
    unfolding view_matching_def by blast
  then show "n \<in> V" using lookup by auto
qed

lemma configuration_actual_nodes:
  fixes R :: "'r set"
  shows "discovered_configuration R lookup \<inter> Discovered_ID ` Q =
    Discovered_ID ` (matched_ids R lookup \<inter> Q)"
proof (rule equalityI)
  show "discovered_configuration R lookup \<inter> Discovered_ID ` Q \<subseteq>
      Discovered_ID ` (matched_ids R lookup \<inter> Q)"
  proof
    fix x :: "'r initial_member"
    assume x: "x \<in> discovered_configuration R lookup \<inter> Discovered_ID ` Q"
    then obtain n where n: "n \<in> Q" "x = Discovered_ID n" by blast
    obtain r where r: "r \<in> R" "slot_member lookup r = x"
      using x unfolding discovered_configuration_def by blast
    have "lookup r = Some n" using r(2) n(2) unfolding slot_member_def by (cases "lookup r") simp_all
    then have "n \<in> matched_ids R lookup" using r(1) unfolding matched_ids_def by blast
    then show "x \<in> Discovered_ID ` (matched_ids R lookup \<inter> Q)" using n by blast
  qed
  show "Discovered_ID ` (matched_ids R lookup \<inter> Q) \<subseteq>
      discovered_configuration R lookup \<inter> Discovered_ID ` Q"
  proof
    fix x :: "'r initial_member"
    assume "x \<in> Discovered_ID ` (matched_ids R lookup \<inter> Q)"
    then obtain n where n: "n \<in> matched_ids R lookup" "n \<in> Q" "x = Discovered_ID n" by blast
    from n(1) obtain r where r: "r \<in> R" "lookup r = Some n" unfolding matched_ids_def by blast
    then have "x = slot_member lookup r" using n(3) by (simp add: slot_member_def)
    then show "x \<in> discovered_configuration R lookup \<inter> Discovered_ID ` Q"
      using r(1) n(2,3) unfolding discovered_configuration_def by blast
  qed
qed

lemma configured_known_quorum:
  assumes "configured_bootstrap R V matches self C"
  shows "Discovered_ID self \<in> C" "initial_quorum C V"
proof -
  obtain lookup where matching: "view_matching R V matches lookup"
    and self: "self \<in> matched_ids R lookup"
    and threshold: "card R < 2 * card (matched_ids R lookup)"
    and cfg: "C = discovered_configuration R lookup"
    using assms unfolding configured_bootstrap_def by blast
  have sub: "matched_ids R lookup \<subseteq> V" by (rule matched_in_view[OF matching])
  have agree: "matched_ids R lookup \<inter> V = matched_ids R lookup" using sub by blast
  obtain r where r: "r \<in> R" "lookup r = Some self" using self unfolding matched_ids_def by blast
  from imageI[OF r(1), of "slot_member lookup"] r(2) show "Discovered_ID self \<in> C"
    by (simp add: cfg discovered_configuration_def slot_member_def)
  have "finite R" using assms unfolding configured_bootstrap_def by simp
  then have "finite C" by (simp add: cfg discovered_configuration_def)
  show "initial_quorum C V"
    using \<open>finite C\<close> configured_count[OF matching] threshold agree
    unfolding initial_quorum_def cfg by (simp add: configuration_actual_nodes)
qed

lemma configured_can_install_in_matching_view:
  assumes "configured_bootstrap R V matches self C" "\<not> installed" "master_eligible"
  shows "installation_allowed installed master_eligible V self C"
  using configured_known_quorum[OF assms(1)] assms(2,3)
  by (simp add: installation_allowed_def)

section \<open>Shared requirements and consistent persistent identities\<close>

definition stable_requirements where
  "stable_requirements R matches bind \<longleftrightarrow>
    inj_on bind R \<and> (\<forall>r\<in>R. \<forall>n. matches n r \<longleftrightarrow> n = bind r)"

definition view_lookup where
  "view_lookup bind V r = (if bind r \<in> V then Some (bind r) else None)"

lemma stable_view_matching:
  assumes "stable_requirements R matches bind"
  shows "view_matching R V matches (view_lookup bind V)"
  using assms unfolding stable_requirements_def view_matching_def view_lookup_def inj_on_def
  by (auto split: if_splits)

lemma stable_lookup:
  assumes lookup: "stable_requirements R matches bind" "view_matching R V matches lookup"
    and member: "r \<in> R"
  shows "lookup r = view_lookup bind V r"
proof -
  from lookup(2) member have prev: "{n \<in> V. matches n r} =
      (case lookup r of Some n \<Rightarrow> {n} | None \<Rightarrow> {})"
    unfolding view_matching_def by blast
  from stable_view_matching[OF lookup(1), of V] member
  have "{n \<in> V. matches n r} =
      (case view_lookup bind V r of Some n \<Rightarrow> {n} | None \<Rightarrow> {})"
    unfolding view_matching_def by blast
  with prev show ?thesis by (cases "lookup r"; cases "view_lookup bind V r") simp_all
qed

lemma stable_matched_ids:
  assumes "stable_requirements R matches bind" "view_matching R V matches lookup"
  shows "matched_ids R lookup = bind ` R \<inter> V"
proof -
  show ?thesis
  proof (rule equalityI)
    show "matched_ids R lookup \<subseteq> bind ` R \<inter> V"
    proof
      fix n
      assume "n \<in> matched_ids R lookup"
      then obtain r where r: "r \<in> R" "lookup r = Some n" unfolding matched_ids_def by blast
      from stable_lookup[OF assms r(1)] r(2) have "n = bind r" "n \<in> V"
        by (auto simp: view_lookup_def split: if_splits)
      with r(1) show "n \<in> bind ` R \<inter> V" by blast
    qed
    show "bind ` R \<inter> V \<subseteq> matched_ids R lookup"
    proof
      fix n
      assume "n \<in> bind ` R \<inter> V"
      then obtain r where r: "r \<in> R" "bind r = n" "n \<in> V" by blast
      from stable_lookup[OF assms r(1)] r(2,3) have "lookup r = Some n" by (simp add: view_lookup_def)
      with r(1) show "n \<in> matched_ids R lookup" unfolding matched_ids_def by blast
    qed
  qed
qed

lemma configuration_cong:
  assumes "\<And>r. r \<in> R \<Longrightarrow> lookup r = lookup' r"
  shows "discovered_configuration R lookup = discovered_configuration R lookup'"
  unfolding discovered_configuration_def by (rule image_cong[OF refl]) (simp add: slot_member_def assms)

lemma configured_view_form:
  assumes stable: "stable_requirements R matches bind"
    and configured: "configured_bootstrap R V matches self C"
  shows "C = discovered_configuration R (view_lookup bind V)"
proof -
  obtain lookup where matching: "view_matching R V matches lookup"
    and cfg: "C = discovered_configuration R lookup"
    using configured unfolding configured_bootstrap_def by blast
  show ?thesis unfolding cfg by (rule configuration_cong[OF stable_lookup[OF stable matching]])
qed

lemma configured_stable_attempt:
  assumes stable: "stable_requirements R matches bind" and finite: "finite R"
    and self: "self \<in> bind ` R \<inter> V"
    and threshold: "card R < 2 * card (bind ` R \<inter> V)"
  shows "configured_bootstrap R V matches self (discovered_configuration R (view_lookup bind V))"
proof -
  have matching: "view_matching R V matches (view_lookup bind V)" by (rule stable_view_matching[OF stable])
  have ids: "matched_ids R (view_lookup bind V) = bind ` R \<inter> V" by (rule stable_matched_ids[OF stable matching])
  show ?thesis by (rule configured_bootstrapI[OF finite matching]) (use self threshold in \<open>simp_all add: ids\<close>)
qed

lemma placeholder_present[simp]:
  "Bootstrap_Placeholder r \<in> discovered_configuration R (view_lookup bind V)
    \<longleftrightarrow> r \<in> R \<and> bind r \<notin> V"
proof -
  have slot: "Bootstrap_Placeholder r = slot_member (view_lookup bind V) s
      \<longleftrightarrow> r = s \<and> bind s \<notin> V" for s
    by (cases "bind s \<in> V") (simp_all add: slot_member_def view_lookup_def)
  show ?thesis by (simp add: discovered_configuration_def image_iff slot)
qed

theorem configured_exact_agreement:
  assumes "stable_requirements R matches bind"
    "configured_bootstrap R V matches a C"
    "configured_bootstrap R W matches b D"
  shows "C = D \<longleftrightarrow> bind ` R \<inter> V = bind ` R \<inter> W"
proof -
  have cfg: "C = discovered_configuration R (view_lookup bind V)"
    and cfg': "D = discovered_configuration R (view_lookup bind W)"
    using configured_view_form[OF assms(1) assms(2)] configured_view_form[OF assms(1) assms(3)] by auto
  show ?thesis
  proof
    assume "C = D"
    then have "bind r \<in> V \<longleftrightarrow> bind r \<in> W" if "r \<in> R" for r
    proof -
      have "(Bootstrap_Placeholder r \<in> C) = (Bootstrap_Placeholder r \<in> D)"
        using \<open>C = D\<close> by simp
      then show ?thesis by (simp add: cfg cfg' that)
    qed
    then show "bind ` R \<inter> V = bind ` R \<inter> W" by (auto simp: image_iff)
  next
    assume same_ids: "bind ` R \<inter> V = bind ` R \<inter> W"
    have "view_lookup bind V r = view_lookup bind W r" if "r \<in> R" for r
    proof -
      from same_ids have "(bind r \<in> bind ` R \<inter> V) = (bind r \<in> bind ` R \<inter> W)" by simp
      with imageI[OF that, of bind] show ?thesis by (simp add: view_lookup_def)
    qed
    then show "C = D" unfolding cfg cfg' by (rule configuration_cong)
  qed
qed

corollary complete_configured_views_agree:
  assumes "stable_requirements R matches bind"
    "configured_bootstrap R V matches a C"
    "configured_bootstrap R W matches b D"
    "bind ` R \<subseteq> V" "bind ` R \<subseteq> W"
  shows "C = D"
  using configured_exact_agreement[OF assms(1-3)] assms(4,5) by (simp add: Int_absorb2)

theorem configured_quorum_projects:
  assumes stable: "stable_requirements R matches bind"
    and started: "configured_bootstrap R V matches self C"
    and votes: "initial_quorum C Q"
  shows "majority (bind ` R) (bind ` R \<inter> Q)"
proof -
  obtain lookup where finite: "finite R" and matching: "view_matching R V matches lookup"
    and cfg: "C = discovered_configuration R lookup"
    using started unfolding configured_bootstrap_def by blast
  have inj: "inj_on bind R" using stable unfolding stable_requirements_def by simp
  have counted: "card (C \<inter> Discovered_ID ` Q) = card ((bind ` R \<inter> V) \<inter> Q)"
    by (simp add: cfg configuration_actual_nodes stable_matched_ids[OF stable matching])
  have bound: "card ((bind ` R \<inter> V) \<inter> Q) \<le> card (bind ` R \<inter> Q)"
    by (rule card_mono) (use finite in auto)
  have size: "card C = card (bind ` R)" using configured_count[OF matching] card_image[OF inj] by (simp add: cfg)
  have "card (bind ` R) < 2 * card ((bind ` R \<inter> V) \<inter> Q)"
    using votes by (simp add: initial_quorum_def size counted)
  then have "card (bind ` R) < 2 * card (bind ` R \<inter> Q)" using bound by linarith
  then show ?thesis using finite unfolding majority_def by auto
qed

theorem configured_quorums_intersect:
  assumes "stable_requirements R matches bind"
    "configured_bootstrap R V matches a C" "configured_bootstrap R W matches b D"
    "initial_quorum C Q" "initial_quorum D U"
  shows "\<exists>n\<in>Q. n \<in> U"
  using majority_intersects[OF configured_quorum_projects[OF assms(1,2,4)]
      configured_quorum_projects[OF assms(1,3,5)]] by blast

theorem configured_initial_leader_unique:
  assumes "stable_requirements R matches bind"
    "configured_bootstrap R V matches a C" "configured_bootstrap R W matches b D"
    "initial_quorum C Q" "initial_quorum D U"
    "\<And>n. n \<in> Q \<Longrightarrow> vote n = Some a"
    "\<And>n. n \<in> U \<Longrightarrow> vote n = Some b"
  shows "a = b"
proof -
  obtain n where common: "n \<in> Q" "n \<in> U" using configured_quorums_intersect[OF assms(1-5)] by blast
  from assms(6)[OF common(1)] assms(7)[OF common(2)] show ?thesis by simp
qed

section \<open>Bootstrap boundaries\<close>

text \<open>
  The shared-roster theorem concerns certificates still using their initial
  configurations. Its vote function represents the one-vote-per-term property
  for a fixed term. It does not initialize the existing common-configuration
  refinement when different placeholders are installed, and imposes no claim
  about switching to a publication's configuration or progressing through
  reconfiguration. The next examples separate literal agreement from quorum
  intersection and exhibit why the configuration and identity premises matter.
\<close>

definition demo_requirements :: "nat set" where "demo_requirements = {0,1,2}"

definition left_config :: "nat initial_member set" where
  "left_config = {Discovered_ID 0, Discovered_ID 1, Bootstrap_Placeholder 2}"

definition right_config :: "nat initial_member set" where
  "right_config = {Bootstrap_Placeholder 0, Discovered_ID 1, Discovered_ID 2}"

lemma stable_view_example:
  "configured_bootstrap demo_requirements {0,1} (=) 0 left_config"
  "configured_bootstrap demo_requirements {1,2} (=) 2 right_config"
  "left_config \<noteq> right_config"
proof -
  have stable: "stable_requirements demo_requirements (=) id"
    by (simp add: stable_requirements_def inj_on_def)
  have "configured_bootstrap demo_requirements {0,1} (=) 0
      (discovered_configuration demo_requirements (view_lookup id {0,1}))"
    by (rule configured_stable_attempt[OF stable]) (simp_all add: demo_requirements_def Int_insert_left)
  then show "configured_bootstrap demo_requirements {0,1} (=) 0 left_config"
    by (simp add: demo_requirements_def left_config_def discovered_configuration_def slot_member_def view_lookup_def)
  have "configured_bootstrap demo_requirements {1,2} (=) 2
      (discovered_configuration demo_requirements (view_lookup id {1,2}))"
    by (rule configured_stable_attempt[OF stable]) (simp_all add: demo_requirements_def Int_insert_left)
  then show "configured_bootstrap demo_requirements {1,2} (=) 2 right_config"
    by (simp add: demo_requirements_def right_config_def discovered_configuration_def slot_member_def view_lookup_def)
  have "Discovered_ID 0 \<in> left_config" "Discovered_ID 0 \<notin> right_config"
    by (simp_all add: left_config_def right_config_def)
  then show "left_config \<noteq> right_config" by blast
qed

definition ambiguous_match :: "node \<Rightarrow> nat \<Rightarrow> bool" where
  "ambiguous_match n r \<longleftrightarrow> (n = 0 \<or> n = 2) \<and> r = 0 \<or> (n = 1 \<or> n = 3) \<and> r = 1"

definition alias_config :: "nat initial_member set" where
  "alias_config = {Discovered_ID 2, Discovered_ID 3, Bootstrap_Placeholder 2}"

definition demo_lookup :: "node \<Rightarrow> node \<Rightarrow> nat \<Rightarrow> node option" where
  "demo_lookup a b r = (if r = 0 then Some a else if r = 1 then Some b else None)"

lemma demo_matched_ids[simp]: "matched_ids demo_requirements (demo_lookup a b) = {a,b}"
  unfolding demo_requirements_def demo_lookup_def matched_ids_def by auto

lemma demo_bootstrap:
  assumes matching: "view_matching demo_requirements V matches (demo_lookup a b)"
    and self: "self \<in> {a,b}" and distinct: "a \<noteq> b"
  shows "configured_bootstrap demo_requirements V matches self {Discovered_ID a, Discovered_ID b, Bootstrap_Placeholder 2}"
proof -
  have known: "self \<in> matched_ids demo_requirements (demo_lookup a b)" using self by simp
  have threshold: "card demo_requirements < 2 * card (matched_ids demo_requirements (demo_lookup a b))"
    unfolding demo_matched_ids using distinct by (simp add: demo_requirements_def)
  show ?thesis by (rule configured_bootstrapI[OF _ matching known threshold])
    (simp_all add: demo_requirements_def discovered_configuration_def slot_member_def demo_lookup_def)
qed

lemma shared_requirements_can_split:
  "configured_bootstrap demo_requirements {0,1} ambiguous_match 0 left_config"
  "configured_bootstrap demo_requirements {2,3} ambiguous_match 2 alias_config"
  "initial_quorum left_config {0,1}"
  "initial_quorum alias_config {2,3}"
  "({0,1} :: node set) \<inter> {2,3} = {}"
proof -
  have left: "view_matching demo_requirements {0,1} ambiguous_match (demo_lookup 0 1)"
    by (auto simp: view_matching_def demo_requirements_def demo_lookup_def ambiguous_match_def)
  show "configured_bootstrap demo_requirements {0,1} ambiguous_match 0 left_config"
    unfolding left_config_def by (rule demo_bootstrap[OF left]) simp_all
  have right: "view_matching demo_requirements {2,3} ambiguous_match (demo_lookup 2 3)"
    by (auto simp: view_matching_def demo_requirements_def demo_lookup_def ambiguous_match_def)
  show "configured_bootstrap demo_requirements {2,3} ambiguous_match 2 alias_config"
    unfolding alias_config_def by (rule demo_bootstrap[OF right]) simp_all
  show "initial_quorum left_config {0,1}" "initial_quorum alias_config {2,3}"
    by (simp_all add: left_config_def alias_config_def initial_quorum_def Int_insert_left)
  show "({0,1} :: node set) \<inter> {2,3} = {}" by auto
qed

lemma singleton_bootstrap:
  "configured_bootstrap {n :: nat} {n} (=) n {Discovered_ID n}"
proof -
  have ids: "matched_ids {n :: nat} (\<lambda>_. Some n) = {n}" unfolding matched_ids_def by auto
  show ?thesis by (rule configured_bootstrapI[where lookup="\<lambda>_. Some n"])
    (auto simp: ids view_matching_def discovered_configuration_def slot_member_def)
qed

lemma different_settings_can_split:
  "configured_bootstrap {0 :: nat} {0} (=) 0 {Discovered_ID 0}"
  "configured_bootstrap {1 :: nat} {1} (=) 1 {Discovered_ID 1}"
  "initial_quorum {Discovered_ID 0 :: nat initial_member} {0}"
  "initial_quorum {Discovered_ID 1 :: nat initial_member} {1}"
  "({0} :: node set) \<inter> {1} = {}"
proof -
  show "configured_bootstrap {0 :: nat} {0} (=) 0 {Discovered_ID 0}"
    by (rule singleton_bootstrap)
  show "configured_bootstrap {1 :: nat} {1} (=) 1 {Discovered_ID 1}"
    by (rule singleton_bootstrap)
  show "initial_quorum {Discovered_ID 0 :: nat initial_member} {0}"
    "initial_quorum {Discovered_ID 1 :: nat initial_member} {1}"
    "({0} :: node set) \<inter> {1} = {}"
    by (simp_all add: initial_quorum_def)
qed

definition best_effort_bootstrap where
  "best_effort_bootstrap V self C \<longleftrightarrow>
    finite V \<and> self \<in> V \<and> C = Discovered_ID ` V"

lemma best_effort_disjoint_views:
  assumes "best_effort_bootstrap V a C" "best_effort_bootstrap W b D" "V \<inter> W = {}"
  shows "initial_quorum C V" "initial_quorum D W" "C \<inter> D = {}"
proof -
  have V: "finite V" "V \<noteq> {}" "C = Discovered_ID ` V"
    using assms(1) unfolding best_effort_bootstrap_def by auto
  have W: "finite W" "W \<noteq> {}" "D = Discovered_ID ` W"
    using assms(2) unfolding best_effort_bootstrap_def by auto
  show "initial_quorum C V" "initial_quorum D W"
    using V W by (simp_all add: initial_quorum_def card_gt_0_iff)
  show "C \<inter> D = {}" using V(3) W(3) assms(3) by (auto simp: image_iff)
qed

end
