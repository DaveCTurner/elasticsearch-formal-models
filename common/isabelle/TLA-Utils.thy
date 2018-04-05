theory "TLA-Utils"
  imports "HOL-TLA.TLA"
begin

syntax
  "_liftSubset" :: "[lift, lift] \<Rightarrow> lift"                ("(_/ \<subseteq> _)" [50, 51] 50)
  "_liftInter"  :: "[lift, lift] \<Rightarrow> lift"                ("(_/ \<inter> _)" [50, 51] 50)
  "_liftUn"     :: "[lift, lift] \<Rightarrow> lift"                ("(_/ \<union> _)" [50, 51] 50)

translations
  "_liftSubset"   == "_lift2 (op \<subseteq>)"
  "_liftInter"    == "_lift2 (op \<inter>)"
  "_liftUn"       == "_lift2 (op \<union>)"

lemma imp_imp_leadsto:
  fixes S :: temporal
  assumes "\<turnstile> F \<longrightarrow> G"
  shows "\<turnstile> S \<longrightarrow> (F \<leadsto> G)"
  apply (auto simp add: Valid_def)
  using ImplLeadsto_simple assms by blast

lemma imp_leadsto_transitive[trans]:
  fixes S :: temporal
  assumes "\<turnstile> S \<longrightarrow> (F \<leadsto> G)"
  assumes "\<turnstile> S \<longrightarrow> (G \<leadsto> H)"
  shows "\<turnstile> S \<longrightarrow> (F \<leadsto> H)"
  using assms
  apply (auto simp add: Valid_def)
  using LatticeTransitivity by fastforce

lemma temp_impI:
  assumes "sigma \<Turnstile> P \<Longrightarrow> sigma \<Turnstile> Q"
  shows "sigma \<Turnstile> P \<longrightarrow> Q"
  using assms by auto

lemma temp_conjI:
  assumes "sigma \<Turnstile> P" "sigma \<Turnstile> Q"
  shows "sigma \<Turnstile> P \<and> Q"
  using assms by auto

lemma temp_conjE:
  assumes "sigma \<Turnstile> F \<and> G"
  assumes  "\<lbrakk> sigma \<Turnstile> F; sigma \<Turnstile> G \<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms by auto

lemma temp_disjE:
  assumes "sigma \<Turnstile> F \<or> G"
  assumes "sigma \<Turnstile> F \<Longrightarrow> P"
  assumes "sigma \<Turnstile> G \<Longrightarrow> P"
  shows "P"
  using assms by auto

lemma temp_exI:
  assumes "sigma \<Turnstile> F x"
  shows "sigma \<Turnstile> (\<exists>x. F x)"
  using assms by auto

lemma temp_exE:
  assumes "sigma \<Turnstile> \<exists>x. F x"
  assumes "\<And>x. sigma \<Turnstile> F x \<Longrightarrow> P"
  shows "P"
  using assms by auto

lemma temp_ex_impI:
  assumes "\<And>x. \<turnstile> F x \<longrightarrow> G"
  shows "\<turnstile> (\<exists>x. F x) \<longrightarrow> G"
  using assms by (auto simp add: Valid_def)

lemma action_beforeI: assumes "s \<Turnstile> P" shows "(s,t) \<Turnstile> $P" using assms by simp
lemma action_afterI:  assumes "t \<Turnstile> P" shows "(s,t) \<Turnstile> P$" using assms by simp

lemma temp_imp_conjI:
  assumes "\<turnstile> S \<longrightarrow> P" "\<turnstile> S \<longrightarrow> Q"
  shows "\<turnstile> S \<longrightarrow> P \<and> Q"
  using assms unfolding Valid_def
  by auto

lemma temp_imp_box_conjI:
  assumes "\<turnstile> S \<longrightarrow> \<box>P" "\<turnstile> S \<longrightarrow> \<box>Q"
  shows "\<turnstile> S \<longrightarrow> \<box>(P \<and> Q)"
  using assms by (simp add: split_box_conj Valid_def)

lemma temp_box_conjE:
  assumes "sigma \<Turnstile> \<box>(F \<and> G)"
  assumes  "\<lbrakk> sigma \<Turnstile> \<box>F; sigma \<Turnstile> \<box>G \<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms STL5 unfolding Valid_def
  by (simp add: split_box_conj)

lemma temp_imp_trans [trans]:
  assumes "\<turnstile> F \<longrightarrow> G"
  assumes "\<turnstile> G \<longrightarrow> H"
  shows "\<turnstile> F \<longrightarrow> H"
  using assms unfolding Valid_def by auto

lemma imp_leadsto_invariant:
  fixes S :: temporal
  fixes P I :: stpred
  assumes "\<turnstile> S \<longrightarrow> \<box>I"
  shows "\<turnstile> S \<longrightarrow> (P \<leadsto> I)"
proof (intro tempI temp_impI)
  fix sigma
  assume S: "sigma \<Turnstile> S"
  with assms have "sigma \<Turnstile> \<box>I" by auto
  thus "sigma \<Turnstile> P \<leadsto> I"
    unfolding leadsto_def
    by (metis InitDmd STL4E boxInit_stp dmdInit_stp intI temp_impI)
qed

lemma imp_forall_leadsto:
  fixes S :: temporal
  fixes P :: "'a \<Rightarrow> bool"
  fixes Q :: "'a \<Rightarrow> stpred"
  fixes R :: stpred
  assumes "\<And>x. P x \<Longrightarrow> \<turnstile> S \<longrightarrow> (Q x \<leadsto> R)"
  shows "\<turnstile> S \<longrightarrow> (\<forall> x. (#(P x) \<and> Q x) \<leadsto> R)"
  using assms
  unfolding Valid_def leadsto_def
  apply auto
  by (metis (full_types) ImplLeadsto_simple TrueW int_simps(11) int_simps(17) int_simps(19) inteq_reflection leadsto_def tempD)

lemma temp_dmd_box_imp: 
  assumes "sigma \<Turnstile> \<diamond>\<box> P"
  assumes "\<turnstile> P \<longrightarrow> Q"
  shows "sigma \<Turnstile> \<diamond>\<box> Q"
  using assms DmdImplE STL4 by blast

lemma temp_box_dmd_imp: 
  assumes "sigma \<Turnstile> \<box>\<diamond> P"
  assumes "\<turnstile> P \<longrightarrow> Q"
  shows "sigma \<Turnstile> \<box>\<diamond> Q"
  using assms DmdImpl STL4E by blast

lemma not_stuck_forever:
  fixes Stuck :: stpred
  fixes Progress :: action
  assumes "\<turnstile> Progress \<longrightarrow> $Stuck \<longrightarrow> \<not> Stuck$"
  shows "\<turnstile> \<box>\<diamond>Progress \<longrightarrow> \<not> \<diamond>\<box>Stuck"
  using assms
  by (unfold dmd_def, simp, intro STL4, simp, intro TLA2, auto)

lemma stable_dmd_stuck:
  assumes "\<turnstile> S \<longrightarrow> stable P"
  assumes "\<turnstile> S \<longrightarrow> \<diamond>P"
  shows "\<turnstile> S \<longrightarrow> \<diamond>\<box>P"
  using assms DmdStable by (meson temp_imp_conjI temp_imp_trans)

lemma enabled_before_conj[simp]:
  "PRED Enabled ($P \<and> Q) = (PRED (P \<and> Enabled Q))"
  unfolding enabled_def by (intro ext, auto)

lemma imp_leadsto_reflexive: "\<turnstile> S \<longrightarrow> (F \<leadsto> F)" using LatticeReflexivity [where F = F] by auto

lemma imp_leadsto_diamond:
  assumes "\<turnstile> S \<longrightarrow> (A \<leadsto> (B \<or> C))"
  assumes "\<turnstile> S \<longrightarrow> (B \<leadsto> D)"
  assumes "\<turnstile> S \<longrightarrow> (C \<leadsto> D)"
  shows   "\<turnstile> S \<longrightarrow> (A \<leadsto> D)"
proof (intro tempI temp_impI)
  fix sigma
  assume S: "sigma \<Turnstile> S"
  with assms have
    ABC: "sigma \<Turnstile> A \<leadsto> (B \<or> C)" and
    BD:  "sigma \<Turnstile> B \<leadsto> D" and
    CD:  "sigma \<Turnstile> C \<leadsto> D"
    by (auto simp add: Valid_def)
  with LatticeDiamond [where A = A and B = B and C = C and D = D]
  show "sigma \<Turnstile> A \<leadsto> D"
    by (auto simp add: Valid_def)
qed

lemma imp_disj_leadstoI:
  assumes 1: "\<turnstile> S \<longrightarrow> (A \<leadsto> C)"
  assumes 2: "\<turnstile> S \<longrightarrow> (B \<leadsto> C)"
  shows "\<turnstile> S \<longrightarrow> (A \<or> B \<leadsto> C)"
  by (intro imp_leadsto_diamond [OF imp_leadsto_reflexive] assms)

lemma temp_conj_eq_imp:
  assumes "\<turnstile> P \<longrightarrow> (Q = R)"
  shows "\<turnstile> (P \<and> Q) = (P \<and> R)"
  using assms by (auto simp add: Valid_def)

text \<open>The following lemma is particularly useful for a system that makes
some progress which either reaches the desired state directly or which leaves it in
a state that is definitely not the desired state but from which it can reach the desired state via
some further progress.\<close>

lemma imp_leadsto_triangle_excl:
  assumes AB: "\<turnstile> S \<longrightarrow> (A \<leadsto> B)"
  assumes BC: "\<turnstile> S \<longrightarrow> ((B \<and> \<not>C) \<leadsto> C)"
  shows "\<turnstile> S \<longrightarrow> (A \<leadsto> C)"
proof -
  have "\<turnstile> ((B \<and> \<not>C) \<or> (B \<and> C)) = B" by auto
  from inteq_reflection [OF this] AB have ABCBC: "\<turnstile> S \<longrightarrow> (A \<leadsto> ((B \<and> \<not>C) \<or> (B \<and> C)))" by simp

  show ?thesis
  proof (intro imp_leadsto_diamond [OF ABCBC] BC)
    from ImplLeadsto_simple [where F = "LIFT (B \<and> C)"]
    show "\<turnstile> S \<longrightarrow> (B \<and> C \<leadsto> C)"
      by (auto simp add: Valid_def)
  qed
qed

lemma imp_leadsto_triangle_extra_assm:
  assumes AB: "\<turnstile> S \<longrightarrow> (A \<and> \<not>B \<leadsto> A \<and> B)"
  shows "\<turnstile> S \<longrightarrow> (A \<leadsto> A \<and> B)"
proof (rule imp_leadsto_triangle_excl [OF imp_leadsto_reflexive])
  have "\<turnstile> S \<longrightarrow> (A \<and> \<not> (A \<and> B) \<leadsto> A \<and> \<not>B)"
    by (intro imp_imp_leadsto, auto)
  with AB show "\<turnstile> S \<longrightarrow> (A \<and> \<not> (A \<and> B) \<leadsto> A \<and> B)" by (metis imp_leadsto_transitive)
qed

lemma imp_forall:
  assumes "\<And>x. \<turnstile> S \<longrightarrow> P x"
  shows "\<turnstile> S \<longrightarrow> (\<forall>x. P x)"
  using assms by (auto simp add: Valid_def)

lemma imp_exists_leadstoI:
  assumes "\<And>x. \<turnstile> S \<longrightarrow> (P x \<leadsto> Q)"
  shows "\<turnstile> S \<longrightarrow> ((\<exists> x. P x) \<leadsto> Q)"
  unfolding inteq_reflection [OF leadsto_exists]
  by (intro imp_forall assms)

lemma imp_INV_leadsto:
  "\<turnstile> S \<longrightarrow> \<box>I \<Longrightarrow> \<turnstile> S \<longrightarrow> (P \<and> I \<leadsto> Q) \<Longrightarrow> \<turnstile> S \<longrightarrow> (P \<leadsto> Q)"
  using INV_leadsto by (auto simp add: Valid_def, blast)

lemma wf_imp_leadsto:
  assumes 1: "wf r"
  and 2: "\<And>x. \<turnstile> S \<longrightarrow> (F x \<leadsto> (G \<or> (\<exists>y. #((y,x)\<in>r) \<and> F y)))"
  shows "\<turnstile> S \<longrightarrow> (F x \<leadsto> G)"
proof (intro tempI temp_impI)
  fix sigma assume sigma: "sigma \<Turnstile> S"
  with 2 have "\<And>x. sigma \<Turnstile> F x \<leadsto> (G \<or> (\<exists>y. #((y,x)\<in>r) \<and> F y))"
    by (auto simp add: Valid_def)
  from 1 this show "sigma \<Turnstile> F x \<leadsto> G" by (rule wf_leadsto)
qed

lemma wf_imp_ex_leadsto:
  assumes 1: "wf r" and 2: "\<And>x. \<turnstile> S \<longrightarrow> (F x \<leadsto> (G \<or> (\<exists>y. #((y,x)\<in>r) \<and> F y)))"
  shows "\<turnstile> S \<longrightarrow> ((\<exists>x. F x) \<leadsto> G)"
  using 1 2
  by (intro imp_exists_leadstoI wf_imp_leadsto [where G = G], auto)

lemma unstable_implies_infinitely_often:
  fixes P :: stpred
  assumes "\<turnstile> S \<longrightarrow> (\<not>P \<leadsto> P)"
  shows "\<turnstile> S \<longrightarrow> \<box>\<diamond>P"
proof -
  define T :: stpred where "T \<equiv> PRED #True"
  have "\<turnstile> S \<longrightarrow> (T \<leadsto> P)"
  proof (rule imp_leadsto_triangle_excl)
    show "\<turnstile> S \<longrightarrow> (T \<leadsto> T)" by (intro imp_imp_leadsto, simp)
    from assms show "\<turnstile> S \<longrightarrow> (T \<and> \<not> P \<leadsto> P)" by (simp add: T_def)
  qed
  thus ?thesis by (simp add: leadsto_def T_def)
qed

lemma imp_infinitely_often_implies_eventually:
  fixes P :: stpred
  assumes "\<turnstile> S \<longrightarrow> \<box>\<diamond>P"
  shows "\<turnstile> S \<longrightarrow> \<diamond>P"
  using assms reflT temp_imp_trans by blast

lemma imp_leadsto_add_precondition:
  assumes "\<turnstile> S \<longrightarrow> \<box>R"
  assumes "\<turnstile> S \<longrightarrow> ((P \<and> R) \<leadsto> Q)"
  shows "\<turnstile> S \<longrightarrow> (P \<leadsto> Q)"
  using assms
  by (meson INV_leadsto temp_imp_conjI temp_imp_trans)

lemma box_conj_simp[simp]: "(TEMP \<box>(F \<and> G)) = (TEMP \<box>F \<and> \<box>G)"
  using STL5 by fastforce

lemma box_box_conj:
  shows "\<turnstile> (\<box>(F \<and> \<box>P)) = (\<box>F \<and> \<box>P)"
  by (metis STL3 STL5 inteq_reflection)

lemmas box_box_conj_simp[simp] = inteq_reflection [OF box_box_conj]

lemma box_before_conj:
  shows "\<turnstile> (\<box>A \<and> \<box>P) \<longrightarrow> (\<box>(A \<and> $P))"
  by (metis STL5 TLA.Init_simps(2) TrueW boxInit_act boxInit_stp int_simps(13) inteq_reflection)

lemma box_conj_box_dmd:
  shows "\<turnstile> (\<box>P \<and> \<box>\<diamond>Q) \<longrightarrow> \<box>\<diamond>(P \<and> Q)"
  by (metis (mono_tags, lifting) BoxDmd_simple STL3 STL4 STL5 inteq_reflection)

lemma imp_box_imp_leadsto:
  assumes "\<turnstile> S \<longrightarrow> \<box>(P \<longrightarrow> Q)"
  shows "\<turnstile> S \<longrightarrow> (P \<leadsto> Q)"
  using assms
  unfolding Valid_def
  apply auto
  by (metis ImplLeadsto Init.Init_simps(1) Init_simps2(3) STL4E boxInitD dmdInitD leadsto_def more_temp_simps3(2))

lemma temp_conj_assoc[simp]: "TEMP ((P \<and> Q) \<and> R) = TEMP (P \<and> Q \<and> R)" by auto

lemma enabled_exI:
  assumes "s \<Turnstile> Enabled P x"
  shows "s \<Turnstile> Enabled (\<exists> x. P x)"
  using assms
  unfolding enabled_def by auto

lemma enabled_guard_conjI:
  assumes "\<And>t. (s,t) \<Turnstile> P"
  assumes "s \<Turnstile> Enabled Q"
  shows "s \<Turnstile> Enabled (P \<and> Q)"
  using assms unfolding enabled_def by auto

lemma angle_ex_simp[simp]: "(ACT <\<exists>x. P x>_vs) = (ACT \<exists>x. <P x>_vs)"
  by (auto simp add: angle_def)

lemma leadsto_dmd_classical: "\<turnstile> ((\<diamond>F) \<and> ((\<box>\<not>G) \<leadsto> G)) \<longrightarrow> (F \<leadsto> G)"
  unfolding leadsto_def dmd_def
  by (force simp: Init_simps elim: STL4E)

lemma "\<turnstile> WF(A)_vars \<longrightarrow> \<box>[\<not> A]_vars \<longrightarrow> \<box>\<diamond>\<not>Enabled (<A>_vars)"
proof -
  have 1: "\<turnstile> [\<not> A]_vars = (\<not><A>_vars)" by (auto simp add: angle_def square_def)
  have 2: "\<turnstile> (\<box>\<diamond>\<not>Enabled (<A>_vars)) = (\<not>\<diamond>\<box>Enabled (<A>_vars))"
    by (auto simp add: more_temp_simps)
  show ?thesis
    unfolding WF_def inteq_reflection[OF 1] inteq_reflection[OF 2]
    apply auto
    using more_temp_simps3(7) reflT by fastforce
qed

lemma imp_SFI:
  assumes "\<turnstile> S \<longrightarrow> (Enabled (<A>_v) \<leadsto> <A>_v)" 
  shows "\<turnstile> S \<longrightarrow> SF(A)_v"
  unfolding SF_def using assms leadsto_infinite apply auto by fastforce

lemma imp_pred_leadsto_act_reflexive: "\<turnstile> S \<longrightarrow> (A \<leadsto> $A)"
  by (metis Init_stp_act_rev imp_leadsto_reflexive leadsto_def)

lemma imp_unstable_leadsto_change:
  assumes "\<turnstile> S \<longrightarrow> (P \<leadsto> \<not>P)"
  shows "\<turnstile> S \<longrightarrow> (P \<leadsto> ($P \<and> \<not>P$))"
proof -
  note assms
  also have "\<turnstile> (P \<leadsto> \<not>P) \<longrightarrow> (P \<leadsto> ($P \<and> \<not>P$))"
    unfolding leadsto_def
  proof (intro STL4 tempI temp_impI)
    fix sigma
    assume Init_P: "sigma \<Turnstile> Init P"
    assume "sigma \<Turnstile> Init P \<longrightarrow> \<diamond>\<not> P"
    with Init_P have not_always_P: "sigma \<Turnstile> \<not>\<box>P"
      by (auto simp add: more_temp_simps)

    show "sigma \<Turnstile> \<diamond>($P \<and> \<not> P$)"
    proof (rule ccontr, simp add: more_temp_simps)
      assume no_transition: "sigma \<Turnstile> \<box>\<not> ($P \<and> \<not> P$)"
      have "sigma \<Turnstile> \<box>P"
      proof (invariant, intro Init_P, intro Stable)
        from no_transition show "sigma \<Turnstile> \<box>\<not> ($P \<and> \<not> P$)".
        show "\<turnstile> $P \<and> \<not> ($P \<and> \<not> P$) \<longrightarrow> P$" by auto
      qed
      with not_always_P show False by simp
    qed
  qed
  finally show ?thesis by simp
qed

lemma 
  fixes A B C :: temporal
  assumes "\<turnstile> A \<longrightarrow> B \<longrightarrow> C" "sigma \<Turnstile> \<box>A" "sigma \<Turnstile> \<box>B" 
  shows ABC_imp_box: "sigma \<Turnstile> \<box>C"
  using assms by (metis (full_types) STL4E normalT tempD unl_lift2)

lemma shows imp_after_leadsto: "\<turnstile> S \<longrightarrow> (P$ \<leadsto> P)"
  unfolding Valid_def leadsto_def apply auto
  by (metis DmdPrime InitDmd dmdInitD necT tempD temp_imp_trans)

lemma imp_eventually_leadsto_eventually[trans]:
  assumes 1: "\<turnstile> S \<longrightarrow> \<diamond>P"
  assumes 2: "\<turnstile> S \<longrightarrow> (P \<leadsto> Q)"
  shows "\<turnstile> S \<longrightarrow> \<diamond>Q"
proof (intro tempI temp_impI)
  fix sigma assume sigma: "sigma \<Turnstile> S"
  with 1 2 have 1: "sigma \<Turnstile> \<diamond>P" and 2: "sigma \<Turnstile> P \<leadsto> Q" by auto

  from 1 2 show "sigma \<Turnstile> \<diamond>Q"
    apply (simp add: leadsto_def)
    by (metis DmdImpl2 dmdInit dup_dmdD)
qed

lemma imp_eventually_init:
  assumes "\<turnstile> S \<longrightarrow> Init P"
  shows "\<turnstile> S \<longrightarrow> \<diamond> P"
  using assms InitDmd_gen temp_imp_trans by blast

lemma imp_box_before_afterI:
  assumes "\<turnstile> S \<longrightarrow> \<box>P"
  shows "\<turnstile> S \<longrightarrow> \<box>($P \<and> P$)"
  using assms using BoxPrime temp_imp_trans by blast

end
