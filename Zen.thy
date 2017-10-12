theory Zen
  imports Main
begin

datatype Term = Term nat nat

fun era :: "Term \<Rightarrow> nat" where "era (Term e _) = e"
fun termInEra :: "Term \<Rightarrow> nat" where "termInEra (Term _ n) = n"

definition lt_term :: "Term \<Rightarrow> Term \<Rightarrow> bool" (infixl "\<prec>" 50)
  where "t\<^sub>1 \<prec> t\<^sub>2 = (era t\<^sub>1 < era t\<^sub>2 \<or> (era t\<^sub>1 = era t\<^sub>2 \<and> termInEra t\<^sub>1 < termInEra t\<^sub>2))"

definition le_term :: "Term \<Rightarrow> Term \<Rightarrow> bool" (infixl "\<preceq>" 50)
  where "t\<^sub>1 \<preceq> t\<^sub>2 = (t\<^sub>1 \<prec> t\<^sub>2 \<or> t\<^sub>1 = t\<^sub>2)"

lemma term_le_refl[simp]: "t \<preceq> t" by (simp add: le_term_def)

lemma term_lt_lt_trans[trans]:  "\<lbrakk> t\<^sub>1 \<prec> t\<^sub>2; t\<^sub>2 \<prec> t\<^sub>3 \<rbrakk> \<Longrightarrow> t\<^sub>1 \<prec> t\<^sub>3"
  by (smt Term.inject less_trans lt_term_def)

lemma term_lt_le_trans[trans]:  "\<lbrakk> t\<^sub>1 \<prec> t\<^sub>2; t\<^sub>2 \<preceq> t\<^sub>3 \<rbrakk> \<Longrightarrow> t\<^sub>1 \<prec> t\<^sub>3"
  by (metis le_term_def term_lt_lt_trans)

lemma term_le_lt_trans[trans]:  "\<lbrakk> t\<^sub>1 \<preceq> t\<^sub>2; t\<^sub>2 \<prec> t\<^sub>3 \<rbrakk> \<Longrightarrow> t\<^sub>1 \<prec> t\<^sub>3" using term_lt_lt_trans le_term_def by auto
lemma term_le_le_trans[trans]:  "\<lbrakk> t\<^sub>1 \<preceq> t\<^sub>2; t\<^sub>2 \<preceq> t\<^sub>3 \<rbrakk> \<Longrightarrow> t\<^sub>1 \<preceq> t\<^sub>3" using term_lt_lt_trans le_term_def by auto

lemma era_mono: "t\<^sub>1 \<preceq> t\<^sub>2 \<Longrightarrow> era t\<^sub>1 \<le> era t\<^sub>2" using le_term_def lt_term_def by auto

lemma term_lt_le: "t\<^sub>1 \<prec> t\<^sub>2 \<Longrightarrow> t\<^sub>1 \<preceq> t\<^sub>2" using le_term_def by auto

lemma term_not_le_lt[simp]: "(\<not> (t\<^sub>1 \<preceq> t\<^sub>2)) = (t\<^sub>2 \<prec> t\<^sub>1)"
  by (metis era.simps le_term_def lt_term_def nat_neq_iff termInEra.cases termInEra.simps term_le_lt_trans)

lemma term_lt_wf: "wf { (t\<^sub>1, t\<^sub>2). t\<^sub>1 \<prec> t\<^sub>2 }"
proof -
  have "{ (t\<^sub>1, t\<^sub>2). t\<^sub>1 \<prec> t\<^sub>2 } = measures [era, termInEra]"
    by (simp add: measures_def inv_image_def lt_term_def)
  thus ?thesis by simp
qed

lemma term_induct [case_names less]:
  assumes "\<And>t\<^sub>1. (\<forall> t\<^sub>2. t\<^sub>2 \<prec> t\<^sub>1 \<longrightarrow> P t\<^sub>2) \<Longrightarrow> P t\<^sub>1"
  shows "P t"
  using assms
  apply (rule wf_induct [OF term_lt_wf])
  by simp

definition maxTerm :: "Term set \<Rightarrow> Term"
  where "maxTerm S = (THE t. t \<in> S \<and> (\<forall> t' \<in> S. t' \<preceq> t))"

lemma
  assumes finite: "finite S"
  shows maxTerm_mem: "S \<noteq> {} \<Longrightarrow> maxTerm S \<in> S"
    and maxTerm_max: "\<And> t'. t' \<in> S \<Longrightarrow> t' \<preceq> maxTerm S"
proof -
  presume "S \<noteq> {}"
  with assms
  obtain t where t: "t \<in> S" "\<And> t'. t' \<in> S \<Longrightarrow> t' \<preceq> t"
  proof (induct arbitrary: thesis)
    case empty
    then show ?case by simp
  next
    case (insert t S)
    show ?case
    proof (cases "S = {}")
      case True hence [simp]: "insert t S = {t}" by simp
      from insert.prems show ?thesis by simp
    next
      case False
      obtain t' where t': "t' \<in> S" "\<forall> t'' \<in> S. t'' \<preceq> t'"
        by (meson False insert.hyps(3))

      from t'
      show ?thesis
      proof (intro insert.prems ballI)
        fix t'' assume t'': "t'' \<in> insert t S"
        show "t'' \<preceq> (if t \<preceq> t' then t' else t)"
        proof (cases "t'' = t")
          case False
          with t'' have "t'' \<in> S" by simp
          with t' have "t'' \<preceq> t'" by simp
          thus ?thesis
            using term_lt_le_trans term_not_le_lt le_term_def by auto
        qed simp
      qed simp
    qed
  qed

  from t have "maxTerm S = t"
    apply (unfold maxTerm_def, intro the_equality, simp)
    using le_term_def term_not_le_lt by blast

  with t show "maxTerm S \<in> S" "\<And>t'. t' \<in> S \<Longrightarrow> t' \<preceq> maxTerm S" by simp_all
qed auto

datatype Node = Node nat
datatype ClusterState = ClusterState nat

definition intersects :: "'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" (infixl "\<frown>" 50)
  where "A \<frown> B == \<forall> a \<in> A. \<forall> b \<in> B. a \<inter> b \<noteq> {}"

typedef Configuration = "{Q :: Node set set. Q \<frown> Q}"
proof (intro exI CollectI)
  show "{} \<frown> {}"
    by (simp add: intersects_def)
qed

datatype Value
  = NoOp
  | Reconfigure Configuration
  | SetClusterState ClusterState

fun isReconfiguration :: "Value \<Rightarrow> bool"
  where "isReconfiguration (Reconfigure _) = True"
  | "isReconfiguration _ = False"

fun newConfiguration :: "Value \<Rightarrow> Node set set"
  where "newConfiguration (Reconfigure conf) = Rep_Configuration conf"
  | "newConfiguration _                      = Rep_Configuration (SOME _. False)"

locale oneSlot =
  fixes Q :: "Term \<Rightarrow> Node set set"
  fixes v :: "Term \<Rightarrow> Value"

fixes promised\<^sub>f :: "Node \<Rightarrow> Term \<Rightarrow> bool"
fixes promised\<^sub>b :: "Node \<Rightarrow> Term \<Rightarrow> Term \<Rightarrow> bool"
fixes proposed :: "Term \<Rightarrow> bool"
fixes accepted :: "Node \<Rightarrow> Term \<Rightarrow> bool"
fixes committed :: "Term \<Rightarrow> bool"

fixes promised :: "Node \<Rightarrow> Term \<Rightarrow> bool"
defines "promised n t == promised\<^sub>f n t \<or> (\<exists> t'. promised\<^sub>b n t t')"

fixes prevAccepted :: "Term \<Rightarrow> Node set \<Rightarrow> Term set"
defines "prevAccepted t ns == {t'. \<exists> n \<in> ns. promised\<^sub>b n t t'}"

assumes Q_intersects: "\<lbrakk> proposed t\<^sub>1; committed t\<^sub>2; t\<^sub>2 \<preceq> t\<^sub>1 \<rbrakk> \<Longrightarrow> Q t\<^sub>1 \<frown> Q t\<^sub>2"
assumes Q_nonempty: "q \<in> Q t \<Longrightarrow> q \<noteq> {}"

assumes promised\<^sub>f: "\<lbrakk> promised\<^sub>f n t; t' \<prec> t \<rbrakk> \<Longrightarrow> \<not> accepted n t'"

assumes promised\<^sub>b_lt:       "promised\<^sub>b n t t' \<Longrightarrow> t' \<prec> t"
assumes promised\<^sub>b_accepted: "promised\<^sub>b n t t' \<Longrightarrow> accepted n t'"
assumes promised\<^sub>b_max:    "\<lbrakk> promised\<^sub>b n t t'; t' \<prec> t''; t'' \<prec> t \<rbrakk> \<Longrightarrow> \<not> accepted n t''"

assumes proposed: "proposed t \<Longrightarrow> \<exists> q \<in> Q t. (\<forall> n \<in> q. promised n t)
                                           \<and> (prevAccepted t q = {}
                                                \<or> v t = v (maxTerm (prevAccepted t q)))"

assumes proposed_finite: "finite {t. proposed t}"

assumes accepted: "accepted n t \<Longrightarrow> proposed t"

assumes committed: "committed t \<Longrightarrow> \<exists> q \<in> Q t. \<forall> n \<in> q. accepted n t"

lemma (in oneSlot) prevAccepted_proposed: "prevAccepted t ns \<subseteq> {t. proposed t}"
  using accepted prevAccepted_def promised\<^sub>b_accepted by fastforce

lemma (in oneSlot) prevAccepted_finite: "finite (prevAccepted p ns)"
  using prevAccepted_proposed proposed_finite by (meson rev_finite_subset)

lemma (in oneSlot) p2b:
  assumes "proposed t\<^sub>1" "committed t\<^sub>2" "t\<^sub>2 \<prec> t\<^sub>1"
  shows "v t\<^sub>1 = v t\<^sub>2"
  using assms
proof (induct t\<^sub>1 rule: term_induct)
  case (less t\<^sub>1)

  hence hyp: "\<And> t\<^sub>1'. \<lbrakk> t\<^sub>1' \<prec> t\<^sub>1; proposed t\<^sub>1'; t\<^sub>2 \<preceq> t\<^sub>1' \<rbrakk> \<Longrightarrow> v t\<^sub>1' = v t\<^sub>2"
    using le_term_def by blast

  from `proposed t\<^sub>1` obtain q\<^sub>1 where
    q\<^sub>1_quorum:   "q\<^sub>1 \<in> Q t\<^sub>1" and
    q\<^sub>1_promised: "\<And>n. n \<in> q\<^sub>1 \<Longrightarrow> promised n t\<^sub>1" and
    q\<^sub>1_value:    "prevAccepted t\<^sub>1 q\<^sub>1 = {} \<or> v t\<^sub>1 = v (maxTerm (prevAccepted t\<^sub>1 q\<^sub>1))"
    by (meson proposed)

  from `committed t\<^sub>2` obtain q\<^sub>2 where
    q\<^sub>2_quorum:   "q\<^sub>2 \<in> Q t\<^sub>2" and
    q\<^sub>2_accepted: "\<And>n. n \<in> q\<^sub>2 \<Longrightarrow> accepted n t\<^sub>2"
    using committed by force

  have "q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}"
    by (meson intersects_def less.prems(1) less.prems(2) less.prems(3) oneSlot.Q_intersects oneSlot_axioms q\<^sub>1_quorum q\<^sub>2_quorum term_lt_le)

  then obtain n where n\<^sub>1: "n \<in> q\<^sub>1" and n\<^sub>2: "n \<in> q\<^sub>2" by auto

  from n\<^sub>1 q\<^sub>1_promised have "promised n t\<^sub>1" by simp
  moreover from n\<^sub>2 q\<^sub>2_accepted have "accepted n t\<^sub>2" by simp
  ultimately obtain t\<^sub>2' where t\<^sub>2': "promised\<^sub>b n t\<^sub>1 t\<^sub>2'"
    using less.prems(3) promised\<^sub>f promised_def by blast

  have q\<^sub>1_value: "v t\<^sub>1 = v (maxTerm (prevAccepted t\<^sub>1 q\<^sub>1))"
    using n\<^sub>1 prevAccepted_def q\<^sub>1_value t\<^sub>2' by auto

  also have "... = v t\<^sub>2"
  proof (intro hyp)
    have p: "maxTerm (prevAccepted t\<^sub>1 q\<^sub>1) \<in> prevAccepted t\<^sub>1 q\<^sub>1"
      apply (intro maxTerm_mem prevAccepted_finite)
      using n\<^sub>1 prevAccepted_def t\<^sub>2' by auto

    show "maxTerm (prevAccepted t\<^sub>1 q\<^sub>1) \<prec> t\<^sub>1"
      using p prevAccepted_def promised\<^sub>b_lt by auto

    show "proposed (maxTerm (prevAccepted t\<^sub>1 q\<^sub>1))"
      using p prevAccepted_proposed by auto

    have "t\<^sub>2 \<preceq> t\<^sub>2'"
      using \<open>accepted n t\<^sub>2\<close> less.prems(3) promised\<^sub>b_max t\<^sub>2' term_not_le_lt by blast
    also have "t\<^sub>2' \<preceq> maxTerm (prevAccepted t\<^sub>1 q\<^sub>1)"
      using n\<^sub>1 prevAccepted_def t\<^sub>2' prevAccepted_finite by (intro maxTerm_max, auto)
    finally show "t\<^sub>2 \<preceq> maxTerm (prevAccepted t\<^sub>1 q\<^sub>1)" .
  qed

  finally show ?case .
qed

lemma (in oneSlot) consistent:
  assumes "committed t\<^sub>1" "committed t\<^sub>2"
  shows "v t\<^sub>1 = v t\<^sub>2"
  by (metis Q_nonempty accepted all_not_in_conv assms committed le_term_def p2b term_not_le_lt)

locale zen =
  fixes Q\<^sub>0        :: "Node set set"
  fixes v         :: "nat \<Rightarrow> Term \<Rightarrow> Value"

fixes promised\<^sub>m :: "nat \<Rightarrow> Node \<Rightarrow> Term \<Rightarrow> bool"
fixes promised\<^sub>f :: "nat \<Rightarrow> Node \<Rightarrow> Term \<Rightarrow> bool"
fixes promised\<^sub>b :: "nat \<Rightarrow> Node \<Rightarrow> Term \<Rightarrow> Term \<Rightarrow> bool"
fixes proposed  :: "nat \<Rightarrow> Term \<Rightarrow> bool"
fixes accepted  :: "nat \<Rightarrow> Node \<Rightarrow> Term \<Rightarrow> bool"
fixes committed :: "nat \<Rightarrow> Term \<Rightarrow> bool"

fixes isCommitted :: "nat \<Rightarrow> bool"
defines "isCommitted i == \<exists> t. committed i t"

fixes committedTo :: "nat \<Rightarrow> bool"
defines "committedTo i == \<forall> j < i. isCommitted j" 

fixes v\<^sub>c :: "nat \<Rightarrow> Value"
defines "v\<^sub>c i == v i (SOME t. committed i t)"

fixes era\<^sub>i :: "nat \<Rightarrow> nat"
defines "era\<^sub>i i == card { j. j < i \<and> isReconfiguration (v\<^sub>c j) }"

fixes Q :: "nat \<Rightarrow> Node set set"
defines "Q e == if e = 0 then Q\<^sub>0
                else newConfiguration (v\<^sub>c (THE i. isReconfiguration (v\<^sub>c i) \<and> era\<^sub>i i = e-1))"

fixes promised :: "nat \<Rightarrow> Node \<Rightarrow> Term \<Rightarrow> bool"
defines "promised i n t == ((\<exists> j \<le> i. promised\<^sub>m j n t)
                            \<or> promised\<^sub>f i n t)
                            \<or> (\<exists> t'. promised\<^sub>b i n t t')"

fixes prevAccepted :: "nat \<Rightarrow> Term \<Rightarrow> Node set \<Rightarrow> Term set"
defines "prevAccepted i t ns == {t'. \<exists> n \<in> ns. promised\<^sub>b i n t t'}"

assumes Q\<^sub>0_intersects: "Q\<^sub>0 \<frown> Q\<^sub>0"

assumes promised\<^sub>m: "\<lbrakk> promised\<^sub>m i n t; t' \<prec> t; i \<le> j \<rbrakk> \<Longrightarrow> \<not> accepted j n t'"

assumes promised\<^sub>f: "\<lbrakk> promised\<^sub>f i n t; t' \<prec> t \<rbrakk> \<Longrightarrow> \<not> accepted i n t'"

assumes promised\<^sub>b_lt:       "promised\<^sub>b i n t t' \<Longrightarrow> t' \<prec> t"
assumes promised\<^sub>b_accepted: "promised\<^sub>b i n t t' \<Longrightarrow> accepted i n t'"
assumes promised\<^sub>b_max:    "\<lbrakk> promised\<^sub>b i n t t'; t' \<prec> t''; t'' \<prec> t \<rbrakk> \<Longrightarrow> \<not> accepted i n t''"

assumes promised_era: "promised i n t \<Longrightarrow> \<exists> j \<le> i. era t \<le> era\<^sub>i j \<and> committedTo j"

assumes proposed: "proposed i t \<Longrightarrow> \<exists> q \<in> Q (era t). (\<forall> n \<in> q. promised i n t)
                                           \<and> (prevAccepted i t q = {}
                                                \<or> v i t = v i (maxTerm (prevAccepted i t q)))"

assumes proposed_finite: "finite {(i, t). proposed i t}"

assumes accepted: "accepted i n t \<Longrightarrow> proposed i t"

assumes committed:          "committed i t \<Longrightarrow> \<exists> q \<in> Q (era t). \<forall> n \<in> q. accepted i n t"
assumes committed_era:      "committed i t \<Longrightarrow> era\<^sub>i i = era t"
assumes committed_in_order: "committed i t \<Longrightarrow> committedTo i"

lemma (in zen)
  shows Q_intersects: "Q e \<frown> Q e"
proof (cases "e = 0")
  case True thus ?thesis by (simp add: Q\<^sub>0_intersects Q_def)
next
  case False

  from Rep_Configuration
  have [simp]: "\<And>ns. Rep_Configuration ns \<frown> Rep_Configuration ns"
    by simp

  hence [simp]: "\<And>va. newConfiguration va \<frown> newConfiguration va"
  proof -
    fix va
    show "?thesis va"
      by (cases va, simp_all)
  qed

  show ?thesis by (simp add: False Q_def)
qed

lemma (in zen)
  assumes "isCommitted i"
  shows projects_to_oneSlot:
    "oneSlot (Q o era) (v i) (\<lambda> n t. (\<exists>j \<le> i. promised\<^sub>m j n t) \<or> promised\<^sub>f i n t)
      (promised\<^sub>b i) (proposed i) (accepted i) (committed i)"
proof (unfold_locales, fold promised_def prevAccepted_def)
  fix n t assume "accepted i n t" thus "proposed i t" by (intro accepted)
next
  show "finite {t. proposed i t}"
  proof (intro finite_subset [OF _ finite_imageI [OF proposed_finite, of snd]] subsetI image_eqI)
    fix t assume "t \<in> { t. proposed i t }" hence t: "proposed i t" by simp
    thus "t = snd (i, t)" and "(i, t) \<in> {(i, t). proposed i t}" by simp_all
  qed
next
  fix n t t'
  assume p: "promised\<^sub>b i n t t'"
  from promised\<^sub>b_lt p show "t' \<prec> t" .
  from promised\<^sub>b_accepted p show "accepted i n t'" .

  fix t''
  assume "t' \<prec> t''" "t'' \<prec> t"
  with p promised\<^sub>b_max show "\<not>accepted i n t''" by simp
next
  fix n t t'
  assume t't: "t' \<prec> t"
  assume "(\<exists>j\<le>i. promised\<^sub>m j n t) \<or> promised\<^sub>f i n t"
  thus "\<not> accepted i n t'"
  proof (elim disjE)
    from promised\<^sub>f t't
    show "promised\<^sub>f i n t \<Longrightarrow> \<not> accepted i n t'" by simp
    from promised\<^sub>m t't
    show "\<exists>j\<le>i. promised\<^sub>m j n t \<Longrightarrow> \<not> accepted i n t'" by auto
  qed
next
  fix t
  assume "proposed i t"
  from proposed [OF this]
  show "\<exists>q\<in>(Q \<circ> era) t. (\<forall>n\<in>q. promised i n t) \<and> (prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q)))" by simp
next
  fix q t
  assume "q \<in> (Q \<circ> era) t"
  with Q_intersects [of "era t"]
  show "q \<noteq> {}" by (auto simp add: intersects_def)
next
  fix t\<^sub>2
  assume t2: "committed i t\<^sub>2"
  from committed [OF this]
  show "\<exists>q\<in>(Q \<circ> era) t\<^sub>2. \<forall>n\<in>q. accepted i n t\<^sub>2" by simp

  fix t\<^sub>1
  assume t1: "proposed i t\<^sub>1" and t21: "t\<^sub>2 \<preceq> t\<^sub>1"
  hence "era t\<^sub>2 \<le> era t\<^sub>1" using era_mono by blast

  moreover from proposed [OF t1]
  obtain q\<^sub>1 where q\<^sub>1: "q\<^sub>1 \<in> Q (era t\<^sub>1)" "\<And> n. n \<in> q\<^sub>1 \<Longrightarrow> promised i n t\<^sub>1" by auto
  with Q_intersects [of "era t\<^sub>1"] obtain n where "n \<in> q\<^sub>1"
    by (meson IntE all_not_in_conv intersects_def)

  with q\<^sub>1 have "promised i n t\<^sub>1" by simp
  from promised_era [OF this]
  obtain j where ji: "j \<le> i" and "era t\<^sub>1 \<le> era\<^sub>i j" by auto

  moreover
  from ji have "era\<^sub>i j \<le> era\<^sub>i i"
    by (unfold era\<^sub>i_def, intro card_mono, auto)

  moreover from t2 committed_era have "era\<^sub>i i = era t\<^sub>2" by simp

  ultimately show "(Q \<circ> era) t\<^sub>1 \<frown> (Q \<circ> era) t\<^sub>2"
    using Q_intersects order_trans by fastforce
qed

lemma (in zen) consistent:
  assumes "committed i t\<^sub>1" "committed i t\<^sub>2"
  shows "v i t\<^sub>1 = v i t\<^sub>2"
  using assms
  by (intro oneSlot.consistent [OF projects_to_oneSlot], auto simp add: isCommitted_def)

lemma Collect_pair_False[simp]:  "{(i, t). False} = {}" by auto

lemma
  assumes "Q\<^sub>0 \<frown> Q\<^sub>0"
  shows zen_initial_state:
    "zen Q\<^sub>0 v (\<lambda> _ _ _. False) (\<lambda> _ _ _. False) (\<lambda> _ _ _ _. False) (\<lambda> _ _. False)
             (\<lambda> _ _ _. False) (\<lambda> _ _. False)"
  using assms by (unfold_locales, auto)

lemma (in zen)
  fixes promised\<^sub>m' promised\<^sub>f' promised\<^sub>b'

fixes promised' :: "nat \<Rightarrow> Node \<Rightarrow> Term \<Rightarrow> bool"
defines "promised' i n t == ((\<exists> j \<le> i. promised\<^sub>m' j n t)
                            \<or> promised\<^sub>f' i n t)
                            \<or> (\<exists> t'. promised\<^sub>b' i n t t')"

fixes prevAccepted' :: "nat \<Rightarrow> Term \<Rightarrow> Node set \<Rightarrow> Term set"
defines "prevAccepted' i t ns == {t'. \<exists> n \<in> ns. promised\<^sub>b' i n t t'}"

assumes "\<And>i j n t t'. \<lbrakk> promised\<^sub>m' i n t; t' \<prec> t; i \<le> j \<rbrakk> \<Longrightarrow> \<not> accepted' j n t'"

assumes "\<And>i n t t'. \<lbrakk> promised\<^sub>f' i n t; t' \<prec> t \<rbrakk> \<Longrightarrow> \<not> accepted' i n t'"

assumes  "\<And>i n t t'. promised\<^sub>b' i n t t' \<Longrightarrow> t' \<prec> t"
assumes  "\<And>i n t t'. promised\<^sub>b' i n t t' \<Longrightarrow> accepted' i n t'"
assumes  "\<And>i n t t' t''. \<lbrakk> promised\<^sub>b' i n t t'; t' \<prec> t''; t'' \<prec> t \<rbrakk> \<Longrightarrow> \<not> accepted' i n t''"

assumes "\<And>i n t. promised' i n t \<Longrightarrow> \<exists> j \<le> i. era t \<le> era\<^sub>i j \<and> committedTo j"

assumes "\<And>i t. proposed' i t \<Longrightarrow> \<exists> q \<in> Q (era t). (\<forall> n \<in> q. promised' i n t)
                                                 \<and> (prevAccepted' i t q = {}
                                                     \<or> v i t = v i (maxTerm (prevAccepted' i t q)))"

assumes "finite {(i, t). proposed' i t}"

assumes "\<And>i n t. accepted' i n t \<Longrightarrow> proposed' i t"

assumes "\<And>i t. committed i t \<Longrightarrow> \<exists> q \<in> Q (era t). \<forall> n \<in> q. accepted' i n t"

shows zenI_simple:
  "zen Q\<^sub>0 v promised\<^sub>m' promised\<^sub>f' promised\<^sub>b' proposed' accepted' committed"
  using assms Q\<^sub>0_intersects committed_era committed_in_order
  by (unfold_locales, fold promised'_def prevAccepted'_def era\<^sub>i_def isCommitted_def committedTo_def v\<^sub>c_def, fold committedTo_def era\<^sub>i_def, fold Q_def)

