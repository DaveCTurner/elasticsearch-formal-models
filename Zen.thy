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

lemma (in oneSlot) commit:
  assumes q_quorum: "q \<in> Q t\<^sub>0"
  assumes q_accepted: "\<And>n. n \<in> q \<Longrightarrow> accepted n t\<^sub>0"
  assumes intersects: "\<And>t. proposed t \<Longrightarrow> t\<^sub>0 \<preceq> t \<Longrightarrow> Q t \<frown> Q t\<^sub>0"
  defines "committed' t == committed t \<or> t = t\<^sub>0"
  shows "oneSlot Q v promised\<^sub>f promised\<^sub>b proposed accepted committed'"
  by (smt committed'_def intersects oneSlot_axioms oneSlot_def q_accepted q_quorum)

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

fixes reconfig :: "nat \<Rightarrow> nat"
defines "reconfig e == THE i. isCommitted i \<and> isReconfiguration (v\<^sub>c i) \<and> era\<^sub>i i = e"

fixes Q :: "nat \<Rightarrow> Node set set"
defines "Q e == if e = 0 then Q\<^sub>0 else newConfiguration (v\<^sub>c (reconfig (e-1)))"

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
  by (unfold_locales, fold promised'_def prevAccepted'_def era\<^sub>i_def isCommitted_def committedTo_def v\<^sub>c_def, fold committedTo_def era\<^sub>i_def reconfig_def, fold Q_def)

lemma (in zen)
  assumes not_accepted: "\<And>t j. i\<^sub>0 \<le> j \<Longrightarrow> \<not> accepted j n\<^sub>0 t"
  assumes era: "\<exists> j \<le> i\<^sub>0. era t\<^sub>0 \<le> era\<^sub>i j \<and> committedTo j"
  defines "promised\<^sub>m' i n t == promised\<^sub>m i n t \<or> (i, n, t) = (i\<^sub>0, n\<^sub>0, t\<^sub>0)"
  shows add_promised\<^sub>m: "zen Q\<^sub>0 v promised\<^sub>m' promised\<^sub>f promised\<^sub>b proposed accepted committed"
  using promised\<^sub>f promised\<^sub>b_accepted promised\<^sub>b_lt promised\<^sub>b_max proposed_finite accepted committed
proof (intro zenI_simple, fold prevAccepted_def)
  fix i j n t t'
  assume p: "promised\<^sub>m' i n t" "t' \<prec> t" "i \<le> j"
  hence "promised\<^sub>m i n t \<or> (i, n, t) = (i\<^sub>0, n\<^sub>0, t\<^sub>0)"
    by (auto simp add: promised\<^sub>m'_def)
  thus "\<not> accepted j n t'"
  proof (elim disjE)
    assume "promised\<^sub>m i n t" with promised\<^sub>m p show ?thesis by simp
  next
    assume "(i, n, t) = (i\<^sub>0, n\<^sub>0, t\<^sub>0)"
    with p not_accepted show ?thesis by simp
  qed
next
  fix i n t
  assume "((\<exists>j\<le>i. promised\<^sub>m' j n t) \<or> promised\<^sub>f i n t) \<or> (\<exists>t'. promised\<^sub>b i n t t')"
  hence "(i\<^sub>0 \<le> i \<and> (n, t) = (n\<^sub>0, t\<^sub>0)) \<or> promised i n t"
    by (auto simp add: promised\<^sub>m'_def promised_def)
  thus "\<exists>j\<le>i. era t \<le> era\<^sub>i j \<and> committedTo j"
  proof (elim disjE)
    assume "promised i n t" with promised_era show ?thesis by simp
  next
    assume "i\<^sub>0 \<le> i \<and> (n, t) = (n\<^sub>0, t\<^sub>0)"
    with era show ?thesis using order_trans by auto
  qed
next
  fix i t
  assume "proposed i t"
  from proposed [OF this]
  obtain q where q: "q\<in>Q (era t)" "\<forall>n\<in>q. promised i n t" "prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q))" by auto

  from q
  show "\<exists>q\<in>Q (era t). (\<forall>n\<in>q. ((\<exists>j\<le>i. promised\<^sub>m' j n t) \<or> promised\<^sub>f i n t) \<or> (\<exists>t'. promised\<^sub>b i n t t')) \<and> (prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q)))"
    by (intro bexI [of _ q], auto simp add: q promised\<^sub>m'_def promised_def)
qed

lemma (in zen)
  assumes not_accepted: "\<And>t. \<not> accepted i\<^sub>0 n\<^sub>0 t"
  assumes era: "\<exists> j \<le> i\<^sub>0. era t\<^sub>0 \<le> era\<^sub>i j \<and> committedTo j"
  defines "promised\<^sub>f' i n t == promised\<^sub>f i n t \<or> (i, n, t) = (i\<^sub>0, n\<^sub>0, t\<^sub>0)"
  shows add_promised\<^sub>f: "zen Q\<^sub>0 v promised\<^sub>m promised\<^sub>f' promised\<^sub>b proposed accepted committed"
  using promised\<^sub>m promised\<^sub>b_accepted promised\<^sub>b_lt promised\<^sub>b_max proposed_finite accepted committed
proof (intro zenI_simple, fold prevAccepted_def)
  fix i n t t'
  assume "promised\<^sub>f' i n t" "t' \<prec> t"
  hence "promised\<^sub>f i n t \<or> (i, n, t) = (i\<^sub>0, n\<^sub>0, t\<^sub>0)" by (auto simp add: promised\<^sub>f'_def)
  with not_accepted `t' \<prec> t`
  show "\<not> accepted i n t'"
    by (elim disjE, intro promised\<^sub>f, auto)
next
  fix i n t
  assume "((\<exists>j\<le>i. promised\<^sub>m j n t) \<or> promised\<^sub>f' i n t) \<or> (\<exists>t'. promised\<^sub>b i n t t')"
  hence "promised i n t \<or> (i, n, t) = (i\<^sub>0, n\<^sub>0, t\<^sub>0)"
    by (auto simp add: promised\<^sub>f'_def promised_def)
  with era promised_era
  show "\<exists>j\<le>i. era t \<le> era\<^sub>i j \<and> committedTo j" by auto
next
  fix i t
  assume "proposed i t"
  from proposed [OF this]
  obtain q where q: "q\<in>Q (era t)" "\<forall>n\<in>q. promised i n t" "prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q))" by auto
  thus "\<exists>q\<in>Q (era t). (\<forall>n\<in>q. ((\<exists>j\<le>i. promised\<^sub>m j n t) \<or> promised\<^sub>f' i n t) \<or> (\<exists>t'. promised\<^sub>b i n t t')) \<and> (prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q)))"
    by (intro bexI [of _ q], auto simp add: q promised\<^sub>f'_def promised_def)
qed

lemma (in zen)
  assumes earlier_term: "t\<^sub>0' \<prec> t\<^sub>0"
  assumes accepted\<^sub>0: "accepted i\<^sub>0 n\<^sub>0 t\<^sub>0'"
  assumes max_accepted: "\<And>t\<^sub>0''. accepted i\<^sub>0 n\<^sub>0 t\<^sub>0'' \<Longrightarrow> t\<^sub>0'' \<preceq> t\<^sub>0'"
  assumes era: "\<exists> j \<le> i\<^sub>0. era t\<^sub>0 \<le> era\<^sub>i j \<and> committedTo j"
  defines "promised\<^sub>b' i n t t' == promised\<^sub>b i n t t' \<or> (i, n, t, t') = (i\<^sub>0, n\<^sub>0, t\<^sub>0, t\<^sub>0')"
  shows add_promised\<^sub>b: "zen Q\<^sub>0 v promised\<^sub>m promised\<^sub>f promised\<^sub>b' proposed accepted committed"
  using promised\<^sub>m promised\<^sub>f proposed_finite accepted committed
proof (intro zenI_simple)
  fix i n t t'
  assume p: "promised\<^sub>b' i n t t'"
  from p earlier_term promised\<^sub>b_lt show "t' \<prec> t"
    using promised\<^sub>b'_def by auto

  from p accepted\<^sub>0 promised\<^sub>b_accepted show "accepted i n t'"
    using promised\<^sub>b'_def by auto

  fix t'' assume "t' \<prec> t''" "t'' \<prec> t"
  with p promised\<^sub>b_max max_accepted show "\<not> accepted i n t''"
    using promised\<^sub>b'_def
    by (metis prod.inject term_not_le_lt)

next
  fix i n t
  assume "((\<exists>j\<le>i. promised\<^sub>m j n t) \<or> promised\<^sub>f i n t) \<or> (\<exists>t'. promised\<^sub>b' i n t t')"
  hence "promised i n t \<or> (i, n, t) = (i\<^sub>0, n\<^sub>0, t\<^sub>0)"
    using promised\<^sub>b'_def promised_def by auto
  thus "\<exists>j\<le>i. era t \<le> era\<^sub>i j \<and> committedTo j"
    using era promised_era by auto

next
  have promised\<^sub>b_func: "\<And>t'. promised\<^sub>b i\<^sub>0 n\<^sub>0 t\<^sub>0 t' \<Longrightarrow> t' = t\<^sub>0'"
    using accepted\<^sub>0 earlier_term le_term_def max_accepted promised\<^sub>b_accepted promised\<^sub>b_max by blast

  have promised_imp: "promised i\<^sub>0 n\<^sub>0 t\<^sub>0 \<Longrightarrow> promised\<^sub>b i\<^sub>0 n\<^sub>0 t\<^sub>0 t\<^sub>0'"
    using promised_def accepted\<^sub>0 earlier_term promised\<^sub>b_func promised\<^sub>f promised\<^sub>m by blast

  fix i t
  assume "proposed i t"
  from proposed [OF this]
  obtain q where q: "q\<in>Q (era t)" "\<forall>n\<in>q. promised i n t" "prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q))" by auto

  have [simp]: "{t'. \<exists>n\<in>q. promised\<^sub>b' i n t t'} = prevAccepted i t q"
    using prevAccepted_def promised\<^sub>b'_def promised_imp q(2) by auto

  from q show "\<exists>q\<in>Q (era t). (\<forall>n\<in>q. ((\<exists>j\<le>i. promised\<^sub>m j n t) \<or> promised\<^sub>f i n t) \<or> (\<exists>t'. promised\<^sub>b' i n t t')) \<and> ({t'. \<exists>n\<in>q. promised\<^sub>b' i n t t'} = {} \<or> v i t = v i (maxTerm {t'. \<exists>n\<in>q. promised\<^sub>b' i n t t'}))"
  proof (intro bexI [of _ q] conjI)
    from q show
      "\<forall>n\<in>q. ((\<exists>j\<le>i. promised\<^sub>m j n t) \<or> promised\<^sub>f i n t) \<or> (\<exists>t'. promised\<^sub>b' i n t t')"
      by (auto simp add: promised\<^sub>b'_def promised_def)
  qed simp
qed

lemma (in zen) committed_accepted:
  assumes "committed i t"
  obtains n where "accepted i n t"
  using assms committed isCommitted_def oneSlot.Q_nonempty projects_to_oneSlot by fastforce

lemma (in zen)
  assumes "committed i t"
  shows committed_proposed: "proposed i t"
  by (meson Int_emptyI Q_intersects accepted assms committed intersects_def)

lemma (in zen) proposed_promised:
  assumes "proposed i t"
  obtains n where "promised i n t"
  by (meson Int_emptyI Q_intersects assms intersects_def proposed)

lemma (in zen) committed_promised:
  assumes "committed i t"
  obtains n where "promised i n t"
  using assms committed_proposed proposed_promised by blast

lemma (in zen) era\<^sub>i_Suc_eq:
  assumes "\<not> isReconfiguration (v\<^sub>c i)"
  shows "era\<^sub>i (Suc i) = era\<^sub>i i"
  by (metis (no_types, lifting) Collect_cong assms era\<^sub>i_def less_Suc_eq)

lemma (in zen) era\<^sub>i_Suc_Suc:
  assumes "isReconfiguration (v\<^sub>c i)"
  shows "era\<^sub>i (Suc i) = Suc (era\<^sub>i i)"
proof -
  have "{j. j < Suc i \<and> isReconfiguration (v\<^sub>c j)} = insert i {j. j < i \<and> isReconfiguration (v\<^sub>c j)}"
    using assms by auto
  thus ?thesis by (simp add: era\<^sub>i_def)
qed

lemma (in zen) era\<^sub>i_Suc:
  shows "era\<^sub>i (Suc i) = (if isReconfiguration (v\<^sub>c i) then Suc (era\<^sub>i i) else era\<^sub>i i)"
  by (simp add: era\<^sub>i_Suc_Suc era\<^sub>i_Suc_eq)

lemma (in zen) era\<^sub>i_mono:
  shows "j \<le> i \<Longrightarrow> era\<^sub>i j \<le> era\<^sub>i i"
  by (induct i, simp, metis era\<^sub>i_Suc_Suc era\<^sub>i_Suc_eq le_SucE le_SucI order_refl)

lemma (in zen)
  assumes "j < i" "isReconfiguration (v\<^sub>c j)" "isCommitted i"
  shows era_increases_on_reconfiguration: "era\<^sub>i j < era\<^sub>i i"
  using assms
  by (metis Suc_le_eq era\<^sub>i_Suc_Suc era\<^sub>i_mono)

lemma (in zen)
  assumes "era\<^sub>i i = era\<^sub>i j"
  assumes "isCommitted i"
  assumes "isCommitted j"
  assumes "isReconfiguration (v\<^sub>c i)"
  assumes "isReconfiguration (v\<^sub>c j)"
  shows unique_reconfiguration_in_era: "i = j"
  by (metis assms era_increases_on_reconfiguration nat_neq_iff)

lemma (in zen) committedTo_mono: "j \<le> i \<Longrightarrow> committedTo i \<Longrightarrow> committedTo j"
  using committedTo_def by auto

lemma (in zen) committed_committedTo_Suc: "isCommitted i \<Longrightarrow> committedTo (Suc i)"
  using committedTo_def committed_in_order isCommitted_def less_Suc_eq by auto

lemma (in zen) committed_committedTo: "isCommitted i \<Longrightarrow> committedTo i"
  using committed_in_order isCommitted_def by auto

lemma (in zen)
  assumes "committedTo i"
  assumes "e < era\<^sub>i i"
  shows reconfig_lt: "reconfig e < i"
    and reconfig_committed: "isCommitted (reconfig e)"
    and reconfig_isReconfiguration: "isReconfiguration (v\<^sub>c (reconfig e))"
    and reconfig_era: "era\<^sub>i (reconfig e) = e"
proof -
  from assms
  have "\<exists> j. isCommitted j \<and> isReconfiguration (v\<^sub>c j) \<and> era\<^sub>i j = e"
  proof (induct i arbitrary: e)
    case Suc thus ?case
      by (metis committedTo_def committed_committedTo era\<^sub>i_Suc_Suc era\<^sub>i_Suc_eq lessI less_antisym)
  qed (simp add: era\<^sub>i_def)
  then obtain j where j: "isCommitted j" "isReconfiguration (v\<^sub>c j)" "era\<^sub>i j = e" by auto

  define P where "\<And>i. P i == isCommitted i \<and> isReconfiguration (v\<^sub>c i) \<and> era\<^sub>i i = e"
  have reconfig_The: "reconfig e = (THE i. P i)" by (simp add: reconfig_def P_def)

  have "P (reconfig e)"
    apply (unfold reconfig_The)
    apply (intro theI [of P j])
     apply (unfold P_def, intro conjI j)
    using j unique_reconfiguration_in_era by blast

  thus "isCommitted (reconfig e)"
    "isReconfiguration (v\<^sub>c (reconfig e))"
    "era\<^sub>i (reconfig e) = e"
    by (auto simp add: P_def)

  thus "reconfig e < i" using assms by (metis era\<^sub>i_mono not_less)
qed

lemma (in zen)
  assumes "committedTo i"
  assumes "e < era\<^sub>i i"
  assumes "isReconfiguration (v\<^sub>c j)"
  assumes "era\<^sub>i j = e"
  shows reconfig_eq: "j = reconfig e"
  by (metis Suc_leI assms era\<^sub>i_Suc_Suc era\<^sub>i_mono leD lessI nat_neq_iff reconfig_era reconfig_isReconfiguration)

lemma (in zen)
  finite_prevAccepted: "finite (prevAccepted i t q)"
proof -
  have "prevAccepted i t q \<subseteq> { t'. \<exists> n. \<exists> i. promised\<^sub>b i n t t' }" using prevAccepted_def by auto
  also have "... \<subseteq> { t'. \<exists> n. \<exists> i. accepted i n t' }" using promised\<^sub>b_accepted by fastforce
  also have "... \<subseteq> { t'. \<exists> i. proposed i t' }" using accepted by fastforce
  also have "... \<subseteq> snd ` { (i, t). proposed i t }" by force
  finally show ?thesis using finite_surj proposed_finite by auto
qed

lemma (in zen)
  assumes not_already_proposed: "\<not> proposed i\<^sub>0 t\<^sub>0"
  assumes q_promised: "\<And>n. n \<in> q \<Longrightarrow> promised i\<^sub>0 n t\<^sub>0"
  assumes q_quorum: "q \<in> Q (era t\<^sub>0)"

fixes v\<^sub>0
defines "v' i t == if (i, t) = (i\<^sub>0, t\<^sub>0)
                        then if prevAccepted i\<^sub>0 t\<^sub>0 q = {}
                                then v\<^sub>0
                                else v i\<^sub>0 (maxTerm (prevAccepted i\<^sub>0 t\<^sub>0 q))
                        else v i t"

defines "proposed' i t == proposed i t \<or> (i, t) = (i\<^sub>0, t\<^sub>0)"
shows add_proposed: "zen Q\<^sub>0 v' promised\<^sub>m promised\<^sub>f promised\<^sub>b proposed' accepted committed"
proof -
  define v\<^sub>c' where "\<And>i. v\<^sub>c' i == v' i (SOME t. committed i t)"
  define era\<^sub>i' where "\<And>i. era\<^sub>i' i == card {j. j < i \<and> isReconfiguration (v\<^sub>c' j)}"
  define reconfig' where "\<And>e. reconfig' e == THE i. isCommitted i \<and> isReconfiguration (v\<^sub>c' i) \<and> era\<^sub>i' i = e"
  define Q' where "\<And>e. Q' e == if e = 0 then Q\<^sub>0 else newConfiguration (v\<^sub>c' (reconfig' (e-1)))"

  have v\<^sub>c_eq: "\<And>i. isCommitted i \<Longrightarrow> v\<^sub>c' i = v\<^sub>c i"
    using committed_proposed isCommitted_def not_already_proposed tfl_some v'_def v\<^sub>c'_def v\<^sub>c_def by auto

  have era\<^sub>i_eq: "\<And>i. committedTo i \<Longrightarrow> era\<^sub>i' i = era\<^sub>i i"
    by (metis (mono_tags, lifting) Collect_cong committedTo_def era\<^sub>i'_def era\<^sub>i_def v\<^sub>c_eq)

  have reconfig_eq: "\<And>i e. committedTo i \<Longrightarrow> e < era\<^sub>i i \<Longrightarrow> reconfig' e = reconfig e"
  proof -
    fix i e
    assume a: "committedTo i" "e < era\<^sub>i i"

    define P where "\<And>i. P i == isCommitted i \<and> isReconfiguration (v\<^sub>c' i) \<and> era\<^sub>i' i = e"
    have reconfig'_eq: "reconfig' e = (THE i. P i)" by (simp add: P_def reconfig'_def)

    have "P (reconfig' e)"
    proof (unfold reconfig'_eq, intro theI [of P])
      show "P (reconfig e)"
        using P_def a committed_committedTo era\<^sub>i_eq reconfig_committed reconfig_era reconfig_isReconfiguration v\<^sub>c_eq by auto
      fix j assume "P j" thus "j = reconfig e"
        using P_def a committed_committedTo era\<^sub>i_eq reconfig_eq v\<^sub>c_eq by auto
    qed

    from a this show "?thesis i e"
      by (intro reconfig_eq [of i], auto simp add: P_def v\<^sub>c_eq era\<^sub>i_eq committed_committedTo)
  qed

  have Q_eq: "\<And>i. committedTo i \<Longrightarrow> \<forall> e \<le> era\<^sub>i i. Q' e = Q e"
    by (simp add: Q'_def Q_def reconfig_committed reconfig_eq v\<^sub>c_eq)

  have v_prevAccepted_eq: "\<And>i t q. prevAccepted i t q \<noteq> {} \<Longrightarrow> v' i (maxTerm (prevAccepted i t q)) = v i (maxTerm (prevAccepted i t q))"
  proof -
    fix i t q
    assume bound: "prevAccepted i t q \<noteq> {}"

    have "maxTerm (prevAccepted i t q) \<in> prevAccepted i t q"
      by (intro maxTerm_mem `prevAccepted i t q \<noteq> {}` finite_prevAccepted)

    then obtain n where "promised\<^sub>b i n t (maxTerm (prevAccepted i t q))" by (auto simp add: prevAccepted_def)
    hence "accepted i n (maxTerm (prevAccepted i t q))" using promised\<^sub>b_accepted by auto
    hence "proposed i   (maxTerm (prevAccepted i t q))" using accepted by auto

    thus "?thesis i t q" using not_already_proposed v'_def by auto
  qed

  from Q\<^sub>0_intersects proposed_finite accepted promised\<^sub>m promised\<^sub>f promised\<^sub>b_lt promised\<^sub>b_accepted promised\<^sub>b_max
  have update_value: "zen Q\<^sub>0 v' promised\<^sub>m promised\<^sub>f promised\<^sub>b proposed accepted committed"
  proof (unfold_locales, fold promised_def isCommitted_def v\<^sub>c'_def prevAccepted_def, fold committedTo_def era\<^sub>i'_def reconfig'_def, fold Q'_def)
    fix i t assume "committed i t" with committed_in_order show "committedTo i" .

    from `committed i t` have [simp]: "v\<^sub>c' i = v\<^sub>c i"
      by (intro v\<^sub>c_eq, auto simp add: isCommitted_def)

    have "era\<^sub>i' i = era\<^sub>i i"
      by (simp add: \<open>committedTo i\<close> era\<^sub>i_eq)
    also have "era\<^sub>i i = era t"
      by (simp add: \<open>committed i t\<close> committed_era)
    finally show "era\<^sub>i' i = era t" .

    have Q'_eq: "Q' (era t) = Q (era t)"
      using Q_eq \<open>committedTo i\<close> \<open>era\<^sub>i i = era t\<close> by auto

    show "\<exists>q\<in>Q' (era t). \<forall>n\<in>q. accepted i n t"
      by (simp add: Q'_eq, intro committed `committed i t`)

  next
    fix i n t
    assume "promised i n t"
    with promised_era
    obtain j where "j \<le> i" "era t \<le> era\<^sub>i j" "committedTo j" by fastforce
    have "era\<^sub>i' j = era\<^sub>i j" by (simp add: \<open>committedTo j\<close> era\<^sub>i_eq)
    thus "\<exists>j\<le>i. era t \<le> era\<^sub>i' j \<and> committedTo j"
      using \<open>committedTo j\<close> \<open>era t \<le> era\<^sub>i j\<close> \<open>j \<le> i\<close> by auto

  next
    fix i t
    assume "proposed i t"
    from proposed [OF this]
    obtain q where q: "q \<in> Q (era t)" "\<And>n. n \<in> q \<Longrightarrow> promised i n t"
      "prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q))" by auto

    have "Q' (era t) = Q (era t)"
      by (metis IntE Q_eq Q_intersects `\<And>n. n \<in> q \<Longrightarrow> promised i n t` \<open>q \<in> Q (era t)\<close> all_not_in_conv intersects_def promised_era)

    show "\<exists>q\<in>Q' (era t). (\<forall>n\<in>q. promised i n t) \<and> (prevAccepted i t q = {} \<or> v' i t = v' i (maxTerm (prevAccepted i t q)))"
    proof (intro bexI conjI ballI `\<And>n. n \<in> q \<Longrightarrow> promised i n t` iffD1 [OF disj_commute, OF disjCI])
      from `q \<in> Q (era t)` `Q' (era t) = Q (era t)`
      show "q \<in> Q' (era t)" by simp

      assume bound: "prevAccepted i t q \<noteq> {}"
      hence [simp]: "v' i (maxTerm (prevAccepted i t q)) = v i (maxTerm (prevAccepted i t q))"
        by (simp add: v_prevAccepted_eq)

      have [simp]: "v' i t = v i t"
        using \<open>proposed i t\<close> not_already_proposed v'_def by auto

      show "v' i t = v' i (maxTerm (prevAccepted i t q))"
        using bound q by auto
    qed
  qed

  from promised\<^sub>m promised\<^sub>f promised\<^sub>b_lt promised\<^sub>b_accepted promised\<^sub>b_max
  show ?thesis
  proof (intro zen.zenI_simple [OF update_value],
      fold prevAccepted_def promised_def isCommitted_def, fold committedTo_def v\<^sub>c'_def,
      fold era\<^sub>i'_def reconfig'_def, fold Q'_def)

    fix i n t
    assume "promised i n t"
    from promised_era [OF this] obtain j where j: "j \<le> i" "era t \<le> era\<^sub>i j" "committedTo j" by auto
    have [simp]: "era\<^sub>i' j = era\<^sub>i j" by (simp add: era\<^sub>i_eq j)

    from j show "\<exists>j\<le>i. era t \<le> era\<^sub>i' j \<and> committedTo j" by auto

  next
    have "{(i, t). proposed' i t} = {(i, t). proposed i t} \<union> { (i\<^sub>0, t\<^sub>0) }"
      by (auto simp add: proposed'_def)
    with proposed_finite
    show "finite {(i, t). proposed' i t}" by auto

  next
    fix i n t assume "accepted i n t" thus "proposed' i t"
      using accepted proposed'_def by blast

  next
    fix i t assume "committed i t"

    have "Q' (era t) = Q (era t)"
      using Q_eq \<open>committed i t\<close> committed_era committed_in_order by fastforce

    with `committed i t` committed
    show "\<exists>q\<in>Q' (era t). \<forall>n\<in>q. accepted i n t" by auto

  next
    fix i t assume "proposed' i t"

    hence "proposed i t \<or> (i, t) = (i\<^sub>0, t\<^sub>0)" by (auto simp add: proposed'_def)
    thus "\<exists>q\<in>Q' (era t). (\<forall>n\<in>q. promised i n t) \<and> (prevAccepted i t q = {} \<or> v' i t = v' i (maxTerm (prevAccepted i t q)))"
    proof (elim disjE)
      assume p: "proposed i t"
      hence Q_eq: "Q' (era t) = Q (era t)"
        by (metis IntE Q_eq Q_intersects equals0I intersects_def promised_era proposed)

      from p have v_eq: "v' i t = v i t"
        using not_already_proposed v'_def by auto

      from p have v_eq2: "\<And>q. prevAccepted i t q = {} \<or> v' i (maxTerm (prevAccepted i t q)) = v i (maxTerm (prevAccepted i t q))"
        using v_prevAccepted_eq by auto

      from Q_eq v_eq v_eq2 proposed [OF `proposed i t`] show ?thesis by metis

    next
      assume "(i, t) = (i\<^sub>0, t\<^sub>0)"
      hence [simp]: "i = i\<^sub>0" "t = t\<^sub>0" by simp_all

      from q_quorum have "q \<noteq> {}"
        by (meson Int_emptyI Q_intersects equals0D intersects_def)
      then obtain n where "n \<in> q" by auto

      with q_promised have "promised i\<^sub>0 n t\<^sub>0" .
      from promised_era [OF this]
      obtain j where "j\<le>i\<^sub>0" "era t\<^sub>0 \<le> era\<^sub>i j" "committedTo j" by auto

      have Q_eq: "Q' (era t\<^sub>0) = Q (era t\<^sub>0)"
        using Q_eq \<open>committedTo j\<close> \<open>era t\<^sub>0 \<le> era\<^sub>i j\<close> by blast

      show ?thesis
        by (intro bexI [of _ q] conjI ballI, simp_all add: assms Q_eq)
    qed
  qed
qed

lemma (in zen)
  assumes "proposed i\<^sub>0 t\<^sub>0"
  assumes "\<And>t. promised i\<^sub>0 n\<^sub>0 t \<Longrightarrow> t \<preceq> t\<^sub>0"
  defines "accepted' i n t == accepted i n t \<or> (i, n, t) = (i\<^sub>0, n\<^sub>0, t\<^sub>0)"
  shows add_accepted: "zen Q\<^sub>0 v promised\<^sub>m promised\<^sub>f promised\<^sub>b proposed accepted' committed"
  using promised\<^sub>b_lt proposed_finite proposed
proof (intro zenI_simple)
  show "\<And>i j n t t'. promised\<^sub>m i n t \<Longrightarrow> t' \<prec> t \<Longrightarrow> i \<le> j \<Longrightarrow> \<not> accepted' j n t'"
    by (metis Pair_inject accepted'_def assms(2) promised\<^sub>m promised_def term_not_le_lt)
  show "\<And>i n t t'. promised\<^sub>f i n t \<Longrightarrow> t' \<prec> t \<Longrightarrow> \<not> accepted' i n t'"
    by (metis Pair_inject accepted'_def assms(2) promised\<^sub>f promised_def term_not_le_lt)
  show "\<And>i n t t'. promised\<^sub>b i n t t' \<Longrightarrow> accepted' i n t'"
    by (simp add: accepted'_def promised\<^sub>b_accepted)
  show "\<And>i n t t' t''. promised\<^sub>b i n t t' \<Longrightarrow> t' \<prec> t'' \<Longrightarrow> t'' \<prec> t \<Longrightarrow> \<not> accepted' i n t''"
    by (metis accepted'_def assms(2) prod.inject promised\<^sub>b_max promised_def term_not_le_lt)
  show "\<And>i n t. ((\<exists>j\<le>i. promised\<^sub>m j n t) \<or> promised\<^sub>f i n t) \<or> (\<exists>t'. promised\<^sub>b i n t t') \<Longrightarrow> \<exists>j\<le>i. era t \<le> era\<^sub>i j \<and> committedTo j"
    by (simp add: promised_def promised_era)
  show "\<And>i t. proposed i t \<Longrightarrow> \<exists>q\<in>Q (era t). (\<forall>n\<in>q. ((\<exists>j\<le>i. promised\<^sub>m j n t) \<or> promised\<^sub>f i n t) \<or> (\<exists>t'. promised\<^sub>b i n t t')) \<and> ({t'. \<exists>n\<in>q. promised\<^sub>b i n t t'} = {} \<or> v i t = v i (maxTerm {t'. \<exists>n\<in>q. promised\<^sub>b i n t t'}))"
    using prevAccepted_def promised_def proposed by auto
  show "\<And>i n t. accepted' i n t \<Longrightarrow> proposed i t"
    using accepted accepted'_def assms(1) by auto
  show "\<And>i t. committed i t \<Longrightarrow> \<exists>q\<in>Q (era t). \<forall>n\<in>q. accepted' i n t"
    by (meson accepted'_def committed)
qed

lemma (in zen)
  assumes committed_previous: "i\<^sub>0 > 0 \<Longrightarrow> isCommitted (i\<^sub>0 - 1)"
  assumes correct_era: "era\<^sub>i i\<^sub>0 = era t\<^sub>0"
  assumes q_accepted: "\<And>n. n \<in> q \<Longrightarrow> accepted i\<^sub>0 n t\<^sub>0"
  assumes q_quorum: "q \<in> Q (era t\<^sub>0)"
  defines "committed' i t == committed i t \<or> (i, t) = (i\<^sub>0, t\<^sub>0)"
  shows add_committed: "zen Q\<^sub>0 v promised\<^sub>m promised\<^sub>f promised\<^sub>b proposed accepted committed'"
proof -

  from committed_previous have committedTo: "committedTo i\<^sub>0"
    by (metis committedTo_def committed_committedTo_Suc diff_Suc_1 gr0_conv_Suc neq0_conv not_less_zero)

  note reconfig_def

  define isCommitted' where "\<And>i. isCommitted' i == \<exists>t. committed' i t"
  define committedTo' where "\<And>i. committedTo' i == \<forall>j < i. isCommitted' j"
  define v\<^sub>c' where "\<And>i. v\<^sub>c' i == v i (SOME t. committed' i t)"
  define era\<^sub>i' where "\<And>i. era\<^sub>i' i == card {j. j < i \<and> isReconfiguration (v\<^sub>c' j)}"
  define reconfig' where "\<And>e. reconfig' e \<equiv> THE i. isCommitted' i \<and> isReconfiguration (v\<^sub>c' i) \<and> era\<^sub>i' i = e"
  define Q' where "\<And>e. Q' e == if e = 0 then Q\<^sub>0 else newConfiguration (v\<^sub>c' (reconfig' (e-1)))"

  have isCommitted'_simp: "\<And>i. isCommitted' i = (isCommitted i \<or> i = i\<^sub>0)"
    using committed'_def isCommitted'_def isCommitted_def by auto
  have committedTo'_simp: "\<And>i. committedTo' i = (committedTo i \<or> i = Suc i\<^sub>0)"
    by (metis Suc_lessI isCommitted'_simp committedTo committedTo'_def committedTo_def
        committed_in_order isCommitted_def le_neq_implies_less lessI less_Suc_eq_le)

  have v\<^sub>c'_eq: "\<And>i. isCommitted i \<Longrightarrow> v\<^sub>c' i = v\<^sub>c i"
  proof -
    fix i assume i: "isCommitted i" thus "v\<^sub>c' i = v\<^sub>c i"
    proof (cases "i = i\<^sub>0")
      case False
      show ?thesis
        by (simp add: False committed'_def v\<^sub>c'_def v\<^sub>c_def)
    next
      case True
      from i obtain t where t: "committed i t" by (auto simp add: isCommitted_def)
      have "v\<^sub>c i\<^sub>0 = v i\<^sub>0 t"
        by (metis True consistent someI_ex t v\<^sub>c_def)

      moreover have "v\<^sub>c' i\<^sub>0 = v i\<^sub>0 t \<or> v\<^sub>c' i\<^sub>0 = v i\<^sub>0 t\<^sub>0"
        by (metis True v\<^sub>c'_def committed'_def consistent prod.sel(2) someI_ex t)

      moreover have "v i\<^sub>0 t\<^sub>0 = v i\<^sub>0 t"
      proof (rule oneSlot.consistent [OF oneSlot.commit [OF projects_to_oneSlot]])
        from i True show "isCommitted i\<^sub>0" by simp
        from q_quorum show "q \<in> (Q o era) t\<^sub>0" by simp
        from q_accepted show "\<And>n. n \<in> q \<Longrightarrow> accepted i\<^sub>0 n t\<^sub>0" .
        from t True show "committed i\<^sub>0 t \<or> t = t\<^sub>0" by simp
        show "committed i\<^sub>0 t\<^sub>0 \<or> t\<^sub>0 = t\<^sub>0" by simp
        show "\<And>t. proposed i\<^sub>0 t \<Longrightarrow> t\<^sub>0 \<preceq> t \<Longrightarrow> (Q \<circ> era) t \<frown> (Q \<circ> era) t\<^sub>0"
          using Q_intersects True \<open>isCommitted i\<^sub>0\<close> committed_era correct_era
            le_term_def lt_term_def oneSlot.Q_intersects projects_to_oneSlot t by fastforce
      qed

      ultimately show ?thesis by (simp add: True)
    qed
  qed

  have era\<^sub>i'_eq: "\<And>i. committedTo i \<Longrightarrow> era\<^sub>i' i = era\<^sub>i i"
    by (metis (mono_tags, lifting) Collect_cong committedTo_def era\<^sub>i'_def era\<^sub>i_def v\<^sub>c'_eq)

  have reconfig'_eq: "\<And>e i. committedTo i \<Longrightarrow> e < era\<^sub>i i \<Longrightarrow> reconfig' e = reconfig e"
  proof -
    fix e i
    assume a: "committedTo i" "e < era\<^sub>i i"

    define P where "\<And>i. P i == isCommitted' i \<and> isReconfiguration (v\<^sub>c' i) \<and> era\<^sub>i' i = e"
    have reconfig'_the: "reconfig' e = (THE i. P i)" by (simp add: P_def reconfig'_def)

    have "P (reconfig' e)"
    proof (unfold reconfig'_the, intro theI [of P])
      show "P (reconfig e)"
        by (metis P_def \<open>committedTo' \<equiv> \<lambda>i. \<forall>j<i. isCommitted' j\<close> a committedTo'_simp committed_committedTo era\<^sub>i'_eq reconfig_committed reconfig_era reconfig_isReconfiguration reconfig_lt v\<^sub>c'_eq)

      show "\<And>j. P j \<Longrightarrow> j = reconfig e"
        by (metis P_def a committedTo committedTo_def committed_committedTo era\<^sub>i'_eq era\<^sub>i_mono isCommitted'_simp leD not_le_imp_less reconfig_era reconfig_isReconfiguration unique_reconfiguration_in_era v\<^sub>c'_eq)
    qed

    show "?thesis e i"
      by (metis \<open>P (reconfig' e)\<close> \<open>P \<equiv> \<lambda>i. isCommitted' i \<and> isReconfiguration (v\<^sub>c' i) \<and> era\<^sub>i' i = e\<close> a committedTo committedTo_def committed_committedTo era\<^sub>i'_eq era\<^sub>i_mono isCommitted'_simp not_le reconfig_eq v\<^sub>c'_eq)
  qed

  have Q'_eq: "\<And>e i. committedTo i \<Longrightarrow> e \<le> era\<^sub>i i \<Longrightarrow> Q' e = Q e"
    using Q'_def Q_def reconfig'_eq reconfig_committed v\<^sub>c'_eq by auto

  show ?thesis
    apply (unfold_locales)
                apply (fold isCommitted'_def v\<^sub>c'_def promised_def prevAccepted_def)
                apply (fold committedTo'_def era\<^sub>i'_def reconfig'_def)
                apply (fold Q'_def)
    using Q\<^sub>0_intersects promised\<^sub>m promised\<^sub>f promised\<^sub>b_lt promised\<^sub>b_accepted promised\<^sub>b_max proposed_finite accepted
  proof -
    from committed_in_order committedTo
    show "\<And>i t. committed' i t \<Longrightarrow> committedTo' i"
      using committedTo'_simp isCommitted'_def isCommitted'_simp isCommitted_def by blast

    show "\<And>i n t. promised i n t \<Longrightarrow> \<exists>j\<le>i. era t \<le> era\<^sub>i' j \<and> committedTo' j"
      using committedTo'_simp era\<^sub>i'_eq promised_era by force

    show "\<And>i t. committed' i t \<Longrightarrow> era\<^sub>i' i = era t"
      using committed'_def committedTo committed_era committed_in_order correct_era era\<^sub>i'_eq by auto

    show "\<And>i t. committed' i t \<Longrightarrow> \<exists>q\<in>Q' (era t). \<forall>n\<in>q. accepted i n t"
      by (metis Q'_eq committed committed'_def committedTo committed_era committed_in_order correct_era order_refl prod.inject q_accepted q_quorum)

    show "\<And>i t. proposed i t \<Longrightarrow> \<exists>q\<in>Q' (era t). (\<forall>n\<in>q. promised i n t) \<and> (prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q)))"
      by (metis Q'_eq promised_era proposed proposed_promised)
  qed
qed

end
