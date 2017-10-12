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

datatype Value
  = NoOp
  | Reconfigure "Node set set"
  | SetClusterState ClusterState

fun isReconfiguration :: "Value \<Rightarrow> bool"
  where "isReconfiguration (Reconfigure _) = True"
  | "isReconfiguration _ = False"

fun newConfiguration :: "Value \<Rightarrow> Node set set"
  where "newConfiguration (Reconfigure nss) = nss"
  | "newConfiguration _ = (SOME _. False)"

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

assumes Q_intersects: "\<lbrakk> proposed t\<^sub>1; chosen t\<^sub>2 \<rbrakk> \<Longrightarrow> Q t\<^sub>1 \<frown> Q t\<^sub>2"
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
    by (meson Q_intersects intersects_def less.prems(1) q\<^sub>1_quorum q\<^sub>2_quorum)

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
  fixes v         :: "nat \<Rightarrow> Term \<Rightarrow> Value"

fixes promised\<^sub>m :: "nat \<Rightarrow> Node \<Rightarrow> Term \<Rightarrow> bool"
fixes promised\<^sub>f :: "nat \<Rightarrow> Node \<Rightarrow> Term \<Rightarrow> bool"
fixes promised\<^sub>b :: "nat \<Rightarrow> Node \<Rightarrow> Term \<Rightarrow> Term \<Rightarrow> bool"
fixes proposed  :: "nat \<Rightarrow> Term \<Rightarrow> bool"
fixes accepted  :: "nat \<Rightarrow> Node \<Rightarrow> Term \<Rightarrow> bool"
fixes committed :: "nat \<Rightarrow> Term \<Rightarrow> bool"
fixes Q\<^sub>0        :: "Node set set"

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
defines "promised i n t == (\<exists> j \<le> i. promised\<^sub>m j n t)
                            \<or> promised\<^sub>f i n t
                            \<or> (\<exists> t'. promised\<^sub>b i n t t')"

fixes prevAccepted :: "nat \<Rightarrow> Term \<Rightarrow> Node set \<Rightarrow> Term set"
defines "prevAccepted i t ns == {t'. \<exists> n \<in> ns. promised\<^sub>b i n t t'}"

assumes Q\<^sub>0_intersects: "Q\<^sub>0 \<frown> Q\<^sub>0"
assumes Q\<^sub>_intersects:  "\<lbrakk> proposed i t; isReconfiguration (v i t) \<rbrakk>
  \<Longrightarrow> newConfiguration (v i t) \<frown> newConfiguration (v i t)"

assumes Q\<^sub>0_nonempty: "q \<in> Q\<^sub>0 \<Longrightarrow> q \<noteq> {}"
assumes Q_nonempty: "\<lbrakk> proposed i t; isReconfiguration (v i t); q \<in> newConfiguration (v i t) \<rbrakk> \<Longrightarrow> q \<noteq> {}"

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

assumes committed:          "committed i t \<Longrightarrow> \<exists> q \<in> Q (era\<^sub>i i). \<forall> n \<in> q. accepted i n t"
assumes committed_era:      "committed i t \<Longrightarrow> era\<^sub>i i \<le> era t"
assumes committed_in_order: "committed i t \<Longrightarrow> committedTo i"
