theory Zen
  imports Main
begin

section \<open>Preliminaries\<close>

subsection \<open>Terms\<close>

datatype Era = e\<^sub>0 | nextEra Era

instantiation Era :: linorder
begin

fun less_Era :: "Era \<Rightarrow> Era \<Rightarrow> bool" where
    "less_Era    _ e\<^sub>0 = False"
  | "less_Era    e\<^sub>0 _ = True" 
  | "less_Era    (nextEra e\<^sub>1) (nextEra e\<^sub>2) = less_Era e\<^sub>1 e\<^sub>2"
definition less_eq_Era :: "Era \<Rightarrow> Era \<Rightarrow> bool" where
  "less_eq_Era e\<^sub>1 e\<^sub>2 == e\<^sub>1 < e\<^sub>2 \<or> e\<^sub>1 = e\<^sub>2"

instance proof
  fix e\<^sub>1 :: Era
  show "e\<^sub>1 \<le> e\<^sub>1" by (induct e\<^sub>1, auto simp add: less_eq_Era_def)

  fix e\<^sub>2
  show "(e\<^sub>1 < e\<^sub>2) = (e\<^sub>1 \<le> e\<^sub>2 \<and> \<not> e\<^sub>2 \<le> e\<^sub>1)"
    apply (induct e\<^sub>1 arbitrary: e\<^sub>2) 
    using less_eq_Era_def apply auto[1]
    by (metis less_Era.elims(2) less_Era.simps(3) less_eq_Era_def)

  show "e\<^sub>1 \<le> e\<^sub>2 \<or> e\<^sub>2 \<le> e\<^sub>1"
    apply (induct e\<^sub>1 arbitrary: e\<^sub>2)
    using less_Era.elims(3) less_eq_Era_def apply auto[1]
    by (metis less_Era.elims(3) less_Era.simps(3) less_eq_Era_def)

  show "e\<^sub>1 \<le> e\<^sub>2 \<Longrightarrow> e\<^sub>2 \<le> e\<^sub>1 \<Longrightarrow> e\<^sub>1 = e\<^sub>2"
    apply (induct e\<^sub>1 arbitrary: e\<^sub>2)
     apply (simp add: less_eq_Era_def)
    by (metis less_Era.elims(2) less_Era.simps(3) less_eq_Era_def)

  fix e\<^sub>3
  show "e\<^sub>1 \<le> e\<^sub>2 \<Longrightarrow> e\<^sub>2 \<le> e\<^sub>3 \<Longrightarrow> e\<^sub>1 \<le> e\<^sub>3"
    apply (induct e\<^sub>1 arbitrary: e\<^sub>2 e\<^sub>3) 
    using less_Era.elims(3) less_eq_Era_def apply auto[1]
    by (smt Era.exhaust less_Era.elims(2) less_Era.simps(3) less_eq_Era_def)
qed
end

fun natOfEra :: "Era \<Rightarrow> nat" where
  "natOfEra e\<^sub>0 = 0" | "natOfEra (nextEra e) = Suc (natOfEra e)"

lemma natOfEra_le[simp]: "(natOfEra e\<^sub>1 \<le> natOfEra e\<^sub>2) = (e\<^sub>1 \<le> e\<^sub>2)"
  apply (induct e\<^sub>1 arbitrary: e\<^sub>2, simp add: leI)
  by (metis (no_types, lifting) Suc_le_mono less_Era.elims(3) less_Era.simps(3) less_irrefl natOfEra.simps(1) natOfEra.simps(2) not_less zero_less_Suc)

lemma natOfEra_eq[simp]: "(natOfEra e\<^sub>1 = natOfEra e\<^sub>2) = (e\<^sub>1 = e\<^sub>2)"
  by (simp add: eq_iff)

lemma natOfEra_lt[simp]: "(natOfEra e\<^sub>1 < natOfEra e\<^sub>2) = (e\<^sub>1 < e\<^sub>2)"
  by (meson natOfEra_le not_less)

fun eraOfNat :: "nat \<Rightarrow> Era" where
  "eraOfNat 0 = e\<^sub>0" | "eraOfNat (Suc n) = nextEra (eraOfNat n)"

lemma eraOfNat_inv[simp]: "eraOfNat (natOfEra e) = e" by (induct e, simp_all)
lemma natOfEra_inv[simp]: "natOfEra (eraOfNat n) = n" by (induct n, simp_all)

lemma eraOfNat_le[simp]: "(eraOfNat n\<^sub>1 \<le> eraOfNat n\<^sub>2) = (n\<^sub>1 \<le> n\<^sub>2)" by (metis natOfEra_inv natOfEra_le)
lemma eraOfNat_lt[simp]: "(eraOfNat n\<^sub>1 < eraOfNat n\<^sub>2) = (n\<^sub>1 < n\<^sub>2)" by (metis natOfEra_inv natOfEra_lt)
lemma eraOfNat_eq[simp]: "(eraOfNat n\<^sub>1 = eraOfNat n\<^sub>2) = (n\<^sub>1 = n\<^sub>2)" by (metis natOfEra_inv)

lemma e0_le[simp]: "e\<^sub>0 \<le> e" by (simp add: leI)
lemma le_e0[simp]: "e \<le> e\<^sub>0 = (e = e\<^sub>0)" by (simp add: eq_iff)


datatype Term = Term Era nat

fun era\<^sub>t :: "Term \<Rightarrow> Era" where "era\<^sub>t (Term e _) = e"
fun termInEra :: "Term \<Rightarrow> nat" where "termInEra (Term _ n) = n"

definition lt_term :: "Term \<Rightarrow> Term \<Rightarrow> bool" (infixl "\<prec>" 50)
  where "t\<^sub>1 \<prec> t\<^sub>2 = (era\<^sub>t t\<^sub>1 < era\<^sub>t t\<^sub>2 \<or> (era\<^sub>t t\<^sub>1 = era\<^sub>t t\<^sub>2 \<and> termInEra t\<^sub>1 < termInEra t\<^sub>2))"

definition le_term :: "Term \<Rightarrow> Term \<Rightarrow> bool" (infixl "\<preceq>" 50)
  where "t\<^sub>1 \<preceq> t\<^sub>2 = (t\<^sub>1 \<prec> t\<^sub>2 \<or> t\<^sub>1 = t\<^sub>2)"

lemma term_le_refl[simp]: "t \<preceq> t" by (simp add: le_term_def)

lemma term_lt_lt_trans[trans]:  "\<lbrakk> t\<^sub>1 \<prec> t\<^sub>2; t\<^sub>2 \<prec> t\<^sub>3 \<rbrakk> \<Longrightarrow> t\<^sub>1 \<prec> t\<^sub>3"
  by (smt Term.inject less_trans lt_term_def)

lemma term_lt_le_trans[trans]:  "\<lbrakk> t\<^sub>1 \<prec> t\<^sub>2; t\<^sub>2 \<preceq> t\<^sub>3 \<rbrakk> \<Longrightarrow> t\<^sub>1 \<prec> t\<^sub>3"
  by (metis le_term_def term_lt_lt_trans)

lemma term_le_lt_trans[trans]:  "\<lbrakk> t\<^sub>1 \<preceq> t\<^sub>2; t\<^sub>2 \<prec> t\<^sub>3 \<rbrakk> \<Longrightarrow> t\<^sub>1 \<prec> t\<^sub>3" using term_lt_lt_trans le_term_def by auto
lemma term_le_le_trans[trans]:  "\<lbrakk> t\<^sub>1 \<preceq> t\<^sub>2; t\<^sub>2 \<preceq> t\<^sub>3 \<rbrakk> \<Longrightarrow> t\<^sub>1 \<preceq> t\<^sub>3" using term_lt_lt_trans le_term_def by auto

lemma era\<^sub>t_mono: "t\<^sub>1 \<preceq> t\<^sub>2 \<Longrightarrow> era\<^sub>t t\<^sub>1 \<le> era\<^sub>t t\<^sub>2" using le_term_def lt_term_def by auto

lemma term_lt_le: "t\<^sub>1 \<prec> t\<^sub>2 \<Longrightarrow> t\<^sub>1 \<preceq> t\<^sub>2" using le_term_def by auto

lemma term_not_le_lt[simp]: "(\<not> (t\<^sub>1 \<preceq> t\<^sub>2)) = (t\<^sub>2 \<prec> t\<^sub>1)"
  by (metis Term.exhaust era\<^sub>t.simps le_term_def lt_term_def not_less_iff_gr_or_eq termInEra.simps)

lemma term_lt_wf: "wf { (t\<^sub>1, t\<^sub>2). t\<^sub>1 \<prec> t\<^sub>2 }"
proof -
  have "{ (t\<^sub>1, t\<^sub>2). t\<^sub>1 \<prec> t\<^sub>2 } = measures [natOfEra \<circ> era\<^sub>t, termInEra]"
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

subsection \<open>Nodes and quorums\<close>

datatype Node = Node nat

definition intersects :: "'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" (infixl "\<frown>" 50)
  where "A \<frown> B \<equiv> \<forall> a \<in> A. \<forall> b \<in> B. a \<inter> b \<noteq> {}"

typedef Configuration = "{Q :: Node set set. Q \<frown> Q}"
proof (intro exI CollectI)
  show "{} \<frown> {}"
    by (simp add: intersects_def)
qed

definition Q\<^sub>0 :: "Node set set" where "Q\<^sub>0 \<equiv> SOME Q. Q \<frown> Q"

lemma Q\<^sub>0_intersects: "Q\<^sub>0 \<frown> Q\<^sub>0"
  by (metis Collect_empty_eq Q\<^sub>0_def Rep_Configuration empty_iff some_eq_ex)

subsection \<open>Values\<close>

datatype ClusterState = ClusterState nat

datatype Value
  = NoOp
  | Reconfigure Configuration
  | SetClusterState ClusterState

fun isReconfiguration :: "Value \<Rightarrow> bool"
  where "isReconfiguration (Reconfigure _) = True"
  | "isReconfiguration _ = False"

fun getConf :: "Value \<Rightarrow> Node set set"
  where "getConf (Reconfigure conf) = Rep_Configuration conf"
  | "getConf _                      = Rep_Configuration (SOME _. False)"

lemma getConf_intersects: "getConf v \<frown> getConf v"
  by (metis (no_types, lifting) Rep_Configuration getConf.elims mem_Collect_eq)

definition reconfigure :: "Node set set \<Rightarrow> Value"
  where "reconfigure Q = Reconfigure (Abs_Configuration Q)"

lemma getConf_reconfigure: "Q \<frown> Q \<Longrightarrow> getConf (reconfigure Q) = Q"
  by (simp add: Abs_Configuration_inverse reconfigure_def)

lemma reconfigure_isReconfiguration: "isReconfiguration (reconfigure Q)"
  by (simp add: reconfigure_def)

subsection \<open>One-slot consistency\<close>

locale oneSlot =
  fixes Q :: "Term \<Rightarrow> Node set set"
  fixes v :: "Term \<Rightarrow> Value"
  
  fixes promised\<^sub>f :: "Node \<Rightarrow> Term \<Rightarrow> bool"
  fixes promised\<^sub>b :: "Node \<Rightarrow> Term \<Rightarrow> Term \<Rightarrow> bool"
  fixes proposed :: "Term \<Rightarrow> bool"
  fixes accepted :: "Node \<Rightarrow> Term \<Rightarrow> bool"
  fixes committed :: "Term \<Rightarrow> bool"
  
  fixes promised :: "Node \<Rightarrow> Term \<Rightarrow> bool"
  defines "promised n t \<equiv> promised\<^sub>f n t \<or> (\<exists> t'. promised\<^sub>b n t t')"
  
  fixes prevAccepted :: "Term \<Rightarrow> Node set \<Rightarrow> Term set"
  defines "prevAccepted t ns \<equiv> {t'. \<exists> n \<in> ns. promised\<^sub>b n t t'}"
  
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
  assumes "proposed t\<^sub>1" and "committed t\<^sub>2" and "t\<^sub>2 \<prec> t\<^sub>1"
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
  assumes "committed t\<^sub>1" and "committed t\<^sub>2"
  shows "v t\<^sub>1 = v t\<^sub>2"
  by (metis Q_nonempty accepted all_not_in_conv assms committed le_term_def p2b term_not_le_lt)

lemma (in oneSlot) commit:
  assumes q_quorum: "q \<in> Q t\<^sub>0"
  assumes q_accepted: "\<And>n. n \<in> q \<Longrightarrow> accepted n t\<^sub>0"
  assumes intersects: "\<And>t. proposed t \<Longrightarrow> t\<^sub>0 \<preceq> t \<Longrightarrow> Q t \<frown> Q t\<^sub>0"
  defines "committed' t \<equiv> committed t \<or> t = t\<^sub>0"
  shows "oneSlot Q v promised\<^sub>f promised\<^sub>b proposed accepted committed'"
  by (smt committed'_def intersects oneSlot_axioms oneSlot_def q_accepted q_quorum)

subsection \<open>Paxos: multi-slot consistency\<close>

locale paxos =
  fixes v         :: "nat \<Rightarrow> Term \<Rightarrow> Value"
  
  fixes promised\<^sub>m :: "nat \<Rightarrow> Node \<Rightarrow> Term \<Rightarrow> bool"
  fixes promised\<^sub>f :: "nat \<Rightarrow> Node \<Rightarrow> Term \<Rightarrow> bool"
  fixes promised\<^sub>b :: "nat \<Rightarrow> Node \<Rightarrow> Term \<Rightarrow> Term \<Rightarrow> bool"
  fixes proposed  :: "nat \<Rightarrow> Term \<Rightarrow> bool"
  fixes accepted  :: "nat \<Rightarrow> Node \<Rightarrow> Term \<Rightarrow> bool"
  fixes committed :: "nat \<Rightarrow> Term \<Rightarrow> bool"
  
  fixes isCommitted :: "nat \<Rightarrow> bool"
  defines "isCommitted i \<equiv> \<exists> t. committed i t"
  
  fixes committedTo :: "nat \<Rightarrow> bool" ("committed\<^sub><")
  defines "committed\<^sub>< i \<equiv> \<forall> j < i. isCommitted j" 
  
  fixes v\<^sub>c :: "nat \<Rightarrow> Value"
  defines "v\<^sub>c i \<equiv> v i (SOME t. committed i t)"
  
  fixes era\<^sub>i :: "nat \<Rightarrow> Era"
  defines "era\<^sub>i i \<equiv> eraOfNat (card { j. j < i \<and> isReconfiguration (v\<^sub>c j) })"
  
  fixes reconfig :: "Era \<Rightarrow> nat"
  defines "reconfig e \<equiv> THE i. isCommitted i \<and> isReconfiguration (v\<^sub>c i) \<and> era\<^sub>i i = e"
  
  fixes Q :: "Era \<Rightarrow> Node set set"
  defines "Q e \<equiv> case e of e\<^sub>0 \<Rightarrow> Q\<^sub>0 | nextEra e' \<Rightarrow> getConf (v\<^sub>c (reconfig e'))"
  
  fixes promised :: "nat \<Rightarrow> Node \<Rightarrow> Term \<Rightarrow> bool"
  defines "promised i n t \<equiv> ((\<exists> j \<le> i. promised\<^sub>m j n t)
                              \<or> promised\<^sub>f i n t)
                              \<or> (\<exists> t'. promised\<^sub>b i n t t')"
  
  fixes prevAccepted :: "nat \<Rightarrow> Term \<Rightarrow> Node set \<Rightarrow> Term set"
  defines "prevAccepted i t ns \<equiv> {t'. \<exists> n \<in> ns. promised\<^sub>b i n t t'}"
  
  assumes promised\<^sub>m: "\<lbrakk> promised\<^sub>m i n t; t' \<prec> t; i \<le> j \<rbrakk> \<Longrightarrow> \<not> accepted j n t'"
  
  assumes promised\<^sub>f: "\<lbrakk> promised\<^sub>f i n t; t' \<prec> t \<rbrakk> \<Longrightarrow> \<not> accepted i n t'"
  
  assumes promised\<^sub>b_lt:       "promised\<^sub>b i n t t' \<Longrightarrow> t' \<prec> t"
  assumes promised\<^sub>b_accepted: "promised\<^sub>b i n t t' \<Longrightarrow> accepted i n t'"
  assumes promised\<^sub>b_max:    "\<lbrakk> promised\<^sub>b i n t t'; t' \<prec> t''; t'' \<prec> t \<rbrakk> \<Longrightarrow> \<not> accepted i n t''"
  
  assumes promised_era: "promised i n t \<Longrightarrow> \<exists> j \<le> i. era\<^sub>t t \<le> era\<^sub>i j \<and> committed\<^sub>< j"
  
  assumes proposed: "proposed i t \<Longrightarrow> \<exists> q \<in> Q (era\<^sub>t t). (\<forall> n \<in> q. promised i n t)
                                             \<and> (prevAccepted i t q = {}
                                                  \<or> v i t = v i (maxTerm (prevAccepted i t q)))"
  
  assumes proposed_finite: "finite {(i, t). proposed i t}"
  
  assumes accepted: "accepted i n t \<Longrightarrow> proposed i t"
  
  assumes committed:          "committed i t \<Longrightarrow> \<exists> q \<in> Q (era\<^sub>t t). \<forall> n \<in> q. accepted i n t"
  assumes committed_era:      "committed i t \<Longrightarrow> era\<^sub>i i = era\<^sub>t t"
  assumes committed_in_order: "committed i t \<Longrightarrow> committed\<^sub>< i"

lemma (in paxos)
  shows Q_intersects: "Q e \<frown> Q e"
proof (cases e)
  case e\<^sub>0 thus ?thesis by (simp add: Q\<^sub>0_intersects Q_def)
next
  case nextEra

  from Rep_Configuration
  have [simp]: "\<And>ns. Rep_Configuration ns \<frown> Rep_Configuration ns"
    by simp

  hence [simp]: "\<And>va. getConf va \<frown> getConf va"
    by (metis getConf.elims)

  show ?thesis by (simp add: nextEra Q_def)
qed

lemma (in paxos)
  assumes "isCommitted i"
  shows projects_to_oneSlot:
    "oneSlot (Q o era\<^sub>t) (v i) (\<lambda> n t. (\<exists>j \<le> i. promised\<^sub>m j n t) \<or> promised\<^sub>f i n t)
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
  show "\<exists>q\<in>(Q \<circ> era\<^sub>t) t. (\<forall>n\<in>q. promised i n t) \<and> (prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q)))" by simp
next
  fix q t
  assume "q \<in> (Q \<circ> era\<^sub>t) t"
  with Q_intersects [of "era\<^sub>t t"]
  show "q \<noteq> {}" by (auto simp add: intersects_def)
next
  fix t\<^sub>2
  assume t2: "committed i t\<^sub>2"
  from committed [OF this]
  show "\<exists>q\<in>(Q \<circ> era\<^sub>t) t\<^sub>2. \<forall>n\<in>q. accepted i n t\<^sub>2" by simp

  fix t\<^sub>1
  assume t1: "proposed i t\<^sub>1" and t21: "t\<^sub>2 \<preceq> t\<^sub>1"
  hence "era\<^sub>t t\<^sub>2 \<le> era\<^sub>t t\<^sub>1" using era\<^sub>t_mono by blast

  moreover from proposed [OF t1]
  obtain q\<^sub>1 where q\<^sub>1: "q\<^sub>1 \<in> Q (era\<^sub>t t\<^sub>1)" "\<And> n. n \<in> q\<^sub>1 \<Longrightarrow> promised i n t\<^sub>1" by auto
  with Q_intersects [of "era\<^sub>t t\<^sub>1"] obtain n where "n \<in> q\<^sub>1"
    by (meson IntE all_not_in_conv intersects_def)

  with q\<^sub>1 have "promised i n t\<^sub>1" by simp
  from promised_era [OF this]
  obtain j where ji: "j \<le> i" and "era\<^sub>t t\<^sub>1 \<le> era\<^sub>i j" by auto

  moreover
  from ji have "era\<^sub>i j \<le> era\<^sub>i i"
    by (unfold era\<^sub>i_def, simp, intro card_mono, auto)

  moreover from t2 committed_era have "era\<^sub>i i = era\<^sub>t t\<^sub>2" by simp

  ultimately show "(Q \<circ> era\<^sub>t) t\<^sub>1 \<frown> (Q \<circ> era\<^sub>t) t\<^sub>2"
    using Q_intersects order_trans by fastforce
qed

lemma Collect_pair_False[simp]:  "{(i, t). False} = {}" by auto

lemma (in paxos)
  fixes promised\<^sub>m' promised\<^sub>f' promised\<^sub>b'
  
  fixes promised' :: "nat \<Rightarrow> Node \<Rightarrow> Term \<Rightarrow> bool"
  defines "promised' i n t \<equiv> ((\<exists> j \<le> i. promised\<^sub>m' j n t)
                              \<or> promised\<^sub>f' i n t)
                              \<or> (\<exists> t'. promised\<^sub>b' i n t t')"
  
  fixes prevAccepted' :: "nat \<Rightarrow> Term \<Rightarrow> Node set \<Rightarrow> Term set"
  defines "prevAccepted' i t ns \<equiv> {t'. \<exists> n \<in> ns. promised\<^sub>b' i n t t'}"
  
  assumes "\<And>i j n t t'. \<lbrakk> promised\<^sub>m' i n t; t' \<prec> t; i \<le> j \<rbrakk> \<Longrightarrow> \<not> accepted' j n t'"
  
  assumes "\<And>i n t t'. \<lbrakk> promised\<^sub>f' i n t; t' \<prec> t \<rbrakk> \<Longrightarrow> \<not> accepted' i n t'"
  
  assumes  "\<And>i n t t'. promised\<^sub>b' i n t t' \<Longrightarrow> t' \<prec> t"
  assumes  "\<And>i n t t'. promised\<^sub>b' i n t t' \<Longrightarrow> accepted' i n t'"
  assumes  "\<And>i n t t' t''. \<lbrakk> promised\<^sub>b' i n t t'; t' \<prec> t''; t'' \<prec> t \<rbrakk> \<Longrightarrow> \<not> accepted' i n t''"
  
  assumes "\<And>i n t. promised' i n t \<Longrightarrow> \<exists> j \<le> i. era\<^sub>t t \<le> era\<^sub>i j \<and> committed\<^sub>< j"
  
  assumes "\<And>i t. proposed' i t \<Longrightarrow> \<exists> q \<in> Q (era\<^sub>t t). (\<forall> n \<in> q. promised' i n t)
                                                   \<and> (prevAccepted' i t q = {}
                                                       \<or> v i t = v i (maxTerm (prevAccepted' i t q)))"
  
  assumes "finite {(i, t). proposed' i t}"
  
  assumes "\<And>i n t. accepted' i n t \<Longrightarrow> proposed' i t"
  
  assumes "\<And>i t. committed i t \<Longrightarrow> \<exists> q \<in> Q (era\<^sub>t t). \<forall> n \<in> q. accepted' i n t"
  
  shows paxosI_simple:
    "paxos v promised\<^sub>m' promised\<^sub>f' promised\<^sub>b' proposed' accepted' committed"
  using assms committed_era committed_in_order
  by (unfold_locales, fold promised'_def prevAccepted'_def era\<^sub>i_def isCommitted_def v\<^sub>c_def, fold committedTo_def era\<^sub>i_def reconfig_def, fold Q_def)

lemma (in paxos) committed_accepted:
  assumes "committed i t"
  obtains n where "accepted i n t"
  using assms committed isCommitted_def oneSlot.Q_nonempty projects_to_oneSlot by fastforce

lemma (in paxos)
  assumes "committed i t"
  shows committed_proposed: "proposed i t"
  by (meson Int_emptyI Q_intersects accepted assms committed intersects_def)

lemma (in paxos) proposed_promised:
  assumes "proposed i t"
  obtains n where "promised i n t"
  by (meson Int_emptyI Q_intersects assms intersects_def proposed)

lemma (in paxos) committed_promised:
  assumes "committed i t"
  obtains n where "promised i n t"
  using assms committed_proposed proposed_promised by blast

lemma (in paxos) era\<^sub>i_Suc_eq:
  assumes "\<not> isReconfiguration (v\<^sub>c i)"
  shows "era\<^sub>i (Suc i) = era\<^sub>i i"
  by (metis (no_types, lifting) Collect_cong assms era\<^sub>i_def less_Suc_eq)

lemma (in paxos) era\<^sub>i_Suc_Suc:
  assumes "isReconfiguration (v\<^sub>c i)"
  shows "era\<^sub>i (Suc i) = nextEra (era\<^sub>i i)"
proof -
  have "{j. j < Suc i \<and> isReconfiguration (v\<^sub>c j)} = insert i {j. j < i \<and> isReconfiguration (v\<^sub>c j)}"
    using assms by auto
  thus ?thesis by (simp add: era\<^sub>i_def)
qed

lemma (in paxos) era\<^sub>i_Suc:
  shows "era\<^sub>i (Suc i) = (if isReconfiguration (v\<^sub>c i) then nextEra (era\<^sub>i i) else era\<^sub>i i)"
  by (simp add: era\<^sub>i_Suc_Suc era\<^sub>i_Suc_eq)

lemma (in paxos) era\<^sub>i_mono:
  shows "j \<le> i \<Longrightarrow> era\<^sub>i j \<le> era\<^sub>i i"
  by (induct i, simp, metis era\<^sub>i_Suc le_SucE le_SucI natOfEra.simps(2) natOfEra_le order_refl)

lemma (in paxos)
  assumes "j < i" and "isReconfiguration (v\<^sub>c j)" and "isCommitted i"
  shows era_increases_on_reconfiguration: "era\<^sub>i j < era\<^sub>i i"
  using assms
  by (metis Suc_leI Suc_le_lessD era\<^sub>i_Suc era\<^sub>i_mono natOfEra.simps(2) natOfEra_le natOfEra_lt)

lemma (in paxos)
  assumes "era\<^sub>i i = era\<^sub>i j"
  assumes "isCommitted i"
  assumes "isCommitted j"
  assumes "isReconfiguration (v\<^sub>c i)"
  assumes "isReconfiguration (v\<^sub>c j)"
  shows unique_reconfiguration_in_era: "i = j"
  using assms
  by (metis era_increases_on_reconfiguration less_irrefl nat_neq_iff)

lemma (in paxos) committedTo_mono: "j \<le> i \<Longrightarrow> committed\<^sub>< i \<Longrightarrow> committed\<^sub>< j"
  using committedTo_def by auto

lemma (in paxos) committed_committedTo_Suc: "isCommitted i \<Longrightarrow> committed\<^sub>< (Suc i)"
  using committedTo_def committed_in_order isCommitted_def less_Suc_eq by auto

lemma (in paxos) committed_committedTo: "isCommitted i \<Longrightarrow> committed\<^sub>< i"
  using committed_in_order isCommitted_def by auto

lemma (in paxos)
  assumes "committed\<^sub>< i"
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
      by (metis committedTo_def committed_committedTo eraOfNat_inv era\<^sub>i_Suc lessI less_antisym natOfEra.simps(2) natOfEra_lt)
  qed (simp add: era\<^sub>i_def)
  then obtain j where j: "isCommitted j" "isReconfiguration (v\<^sub>c j)" "era\<^sub>i j = e" by auto

  define P where "\<And>i. P i \<equiv> isCommitted i \<and> isReconfiguration (v\<^sub>c i) \<and> era\<^sub>i i = e"
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

lemma (in paxos)
  assumes "committed\<^sub>< i" and "e < era\<^sub>i i" and "isReconfiguration (v\<^sub>c j)" and "era\<^sub>i j = e"
  shows reconfig_eq: "j = reconfig e"
  using assms
  by (metis committedTo_def era\<^sub>i_mono leD leI reconfig_era reconfig_isReconfiguration unique_reconfiguration_in_era)

lemma (in paxos)
  finite_prevAccepted: "finite (prevAccepted i t q)"
proof -
  have "prevAccepted i t q \<subseteq> { t'. \<exists> n. \<exists> i. promised\<^sub>b i n t t' }" using prevAccepted_def by auto
  also have "... \<subseteq> { t'. \<exists> n. \<exists> i. accepted i n t' }" using promised\<^sub>b_accepted by fastforce
  also have "... \<subseteq> { t'. \<exists> i. proposed i t' }" using accepted by fastforce
  also have "... \<subseteq> snd ` { (i, t). proposed i t }" by force
  finally show ?thesis using finite_surj proposed_finite by auto
qed

section \<open>Important facts\<close>

subsection \<open>Definitions\<close>

text \<open>The @{term promised} predicate means any of the three kinds of promises has been sent:\<close>

lemma (in paxos) "promised i n t \<equiv>
                                 (\<exists>j\<le>i. promised\<^sub>m j n t)
                                  \<or> promised\<^sub>f i n t
                                  \<or> (\<exists>t'. promised\<^sub>b i n t t')"
  by (auto simp add: promised_def)

text \<open>The @{term prevAccepted} function gives the set of previously-accepted terms from received @{term promised\<^sub>b} messages:\<close>

lemma (in paxos) "prevAccepted i t q \<equiv> {t'. \<exists> n \<in> q. promised\<^sub>b i n t t'}"
  using prevAccepted_def by simp

text \<open>The @{term maxTerm} function finds the largest term in a set:\<close>

lemma "maxTerm S \<equiv> THE t. t \<in> S \<and> (\<forall>t' \<in> S. t' \<preceq> t)" using maxTerm_def by simp

text \<open>This predicate says that all strictly-earlier slots are committed:\<close>

lemma (in paxos) "committed\<^sub>< i \<equiv> \<forall> j < i. \<exists> t. committed j t"
  by (simp add: committedTo_def isCommitted_def)

text \<open>The @{term v\<^sub>c} function gives the value committed in each slot (and is arbitrary for uncommitted slots):\<close>

lemma (in paxos) "committed i t \<Longrightarrow> v\<^sub>c i = v i t"
  by (metis (mono_tags, lifting) isCommitted_def oneSlot.consistent projects_to_oneSlot someI_ex v\<^sub>c_def)

text \<open>The configuration of the first era is the constant @{term Q\<^sub>0}:\<close>

lemma (in paxos) "era\<^sub>i 0 = e\<^sub>0" and "Q e\<^sub>0 = Q\<^sub>0" by (simp_all add: Q_def era\<^sub>i_def)

text \<open>Each committed reconfiguration defines the configuration of the next slot and therefore all other slots in the same era:\<close>

lemma (in paxos)
  assumes "committed i t" and "v\<^sub>c i = reconfigure Q'" and "Q' \<frown> Q'"
  shows "era\<^sub>i (i + 1) \<equiv> nextEra (era\<^sub>i i)" and "Q (era\<^sub>i (i + 1)) \<equiv> Q'"
proof -
  show h1: "era\<^sub>i (i + 1) \<equiv> nextEra (era\<^sub>i i)"
    by (simp add: assms(2) era\<^sub>i_Suc_Suc reconfigure_isReconfiguration)

  hence "Q (era\<^sub>i (i + 1)) = getConf (v\<^sub>c (reconfig (era\<^sub>i i)))"
    by (simp add: Q_def)
  also from h1 assms have "... = Q'"
    by (metis Suc_eq_plus1_left add.commute committed_committedTo_Suc getConf_reconfigure isCommitted_def lessI natOfEra.simps(2) natOfEra_lt reconfig_eq reconfigure_isReconfiguration)
  finally show "Q (era\<^sub>i (i + 1)) \<equiv> Q'" by simp
qed
 
subsection \<open>Safety\<close>

lemma (in paxos) consistent:
  assumes "committed i t\<^sub>1" and "committed i t\<^sub>2"
  shows "v i t\<^sub>1 = v i t\<^sub>2"
  using assms
  by (intro oneSlot.consistent [OF projects_to_oneSlot], auto simp add: isCommitted_def)

subsection \<open>Preserving invariants\<close>

subsubsection \<open>Starting point\<close>

text \<open>If no messages have been sent then the invariants hold:\<close>

lemma
  assumes "\<And>i n t. \<not> promised\<^sub>m i n t"
  assumes "\<And>i n t. \<not> promised\<^sub>f i n t"
  assumes "\<And>i n t t'. \<not> promised\<^sub>b i n t t'"
  assumes "\<And>i t. \<not> proposed i t"
  assumes "\<And>i n t. \<not> accepted i n t"
  assumes "\<And>i t. \<not> committed i t"
  shows "paxos v promised\<^sub>m promised\<^sub>f promised\<^sub>b proposed accepted committed"
  using assms by (unfold_locales, auto)

subsubsection \<open>Promises\<close>

text \<open>A @{term promised\<^sub>m} message can be sent if nothing has been accepted for this slot and for any
later slot, and the configuration of the era of its term is known:\<close>

lemma (in paxos) send_promised\<^sub>m:
  assumes "\<And>t j. i\<^sub>0 \<le> j \<Longrightarrow> \<not> accepted j n\<^sub>0 t"
  assumes "\<exists> j \<le> i\<^sub>0. era\<^sub>t t\<^sub>0 \<le> era\<^sub>i j \<and> committed\<^sub>< j"
  defines "promised\<^sub>m' i n t \<equiv> promised\<^sub>m i n t \<or> (i, n, t) = (i\<^sub>0, n\<^sub>0, t\<^sub>0)"
  shows "paxos v promised\<^sub>m' promised\<^sub>f promised\<^sub>b proposed accepted committed"
  using promised\<^sub>f promised\<^sub>b_accepted promised\<^sub>b_lt promised\<^sub>b_max proposed_finite accepted committed
proof (intro paxosI_simple, fold prevAccepted_def)
  fix i j n t t'
  assume p: "promised\<^sub>m' i n t" "t' \<prec> t" "i \<le> j"
  hence "promised\<^sub>m i n t \<or> (i, n, t) = (i\<^sub>0, n\<^sub>0, t\<^sub>0)"
    by (auto simp add: promised\<^sub>m'_def)
  thus "\<not> accepted j n t'"
  proof (elim disjE)
    assume "promised\<^sub>m i n t" with promised\<^sub>m p show ?thesis by simp
  next
    assume "(i, n, t) = (i\<^sub>0, n\<^sub>0, t\<^sub>0)"
    with p assms show ?thesis by simp
  qed
next
  fix i n t
  assume "((\<exists>j\<le>i. promised\<^sub>m' j n t) \<or> promised\<^sub>f i n t) \<or> (\<exists>t'. promised\<^sub>b i n t t')"
  hence "(i\<^sub>0 \<le> i \<and> (n, t) = (n\<^sub>0, t\<^sub>0)) \<or> promised i n t"
    by (auto simp add: promised\<^sub>m'_def promised_def)
  thus "\<exists>j\<le>i. era\<^sub>t t \<le> era\<^sub>i j \<and> committed\<^sub>< j"
  proof (elim disjE)
    assume "promised i n t" with promised_era show ?thesis by simp
  next
    assume "i\<^sub>0 \<le> i \<and> (n, t) = (n\<^sub>0, t\<^sub>0)"
    with assms(2) show ?thesis using order_trans by auto
  qed
next
  fix i t
  assume "proposed i t"
  from proposed [OF this]
  obtain q where q: "q\<in>Q (era\<^sub>t t)" "\<forall>n\<in>q. promised i n t" "prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q))" by auto

  from q
  show "\<exists>q\<in>Q (era\<^sub>t t). (\<forall>n\<in>q. ((\<exists>j\<le>i. promised\<^sub>m' j n t) \<or> promised\<^sub>f i n t) \<or> (\<exists>t'. promised\<^sub>b i n t t')) \<and> (prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q)))"
    by (intro bexI [of _ q], auto simp add: q promised\<^sub>m'_def promised_def)
qed

text \<open>A @{term promised\<^sub>f} message can be sent if nothing has been accepted for this slot,
and the configuration of the era of its term is known:\<close>

lemma (in paxos) send_promised\<^sub>f:
  assumes "\<And>t. \<not> accepted i\<^sub>0 n\<^sub>0 t"
  assumes "\<exists> j \<le> i\<^sub>0. era\<^sub>t t\<^sub>0 \<le> era\<^sub>i j \<and> committed\<^sub>< j"
  defines "promised\<^sub>f' i n t \<equiv> promised\<^sub>f i n t \<or> (i, n, t) = (i\<^sub>0, n\<^sub>0, t\<^sub>0)"
  shows "paxos v promised\<^sub>m promised\<^sub>f' promised\<^sub>b proposed accepted committed"
  using promised\<^sub>m promised\<^sub>b_accepted promised\<^sub>b_lt promised\<^sub>b_max proposed_finite accepted committed
proof (intro paxosI_simple, fold prevAccepted_def)
  fix i n t t'
  assume "promised\<^sub>f' i n t" "t' \<prec> t"
  hence "promised\<^sub>f i n t \<or> (i, n, t) = (i\<^sub>0, n\<^sub>0, t\<^sub>0)" by (auto simp add: promised\<^sub>f'_def)
  with assms `t' \<prec> t`
  show "\<not> accepted i n t'"
    by (elim disjE, intro promised\<^sub>f, auto)
next
  fix i n t
  assume "((\<exists>j\<le>i. promised\<^sub>m j n t) \<or> promised\<^sub>f' i n t) \<or> (\<exists>t'. promised\<^sub>b i n t t')"
  hence "promised i n t \<or> (i, n, t) = (i\<^sub>0, n\<^sub>0, t\<^sub>0)"
    by (auto simp add: promised\<^sub>f'_def promised_def)
  with assms promised_era
  show "\<exists>j\<le>i. era\<^sub>t t \<le> era\<^sub>i j \<and> committed\<^sub>< j" by auto
next
  fix i t
  assume "proposed i t"
  from proposed [OF this]
  obtain q where q: "q\<in>Q (era\<^sub>t t)" "\<forall>n\<in>q. promised i n t" "prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q))" by auto
  thus "\<exists>q\<in>Q (era\<^sub>t t). (\<forall>n\<in>q. ((\<exists>j\<le>i. promised\<^sub>m j n t) \<or> promised\<^sub>f' i n t) \<or> (\<exists>t'. promised\<^sub>b i n t t')) \<and> (prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q)))"
    by (intro bexI [of _ q], auto simp add: q promised\<^sub>f'_def promised_def)
qed

text \<open>A @{term promised\<^sub>b} message can be sent if something has been accepted for this slot, and the
configuration of the era of its term is known. The message must include the greatest term for which
an @{term accepted} message has been sent:\<close>

lemma (in paxos) send_promised\<^sub>b:
  assumes "t\<^sub>0' \<prec> t\<^sub>0"
  assumes "accepted i\<^sub>0 n\<^sub>0 t\<^sub>0'"
  assumes "\<And>t''. accepted i\<^sub>0 n\<^sub>0 t'' \<Longrightarrow> t'' \<preceq> t\<^sub>0'"
  assumes "\<exists> j \<le> i\<^sub>0. era\<^sub>t t\<^sub>0 \<le> era\<^sub>i j \<and> committed\<^sub>< j"
  defines "promised\<^sub>b' i n t t' \<equiv> promised\<^sub>b i n t t' \<or> (i, n, t, t') = (i\<^sub>0, n\<^sub>0, t\<^sub>0, t\<^sub>0')"
  shows "paxos v promised\<^sub>m promised\<^sub>f promised\<^sub>b' proposed accepted committed"
  using promised\<^sub>m promised\<^sub>f proposed_finite accepted committed
proof (intro paxosI_simple)
  fix i n t t'
  assume p: "promised\<^sub>b' i n t t'"
  from p assms promised\<^sub>b_lt show "t' \<prec> t"
    using promised\<^sub>b'_def by auto

  from p assms promised\<^sub>b_accepted show "accepted i n t'"
    using promised\<^sub>b'_def by auto

  fix t'' assume "t' \<prec> t''" "t'' \<prec> t"
  with p promised\<^sub>b_max assms show "\<not> accepted i n t''"
    using promised\<^sub>b'_def
    by (metis prod.inject term_not_le_lt)

next
  fix i n t
  assume "((\<exists>j\<le>i. promised\<^sub>m j n t) \<or> promised\<^sub>f i n t) \<or> (\<exists>t'. promised\<^sub>b' i n t t')"
  hence "promised i n t \<or> (i, n, t) = (i\<^sub>0, n\<^sub>0, t\<^sub>0)"
    using promised\<^sub>b'_def promised_def by auto
  thus "\<exists>j\<le>i. era\<^sub>t t \<le> era\<^sub>i j \<and> committed\<^sub>< j"
    using assms promised_era by auto

next
  have promised\<^sub>b_func: "\<And>t'. promised\<^sub>b i\<^sub>0 n\<^sub>0 t\<^sub>0 t' \<Longrightarrow> t' = t\<^sub>0'"
    using assms(1) assms(2) assms(3) le_term_def promised\<^sub>b_accepted promised\<^sub>b_max by blast

  have promised_imp: "promised i\<^sub>0 n\<^sub>0 t\<^sub>0 \<Longrightarrow> promised\<^sub>b i\<^sub>0 n\<^sub>0 t\<^sub>0 t\<^sub>0'"
    using promised_def assms promised\<^sub>b_func promised\<^sub>f promised\<^sub>m by blast

  fix i t
  assume "proposed i t"
  from proposed [OF this]
  obtain q where q: "q\<in>Q (era\<^sub>t t)" "\<forall>n\<in>q. promised i n t" "prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q))" by auto

  have [simp]: "{t'. \<exists>n\<in>q. promised\<^sub>b' i n t t'} = prevAccepted i t q"
    using prevAccepted_def promised\<^sub>b'_def promised_imp q(2) by auto

  from q show "\<exists>q\<in>Q (era\<^sub>t t). (\<forall>n\<in>q. ((\<exists>j\<le>i. promised\<^sub>m j n t) \<or> promised\<^sub>f i n t) \<or> (\<exists>t'. promised\<^sub>b' i n t t')) \<and> ({t'. \<exists>n\<in>q. promised\<^sub>b' i n t t'} = {} \<or> v i t = v i (maxTerm {t'. \<exists>n\<in>q. promised\<^sub>b' i n t t'}))"
  proof (intro bexI [of _ q] conjI)
    from q show
      "\<forall>n\<in>q. ((\<exists>j\<le>i. promised\<^sub>m j n t) \<or> promised\<^sub>f i n t) \<or> (\<exists>t'. promised\<^sub>b' i n t t')"
      by (auto simp add: promised\<^sub>b'_def promised_def)
  qed simp
qed

subsubsection \<open>Proposals\<close>

text \<open>A @{term proposed} message can be sent if it has not previously been sent and a quorum
of suitable promises has been received. If any promise received was a @{term promised\<^sub>b} message
then this determines the value proposed:\<close>

lemma (in paxos) send_proposed:
  assumes "\<not> proposed i\<^sub>0 t\<^sub>0"
  assumes "\<And>n. n \<in> q \<Longrightarrow> promised i\<^sub>0 n t\<^sub>0"
  assumes "q \<in> Q (era\<^sub>t t\<^sub>0)"

  fixes v\<^sub>0
  defines "v' i t \<equiv> if (i, t) = (i\<^sub>0, t\<^sub>0)
                        then if prevAccepted i\<^sub>0 t\<^sub>0 q = {}
                                then v\<^sub>0
                                else v i\<^sub>0 (maxTerm (prevAccepted i\<^sub>0 t\<^sub>0 q))
                        else v i t"
  defines "proposed' i t \<equiv> proposed i t \<or> (i, t) = (i\<^sub>0, t\<^sub>0)"
  shows "paxos v' promised\<^sub>m promised\<^sub>f promised\<^sub>b proposed' accepted committed"
proof -
  define v\<^sub>c' where "\<And>i. v\<^sub>c' i \<equiv> v' i (SOME t. committed i t)"
  define era\<^sub>i' where "\<And>i. era\<^sub>i' i \<equiv> eraOfNat (card {j. j < i \<and> isReconfiguration (v\<^sub>c' j)})"
  define reconfig' where "\<And>e. reconfig' e \<equiv> THE i. isCommitted i \<and> isReconfiguration (v\<^sub>c' i) \<and> era\<^sub>i' i = e"
  define Q' where "\<And>e. Q' e \<equiv> case e of e\<^sub>0 \<Rightarrow> Q\<^sub>0 | nextEra e' \<Rightarrow> getConf (v\<^sub>c' (reconfig' e'))"

  have v\<^sub>c_eq: "\<And>i. isCommitted i \<Longrightarrow> v\<^sub>c' i = v\<^sub>c i"
    using committed_proposed isCommitted_def assms tfl_some v'_def v\<^sub>c'_def v\<^sub>c_def by auto

  have era\<^sub>i_eq: "\<And>i. committed\<^sub>< i \<Longrightarrow> era\<^sub>i' i = era\<^sub>i i"
    by (metis (mono_tags, lifting) Collect_cong committedTo_def era\<^sub>i'_def era\<^sub>i_def v\<^sub>c_eq)

  have reconfig_eq: "\<And>i e. committed\<^sub>< i \<Longrightarrow> e < era\<^sub>i i \<Longrightarrow> reconfig' e = reconfig e"
  proof -
    fix i e
    assume a: "committed\<^sub>< i" "e < era\<^sub>i i"

    define P where "\<And>i. P i \<equiv> isCommitted i \<and> isReconfiguration (v\<^sub>c' i) \<and> era\<^sub>i' i = e"
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

  have Q_eq: "\<And>i. committed\<^sub>< i \<Longrightarrow> \<forall> e \<le> era\<^sub>i i. Q' e = Q e"
  proof (intro allI impI)
    fix i e assume "committed\<^sub>< i" "e \<le> era\<^sub>i i"
    thus "Q' e = Q e"
      apply (cases e, simp_all add: Q'_def Q_def reconfig_committed reconfig_eq v\<^sub>c_eq)
      by (metis less_eq_Suc_le natOfEra.simps(2) natOfEra_le natOfEra_lt reconfig_committed reconfig_eq v\<^sub>c_eq)
  qed

  have v_prevAccepted_eq: "\<And>i t q. prevAccepted i t q \<noteq> {} \<Longrightarrow> v' i (maxTerm (prevAccepted i t q)) = v i (maxTerm (prevAccepted i t q))"
  proof -
    fix i t q
    assume bound: "prevAccepted i t q \<noteq> {}"

    have "maxTerm (prevAccepted i t q) \<in> prevAccepted i t q"
      by (intro maxTerm_mem `prevAccepted i t q \<noteq> {}` finite_prevAccepted)

    then obtain n where "promised\<^sub>b i n t (maxTerm (prevAccepted i t q))" by (auto simp add: prevAccepted_def)
    hence "accepted i n (maxTerm (prevAccepted i t q))" using promised\<^sub>b_accepted by auto
    hence "proposed i   (maxTerm (prevAccepted i t q))" using accepted by auto

    thus "?thesis i t q" using assms v'_def by auto
  qed

  from proposed_finite accepted promised\<^sub>m promised\<^sub>f promised\<^sub>b_lt promised\<^sub>b_accepted promised\<^sub>b_max
  have update_value: "paxos v' promised\<^sub>m promised\<^sub>f promised\<^sub>b proposed accepted committed"
  proof (unfold_locales, fold promised_def isCommitted_def v\<^sub>c'_def prevAccepted_def, fold committedTo_def era\<^sub>i'_def reconfig'_def, fold Q'_def)
    fix i t assume "committed i t" with committed_in_order show "committed\<^sub>< i" .

    from `committed i t` have [simp]: "v\<^sub>c' i = v\<^sub>c i"
      by (intro v\<^sub>c_eq, auto simp add: isCommitted_def)

    have "era\<^sub>i' i = era\<^sub>i i"
      by (simp add: \<open>committed\<^sub>< i\<close> era\<^sub>i_eq)
    also have "era\<^sub>i i = era\<^sub>t t"
      by (simp add: \<open>committed i t\<close> committed_era)
    finally show "era\<^sub>i' i = era\<^sub>t t" .

    have Q'_eq: "Q' (era\<^sub>t t) = Q (era\<^sub>t t)"
      using Q_eq \<open>committed\<^sub>< i\<close> \<open>era\<^sub>i i = era\<^sub>t t\<close> by auto

    show "\<exists>q\<in>Q' (era\<^sub>t t). \<forall>n\<in>q. accepted i n t"
      by (simp add: Q'_eq, intro committed `committed i t`)

  next
    fix i n t
    assume "promised i n t"
    with promised_era
    obtain j where "j \<le> i" "era\<^sub>t t \<le> era\<^sub>i j" "committed\<^sub>< j" by fastforce
    have "era\<^sub>i' j = era\<^sub>i j" by (simp add: \<open>committed\<^sub>< j\<close> era\<^sub>i_eq)
    thus "\<exists>j\<le>i. era\<^sub>t t \<le> era\<^sub>i' j \<and> committed\<^sub>< j"
      using \<open>committed\<^sub>< j\<close> \<open>era\<^sub>t t \<le> era\<^sub>i j\<close> \<open>j \<le> i\<close> by auto

  next
    fix i t
    assume "proposed i t"
    from proposed [OF this]
    obtain q where q: "q \<in> Q (era\<^sub>t t)" "\<And>n. n \<in> q \<Longrightarrow> promised i n t"
      "prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q))" by auto

    have "Q' (era\<^sub>t t) = Q (era\<^sub>t t)"
      by (metis IntE Q_eq Q_intersects `\<And>n. n \<in> q \<Longrightarrow> promised i n t` \<open>q \<in> Q (era\<^sub>t t)\<close> all_not_in_conv intersects_def promised_era)

    show "\<exists>q\<in>Q' (era\<^sub>t t). (\<forall>n\<in>q. promised i n t) \<and> (prevAccepted i t q = {} \<or> v' i t = v' i (maxTerm (prevAccepted i t q)))"
    proof (intro bexI conjI ballI `\<And>n. n \<in> q \<Longrightarrow> promised i n t` iffD1 [OF disj_commute, OF disjCI])
      from `q \<in> Q (era\<^sub>t t)` `Q' (era\<^sub>t t) = Q (era\<^sub>t t)`
      show "q \<in> Q' (era\<^sub>t t)" by simp

      assume bound: "prevAccepted i t q \<noteq> {}"
      hence [simp]: "v' i (maxTerm (prevAccepted i t q)) = v i (maxTerm (prevAccepted i t q))"
        by (simp add: v_prevAccepted_eq)

      have [simp]: "v' i t = v i t"
        using \<open>proposed i t\<close> assms v'_def by auto

      show "v' i t = v' i (maxTerm (prevAccepted i t q))"
        using bound q by auto
    qed
  qed

  from promised\<^sub>m promised\<^sub>f promised\<^sub>b_lt promised\<^sub>b_accepted promised\<^sub>b_max
  show ?thesis
  proof (intro paxos.paxosI_simple [OF update_value],
      fold prevAccepted_def promised_def isCommitted_def, fold committedTo_def v\<^sub>c'_def,
      fold era\<^sub>i'_def reconfig'_def, fold Q'_def)

    fix i n t
    assume "promised i n t"
    from promised_era [OF this] obtain j where j: "j \<le> i" "era\<^sub>t t \<le> era\<^sub>i j" "committed\<^sub>< j" by auto
    have [simp]: "era\<^sub>i' j = era\<^sub>i j" by (simp add: era\<^sub>i_eq j)

    from j show "\<exists>j\<le>i. era\<^sub>t t \<le> era\<^sub>i' j \<and> committed\<^sub>< j" by auto

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

    have "Q' (era\<^sub>t t) = Q (era\<^sub>t t)"
      using Q_eq \<open>committed i t\<close> committed_era committed_in_order by fastforce

    with `committed i t` committed
    show "\<exists>q\<in>Q' (era\<^sub>t t). \<forall>n\<in>q. accepted i n t" by auto

  next
    fix i t assume "proposed' i t"

    hence "proposed i t \<or> (i, t) = (i\<^sub>0, t\<^sub>0)" by (auto simp add: proposed'_def)
    thus "\<exists>q\<in>Q' (era\<^sub>t t). (\<forall>n\<in>q. promised i n t) \<and> (prevAccepted i t q = {} \<or> v' i t = v' i (maxTerm (prevAccepted i t q)))"
    proof (elim disjE)
      assume p: "proposed i t"
      hence Q_eq: "Q' (era\<^sub>t t) = Q (era\<^sub>t t)"
        by (metis IntE Q_eq Q_intersects equals0I intersects_def promised_era proposed)

      from p have v_eq: "v' i t = v i t"
        using assms v'_def by auto

      from p have v_eq2: "\<And>q. prevAccepted i t q = {} \<or> v' i (maxTerm (prevAccepted i t q)) = v i (maxTerm (prevAccepted i t q))"
        using v_prevAccepted_eq by auto

      from Q_eq v_eq v_eq2 proposed [OF `proposed i t`] show ?thesis by metis

    next
      assume "(i, t) = (i\<^sub>0, t\<^sub>0)"
      hence [simp]: "i = i\<^sub>0" "t = t\<^sub>0" by simp_all

      from assms have "q \<noteq> {}"
        by (meson Int_emptyI Q_intersects equals0D intersects_def)
      then obtain n where "n \<in> q" by auto

      with assms have "promised i\<^sub>0 n t\<^sub>0" by simp
      from promised_era [OF this]
      obtain j where "j\<le>i\<^sub>0" "era\<^sub>t t\<^sub>0 \<le> era\<^sub>i j" "committed\<^sub>< j" by auto

      have Q_eq: "Q' (era\<^sub>t t\<^sub>0) = Q (era\<^sub>t t\<^sub>0)"
        using Q_eq \<open>committed\<^sub>< j\<close> \<open>era\<^sub>t t\<^sub>0 \<le> era\<^sub>i j\<close> by blast

      show ?thesis
        by (intro bexI [of _ q] conjI ballI, simp_all add: assms Q_eq)
    qed
  qed
qed

subsubsection \<open>Acceptances\<close>

text \<open>A proposal can be accepted as long as it is compatible with all previously-made promises:\<close>

lemma (in paxos) send_accepted:
  assumes "proposed i\<^sub>0 t\<^sub>0"
  assumes "\<And>t. promised i\<^sub>0 n\<^sub>0 t \<Longrightarrow> t \<preceq> t\<^sub>0"
  defines "accepted' i n t \<equiv> accepted i n t \<or> (i, n, t) = (i\<^sub>0, n\<^sub>0, t\<^sub>0)"
  shows "paxos v promised\<^sub>m promised\<^sub>f promised\<^sub>b proposed accepted' committed"
  using promised\<^sub>b_lt proposed_finite proposed
proof (intro paxosI_simple)
  show "\<And>i j n t t'. promised\<^sub>m i n t \<Longrightarrow> t' \<prec> t \<Longrightarrow> i \<le> j \<Longrightarrow> \<not> accepted' j n t'"
    by (metis Pair_inject accepted'_def assms(2) promised\<^sub>m promised_def term_not_le_lt)
  show "\<And>i n t t'. promised\<^sub>f i n t \<Longrightarrow> t' \<prec> t \<Longrightarrow> \<not> accepted' i n t'"
    by (metis Pair_inject accepted'_def assms(2) promised\<^sub>f promised_def term_not_le_lt)
  show "\<And>i n t t'. promised\<^sub>b i n t t' \<Longrightarrow> accepted' i n t'"
    by (simp add: accepted'_def promised\<^sub>b_accepted)
  show "\<And>i n t t' t''. promised\<^sub>b i n t t' \<Longrightarrow> t' \<prec> t'' \<Longrightarrow> t'' \<prec> t \<Longrightarrow> \<not> accepted' i n t''"
    by (metis accepted'_def assms(2) prod.inject promised\<^sub>b_max promised_def term_not_le_lt)
  show "\<And>i n t. ((\<exists>j\<le>i. promised\<^sub>m j n t) \<or> promised\<^sub>f i n t) \<or> (\<exists>t'. promised\<^sub>b i n t t') \<Longrightarrow> \<exists>j\<le>i. era\<^sub>t t \<le> era\<^sub>i j \<and> committed\<^sub>< j"
    by (simp add: promised_def promised_era)
  show "\<And>i t. proposed i t \<Longrightarrow> \<exists>q\<in>Q (era\<^sub>t t). (\<forall>n\<in>q. ((\<exists>j\<le>i. promised\<^sub>m j n t) \<or> promised\<^sub>f i n t) \<or> (\<exists>t'. promised\<^sub>b i n t t')) \<and> ({t'. \<exists>n\<in>q. promised\<^sub>b i n t t'} = {} \<or> v i t = v i (maxTerm {t'. \<exists>n\<in>q. promised\<^sub>b i n t t'}))"
    using prevAccepted_def promised_def proposed by auto
  show "\<And>i n t. accepted' i n t \<Longrightarrow> proposed i t"
    using accepted accepted'_def assms(1) by auto
  show "\<And>i t. committed i t \<Longrightarrow> \<exists>q\<in>Q (era\<^sub>t t). \<forall>n\<in>q. accepted' i n t"
    by (meson accepted'_def committed)
qed

subsubsection \<open>Commits\<close>

text \<open>A proposal can be committed on receipt of a quorum of acceptances, as long as all previous
slots are committed and this slot's era matches the era of the term of the proposal:\<close>

lemma (in paxos) send_committed:
  assumes "committed\<^sub>< i\<^sub>0"
  assumes "era\<^sub>i i\<^sub>0 = era\<^sub>t t\<^sub>0"
  assumes "\<And>n. n \<in> q \<Longrightarrow> accepted i\<^sub>0 n t\<^sub>0"
  assumes "q \<in> Q (era\<^sub>t t\<^sub>0)"
  defines "committed' i t \<equiv> committed i t \<or> (i, t) = (i\<^sub>0, t\<^sub>0)"
  shows "paxos v promised\<^sub>m promised\<^sub>f promised\<^sub>b proposed accepted committed'"
proof -

  from assms have committedTo: "committed\<^sub>< i\<^sub>0" by metis

  define isCommitted' where "\<And>i. isCommitted' i \<equiv> \<exists>t. committed' i t"
  define committedTo' ("committed\<^sub><' _") where "\<And>i. committed\<^sub><' i \<equiv> \<forall>j < i. isCommitted' j"
  define v\<^sub>c' where "\<And>i. v\<^sub>c' i \<equiv> v i (SOME t. committed' i t)"
  define era\<^sub>i' where "\<And>i. era\<^sub>i' i \<equiv> eraOfNat (card {j. j < i \<and> isReconfiguration (v\<^sub>c' j)})"
  define reconfig' where "\<And>e. reconfig' e \<equiv> THE i. isCommitted' i \<and> isReconfiguration (v\<^sub>c' i) \<and> era\<^sub>i' i = e"
  define Q' where "\<And>e. Q' e \<equiv> case e of e\<^sub>0 \<Rightarrow> Q\<^sub>0 | nextEra e' \<Rightarrow> getConf (v\<^sub>c' (reconfig' e'))"

  have isCommitted'_simp: "\<And>i. isCommitted' i = (isCommitted i \<or> i = i\<^sub>0)"
    using committed'_def isCommitted'_def isCommitted_def by auto
  have committedTo'_simp: "\<And>i. (committed\<^sub><' i) = ((committed\<^sub>< i) \<or> i = Suc i\<^sub>0)"
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
        from assms show "q \<in> (Q o era\<^sub>t) t\<^sub>0" by simp
        from assms show "\<And>n. n \<in> q \<Longrightarrow> accepted i\<^sub>0 n t\<^sub>0" by simp
        from t True show "committed i\<^sub>0 t \<or> t = t\<^sub>0" by simp
        show "committed i\<^sub>0 t\<^sub>0 \<or> t\<^sub>0 = t\<^sub>0" by simp
        show "\<And>t. proposed i\<^sub>0 t \<Longrightarrow> t\<^sub>0 \<preceq> t \<Longrightarrow> (Q \<circ> era\<^sub>t) t \<frown> (Q \<circ> era\<^sub>t) t\<^sub>0"
          using Q_intersects True \<open>isCommitted i\<^sub>0\<close> committed_era `era\<^sub>i i\<^sub>0 = era\<^sub>t t\<^sub>0`
            le_term_def lt_term_def oneSlot.Q_intersects projects_to_oneSlot t by fastforce
      qed

      ultimately show ?thesis by (simp add: True)
    qed
  qed

  have era\<^sub>i'_eq: "\<And>i. committed\<^sub>< i \<Longrightarrow> era\<^sub>i' i = era\<^sub>i i"
    by (metis (mono_tags, lifting) Collect_cong committedTo_def era\<^sub>i'_def era\<^sub>i_def v\<^sub>c'_eq)

  have reconfig'_eq: "\<And>e i. committed\<^sub>< i \<Longrightarrow> e < era\<^sub>i i \<Longrightarrow> reconfig' e = reconfig e"
  proof -
    fix e i
    assume a: "committed\<^sub>< i" "e < era\<^sub>i i"

    define P where "\<And>i. P i \<equiv> isCommitted' i \<and> isReconfiguration (v\<^sub>c' i) \<and> era\<^sub>i' i = e"
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

  have Q'_eq: "\<And>e i. committed\<^sub>< i \<Longrightarrow> e \<le> era\<^sub>i i \<Longrightarrow> Q' e = Q e"
  proof -
    fix e i assume "committed\<^sub>< i" "e \<le> era\<^sub>i i"
    thus "Q' e = Q e" 
      apply (cases e, simp add: Q_def Q'_def)
      by (metis Era.simps(5) Q_def Suc_le_eq Q'_def natOfEra.simps(2) natOfEra_le natOfEra_lt reconfig'_eq reconfig_committed v\<^sub>c'_eq)
  qed

  show ?thesis
    apply (unfold_locales)
                apply (fold isCommitted'_def v\<^sub>c'_def promised_def prevAccepted_def)
                apply (fold committedTo'_def era\<^sub>i'_def reconfig'_def)
                apply (fold Q'_def)
    using promised\<^sub>m promised\<^sub>f promised\<^sub>b_lt promised\<^sub>b_accepted promised\<^sub>b_max proposed_finite accepted
  proof -
    from committed_in_order committedTo
    show "\<And>i t. committed' i t \<Longrightarrow> committed\<^sub><' i"
      using committed'_def committedTo committedTo'_simp committed_in_order by auto

    show "\<And>i n t. promised i n t \<Longrightarrow> \<exists>j\<le>i. era\<^sub>t t \<le> era\<^sub>i' j \<and> committed\<^sub><' j"
      using committedTo'_simp era\<^sub>i'_eq promised_era by force

    show "\<And>i t. committed' i t \<Longrightarrow> era\<^sub>i' i = era\<^sub>t t"
      using committed'_def committedTo committed_era committed_in_order assms era\<^sub>i'_eq by auto

    from assms
    show "\<And>i t. committed' i t \<Longrightarrow> \<exists>q\<in>Q' (era\<^sub>t t). \<forall>n\<in>q. accepted i n t"
      by (metis Q'_eq committed committed'_def committedTo committed_era committed_in_order order_refl prod.inject)

    show "\<And>i t. proposed i t \<Longrightarrow> \<exists>q\<in>Q' (era\<^sub>t t). (\<forall>n\<in>q. promised i n t) \<and> (prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q)))"
      by (metis Q'_eq promised_era proposed proposed_promised)
  qed
qed

subsection \<open>Zen\<close>

text \<open>Zen does not support pipelining so there is only ever at most one active (i.e. proposed-but-not-committed) slot.\<close>

datatype Message
  = JoinResponse  nat Node Term "Term option"
  | ApplyRequest  nat      Term Value
  | ApplyResponse nat Node Term
  | ApplyCommit   nat      Term

locale zen =
  fixes messages :: "Message set"
    (* value proposed in a slot & a term *)
  fixes v :: "nat \<Rightarrow> Term \<Rightarrow> Value"
  defines "v i t \<equiv> THE x. ApplyRequest i t x \<in> messages"
    (* whether a slot is committed *)
  fixes isCommitted :: "nat \<Rightarrow> bool"
  defines "isCommitted i \<equiv> \<exists> t. ApplyCommit i t \<in> messages"
    (* whether all preceding slots are committed *)
  fixes committedTo :: "nat \<Rightarrow> bool" ("committed\<^sub><")
  defines "committed\<^sub>< i \<equiv> \<forall> j < i. isCommitted j" 
    (* the committed value in a slot *)
  fixes v\<^sub>c :: "nat \<Rightarrow> Value"
  defines "v\<^sub>c i \<equiv> v i (SOME t. ApplyCommit i t \<in> messages)"
    (* the era of a slot *)
  fixes era\<^sub>i :: "nat \<Rightarrow> Era"
  defines "era\<^sub>i i \<equiv> eraOfNat (card { j. j < i \<and> isReconfiguration (v\<^sub>c j) })"
    (* the (unique) slot in an era containing a reconfiguration *)
  fixes reconfig :: "Era \<Rightarrow> nat"
  defines "reconfig e \<equiv> THE i. isCommitted i \<and> isReconfiguration (v\<^sub>c i) \<and> era\<^sub>i i = e"
    (* the configuration of an era *)
  fixes Q :: "Era \<Rightarrow> Node set set"
  defines "Q e \<equiv> case e of e\<^sub>0 \<Rightarrow> Q\<^sub>0 | nextEra e' \<Rightarrow> getConf (v\<^sub>c (reconfig e'))"
    (* predicate to say whether an applicable JoinResponse has been sent *)
  fixes promised :: "nat \<Rightarrow> Node \<Rightarrow> Term \<Rightarrow> bool"
  defines "promised i n t \<equiv> \<exists> i' \<le> i. \<exists> mt'. JoinResponse i' n t mt' \<in> messages"
    (* set of previously-accepted terms *)
  fixes prevAccepted :: "nat \<Rightarrow> Term \<Rightarrow> Node set \<Rightarrow> Term set"
  defines "prevAccepted i t ns \<equiv> {t'. \<exists> n \<in> ns. JoinResponse i n t (Some t') \<in> messages}"
    (* ASSUMPTIONS *)
  assumes JoinResponse_future:
    "\<And>i i' n t t' mt. \<lbrakk> JoinResponse i n t mt \<in> messages; i < i'; t' \<prec> t \<rbrakk>
                        \<Longrightarrow> ApplyResponse i' n t' \<notin> messages"
  assumes JoinResponse_None:
    "\<And>i n t t'. \<lbrakk> JoinResponse i n t None \<in> messages; t' \<prec> t \<rbrakk>
                        \<Longrightarrow> ApplyResponse i n t' \<notin> messages"
  assumes JoinResponse_Some_lt:
    "\<And>i n t t'. JoinResponse i n t (Some t') \<in> messages \<Longrightarrow> t' \<prec> t"
  assumes JoinResponse_Some_ApplyResponse:
    "\<And>i n t t'. JoinResponse i n t (Some t') \<in> messages \<Longrightarrow> ApplyResponse i n t' \<in> messages"
  assumes JoinResponse_Some_max:
    "\<And>i n t t' t''. \<lbrakk> JoinResponse i n t (Some t') \<in> messages; t' \<prec> t''; t'' \<prec> t \<rbrakk>
                        \<Longrightarrow> ApplyResponse i n t'' \<notin> messages"
  assumes JoinResponse_era:
    "\<And>i n t mt. JoinResponse i n t mt \<in> messages \<Longrightarrow> \<exists> i' \<le> i. committedTo i' \<and> era\<^sub>t t \<le> era\<^sub>i i'"
  assumes ApplyRequest_committedTo:
    "\<And>i t x. ApplyRequest i t x \<in> messages \<Longrightarrow> committedTo i"
  assumes ApplyRequest_quorum:
    "\<And>i t x. ApplyRequest i t x \<in> messages \<Longrightarrow> \<exists> q \<in> Q (era\<^sub>t t). (\<forall> n \<in> q. promised i n t) \<and>
            (prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q)))"
  assumes ApplyRequest_function:
    "\<And>i t x x'. \<lbrakk> ApplyRequest i t x \<in> messages; ApplyRequest i t x' \<in> messages \<rbrakk> \<Longrightarrow> x = x'"
  assumes finite_messages:
    "finite messages"
  assumes ApplyResponse_ApplyRequest:
    "\<And>i n t. ApplyResponse i n t \<in> messages \<Longrightarrow> \<exists> x. ApplyRequest i t x \<in> messages"
  assumes ApplyCommit_era:
    "\<And>i t. ApplyCommit i t \<in> messages \<Longrightarrow> era\<^sub>i i = era\<^sub>t t"
  assumes ApplyCommit_quorum:
    "\<And>i t. ApplyCommit i t \<in> messages
                        \<Longrightarrow> \<exists> q \<in> Q (era\<^sub>t t). \<forall> n \<in> q. ApplyResponse i n t \<in> messages"

lemma (in zen) promised_long_def: "promised i n t \<equiv> (JoinResponse i n t None \<in> messages \<or> (\<exists>i'<i. \<exists>mt'. JoinResponse i' n t mt' \<in> messages)) \<or> (\<exists>t'. JoinResponse i n t (Some t') \<in> messages)"
  using option.exhaust by (smt nat_less_le not_le promised_def)

lemma (in zen) Q_intersects: "Q e \<frown> Q e"
  by (cases e, simp_all add: Q_def Q\<^sub>0_intersects getConf_intersects)

lemma (in zen) Q_members_nonempty: assumes "q \<in> Q e" shows "q \<noteq> {}"
  using assms Q_intersects 
  by (auto simp add: intersects_def)

lemma (in zen) Q_member_member: assumes "q \<in> Q e" obtains n where "n \<in> q"
  using Q_members_nonempty assms by fastforce

lemma (in zen) ApplyCommit_ApplyResponse:
  assumes "ApplyCommit i t \<in> messages"
  obtains n where "ApplyResponse i n t \<in> messages"
  by (meson ApplyCommit_quorum Q_member_member assms)

lemma (in zen) ApplyCommit_ApplyRequest:
  assumes "ApplyCommit i t \<in> messages"
  shows "ApplyRequest i t (v i t) \<in> messages"
  by (metis ApplyCommit_ApplyResponse ApplyResponse_ApplyRequest assms the_equality v_def ApplyRequest_function)

lemma (in zen) era\<^sub>i_step:
  "era\<^sub>i (Suc i) = (if isReconfiguration (v\<^sub>c i) then nextEra (era\<^sub>i i) else era\<^sub>i i)"
proof (cases "isReconfiguration (v\<^sub>c i)")
  case True
  hence "{j. j < Suc i \<and> isReconfiguration (v\<^sub>c j)}
                = insert i {j. j < i \<and> isReconfiguration (v\<^sub>c j)}"
    using True by auto
  thus ?thesis by (simp add: era\<^sub>i_def True)
next
  case False
  with less_Suc_eq show ?thesis
    by (simp add: era\<^sub>i_def, smt Collect_cong less_or_eq_imp_le)
qed

lemma (in zen) era\<^sub>i_mono:
  assumes "i' \<le> i"
  shows "era\<^sub>i i' \<le> era\<^sub>i i"
  using assms
proof (induct i)
  case (Suc i)
  from Suc.prems have disj1: "i' \<le> i \<or> i' = Suc i" by auto
  thus ?case
  proof (elim disjE)
    assume "i' \<le> i"
    with Suc.hyps have "era\<^sub>i i' \<le> era\<^sub>i i" .
    also have "... \<le> era\<^sub>i (Suc i)"
      by (metis Suc_leD eq_iff era\<^sub>i_step natOfEra.simps(2) natOfEra_le)
    finally show ?thesis .
  qed simp
qed simp

lemma (in zen) reconfig_props:
  assumes "committed\<^sub>< i" "e < era\<^sub>i i"
  shows reconfig_isCommitted: "isCommitted (reconfig e)"
    and reconfig_isReconfiguration: "isReconfiguration (v\<^sub>c (reconfig e))"
    and reconfig_era: "era\<^sub>i (reconfig e) = e"
proof -
  have p: "\<And>e. e < era\<^sub>i i \<Longrightarrow> committed\<^sub>< i \<Longrightarrow> isCommitted (reconfig e) \<and> isReconfiguration (v\<^sub>c (reconfig e)) \<and> (era\<^sub>i (reconfig e) = e)"
  proof (induct i)
    case 0 thus ?case by (auto simp add: era\<^sub>i_def)
  next
    case (Suc i e)
    have "e < era\<^sub>i i \<or> (e = era\<^sub>i i \<and> isReconfiguration (v\<^sub>c i))"
      by (metis Suc.prems(1) era\<^sub>i_step less_antisym natOfEra.simps(2) natOfEra_lt neq_iff)
    thus ?case
    proof (elim disjE conjE)
      assume a: "e < era\<^sub>i i"
      from Suc.prems have "committed\<^sub>< i" by (auto simp add: committedTo_def)
      with a Suc.hyps show ?thesis by simp
    next
      assume a: "e = era\<^sub>i i" "isReconfiguration (v\<^sub>c i)"

      define P where "\<And>i. P i \<equiv> isCommitted i \<and> isReconfiguration (v\<^sub>c i) \<and> era\<^sub>i i = e"
      have p: "reconfig e = (THE i. P i)" by (simp add: reconfig_def P_def)

      have "P (reconfig e)"
        using Suc.prems a
      proof (unfold p, intro theI [of P])
        show "\<And>x. P x \<Longrightarrow> x = i"
          by (metis P_def Suc.prems(1) Suc_inject a(1) era\<^sub>i_mono era\<^sub>i_step leD le_Suc_eq not_less_eq_eq)
      qed (auto simp add: committedTo_def P_def)
      thus ?thesis by (simp add: P_def)
    qed
  qed

  from p assms show "isCommitted (reconfig e)" "isReconfiguration (v\<^sub>c (reconfig e))" "era\<^sub>i (reconfig e) = e" by auto
qed

lemma (in zen) zen_is_oneSlot:
  fixes i
  shows "oneSlot (Q \<circ> era\<^sub>t) (v i)
    (\<lambda> n t. JoinResponse i n t None \<in> messages
        \<or> (\<exists> i' < i. \<exists> mt'. JoinResponse i' n t mt' \<in> messages))
    (\<lambda> n t t'. JoinResponse i n t (Some t') \<in> messages)
    (\<lambda> t. \<exists> x. ApplyRequest i t x \<in> messages)
    (\<lambda> n t. ApplyResponse i n t \<in> messages)
    (\<lambda> t. ApplyCommit i t \<in> messages)"
proof (unfold_locales, fold prevAccepted_def promised_long_def)
  fix t\<^sub>1 t\<^sub>2
  assume "\<exists>x. ApplyRequest i t\<^sub>1 x \<in> messages"
  then obtain x where t\<^sub>1: "ApplyRequest i t\<^sub>1 x \<in> messages" ..
  assume t\<^sub>2: "ApplyCommit i t\<^sub>2 \<in> messages"
  assume t\<^sub>2\<^sub>1: "t\<^sub>2 \<preceq> t\<^sub>1" hence "era\<^sub>t t\<^sub>2 \<le> era\<^sub>t t\<^sub>1"
    by (simp add: era\<^sub>t_mono)

  from t\<^sub>1 obtain i' n mt' where "JoinResponse i' n t\<^sub>1 mt' \<in> messages" "i' \<le> i"
    by (meson ApplyRequest_quorum Q_member_member promised_def)
  with JoinResponse_era obtain i'' where "i'' \<le> i'" "era\<^sub>t t\<^sub>1 \<le> era\<^sub>i i''" by blast

  note `era\<^sub>t t\<^sub>1 \<le> era\<^sub>i i''`
  also from `i'' \<le> i'` have "era\<^sub>i i'' \<le> era\<^sub>i i'" using era\<^sub>i_mono by blast
  also from `i' \<le> i` have "era\<^sub>i i' \<le> era\<^sub>i i" using era\<^sub>i_mono by blast
  also from t\<^sub>2 have "... = era\<^sub>t t\<^sub>2" using ApplyCommit_era by auto
  finally have "era\<^sub>t t\<^sub>1 \<le> era\<^sub>t t\<^sub>2" .

  with `era\<^sub>t t\<^sub>2 \<le> era\<^sub>t t\<^sub>1` have "era\<^sub>t t\<^sub>1 = era\<^sub>t t\<^sub>2" by simp
  thus "(Q \<circ> era\<^sub>t) t\<^sub>1 \<frown> (Q \<circ> era\<^sub>t) t\<^sub>2" by (simp add: Q_intersects)
next
  fix q t assume "q \<in> (Q \<circ> era\<^sub>t) t" thus "q \<noteq> {}" by (simp add: Q_members_nonempty)
next
  fix n t t'
  assume "t' \<prec> t" "JoinResponse i n t None \<in> messages \<or> (\<exists>i'<i. \<exists>mt'. JoinResponse i' n t mt' \<in> messages)"
  thus "ApplyResponse i n t' \<notin> messages"
    using JoinResponse_None JoinResponse_future by blast
next
  fix n t t'
  assume j: "JoinResponse i n t (Some t') \<in> messages"
  from j show "t' \<prec> t" using JoinResponse_Some_lt by blast
  from j show "ApplyResponse i n t' \<in> messages" using JoinResponse_Some_ApplyResponse by blast

  fix t'' assume "t' \<prec> t''" "t'' \<prec> t"
  with j show "ApplyResponse i n t'' \<notin> messages" using JoinResponse_Some_max by blast
next
  fix t
  assume "\<exists>x. ApplyRequest i t x \<in> messages"
  thus "\<exists>q\<in>(Q \<circ> era\<^sub>t) t. (\<forall>n\<in>q. promised i n t) \<and> (prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q)))"
    using ApplyRequest_quorum by auto
next
  fix n t assume "ApplyResponse i n t \<in> messages"
  thus "\<exists>x. ApplyRequest i t x \<in> messages"
    by (simp add: ApplyResponse_ApplyRequest)
next
  fix t assume "ApplyCommit i t \<in> messages"
  thus "\<exists>q\<in>(Q \<circ> era\<^sub>t) t. \<forall>n\<in>q. ApplyResponse i n t \<in> messages"
    by (simp add: ApplyCommit_quorum)
next
  fix t\<^sub>0
  define f where "f \<equiv> \<lambda> m. case m of ApplyRequest i t x \<Rightarrow> t | _ \<Rightarrow> t\<^sub>0"

  have "{t. \<exists>x. ApplyRequest i t x \<in> messages} \<subseteq> f ` messages"
    using f_def image_iff by fastforce

  moreover have "finite (f ` messages)"
    by (simp add: finite_messages)

  ultimately show "finite {t. \<exists>x. ApplyRequest i t x \<in> messages}"
    using finite_subset by blast
qed

lemma (in zen) consistent:
  assumes "ApplyCommit  i t\<^sub>1 \<in> messages"
  assumes "ApplyCommit  i t\<^sub>2 \<in> messages"
  assumes "ApplyRequest i t\<^sub>1 v\<^sub>1 \<in> messages"
  assumes "ApplyRequest i t\<^sub>2 v\<^sub>2 \<in> messages"
  shows "v\<^sub>1 = v\<^sub>2"
proof -
  from oneSlot.consistent [OF zen_is_oneSlot] assms
  have "v i t\<^sub>1 = v i t\<^sub>2" by blast
  moreover have "v\<^sub>1 = v i t\<^sub>1" using ApplyCommit_ApplyRequest assms ApplyRequest_function by blast
  moreover have "v\<^sub>2 = v i t\<^sub>2" using ApplyCommit_ApplyRequest assms ApplyRequest_function by blast
  ultimately show ?thesis by simp
qed

lemma (in zen) JoinResponse_func:
  assumes "JoinResponse i n t mt\<^sub>1 \<in> messages" and "JoinResponse i n t mt\<^sub>2 \<in> messages"
  shows "mt\<^sub>1 = mt\<^sub>2"
  using JoinResponse_Some_ApplyResponse JoinResponse_Some_lt assms JoinResponse_None 
  apply (cases mt\<^sub>1)
   apply (cases mt\<^sub>2)
    apply simp
   apply blast
  apply (cases mt\<^sub>2)
   apply blast
  by (metis le_term_def term_not_le_lt JoinResponse_Some_max)

lemma (in zen) shows finite_messages_insert: "finite (insert m messages)"
  using finite_messages by auto

lemma (in zen) isCommitted_committedTo:
  assumes "isCommitted i"
  shows "committed\<^sub>< i"
  using ApplyCommit_ApplyRequest ApplyRequest_committedTo assms isCommitted_def by blast

lemma shows zen_initial_state: "zen {}" by (unfold_locales, auto)

lemma (in zen) send_JoinResponse_None:
  assumes "\<forall> i \<ge> i\<^sub>0. \<forall> t. ApplyResponse i n\<^sub>0 t \<notin> messages"
  assumes "\<forall> i < i\<^sub>0. \<exists> t. ApplyCommit i t \<in> messages"
  assumes "era\<^sub>t t\<^sub>0 = era\<^sub>i i\<^sub>0"
  shows   "zen (insert (JoinResponse i\<^sub>0 n\<^sub>0 t\<^sub>0 None) messages)" (is "zen ?messages'")
proof -
  define promised' where "\<And>i n t. promised' i n t \<equiv> \<exists>i'\<le>i. \<exists>mt'. JoinResponse i' n t mt' \<in> ?messages'"
  have promised'I: "\<And>i n t. promised i n t \<Longrightarrow> promised' i n t" using promised'_def promised_def by auto

  have messages_simps:
    "\<And>i n t. (JoinResponse i n t None \<in> ?messages') = (JoinResponse i n t None \<in> messages \<or> (i, n, t) = (i\<^sub>0, n\<^sub>0, t\<^sub>0))"
    "\<And>i n t t'. (JoinResponse i n t (Some t') \<in> ?messages') = (JoinResponse i n t (Some t') \<in> messages)"
    "\<And>i t x. (ApplyRequest i t x \<in> ?messages') = (ApplyRequest i t x \<in> messages)"
    "\<And>i n t. (ApplyResponse i n t \<in> ?messages') = (ApplyResponse i n t \<in> messages)"
    "\<And>i t. (ApplyCommit i t \<in> ?messages') = (ApplyCommit i t \<in> messages)"
    by auto

  show ?thesis
    apply (unfold_locales)
    apply (unfold messages_simps)
                apply (fold isCommitted_def v_def prevAccepted_def)
                apply (fold v\<^sub>c_def committedTo_def)
                apply (fold era\<^sub>i_def)
                apply (fold reconfig_def)
                apply (fold Q_def promised'_def)
    using ApplyResponse_ApplyRequest ApplyCommit_era ApplyCommit_quorum ApplyRequest_function
      ApplyRequest_committedTo JoinResponse_Some_lt JoinResponse_Some_ApplyResponse
      JoinResponse_Some_max finite_messages_insert
  proof -
    fix i i' n t t' mt
    assume "JoinResponse i n t mt \<in> insert (JoinResponse i\<^sub>0 n\<^sub>0 t\<^sub>0 None) messages" "i < i'" "t' \<prec> t"
    with JoinResponse_future assms
    show "ApplyResponse i' n t' \<notin> messages" by auto
  next
    fix i n t t'
    assume "JoinResponse i n t None \<in> messages \<or> (i, n, t) = (i\<^sub>0, n\<^sub>0, t\<^sub>0)" "t' \<prec> t"
    with JoinResponse_None assms show "ApplyResponse i n t' \<notin> messages" by auto
  next
    fix i n t mt
    assume "JoinResponse i n t mt \<in> ?messages'"
    hence "JoinResponse i n t mt \<in> messages \<or> (i, n, t, mt) = (i\<^sub>0, n\<^sub>0, t\<^sub>0, None)" by auto
    with JoinResponse_era show "\<exists>i'\<le>i. committed\<^sub>< i' \<and> era\<^sub>t t \<le> era\<^sub>i i'"
    proof (elim disjE)
      assume "(i, n, t, mt) = (i\<^sub>0, n\<^sub>0, t\<^sub>0, None)"
      with assms show ?thesis
        by (intro exI [where x = i\<^sub>0], auto simp add: committedTo_def isCommitted_def)
    qed
  next
    fix i t x assume "ApplyRequest i t x \<in> messages"
    from ApplyRequest_quorum [OF this]
    obtain q
      where q: "q\<in>Q (era\<^sub>t t)" "\<forall>n\<in>q. promised i n t"
        "prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q))" by blast

    from q
    show "\<exists>q\<in>Q (era\<^sub>t t). (\<forall>n\<in>q. promised' i n t) \<and> (prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q)))"
      by (intro bexI [where x = q] conjI ballI promised'I, auto)
  qed
qed


lemma (in zen) send_JoinResponse_Some:
  assumes "\<forall> i > i\<^sub>0. \<forall> t. ApplyResponse i n\<^sub>0 t \<notin> messages"
  assumes "ApplyResponse i\<^sub>0 n\<^sub>0 t\<^sub>0' \<in> messages"
  assumes "t\<^sub>0' \<prec> t\<^sub>0"
  assumes "\<forall> t'. ApplyResponse i\<^sub>0 n\<^sub>0 t' \<in> messages \<longrightarrow> t' \<preceq> t\<^sub>0'"
  assumes "\<forall> i < i\<^sub>0. \<exists> t. ApplyCommit i t \<in> messages"
  assumes "era\<^sub>t t\<^sub>0 = era\<^sub>i i\<^sub>0"
  shows   "zen (insert (JoinResponse i\<^sub>0 n\<^sub>0 t\<^sub>0 (Some t\<^sub>0')) messages)" (is "zen ?messages'")
proof -
  define promised' where "\<And>i n t. promised' i n t \<equiv> \<exists>i'\<le>i. \<exists>mt'. JoinResponse i' n t mt' \<in> ?messages'"
  have promised'I: "\<And>i n t. promised i n t \<Longrightarrow> promised' i n t" using promised'_def promised_def by auto

  define prevAccepted' where "\<And>i t ns. prevAccepted' i t ns \<equiv> {t'. \<exists> n \<in> ns. JoinResponse i n t (Some t') \<in> ?messages'}"

  have messages_simps:
    "\<And>i n t. (JoinResponse i n t None \<in> ?messages') = (JoinResponse i n t None \<in> messages)"
    "\<And>i n t t'. (JoinResponse i n t (Some t') \<in> ?messages') = (JoinResponse i n t (Some t') \<in> messages \<or> (i, n, t, t') = (i\<^sub>0, n\<^sub>0, t\<^sub>0, t\<^sub>0'))"
    "\<And>i t x. (ApplyRequest i t x \<in> ?messages') = (ApplyRequest i t x \<in> messages)"
    "\<And>i n t. (ApplyResponse i n t \<in> ?messages') = (ApplyResponse i n t \<in> messages)"
    "\<And>i t. (ApplyCommit i t \<in> ?messages') = (ApplyCommit i t \<in> messages)"
    by auto

  show ?thesis
    apply (unfold_locales)
                apply (fold prevAccepted'_def)
                apply (unfold messages_simps)
                apply (fold isCommitted_def v_def)
                apply (fold v\<^sub>c_def committedTo_def)
                apply (fold era\<^sub>i_def)
                apply (fold reconfig_def)
                apply (fold Q_def promised'_def)
    using JoinResponse_None  ApplyRequest_committedTo ApplyRequest_function finite_messages_insert ApplyResponse_ApplyRequest ApplyCommit_era  ApplyCommit_quorum 
  proof -

    from assms JoinResponse_future
    show "\<And>i i' n t t' mt. JoinResponse i n t mt \<in> insert (JoinResponse i\<^sub>0 n\<^sub>0 t\<^sub>0 (Some t\<^sub>0')) messages
      \<Longrightarrow> i < i' \<Longrightarrow> t' \<prec> t \<Longrightarrow> ApplyResponse i' n t' \<notin> messages" by auto

    from assms JoinResponse_era
    show "\<And>i n t mt. JoinResponse i n t mt \<in> insert (JoinResponse i\<^sub>0 n\<^sub>0 t\<^sub>0 (Some t\<^sub>0')) messages \<Longrightarrow> \<exists>i'\<le>i. committed\<^sub>< i' \<and> era\<^sub>t t \<le> era\<^sub>i i'"
      by (auto simp add: committedTo_def isCommitted_def)

    from assms JoinResponse_Some_lt
    show "\<And>i n t t'. JoinResponse i n t (Some t') \<in> messages \<or> (i, n, t, t') = (i\<^sub>0, n\<^sub>0, t\<^sub>0, t\<^sub>0') \<Longrightarrow> t' \<prec> t" by auto

    from assms JoinResponse_Some_ApplyResponse
    show "\<And>i n t t'. JoinResponse i n t (Some t') \<in> messages \<or> (i, n, t, t') = (i\<^sub>0, n\<^sub>0, t\<^sub>0, t\<^sub>0') \<Longrightarrow> ApplyResponse i n t' \<in> messages" by auto

    from assms JoinResponse_Some_max
    show "\<And>i n t t' t''. JoinResponse i n t (Some t') \<in> messages \<or> (i, n, t, t') = (i\<^sub>0, n\<^sub>0, t\<^sub>0, t\<^sub>0') \<Longrightarrow> t' \<prec> t'' \<Longrightarrow> t'' \<prec> t \<Longrightarrow> ApplyResponse i n t'' \<notin> messages"
      by (metis Pair_inject term_not_le_lt)

  next

    fix i t x assume "ApplyRequest i t x \<in> messages"
    from ApplyRequest_quorum [OF this]
    obtain q
      where q: "q\<in>Q (era\<^sub>t t)" "\<forall>n\<in>q. promised i n t"
        "prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q))" by blast

    {
      assume p: "n\<^sub>0 \<in> q" "i = i\<^sub>0" "t = t\<^sub>0" with q have "promised i\<^sub>0 n\<^sub>0 t\<^sub>0" by auto
      then obtain i' mt where r: "JoinResponse i' n\<^sub>0 t\<^sub>0 mt \<in> messages" "i' \<le> i\<^sub>0"
        by (auto simp add: promised_def)

      from r assms have "i' = i\<^sub>0" 
        using JoinResponse_future order.not_eq_order_implies_strict by blast

      moreover with r assms have "mt = Some t\<^sub>0'"
        by (metis JoinResponse_None JoinResponse_Some_ApplyResponse JoinResponse_Some_max le_term_def option.exhaust)

      moreover note p r
      ultimately have "JoinResponse i\<^sub>0 n\<^sub>0 t\<^sub>0 (Some t\<^sub>0') \<in> messages" by auto
    }

    hence prevAccepted_eq: "prevAccepted' i t q = prevAccepted i t q"
      by (auto simp add: prevAccepted_def prevAccepted'_def)

    from q
    show "\<exists>q\<in>Q (era\<^sub>t t). (\<forall>n\<in>q. promised' i n t) \<and> (prevAccepted' i t q = {} \<or> v i t = v i (maxTerm (prevAccepted' i t q)))"
      by (intro bexI [where x = q] conjI ballI promised'I, simp_all add: prevAccepted_eq)
  qed
qed

lemma (in zen) send_ApplyRequest:
  assumes "\<forall> x. ApplyRequest i\<^sub>0 t\<^sub>0 x \<notin> messages"
  assumes "\<forall> i < i\<^sub>0. \<exists> t. ApplyCommit i t \<in> messages"
  assumes "q \<in> Q (era\<^sub>t t\<^sub>0)"
  assumes "\<forall> n \<in> q. promised i\<^sub>0 n t\<^sub>0"
  assumes "prevAccepted i\<^sub>0 t\<^sub>0 q \<noteq> {} \<longrightarrow> x\<^sub>0 = v i\<^sub>0 (maxTerm (prevAccepted i\<^sub>0 t\<^sub>0 q))"
  shows "zen (insert (ApplyRequest i\<^sub>0 t\<^sub>0 x\<^sub>0) messages)" (is "zen ?messages'")
proof -

  have messages_simps:
    "\<And>i n t mt'. (JoinResponse i n t mt' \<in> ?messages') = (JoinResponse i n t mt' \<in> messages)"
    "\<And>i t x. (ApplyRequest i t x \<in> ?messages') = (ApplyRequest i t x \<in> messages \<or> (i, t, x) = (i\<^sub>0, t\<^sub>0, x\<^sub>0))"
    "\<And>i n t. (ApplyResponse i n t \<in> ?messages') = (ApplyResponse i n t \<in> messages)"
    "\<And>i t. (ApplyCommit i t \<in> ?messages') = (ApplyCommit i t \<in> messages)"
    by auto

  define v' where "\<And>i t. v' i t \<equiv> THE x. ApplyRequest i t x \<in> ?messages'"
  define v\<^sub>c' where "\<And>i. v\<^sub>c' i \<equiv> v' i (SOME t. ApplyCommit i t \<in> ?messages')"
  define era\<^sub>i' where "\<And>i. era\<^sub>i' i \<equiv> eraOfNat (card {j. j < i \<and> isReconfiguration (v\<^sub>c' j)})"
  define reconfig' where "\<And>e. reconfig' e \<equiv> THE i. isCommitted i \<and> isReconfiguration (v\<^sub>c' i) \<and> era\<^sub>i' i = e"
  define Q' where "\<And>e. Q' e \<equiv> case e of e\<^sub>0 \<Rightarrow> Q\<^sub>0 | nextEra e' \<Rightarrow> getConf (v\<^sub>c' (reconfig' e'))"

  have v'_eq: "\<And>i t. v' i t = (if (i, t) = (i\<^sub>0, t\<^sub>0) then x\<^sub>0 else v i t)"
  proof -
    fix i t
    show "?thesis i t"
    proof (cases "(i, t) = (i\<^sub>0, t\<^sub>0)")
      case False
      hence eq: "\<And>x. (ApplyRequest i t x \<in> ?messages') = (ApplyRequest i t x \<in> messages)" by auto
      from False show ?thesis by (unfold v'_def eq, auto simp add: v_def)
    next
      case True with assms have eq: "\<And>x. (ApplyRequest i t x \<in> ?messages') = (x = x\<^sub>0)" by auto
      from True show ?thesis by (unfold v'_def eq, auto)
    qed
  qed

  have v\<^sub>c'_eq: "\<And>i. isCommitted i \<Longrightarrow> v\<^sub>c' i = v\<^sub>c i"
  proof -
    fix i
    assume i: "isCommitted i"
    show "?thesis i"
    proof (cases "i = i\<^sub>0")
      case False
      with v'_eq show ?thesis by (simp add: v\<^sub>c_def v\<^sub>c'_def)
    next
      case True
      with v'_eq assms show ?thesis apply (simp add: v\<^sub>c_def v\<^sub>c'_def)
        by (metis ApplyCommit_ApplyRequest i isCommitted_def someI_ex)
    qed
  qed

  have era\<^sub>i'_eq: "\<And>i. committed\<^sub>< i \<Longrightarrow> era\<^sub>i' i = era\<^sub>i i"
  proof -
    fix i assume i: "committed\<^sub>< i"
    have "{j. j < i \<and> isReconfiguration (v\<^sub>c' j)} = {j. j < i \<and> isReconfiguration (v\<^sub>c j)}"
      using committedTo_def i v\<^sub>c'_eq by auto
    thus "?thesis i" by (auto simp add: era\<^sub>i_def era\<^sub>i'_def)
  qed

  have reconfig'_eq: "\<And>e. reconfig' e = reconfig e"
  proof -
    fix e
    have "\<And>i. (isCommitted i \<and> isReconfiguration (v\<^sub>c' i) \<and> era\<^sub>i' i = e)
            = (isCommitted i \<and> isReconfiguration (v\<^sub>c  i) \<and> era\<^sub>i  i = e)"
      using era\<^sub>i'_eq isCommitted_committedTo v\<^sub>c'_eq by auto
    thus "?thesis e" by (simp add: reconfig'_def reconfig_def)
  qed

  have Q'_eq: "\<And> i. committed\<^sub>< i \<Longrightarrow> Q' (era\<^sub>i i) = Q (era\<^sub>i i)"
  proof -
    fix i assume "committed\<^sub>< i" thus "?thesis i"
    proof (induct i)
      case 0 thus ?case by (simp add: Q_def era\<^sub>i_def Q'_def)
    next
      case (Suc i)
      from Suc.prems
      have eq: "Q' (era\<^sub>i i) = Q (era\<^sub>i i)" by (intro Suc.hyps, auto simp add: committedTo_def)
      show ?case
      proof (cases "isReconfiguration (v\<^sub>c i)")
        case False
        with eq era\<^sub>i_step show ?thesis by simp
      next
        case True
        with era\<^sub>i_step have nextEra: "era\<^sub>i (Suc i) = nextEra (era\<^sub>i i)" by simp

        show ?thesis
        proof (unfold nextEra, simp add: Q_def Q'_def reconfig'_eq,
            intro cong [OF refl, where f = getConf] v\<^sub>c'_eq reconfig_isCommitted)
          show "era\<^sub>i i < era\<^sub>i (Suc i)"
            using natOfEra_lt nextEra by fastforce
          from Suc.prems show "committed\<^sub>< (Suc i)" .
        qed
      qed
    qed
  qed

  show ?thesis
    apply (unfold_locales)
                apply (fold v'_def)
                apply (fold v\<^sub>c'_def)
                apply (unfold messages_simps)
                apply (fold isCommitted_def)
                apply (fold committedTo_def)
                apply (fold era\<^sub>i'_def)
                apply (fold reconfig'_def)
                apply (fold Q'_def promised_def prevAccepted_def)
  proof -
    from JoinResponse_future show "\<And>i i' n t t' mt. JoinResponse i n t mt \<in> messages \<Longrightarrow> i < i' \<Longrightarrow> t' \<prec> t \<Longrightarrow> ApplyResponse i' n t' \<notin> messages" .
    from JoinResponse_None show "\<And>i n t t'. JoinResponse i n t None \<in> messages \<Longrightarrow> t' \<prec> t \<Longrightarrow> ApplyResponse i n t' \<notin> messages" .
    from JoinResponse_Some_lt show "\<And>i n t t'. JoinResponse i n t (Some t') \<in> messages \<Longrightarrow> t' \<prec> t" .
    from JoinResponse_Some_ApplyResponse show "\<And>i n t t'. JoinResponse i n t (Some t') \<in> messages \<Longrightarrow> ApplyResponse i n t' \<in> messages" .
    from JoinResponse_Some_max show "\<And>i n t t' t''. JoinResponse i n t (Some t') \<in> messages \<Longrightarrow> t' \<prec> t'' \<Longrightarrow> t'' \<prec> t \<Longrightarrow> ApplyResponse i n t'' \<notin> messages" .
    from finite_messages_insert show "finite (insert (ApplyRequest i\<^sub>0 t\<^sub>0 x\<^sub>0) messages)" .

    from assms ApplyRequest_committedTo show "\<And>i t x. ApplyRequest i t x \<in> messages \<or> (i, t, x) = (i\<^sub>0, t\<^sub>0, x\<^sub>0) \<Longrightarrow> committed\<^sub>< i" 
      by (auto simp add: committedTo_def isCommitted_def)

    from assms ApplyRequest_function show "\<And>i t x x'. ApplyRequest i t x \<in> messages \<or> (i, t, x) = (i\<^sub>0, t\<^sub>0, x\<^sub>0) \<Longrightarrow> ApplyRequest i t x' \<in> messages \<or> (i, t, x') = (i\<^sub>0, t\<^sub>0, x\<^sub>0) \<Longrightarrow> x = x'"
      by auto

    from ApplyResponse_ApplyRequest show "\<And>i n t. ApplyResponse i n t \<in> messages \<Longrightarrow> \<exists>x. ApplyRequest i t x \<in> messages \<or> (i, t, x) = (i\<^sub>0, t\<^sub>0, x\<^sub>0)" by blast

    from ApplyCommit_era era\<^sub>i'_eq show "\<And>i t. ApplyCommit i t \<in> messages \<Longrightarrow> era\<^sub>i' i = era\<^sub>t t"
      apply (auto simp add: committedTo_def isCommitted_def)
      using era\<^sub>i'_eq isCommitted_committedTo isCommitted_def by fastforce

    show " \<And>i n t mt. JoinResponse i n t mt \<in> messages \<Longrightarrow> \<exists>i'\<le>i. committed\<^sub>< i' \<and> era\<^sub>t t \<le> era\<^sub>i' i'"
      using JoinResponse_era era\<^sub>i'_eq by force

  next
    fix i t
    assume a: "ApplyCommit i t \<in> messages"
    hence "committed\<^sub>< i" using ApplyCommit_ApplyRequest ApplyRequest_committedTo by blast
    hence "Q' (era\<^sub>i i) = Q (era\<^sub>i i)" by (simp add: Q'_eq)
    moreover from a have "era\<^sub>t t = era\<^sub>i i"
      using ApplyCommit_era by auto
    moreover note ApplyCommit_quorum [OF a]
    ultimately show "\<exists>q\<in>Q' (era\<^sub>t t). \<forall>n\<in>q. ApplyResponse i n t \<in> messages" by simp
  next



end
