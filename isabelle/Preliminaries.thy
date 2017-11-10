section \<open>Preliminaries\<close>

text \<open>We start with some definitions of the types involved.\<close>

theory Preliminaries
  imports Main
begin

subsection \<open>Eras\<close>

text \<open>Eras are numbered from $0$. To keep the types separate in the proof, we define a separate
type for them:\<close>

datatype Era = e\<^sub>0 | nextEra Era

text \<open>This is followed by some routine development to help the prover understand that they
behave like natural numbers. First, they are ordered:\<close>

text \<open>The isomorphism with the natural numbers is spelled out in full.\<close>

fun natOfEra :: "Era \<Rightarrow> nat" where
  "natOfEra e\<^sub>0 = 0" | "natOfEra (nextEra e) = Suc (natOfEra e)"
fun eraOfNat :: "nat \<Rightarrow> Era" where
  "eraOfNat 0 = e\<^sub>0" | "eraOfNat (Suc n) = nextEra (eraOfNat n)"

lemma eraOfNat_inv[simp]: "eraOfNat (natOfEra e) = e" by (induct e, simp_all)
lemma natOfEra_inv[simp]: "natOfEra (eraOfNat n) = n" by (induct n, simp_all)
lemma natOfEra_inj[simp]: "(natOfEra e\<^sub>1 = natOfEra e\<^sub>2) = (e\<^sub>1 = e\<^sub>2)" by (metis eraOfNat_inv)

instantiation Era :: linorder
begin
definition less_Era where "e\<^sub>1 < e\<^sub>2 \<equiv> natOfEra e\<^sub>1 < natOfEra e\<^sub>2"
definition less_eq_Era where "e\<^sub>1 \<le> e\<^sub>2 \<equiv> natOfEra e\<^sub>1 \<le> natOfEra e\<^sub>2"
instance proof
  fix e\<^sub>1 e\<^sub>2 :: Era
  show "e\<^sub>1 \<le> e\<^sub>2 \<Longrightarrow> e\<^sub>2 \<le> e\<^sub>1 \<Longrightarrow> e\<^sub>1 = e\<^sub>2"
    by (metis eq_iff eraOfNat_inv less_eq_Era_def)
qed (auto simp add: less_eq_Era_def less_Era_def)
end

lemma lt_e0[simp]: "e < e\<^sub>0 = False" by (auto simp add: less_Era_def)

subsection \<open>Terms\<close>

subsubsection \<open>Definitions\<close>

text \<open>Terms are pairs of an @{type Era} together with an \textit{election number} within the era.\<close>

datatype Term = Term Era nat

fun era\<^sub>t :: "Term \<Rightarrow> Era" where "era\<^sub>t (Term e _) = e"
fun termInEra :: "Term \<Rightarrow> nat" where "termInEra (Term _ n) = n"

text \<open>Terms are ordered lexicographically:\<close>

instantiation Term :: linorder
begin
definition less_Term where "t\<^sub>1 < t\<^sub>2 \<equiv> (t\<^sub>1, t\<^sub>2) \<in> measures [natOfEra \<circ> era\<^sub>t, termInEra]"
definition less_eq_Term where "(t\<^sub>1::Term) \<le> t\<^sub>2 \<equiv> (t\<^sub>1 < t\<^sub>2 \<or> t\<^sub>1 = t\<^sub>2)"
instance proof
  fix x y :: Term
  show "x \<le> y \<or> y \<le> x"
    apply (cases x, cases y)
    by (auto simp add: less_Term_def less_eq_Term_def)
qed (auto simp add: less_Term_def less_eq_Term_def)
end

lemma lt_term: "t\<^sub>1 < t\<^sub>2 = (era\<^sub>t t\<^sub>1 < era\<^sub>t t\<^sub>2
      \<or> (era\<^sub>t t\<^sub>1 = era\<^sub>t t\<^sub>2 \<and> (termInEra t\<^sub>1 < termInEra t\<^sub>2)))"
  by (cases t\<^sub>1, cases t\<^sub>2, simp add: less_Term_def less_Era_def)

lemma era\<^sub>t_mono: "t\<^sub>1 \<le> t\<^sub>2 \<Longrightarrow> era\<^sub>t t\<^sub>1 \<le> era\<^sub>t t\<^sub>2" using less_eq_Term_def lt_term by auto

text \<open>Terms support wellfounded induction:\<close>

lemma term_induct [case_names less]:
  fixes t :: Term
  assumes "\<And>t\<^sub>1. (\<forall> t\<^sub>2. t\<^sub>2 < t\<^sub>1 \<longrightarrow> P t\<^sub>2) \<Longrightarrow> P t\<^sub>1"
  shows "P t"
proof -
  have p: "{ (t\<^sub>1, t\<^sub>2). t\<^sub>1 < t\<^sub>2 } = measures [natOfEra \<circ> era\<^sub>t, termInEra]"
    by (auto simp add: less_Term_def)

  have term_lt_wf: "wf { (t\<^sub>1, t\<^sub>2). t\<^sub>1 < (t\<^sub>2 :: Term) }"
    by (unfold p, simp)

  show ?thesis
    using assms
    apply (rule wf_induct [OF term_lt_wf]) by auto
qed

subsubsection \<open>Maximum term of a set\<close>

text \<open>A function for finding the maximum term in a set is as follows.\<close>

definition maxTerm :: "Term set \<Rightarrow> Term"
  where "maxTerm S \<equiv> THE t. t \<in> S \<and> (\<forall> t' \<in> S. t' \<le> t)"

text \<open>It works correctly on finite and nonempty sets as follows:\<close>

lemma
  assumes finite: "finite S"
  shows maxTerm_mem: "S \<noteq> {} \<Longrightarrow> maxTerm S \<in> S"
    and maxTerm_max: "\<And> t'. t' \<in> S \<Longrightarrow> t' \<le> maxTerm S"
proof -
  presume "S \<noteq> {}"
  with assms
  obtain t where t: "t \<in> S" "\<And> t'. t' \<in> S \<Longrightarrow> t' \<le> t"
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
      obtain t' where t': "t' \<in> S" "\<forall> t'' \<in> S. t'' \<le> t'"
        by (meson False insert.hyps(3))

      from t'
      show ?thesis
      proof (intro insert.prems ballI)
        fix t'' assume t'': "t'' \<in> insert t S"
        show "t'' \<le> (if t \<le> t' then t' else t)"
        proof (cases "t'' = t")
          case False
          with t'' have "t'' \<in> S" by simp
          with t' have "t'' \<le> t'" by simp
          thus ?thesis by auto
        qed simp
      qed simp
    qed
  qed

  from t have "maxTerm S = t"
    by (unfold maxTerm_def, intro the_equality, simp_all add: eq_iff)

  with t show "maxTerm S \<in> S" "\<And>t'. t' \<in> S \<Longrightarrow> t' \<le> maxTerm S" by simp_all
qed auto

subsection \<open>Configurations and quorums\<close>

text \<open>Nodes are simply identified by a natural number.\<close>

datatype Node = Node nat

definition natOfNode :: "Node \<Rightarrow> nat" where "natOfNode node \<equiv> case node of Node n \<Rightarrow> n"
lemma natOfNode_Node[simp]: "natOfNode (Node n) = n" by (simp add: natOfNode_def)
lemma Node_natOfNode[simp]: "Node (natOfNode n) = n" by (cases n, simp add: natOfNode_def)
lemma natOfNode_inj[simp]: "(natOfNode n\<^sub>1 = natOfNode n\<^sub>2) = (n\<^sub>1 = n\<^sub>2)" by (metis Node_natOfNode)

text \<open>It is useful to be able to talk about whether sets-of-sets-of nodes mutually intersect or not.\<close>

definition intersects :: "Node set set \<Rightarrow> Node set set \<Rightarrow> bool" (infixl "\<frown>" 50)
  where "A \<frown> B \<equiv> \<forall> a \<in> A. \<forall> b \<in> B. a \<inter> b \<noteq> {}"

text \<open>A configuration of the system defines the sets of master-eligible nodes that can be counted as a quorum.
The initial configuration of the system is fixed to some arbitrary (valid) value.\<close>

definition Q\<^sub>0 :: "Node set set" where "Q\<^sub>0 \<equiv> SOME Q. Q \<frown> Q"

lemma Q\<^sub>0_intersects: "Q\<^sub>0 \<frown> Q\<^sub>0"
proof -
  define P :: "Node set set \<Rightarrow> bool" where "\<And>Q. P Q \<equiv> Q \<frown> Q"
  have Q\<^sub>0_eq: "Q\<^sub>0 = (SOME Q. P Q)" by (simp add: P_def Q\<^sub>0_def)
  have "P Q\<^sub>0" proof (unfold Q\<^sub>0_eq, intro someI)
    show "P {}" by (auto simp add: P_def intersects_def)
  qed
  thus ?thesis by (simp add: P_def)
qed

text \<open>A valid configuration is one in which all quorums intersect.\<close>

typedef Configuration = "{Q :: Node set set. Q \<frown> Q}"
proof (intro exI CollectI)
  show "{} \<frown> {}"
    by (simp add: intersects_def)
qed

subsection \<open>Values\<close>

text \<open>The model is a replicated state machine, with transitions that either do nothing, alter
the configuration of the system or set a new \texttt{ClusterState}. \texttt{ClusterState} values
are modelled simply as natural numbers.\<close>

datatype ClusterState = ClusterState nat

datatype Value
  = NoOp
  | Reconfigure Configuration
  | SetClusterState ClusterState

text \<open>Some useful definitions and lemmas follow.\<close>

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

end