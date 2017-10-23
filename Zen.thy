section \<open>Introduction\<close>

text \<open>This is a presentation of an Isabelle/HOL theory that describes, and proves correct, a
protocol for sharing \texttt{ClusterState} updates in Elasticsearch.\<close>

theory Zen
  imports Main
begin

section \<open>Preliminaries\<close>

subsection \<open>Eras\<close>

text \<open>Eras are numbered from $0$. To keep the types separate in the proof, we define a separate
type for them:\<close>

datatype Era = e\<^sub>0 | nextEra Era

text \<open>This is followed by some routine development to help the prover understand that they
behave like natural numbers. First, they are ordered:\<close>

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

text \<open>The isomorphism with the natural numbers is spelled out in full.\<close>

fun natOfEra :: "Era \<Rightarrow> nat" where
  "natOfEra e\<^sub>0 = 0" | "natOfEra (nextEra e) = Suc (natOfEra e)"
fun eraOfNat :: "nat \<Rightarrow> Era" where
  "eraOfNat 0 = e\<^sub>0" | "eraOfNat (Suc n) = nextEra (eraOfNat n)"

text \<open>A handful of lemmas that are useful for the simplifier follow.\<close>

lemma natOfEra_le[simp]: "(natOfEra e\<^sub>1 \<le> natOfEra e\<^sub>2) = (e\<^sub>1 \<le> e\<^sub>2)"
  apply (induct e\<^sub>1 arbitrary: e\<^sub>2, simp add: leI)
  by (metis (no_types, lifting) Suc_le_mono less_Era.elims(3) less_Era.simps(3) less_irrefl natOfEra.simps(1) natOfEra.simps(2) not_less zero_less_Suc)

lemma natOfEra_eq[simp]: "(natOfEra e\<^sub>1 = natOfEra e\<^sub>2) = (e\<^sub>1 = e\<^sub>2)"
  by (simp add: eq_iff)

lemma natOfEra_lt[simp]: "(natOfEra e\<^sub>1 < natOfEra e\<^sub>2) = (e\<^sub>1 < e\<^sub>2)"
  by (meson natOfEra_le not_less)

lemma eraOfNat_inv[simp]: "eraOfNat (natOfEra e) = e" by (induct e, simp_all)
lemma natOfEra_inv[simp]: "natOfEra (eraOfNat n) = n" by (induct n, simp_all)

lemma eraOfNat_le[simp]: "(eraOfNat n\<^sub>1 \<le> eraOfNat n\<^sub>2) = (n\<^sub>1 \<le> n\<^sub>2)" by (metis natOfEra_inv natOfEra_le)
lemma eraOfNat_lt[simp]: "(eraOfNat n\<^sub>1 < eraOfNat n\<^sub>2) = (n\<^sub>1 < n\<^sub>2)" by (metis natOfEra_inv natOfEra_lt)
lemma eraOfNat_eq[simp]: "(eraOfNat n\<^sub>1 = eraOfNat n\<^sub>2) = (n\<^sub>1 = n\<^sub>2)" by (metis natOfEra_inv)

lemma e0_le[simp]: "e\<^sub>0 \<le> e" by (simp add: leI)
lemma le_e0[simp]: "e \<le> e\<^sub>0 = (e = e\<^sub>0)" by (simp add: eq_iff)

section \<open>Terms\<close>

subsection \<open>Definitions\<close>

text \<open>Terms are pairs of an @{type Era} and an \textit{election number} within the era.\<close>

datatype Term = Term Era nat

fun era\<^sub>t :: "Term \<Rightarrow> Era" where "era\<^sub>t (Term e _) = e"
fun termInEra :: "Term \<Rightarrow> nat" where "termInEra (Term _ n) = n"

text \<open>Terms are ordered lexicographically:\<close>

definition lt_term :: "Term \<Rightarrow> Term \<Rightarrow> bool" (infixl "\<prec>" 50)
  where "t\<^sub>1 \<prec> t\<^sub>2 = (era\<^sub>t t\<^sub>1 < era\<^sub>t t\<^sub>2 \<or> (era\<^sub>t t\<^sub>1 = era\<^sub>t t\<^sub>2 \<and> termInEra t\<^sub>1 < termInEra t\<^sub>2))"

definition le_term :: "Term \<Rightarrow> Term \<Rightarrow> bool" (infixl "\<preceq>" 50)
  where "t\<^sub>1 \<preceq> t\<^sub>2 = (t\<^sub>1 \<prec> t\<^sub>2 \<or> t\<^sub>1 = t\<^sub>2)"

text \<open>A handful of lemmas that are useful for the simplifier follow.\<close>

lemma term_le_refl[simp]: "t \<preceq> t" by (simp add: le_term_def)

lemma term_lt_lt_trans[trans]:  "\<lbrakk> t\<^sub>1 \<prec> t\<^sub>2; t\<^sub>2 \<prec> t\<^sub>3 \<rbrakk> \<Longrightarrow> t\<^sub>1 \<prec> t\<^sub>3"
  by (smt Term.inject less_trans lt_term_def)

lemma term_lt_le_trans[trans]:  "\<lbrakk> t\<^sub>1 \<prec> t\<^sub>2; t\<^sub>2 \<preceq> t\<^sub>3 \<rbrakk> \<Longrightarrow> t\<^sub>1 \<prec> t\<^sub>3"
  by (metis le_term_def term_lt_lt_trans)

lemma term_le_lt_trans[trans]:  "\<lbrakk> t\<^sub>1 \<preceq> t\<^sub>2; t\<^sub>2 \<prec> t\<^sub>3 \<rbrakk> \<Longrightarrow> t\<^sub>1 \<prec> t\<^sub>3" using term_lt_lt_trans le_term_def by auto
lemma term_le_le_trans[trans]:  "\<lbrakk> t\<^sub>1 \<preceq> t\<^sub>2; t\<^sub>2 \<preceq> t\<^sub>3 \<rbrakk> \<Longrightarrow> t\<^sub>1 \<preceq> t\<^sub>3" using term_lt_lt_trans le_term_def by auto

lemma term_lt_le: "t\<^sub>1 \<prec> t\<^sub>2 \<Longrightarrow> t\<^sub>1 \<preceq> t\<^sub>2" using le_term_def by auto

lemma term_not_le_lt[simp]: "(\<not> (t\<^sub>1 \<preceq> t\<^sub>2)) = (t\<^sub>2 \<prec> t\<^sub>1)"
  by (metis Term.exhaust era\<^sub>t.simps le_term_def lt_term_def not_less_iff_gr_or_eq termInEra.simps)

lemma era\<^sub>t_mono: "t\<^sub>1 \<preceq> t\<^sub>2 \<Longrightarrow> era\<^sub>t t\<^sub>1 \<le> era\<^sub>t t\<^sub>2" using le_term_def lt_term_def by auto

text \<open>Importantly, this shows how to do induction over the terms:\<close>

lemma term_induct [case_names less]:
  assumes "\<And>t\<^sub>1. (\<forall> t\<^sub>2. t\<^sub>2 \<prec> t\<^sub>1 \<longrightarrow> P t\<^sub>2) \<Longrightarrow> P t\<^sub>1"
  shows "P t"
proof -
  have term_lt_wf: "wf { (t\<^sub>1, t\<^sub>2). t\<^sub>1 \<prec> t\<^sub>2 }"
  proof -
    have "{ (t\<^sub>1, t\<^sub>2). t\<^sub>1 \<prec> t\<^sub>2 } = measures [natOfEra \<circ> era\<^sub>t, termInEra]"
      by (simp add: measures_def inv_image_def lt_term_def)
    thus ?thesis by simp
  qed

  show ?thesis
    using assms
    apply (rule wf_induct [OF term_lt_wf])
    by simp
qed

subsection \<open>Maximum term of a set\<close>

text \<open>A function for finding the maximum term in a set is as follows.\<close>

definition maxTerm :: "Term set \<Rightarrow> Term"
  where "maxTerm S = (THE t. t \<in> S \<and> (\<forall> t' \<in> S. t' \<preceq> t))"

text \<open>It works on finite and nonempty sets, which is sufficient.\<close>

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

text \<open>Nodes are simply identified by a natural number.\<close>

datatype Node = Node nat

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

section \<open>One-slot consistency\<close>

text \<open>The replicated state machine determines the values that are committed in each of a sequence
of \textit{slots}. Each slot runs a logically-separate consensus algorithm which is shown to be
consistent here. Further below, the protocol is shown to refine this slot-by-slot model correctly.\<close>

text \<open>Consistency is shown to follow from the invariants listed below. Further below, the protocol
is shown to preserve these invariants in each step, which means it is not enormously important
to understand these in detail.\<close>

locale oneSlot =
  (* basic functions *)
  fixes Q :: "Term \<Rightarrow> Node set set"
  fixes v :: "Term \<Rightarrow> Value"
    (* message-sent predicates *)
  fixes promised\<^sub>f :: "Node \<Rightarrow> Term \<Rightarrow> bool"
  fixes promised\<^sub>b :: "Node \<Rightarrow> Term \<Rightarrow> Term \<Rightarrow> bool"
  fixes proposed :: "Term \<Rightarrow> bool"
  fixes accepted :: "Node \<Rightarrow> Term \<Rightarrow> bool"
  fixes committed :: "Term \<Rightarrow> bool"
    (* other definitions *)
  fixes promised :: "Node \<Rightarrow> Term \<Rightarrow> bool"
  defines "promised n t \<equiv> promised\<^sub>f n t \<or> (\<exists> t'. promised\<^sub>b n t t')"
  fixes prevAccepted :: "Term \<Rightarrow> Node set \<Rightarrow> Term set"
  defines "prevAccepted t ns \<equiv> {t'. \<exists> n \<in> ns. promised\<^sub>b n t t'}"
    (* invariants *)
  assumes Q_intersects: "\<lbrakk> proposed t\<^sub>1; committed t\<^sub>2; t\<^sub>2 \<preceq> t\<^sub>1 \<rbrakk> \<Longrightarrow> Q t\<^sub>1 \<frown> Q t\<^sub>2"
  assumes Q_nonempty: "q \<in> Q t \<Longrightarrow> q \<noteq> {}"
  assumes promised\<^sub>f: "\<lbrakk> promised\<^sub>f n t; t' \<prec> t \<rbrakk> \<Longrightarrow> \<not> accepted n t'"
  assumes promised\<^sub>b_lt: "promised\<^sub>b n t t' \<Longrightarrow> t' \<prec> t"
  assumes promised\<^sub>b_accepted: "promised\<^sub>b n t t' \<Longrightarrow> accepted n t'"
  assumes promised\<^sub>b_max: "\<lbrakk> promised\<^sub>b n t t'; t' \<prec> t''; t'' \<prec> t \<rbrakk>
   \<Longrightarrow> \<not> accepted n t''"
  assumes proposed: "proposed t
     \<Longrightarrow> \<exists> q \<in> Q t. (\<forall> n \<in> q. promised n t)
                     \<and> (prevAccepted t q = {}
                          \<or> v t = v (maxTerm (prevAccepted t q)))"
  assumes proposed_finite: "finite {t. proposed t}"
  assumes accepted: "accepted n t \<Longrightarrow> proposed t"
  assumes committed: "committed t \<Longrightarrow> \<exists> q \<in> Q t. \<forall> n \<in> q. accepted n t"

lemma (in oneSlot) prevAccepted_proposed: "prevAccepted t ns \<subseteq> {t. proposed t}"
  using accepted prevAccepted_def promised\<^sub>b_accepted by fastforce

lemma (in oneSlot) prevAccepted_finite: "finite (prevAccepted p ns)"
  using prevAccepted_proposed proposed_finite by (meson rev_finite_subset)

text \<open>The heart of the consistency proof is property P2b from \textit{Paxos made simple} by Lamport:\<close>

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

text \<open>From this, it follows that any two committed values are equal as desired.\<close>

lemma (in oneSlot) consistent:
  assumes "committed t\<^sub>1" and "committed t\<^sub>2"
  shows "v t\<^sub>1 = v t\<^sub>2"
  by (metis Q_nonempty accepted all_not_in_conv assms committed le_term_def p2b term_not_le_lt)

text \<open>It will be useful later to know the conditions under which a value in a term can be committed,
which is spelled out here:\<close>

lemma (in oneSlot) commit:
  assumes q_quorum: "q \<in> Q t\<^sub>0"
  assumes q_accepted: "\<And>n. n \<in> q \<Longrightarrow> accepted n t\<^sub>0"
  assumes intersects: "\<And>t. proposed t \<Longrightarrow> t\<^sub>0 \<preceq> t \<Longrightarrow> Q t \<frown> Q t\<^sub>0"
  defines "committed' t \<equiv> committed t \<or> t = t\<^sub>0"
  shows "oneSlot Q v promised\<^sub>f promised\<^sub>b proposed accepted committed'"
  by (smt committed'_def intersects oneSlot_axioms oneSlot_def q_accepted q_quorum)

section \<open>Zen\<close>

text \<open>Zen is the protocol used to replicate chosen values, including reconfigurations. The
proven-safe core of the protocol works by sending messages as follows. The remainder of the
protocol may send other messages too, and may drop or reorder any of these messages, but
must not send these messages itself to ensure safety. The @{type nat} parameter to each
message refers to a slot number.\<close>

datatype Message
  = JoinResponse nat Node Term "Term option"
  | ApplyRequest nat Term Value
  | ApplyResponse nat Node Term
  | ApplyCommit nat Term

text \<open>Some prose descriptions of these messages follows, in order to give a bit more of an
intuitive understanding of their purposes. A precise description of the conditions under
which each kind of message can be sent is further below.\<close>

text \<open>The message @{term "JoinResponse i n t mt'"} may be sent by any node @{term n} during an
election. It indicates that the sender knows all committed values for slots strictly below
@{term i}, and that the sender will no longer vote in any term prior to @{term t}. The
field @{term mt'} is either @{term None} or @{term "Some t'"}. In the former case
this indicates that the node has not yet sent any @{term ApplyResponse} message in slot @{term i},
and in the latter case it indicates that the largest term in which it has previously sent an
@{term ApplyResponse} message is @{term t'}. All nodes must avoid sending a @{term JoinResponse}
message to two different masters in the same term. The trigger for sending this message is solely
a liveness concern and therefore is out of the scope of this model.\<close>

text \<open>The message @{term "ApplyRequest i t v"} may be sent by the elected master of term @{term t}
to request the other master-eligible nodes to vote for value @{term v} to be committed in
slot @{term i}.\<close>

text \<open>The message @{term "ApplyResponse i n t"} may be sent by node @{term n} in response
to the corresponding @{term ApplyRequest} message, indicating that the sender votes for
the value proposed by the master of term @{term t} to be committed in slot @{term i}.\<close>

text \<open>The message @{term "ApplyCommit i t"} indicates that the value proposed by the master of term
@{term t} in slot @{term i} received a quorum of votes and is therefore committed.\<close>

text \<open>The abstract model of Zen keeps track of the set of all messages that have ever been sent,
and asserts that this set obeys certain invariants, listed below. Further below, it will
be shown that these invariants imply that each slot obeys the @{term oneSlot} invariants above
and hence that each slot cannot see inconsistent committed values.\<close>

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
  defines "reconfig e
      \<equiv> THE i. isCommitted i \<and> isReconfiguration (v\<^sub>c i) \<and> era\<^sub>i i = e"
    (* the configuration of an era *)
  fixes Q :: "Era \<Rightarrow> Node set set"
  defines "Q e \<equiv> case e of e\<^sub>0 \<Rightarrow> Q\<^sub>0 | nextEra e' \<Rightarrow> getConf (v\<^sub>c (reconfig e'))"
    (* predicate to say whether an applicable JoinResponse has been sent *)
  fixes promised :: "nat \<Rightarrow> Node \<Rightarrow> Term \<Rightarrow> bool"
  defines "promised i n t \<equiv> \<exists> i' \<le> i. \<exists> mt'. JoinResponse i' n t mt' \<in> messages"
    (* set of previously-accepted terms *)
  fixes prevAccepted :: "nat \<Rightarrow> Term \<Rightarrow> Node set \<Rightarrow> Term set"
  defines "prevAccepted i t ns
      \<equiv> {t'. \<exists> n \<in> ns. JoinResponse i n t (Some t') \<in> messages}"
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
    "\<And>i n t t'. JoinResponse i n t (Some t') \<in> messages
      \<Longrightarrow> ApplyResponse i n t' \<in> messages"
  assumes JoinResponse_Some_max:
    "\<And>i n t t' t''. \<lbrakk> JoinResponse i n t (Some t') \<in> messages; t' \<prec> t''; t'' \<prec> t \<rbrakk>
                        \<Longrightarrow> ApplyResponse i n t'' \<notin> messages"
  assumes JoinResponse_era:
    "\<And>i n t mt. JoinResponse i n t mt \<in> messages
      \<Longrightarrow> \<exists> i' \<le> i. committedTo i' \<and> era\<^sub>t t \<le> era\<^sub>i i'"
  assumes ApplyRequest_era:
    "\<And>i t x. ApplyRequest i t x \<in> messages \<Longrightarrow> era\<^sub>i i = era\<^sub>t t"
  assumes ApplyRequest_committedTo:
    "\<And>i t x. ApplyRequest i t x \<in> messages \<Longrightarrow> committedTo i"
  assumes ApplyRequest_quorum:
    "\<And>i t x. ApplyRequest i t x \<in> messages
      \<Longrightarrow> \<exists> q \<in> Q (era\<^sub>t t). (\<forall> n \<in> q. promised i n t) \<and>
            (prevAccepted i t q = {}
                \<or> v i t = v i (maxTerm (prevAccepted i t q)))"
  assumes ApplyRequest_function:
    "\<And>i t x x'. \<lbrakk> ApplyRequest i t x \<in> messages; ApplyRequest i t x' \<in> messages \<rbrakk>
       \<Longrightarrow> x = x'"
  assumes finite_messages:
    "finite messages"
  assumes ApplyResponse_ApplyRequest:
    "\<And>i n t. ApplyResponse i n t \<in> messages \<Longrightarrow> \<exists> x. ApplyRequest i t x \<in> messages"
  assumes ApplyCommit_quorum:
    "\<And>i t. ApplyCommit i t \<in> messages
                        \<Longrightarrow> \<exists> q \<in> Q (era\<^sub>t t). \<forall> n \<in> q. ApplyResponse i n t \<in> messages"

subsection \<open>Utility lemmas\<close>

text \<open>Some results that are useful later:\<close>

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

lemma (in zen) ApplyRequest_JoinResponse:
  assumes "ApplyRequest i t x \<in> messages"
  obtains i' n mt' where "i' \<le> i" "JoinResponse i' n t mt' \<in> messages"
  by (meson ApplyRequest_quorum Q_member_member assms promised_def)

lemma (in zen) finite_prevAccepted: "finite (prevAccepted i t ns)"
proof -
  fix t\<^sub>0
  define f where "f \<equiv> \<lambda> m. case m of JoinResponse i n t (Some t') \<Rightarrow> t' | _ \<Rightarrow> t\<^sub>0"
  have "prevAccepted i t ns \<subseteq> f ` messages"
    apply (simp add: prevAccepted_def f_def, intro subsetI)
    using image_iff by fastforce
  with finite_messages show ?thesis using finite_surj by auto
qed

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

lemma (in zen) era\<^sub>i_contiguous:
  assumes "e \<le> era\<^sub>i i"
  shows "\<exists> i' \<le> i. era\<^sub>i i' = e"
  using assms
proof (induct i)
  case 0
  then show ?case by (auto simp add: era\<^sub>i_def)
next
  case (Suc i)
  then show ?case
    by (metis era\<^sub>i_step le_SucI less_Suc_eq_le less_eq_Era_def natOfEra.simps(2) natOfEra_le natOfEra_lt order_refl)
qed

lemma (in zen) ApplyResponse_era:
  assumes "ApplyResponse i n t \<in> messages"
  shows "era\<^sub>t t = era\<^sub>i i"
  using assms ApplyRequest_era ApplyResponse_ApplyRequest by metis

lemma (in zen) ApplyCommit_era:
  assumes "ApplyCommit i t \<in> messages"
  shows "era\<^sub>t t = era\<^sub>i i"
  by (meson ApplyResponse_era assms ApplyCommit_ApplyResponse)

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

lemma (in zen) reconfig_eq:
  assumes "committed\<^sub>< i" "e < era\<^sub>i i"
  assumes "isReconfiguration (v\<^sub>c j)"
  assumes "era\<^sub>i j = e"
  shows "j = reconfig e"
  by (metis assms era\<^sub>i_mono era\<^sub>i_step le_neq_implies_less lessI natOfEra.simps(2) natOfEra_lt not_le not_less_eq_eq reconfig_era reconfig_isReconfiguration)

lemma (in zen) promised_long_def: "promised i n t
     \<equiv> (JoinResponse i n t None \<in> messages
           \<or> (\<exists>i'<i. \<exists>mt'. JoinResponse i' n t mt' \<in> messages))
           \<or> (\<exists>t'. JoinResponse i n t (Some t') \<in> messages)"
  using option.exhaust by (smt nat_less_le not_le promised_def)

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

subsection \<open>Relationship to @{term oneSlot}\<close>

text \<open>This shows that each slot @{term i} in Zen satisfies the assumptions of the
@{term oneSlot} model above.\<close>

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

  from t\<^sub>1 ApplyRequest_era have "era\<^sub>t t\<^sub>1 = era\<^sub>i i" by simp
  also from t\<^sub>2 have "... = era\<^sub>t t\<^sub>2" using ApplyCommit_era by auto
  finally show "(Q \<circ> era\<^sub>t) t\<^sub>1 \<frown> (Q \<circ> era\<^sub>t) t\<^sub>2" by (simp add: Q_intersects)
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

text \<open>From this it follows that all committed values are equal.\<close>

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

subsection \<open>Preserving invariants\<close>

text \<open>The statement @{term "zen M"} indicates that the set @{term M} of messages satisfies
the invariants of @{term zen}, and therefore all committed values are equal. Lemmas that are
proven ``in zen'' include the variable @{term messages} along with a silent assumption
@{term "zen messages"} and show from this that some modified set of messages also satisfies the
invariants.\<close>

subsubsection \<open>Initial state\<close>

text \<open>When no messages have been sent, the invariants hold:\<close>

lemma shows zen_initial_state: "zen {}" by (unfold_locales, auto)

subsubsection \<open>Sending @{term JoinResponse} messages\<close>

text \<open>@{term "JoinResponse i\<^sub>0 n\<^sub>0 t\<^sub>0 None"} can be sent under these conditions:\<close>

lemma (in zen) send_JoinResponse_None:
  assumes "\<forall> i \<ge> i\<^sub>0. \<forall> t. ApplyResponse i n\<^sub>0 t \<notin> messages"
    (* first-uncommitted slot and the era is ok *)
  assumes "\<forall> i < i\<^sub>0. \<exists> t. ApplyCommit i t \<in> messages"
  assumes "era\<^sub>t t\<^sub>0 = era\<^sub>i i\<^sub>0"
    (* *)
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
    using ApplyResponse_ApplyRequest ApplyRequest_era ApplyCommit_quorum ApplyRequest_function
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

text \<open>@{term "JoinResponse i\<^sub>0 n\<^sub>0 t\<^sub>0 (Some t\<^sub>0')"} can be sent under these conditions:\<close>

lemma (in zen) send_JoinResponse_Some:
  assumes "\<forall> i > i\<^sub>0. \<forall> t. ApplyResponse i n\<^sub>0 t \<notin> messages"
  assumes "ApplyResponse i\<^sub>0 n\<^sub>0 t\<^sub>0' \<in> messages"
  assumes "t\<^sub>0' \<prec> t\<^sub>0"
  assumes "\<forall> t'. ApplyResponse i\<^sub>0 n\<^sub>0 t' \<in> messages \<longrightarrow> t' \<preceq> t\<^sub>0'"
    (* first-uncommitted slot and the era is ok *)
  assumes "\<forall> i < i\<^sub>0. \<exists> t. ApplyCommit i t \<in> messages"
  assumes "era\<^sub>t t\<^sub>0 = era\<^sub>i i\<^sub>0"
    (* *)
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
    using JoinResponse_None  ApplyRequest_committedTo ApplyRequest_function finite_messages_insert
      ApplyResponse_ApplyRequest ApplyRequest_era  ApplyCommit_quorum 
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

subsubsection \<open>Sending @{term ApplyRequest} messages\<close>

text \<open>@{term "ApplyRequest i\<^sub>0 t\<^sub>0 x\<^sub>0"} can be sent under these conditions\<close>

lemma (in zen) send_ApplyRequest:
  assumes "\<forall> x. ApplyRequest i\<^sub>0 t\<^sub>0 x \<notin> messages"
  assumes "\<forall> i < i\<^sub>0. \<exists> t. ApplyCommit i t \<in> messages"
  assumes "era\<^sub>t t\<^sub>0 = era\<^sub>i i\<^sub>0"
  assumes "q \<in> Q (era\<^sub>t t\<^sub>0)"
  assumes "\<forall> n \<in> q. \<exists> i \<le> i\<^sub>0. \<exists> mt'. JoinResponse i n t\<^sub>0 mt' \<in> messages"
  assumes "prevAccepted i\<^sub>0 t\<^sub>0 q \<noteq> {}
    \<longrightarrow> x\<^sub>0 = v i\<^sub>0 (maxTerm (prevAccepted i\<^sub>0 t\<^sub>0 q))"
  shows "zen (insert (ApplyRequest i\<^sub>0 t\<^sub>0 x\<^sub>0) messages)" (is "zen ?messages'")
proof -

  have quorum_promised: "\<forall>n\<in>q. promised i\<^sub>0 n t\<^sub>0"
    by (simp add: assms promised_def)

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

  have v_eq: "\<And>i t. v' i t = (if (i, t) = (i\<^sub>0, t\<^sub>0) then x\<^sub>0 else v i t)"
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

  have v\<^sub>c_eq: "\<And>i. isCommitted i \<Longrightarrow> v\<^sub>c' i = v\<^sub>c i"
  proof -
    fix i
    assume i: "isCommitted i"
    show "?thesis i"
    proof (cases "i = i\<^sub>0")
      case False
      with v_eq show ?thesis by (simp add: v\<^sub>c_def v\<^sub>c'_def)
    next
      case True
      with v_eq assms show ?thesis apply (simp add: v\<^sub>c_def v\<^sub>c'_def)
        by (metis ApplyCommit_ApplyRequest i isCommitted_def someI_ex)
    qed
  qed

  have era\<^sub>i_eq: "\<And>i. committed\<^sub>< i \<Longrightarrow> era\<^sub>i' i = era\<^sub>i i"
  proof -
    fix i assume i: "committed\<^sub>< i"
    have "{j. j < i \<and> isReconfiguration (v\<^sub>c' j)} = {j. j < i \<and> isReconfiguration (v\<^sub>c j)}"
      using committedTo_def i v\<^sub>c_eq by auto
    thus "?thesis i" by (auto simp add: era\<^sub>i_def era\<^sub>i'_def)
  qed

  have reconfig'_eq: "\<And>e. reconfig' e = reconfig e"
  proof -
    fix e
    have "\<And>i. (isCommitted i \<and> isReconfiguration (v\<^sub>c' i) \<and> era\<^sub>i' i = e)
            = (isCommitted i \<and> isReconfiguration (v\<^sub>c  i) \<and> era\<^sub>i  i = e)"
      using era\<^sub>i_eq isCommitted_committedTo v\<^sub>c_eq by auto
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
            intro cong [OF refl, where f = getConf] v\<^sub>c_eq reconfig_isCommitted)
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
    using  JoinResponse_future JoinResponse_None  JoinResponse_Some_lt JoinResponse_Some_ApplyResponse  JoinResponse_Some_max  finite_messages_insert 
  proof -
    from assms ApplyRequest_committedTo show committedTo: "\<And>i t x. ApplyRequest i t x \<in> messages \<or> (i, t, x) = (i\<^sub>0, t\<^sub>0, x\<^sub>0) \<Longrightarrow> committed\<^sub>< i" 
      by (auto simp add: committedTo_def isCommitted_def)

    from assms ApplyRequest_function show "\<And>i t x x'. ApplyRequest i t x \<in> messages \<or> (i, t, x) = (i\<^sub>0, t\<^sub>0, x\<^sub>0) \<Longrightarrow> ApplyRequest i t x' \<in> messages \<or> (i, t, x') = (i\<^sub>0, t\<^sub>0, x\<^sub>0) \<Longrightarrow> x = x'"
      by auto

    from ApplyResponse_ApplyRequest show "\<And>i n t. ApplyResponse i n t \<in> messages \<Longrightarrow> \<exists>x. ApplyRequest i t x \<in> messages \<or> (i, t, x) = (i\<^sub>0, t\<^sub>0, x\<^sub>0)" by blast

    from ApplyRequest_era era\<^sub>i_eq have "\<And>i t x. ApplyRequest i t x \<in> messages \<Longrightarrow> era\<^sub>i' i = era\<^sub>t t"
      apply (auto simp add: committedTo_def isCommitted_def)
      using era\<^sub>i_eq isCommitted_committedTo isCommitted_def 
      by (simp add: ApplyRequest_committedTo)

    with assms committedTo show "\<And>i t x. ApplyRequest i t x \<in> messages \<or> (i, t, x) = (i\<^sub>0, t\<^sub>0, x\<^sub>0) \<Longrightarrow> era\<^sub>i' i = era\<^sub>t t"
      by (metis Pair_inject era\<^sub>i_eq)

    show "\<And>i n t mt. JoinResponse i n t mt \<in> messages \<Longrightarrow> \<exists>i'\<le>i. committed\<^sub>< i' \<and> era\<^sub>t t \<le> era\<^sub>i' i'"
      using JoinResponse_era era\<^sub>i_eq by force

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
    fix i t x
    assume "ApplyRequest i t x \<in> messages \<or> (i, t, x) = (i\<^sub>0, t\<^sub>0, x\<^sub>0)"
    thus "\<exists>q\<in>Q' (era\<^sub>t t). (\<forall>n\<in>q. promised i n t) \<and> (prevAccepted i t q = {} \<or> v' i t = v' i (maxTerm (prevAccepted i t q)))"
    proof (elim disjE)
      assume a: "ApplyRequest i t x \<in> messages"

      from ApplyRequest_quorum [OF this]
      obtain q where q: "q \<in> Q (era\<^sub>t t)" "\<forall> n \<in> q. promised i n t"
        and disj: "prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q))" by blast

      from era\<^sub>i_contiguous ApplyRequest_era a
      obtain i' where "era\<^sub>i i' = era\<^sub>t t" and i':"i' \<le> i" by blast
      hence era_eq: "era\<^sub>t t = era\<^sub>i i'" by simp

      have Q_eq: "Q' (era\<^sub>t t) = Q (era\<^sub>t t)"
        using i' ApplyRequest_committedTo [OF a]
        by (unfold era_eq, intro Q'_eq, auto simp add: committedTo_def)

      have v_eq1: "v' i t = v i t" using a assms v_eq by auto

      show ?thesis
      proof (cases "prevAccepted i t q = {}")
        case True with q show ?thesis by (intro bexI [of _ q], simp_all add: Q_eq v_eq1)
      next
        case False
        have "maxTerm (prevAccepted i t q) \<in> prevAccepted i t q"
          by (intro maxTerm_mem finite_prevAccepted False)
        hence v_eq2: "v' i (maxTerm (prevAccepted i t q)) = v i (maxTerm (prevAccepted i t q))"
          apply (unfold v_eq, simp)
          by (smt assms(1) mem_Collect_eq prevAccepted_def zen.ApplyResponse_ApplyRequest zen.JoinResponse_Some_ApplyResponse zen_axioms)
        from q disj show ?thesis
          by (intro bexI [of _ q], simp_all add: Q_eq v_eq1 v_eq2)
      qed
    next
      assume "(i, t, x) = (i\<^sub>0, t\<^sub>0, x\<^sub>0)"
      hence fixed_simps: "i = i\<^sub>0" "t = t\<^sub>0" "x = x\<^sub>0" "v' i\<^sub>0 t\<^sub>0 = x\<^sub>0" by (simp_all add: v_eq)

      obtain i' where era_eq: "era\<^sub>t t\<^sub>0 = era\<^sub>i i'" "i' \<le> i"
        by (metis (no_types, lifting) JoinResponse_era Q_member_member assms(5) assms(4) dual_order.trans era\<^sub>i_contiguous fixed_simps(1))
      hence "Q' (era\<^sub>t t\<^sub>0) = Q (era\<^sub>t t\<^sub>0)"
        apply (unfold era_eq, intro Q'_eq)
        by (simp add: assms(2) committedTo_def fixed_simps(1) isCommitted_def)
      note fixed_simps = fixed_simps this

      show "\<exists>q\<in>Q' (era\<^sub>t t). (\<forall>n\<in>q. promised i n t) \<and> (prevAccepted i t q = {} \<or> v' i t = v' i (maxTerm (prevAccepted i t q)))"
      proof (unfold fixed_simps, intro bexI [where x = q] conjI quorum_promised assms)

        from assms
        show "prevAccepted i\<^sub>0 t\<^sub>0 q = {} \<or> x\<^sub>0 = v' i\<^sub>0 (maxTerm (prevAccepted i\<^sub>0 t\<^sub>0 q))"
          by (cases "maxTerm (prevAccepted i\<^sub>0 t\<^sub>0 q) = t\<^sub>0", auto simp add: v_eq)
      qed
    qed
  qed
qed

subsubsection \<open>Sending @{term ApplyRequest} messages\<close>

text \<open>@{term "ApplyResponse i\<^sub>0 n\<^sub>0 t\<^sub>0"} can be sent in response to an @{term ApplyRequest}
as long as a @{term JoinResponse} for a later term has not been sent:\<close>

lemma (in zen) send_ApplyResponse:
  assumes "ApplyRequest i\<^sub>0 t\<^sub>0 x\<^sub>0 \<in> messages"
  assumes "\<forall> i t mt'. JoinResponse i n\<^sub>0 t mt' \<in> messages \<longrightarrow> t \<preceq> t\<^sub>0"
  shows "zen (insert (ApplyResponse i\<^sub>0 n\<^sub>0 t\<^sub>0) messages)" (is "zen ?messages'")
proof -

  have messages_simps:
    "\<And>i n t mt'. (JoinResponse i n t mt' \<in> ?messages') = (JoinResponse i n t mt' \<in> messages)"
    "\<And>i t x. (ApplyRequest i t x \<in> ?messages') = (ApplyRequest i t x \<in> messages)"
    "\<And>i n t. (ApplyResponse i n t \<in> ?messages') = (ApplyResponse i n t \<in> messages \<or> (i, n, t) = (i\<^sub>0, n\<^sub>0, t\<^sub>0))"
    "\<And>i t. (ApplyCommit i t \<in> ?messages') = (ApplyCommit i t \<in> messages)"
    by auto

  show ?thesis
    apply (unfold_locales)
                apply (unfold messages_simps)
                apply (fold prevAccepted_def)
                apply (fold isCommitted_def v_def)
                apply (fold v\<^sub>c_def committedTo_def)
                apply (fold era\<^sub>i_def)
                apply (fold reconfig_def)
                apply (fold Q_def promised_def)
    using JoinResponse_Some_lt JoinResponse_era ApplyRequest_committedTo ApplyRequest_quorum
      ApplyRequest_function finite_messages_insert ApplyRequest_era
  proof -
    show "\<And>i i' n t t' mt. JoinResponse i n t mt \<in> messages \<Longrightarrow> i < i' \<Longrightarrow> t' \<prec> t \<Longrightarrow> \<not> (ApplyResponse i' n t' \<in> messages \<or> (i', n, t') = (i\<^sub>0, n\<^sub>0, t\<^sub>0))"
      by (metis JoinResponse_future Pair_inject assms(2) dual_order.strict_implies_order promised_def term_not_le_lt)
    show "\<And>i n t t'. JoinResponse i n t None \<in> messages \<Longrightarrow> t' \<prec> t \<Longrightarrow> \<not> (ApplyResponse i n t' \<in> messages \<or> (i, n, t') = (i\<^sub>0, n\<^sub>0, t\<^sub>0))" 
      by (metis JoinResponse_None assms(2) prod.inject term_not_le_lt)
    show "\<And>i n t t'. JoinResponse i n t (Some t') \<in> messages \<Longrightarrow> ApplyResponse i n t' \<in> messages \<or> (i, n, t') = (i\<^sub>0, n\<^sub>0, t\<^sub>0)" 
      using JoinResponse_Some_ApplyResponse by blast
    show "\<And>i n t t' t''. JoinResponse i n t (Some t') \<in> messages \<Longrightarrow> t' \<prec> t'' \<Longrightarrow> t'' \<prec> t \<Longrightarrow> \<not> (ApplyResponse i n t'' \<in> messages \<or> (i, n, t'') = (i\<^sub>0, n\<^sub>0, t\<^sub>0))" 
      by (metis JoinResponse_Some_max assms(2) prod.inject term_not_le_lt)
    show "\<And>i n t. ApplyResponse i n t \<in> messages \<or> (i, n, t) = (i\<^sub>0, n\<^sub>0, t\<^sub>0) \<Longrightarrow> \<exists>x. ApplyRequest i t x \<in> messages"
      using ApplyResponse_ApplyRequest assms(1) by blast
    show "\<And>i t. ApplyCommit i t \<in> messages \<Longrightarrow> \<exists>q\<in>Q (era\<^sub>t t). \<forall>n\<in>q. ApplyResponse i n t \<in> messages \<or> (i, n, t) = (i\<^sub>0, n\<^sub>0, t\<^sub>0)"
      by (meson ApplyCommit_quorum)
  qed
qed

subsubsection \<open>Sending @{term ApplyCommit} messages\<close>

text \<open>@{term "ApplyCommit i\<^sub>0 t\<^sub>0"} can be sent on receipt of a quorum of corresponding
@{term ApplyResponse} messages, where \textit{quorum} is defined in terms of the current
configuration:\<close>

lemma (in zen) send_ApplyCommit:
  assumes "q \<in> Q (era\<^sub>t t\<^sub>0)"
  assumes "\<forall> n \<in> q. ApplyResponse i\<^sub>0 n t\<^sub>0 \<in> messages"
  shows "zen (insert (ApplyCommit i\<^sub>0 t\<^sub>0) messages)" (is "zen ?messages'")
proof -

  have era: "era\<^sub>i i\<^sub>0 = era\<^sub>t t\<^sub>0"
    by (metis ApplyResponse_era Q_member_member assms(1) assms(2))

  have messages_simps:
    "\<And>i n t mt'. (JoinResponse i n t mt' \<in> ?messages') = (JoinResponse i n t mt' \<in> messages)"
    "\<And>i t x. (ApplyRequest i t x \<in> ?messages') = (ApplyRequest i t x \<in> messages)"
    "\<And>i n t. (ApplyResponse i n t \<in> ?messages') = (ApplyResponse i n t \<in> messages)"
    "\<And>i t. (ApplyCommit i t \<in> ?messages') = (ApplyCommit i t \<in> messages \<or> (i, t) = (i\<^sub>0, t\<^sub>0))"
    by auto

  define isCommitted' where "\<And>i. isCommitted' i \<equiv> \<exists>t. ApplyCommit i t \<in> ?messages'"
  define committedTo' ("committed\<^sub><'") where "\<And>i. committed\<^sub><' i \<equiv> \<forall>j < i. isCommitted' j"
  define v' where "\<And>i t. v' i t \<equiv> THE x. ApplyRequest i t x \<in> ?messages'"
  define v\<^sub>c' where "\<And>i. v\<^sub>c' i \<equiv> v' i (SOME t. ApplyCommit i t \<in> ?messages')"
  define era\<^sub>i' where "\<And>i. era\<^sub>i' i \<equiv> eraOfNat (card {j. j < i \<and> isReconfiguration (v\<^sub>c' j)})"
  define reconfig' where "\<And>e. reconfig' e \<equiv> THE i. isCommitted' i \<and> isReconfiguration (v\<^sub>c' i) \<and> era\<^sub>i' i = e"
  define Q' where "\<And>e. Q' e \<equiv> case e of e\<^sub>0 \<Rightarrow> Q\<^sub>0 | nextEra e' \<Rightarrow> getConf (v\<^sub>c' (reconfig' e'))"

  have committedTo_current: "committed\<^sub>< i\<^sub>0"
    using assms by (metis ApplyRequest_committedTo Q_member_member ApplyResponse_ApplyRequest)

  have isCommitted_eq: "\<And>i. isCommitted' i = (isCommitted i \<or> i = i\<^sub>0)"
    using isCommitted'_def isCommitted_def by auto

  have committedTo_eq: "\<And>i. committed\<^sub><' i = ((committed\<^sub>< i) \<or> (i = Suc i\<^sub>0))"
    apply (unfold committedTo_def committedTo'_def isCommitted_eq)
    using Suc_lessI committedTo_current committedTo_def isCommitted_committedTo by blast

  have v_eq: "\<And>i t. v' i t = v i t" by (simp add: v'_def v_def)

  have v\<^sub>c_eq: "\<And>i. isCommitted i \<Longrightarrow> v\<^sub>c' i = v\<^sub>c i"
  proof -
    fix i assume i: "isCommitted i"
    show "?thesis i"
    proof (cases "i = i\<^sub>0")
      case False thus ?thesis by (simp add: v\<^sub>c_def v\<^sub>c'_def v_eq)
    next
      case True
      define t  where "t  \<equiv> SOME t. ApplyCommit i\<^sub>0 t \<in> messages"
      define t' where "t' \<equiv> SOME t. ApplyCommit i\<^sub>0 t \<in> ?messages'"

      have eq:  "v\<^sub>c  i\<^sub>0 = v i\<^sub>0 t"  by (simp add: v\<^sub>c_def t_def)
      have eq': "v\<^sub>c' i\<^sub>0 = v i\<^sub>0 t'" by (simp add: v\<^sub>c'_def t'_def v_eq)

      show ?thesis
        apply (unfold True eq eq')
      proof (intro oneSlot.consistent [OF oneSlot.commit [OF zen_is_oneSlot]])
        from assms show "q \<in> (Q \<circ> era\<^sub>t) t\<^sub>0" "\<And>n. n \<in> q \<Longrightarrow> ApplyResponse i\<^sub>0 n t\<^sub>0 \<in> messages"
          by simp_all

        from i have "ApplyCommit i\<^sub>0 t  \<in> messages" by (metis True isCommitted_def someI_ex t_def)
        thus "ApplyCommit i\<^sub>0 t \<in> messages \<or> t = t\<^sub>0" by simp
        from i have t': "ApplyCommit i\<^sub>0 t' \<in> ?messages'" by (metis insertI1 someI_ex t'_def)
        thus "ApplyCommit i\<^sub>0 t' \<in> messages \<or> t' = t\<^sub>0" by blast

        fix t assume le: "t\<^sub>0 \<preceq> t"
        assume "\<exists>x. ApplyRequest i\<^sub>0 t x \<in> messages"
        then obtain x where "ApplyRequest i\<^sub>0 t x \<in> messages" by blast

        hence "era\<^sub>t t \<le> era\<^sub>i i\<^sub>0" using ApplyRequest_era by simp
        also from era have "era\<^sub>i i\<^sub>0 = era\<^sub>t t\<^sub>0" by simp
        finally have "era\<^sub>t t \<le> era\<^sub>t t\<^sub>0".

        moreover from le have "era\<^sub>t t\<^sub>0 \<le> era\<^sub>t t" by (simp add: era\<^sub>t_mono)

        ultimately have "era\<^sub>t t\<^sub>0 = era\<^sub>t t" by simp
        thus "(Q \<circ> era\<^sub>t) t \<frown> (Q \<circ> era\<^sub>t) t\<^sub>0"
          by (simp add: Q_intersects)
      qed
    qed
  qed

  have era\<^sub>i_eq: "\<And>i. committed\<^sub>< i \<Longrightarrow> era\<^sub>i' i = era\<^sub>i i"
  proof -
    fix i assume i: "committed\<^sub>< i"
    hence "{j. j < i \<and> isReconfiguration (v\<^sub>c' j)} = {j. j < i \<and> isReconfiguration (v\<^sub>c j)}"
      using v\<^sub>c_eq by (auto simp add: committedTo_def)
    thus "?thesis i" by (simp add: era\<^sub>i_def era\<^sub>i'_def)
  qed

  have reconfig'_eq: "\<And>e i. committed\<^sub>< i \<Longrightarrow> e < era\<^sub>i i \<Longrightarrow> reconfig' e = reconfig e"
  proof -
    fix e i
    assume a: "committed\<^sub>< i" "e < era\<^sub>i i"

    define P where "\<And>i. P i \<equiv> isCommitted' i \<and> isReconfiguration (v\<^sub>c' i) \<and> era\<^sub>i' i = e"
    have reconfig'_the: "reconfig' e = (THE i. P i)" by (simp add: P_def reconfig'_def)

    have "P (reconfig' e)"
    proof (unfold reconfig'_the, intro theI [of P])
      show "P (reconfig e)"
        using P_def a era\<^sub>i_eq isCommitted_committedTo isCommitted_eq reconfig_era reconfig_isCommitted reconfig_isReconfiguration v\<^sub>c_eq by auto

      show "\<And>j. P j \<Longrightarrow> j = reconfig e"
        using P_def a
        by (metis committedTo_current committedTo_def era\<^sub>i_eq era\<^sub>i_mono isCommitted_committedTo isCommitted_eq not_le reconfig_eq v\<^sub>c_eq)
    qed
    thus "?thesis e i"
      using P_def a
      by (metis committedTo_current committedTo_def era\<^sub>i_eq era\<^sub>i_mono isCommitted_committedTo isCommitted_eq not_le reconfig_eq v\<^sub>c_eq)
  qed

  have Q'_eq: "\<And>e i. committed\<^sub>< i \<Longrightarrow> e \<le> era\<^sub>i i \<Longrightarrow> Q' e = Q e"
  proof -
    fix e i assume "committed\<^sub>< i" "e \<le> era\<^sub>i i"
    thus "Q' e = Q e" 
      apply (cases e, simp add: Q_def Q'_def)
      using Q'_def
      by (metis Era.simps(5) Q_def Suc_le_lessD natOfEra.simps(2) natOfEra_le natOfEra_lt reconfig'_eq reconfig_isCommitted v\<^sub>c_eq)
  qed

  show ?thesis
    apply (unfold_locales)
                apply (fold isCommitted'_def)
                apply (fold committedTo'_def)
                apply (fold v'_def)
                apply (fold v\<^sub>c'_def)
                apply (fold era\<^sub>i'_def)
                apply (fold reconfig'_def)
                apply (fold Q'_def)
                apply (unfold messages_simps)
                apply (fold promised_def)
                apply (fold prevAccepted_def)
  proof -
    from JoinResponse_future show "\<And>i i' n t t' mt. JoinResponse i n t mt \<in> messages \<Longrightarrow> i < i' \<Longrightarrow> t' \<prec> t \<Longrightarrow> ApplyResponse i' n t' \<notin> messages" .
    from JoinResponse_None show "\<And>i n t t'. JoinResponse i n t None \<in> messages \<Longrightarrow> t' \<prec> t \<Longrightarrow> ApplyResponse i n t' \<notin> messages" .
    from JoinResponse_Some_lt show "\<And>i n t t'. JoinResponse i n t (Some t') \<in> messages \<Longrightarrow> t' \<prec> t" .
    from JoinResponse_Some_ApplyResponse show "\<And>i n t t'. JoinResponse i n t (Some t') \<in> messages \<Longrightarrow> ApplyResponse i n t' \<in> messages" .
    from JoinResponse_Some_max show "\<And>i n t t' t''. JoinResponse i n t (Some t') \<in> messages \<Longrightarrow> t' \<prec> t'' \<Longrightarrow> t'' \<prec> t \<Longrightarrow> ApplyResponse i n t'' \<notin> messages" .
    from ApplyRequest_function show "\<And>i t x x'. ApplyRequest i t x \<in> messages \<Longrightarrow> ApplyRequest i t x' \<in> messages \<Longrightarrow> x = x'" .
    from finite_messages_insert show "finite ?messages'" .
    from ApplyResponse_ApplyRequest show "\<And>i n t. ApplyResponse i n t \<in> messages \<Longrightarrow> \<exists>x. ApplyRequest i t x \<in> messages" .

    from ApplyRequest_committedTo show "\<And>i t x. ApplyRequest i t x \<in> messages \<Longrightarrow> committed\<^sub><' i" by (simp add: committedTo_eq)

    from JoinResponse_era era\<^sub>i_eq committedTo_eq
    show "\<And>i n t mt. JoinResponse i n t mt \<in> messages \<Longrightarrow> \<exists>i'\<le>i. committed\<^sub><' i' \<and> era\<^sub>t t \<le> era\<^sub>i' i'"
      by force

    from era\<^sub>i_eq show "\<And>i t x. ApplyRequest i t x \<in> messages \<Longrightarrow> era\<^sub>i' i = era\<^sub>t t"
      using ApplyCommit_era era committedTo_current isCommitted_committedTo isCommitted_def 
      by (simp add: ApplyRequest_committedTo ApplyRequest_era)

    show "\<And>i t x. ApplyRequest i t x \<in> messages \<Longrightarrow> \<exists>q\<in>Q' (era\<^sub>t t). (\<forall>n\<in>q. promised i n t) \<and> (prevAccepted i t q = {} \<or> v' i t = v' i (maxTerm (prevAccepted i t q)))"
      by (metis ApplyRequest_JoinResponse ApplyRequest_quorum JoinResponse_era Q'_eq v_eq)

    show "\<And>i t. ApplyCommit i t \<in> messages \<or> (i, t) = (i\<^sub>0, t\<^sub>0) \<Longrightarrow> \<exists>q\<in>Q' (era\<^sub>t t). \<forall>n\<in>q. ApplyResponse i n t \<in> messages"
        by (metis ApplyCommit_quorum ApplyRequest_JoinResponse ApplyResponse_ApplyRequest JoinResponse_era Q'_eq Q_member_member assms(1) assms(2) prod.inject)
  qed
qed

end
