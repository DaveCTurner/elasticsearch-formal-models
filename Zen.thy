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

section \<open>Terms\<close>

subsection \<open>Definitions\<close>

text \<open>Terms are triples of an @{type Era}, an \textit{election number} within the era, and an
\textit{owning node}.\<close>

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

text \<open>A handful of lemmas that are useful for the simplifier follow.\<close>

lemma era\<^sub>t_mono: "t\<^sub>1 \<le> t\<^sub>2 \<Longrightarrow> era\<^sub>t t\<^sub>1 \<le> era\<^sub>t t\<^sub>2" using less_eq_Term_def lt_term by auto

text \<open>Importantly, this shows how to do induction over the terms:\<close>

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

subsection \<open>Maximum term of a set\<close>

text \<open>A function for finding the maximum term in a set is as follows.\<close>

definition maxTerm :: "Term set \<Rightarrow> Term"
  where "maxTerm S \<equiv> THE t. t \<in> S \<and> (\<forall> t' \<in> S. t' \<le> t)"

text \<open>It works on finite and nonempty sets, which is sufficient.\<close>

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

section \<open>Configurations and quorums\<close>

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
  assumes Q_intersects: "\<lbrakk> proposed t\<^sub>1; committed t\<^sub>2; t\<^sub>2 \<le> t\<^sub>1 \<rbrakk> \<Longrightarrow> Q t\<^sub>1 \<frown> Q t\<^sub>2"
  assumes Q_nonempty: "q \<in> Q t \<Longrightarrow> q \<noteq> {}"
  assumes promised\<^sub>f: "\<lbrakk> promised\<^sub>f n t; t' < t \<rbrakk> \<Longrightarrow> \<not> accepted n t'"
  assumes promised\<^sub>b_lt: "promised\<^sub>b n t t' \<Longrightarrow> t' < t"
  assumes promised\<^sub>b_accepted: "promised\<^sub>b n t t' \<Longrightarrow> accepted n t'"
  assumes promised\<^sub>b_max: "\<lbrakk> promised\<^sub>b n t t'; t' < t''; t'' < t \<rbrakk>
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
  assumes "proposed t\<^sub>1" and "committed t\<^sub>2" and "t\<^sub>2 < t\<^sub>1"
  shows "v t\<^sub>1 = v t\<^sub>2"
  using assms
proof (induct t\<^sub>1 rule: term_induct)
  case (less t\<^sub>1)

  hence hyp: "\<And> t\<^sub>1'. \<lbrakk> t\<^sub>1' < t\<^sub>1; proposed t\<^sub>1'; t\<^sub>2 \<le> t\<^sub>1' \<rbrakk> \<Longrightarrow> v t\<^sub>1' = v t\<^sub>2" by auto

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
    using Q_intersects intersects_def less.prems q\<^sub>1_quorum q\<^sub>2_quorum by auto

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

    show "maxTerm (prevAccepted t\<^sub>1 q\<^sub>1) < t\<^sub>1"
      using p prevAccepted_def promised\<^sub>b_lt by auto

    show "proposed (maxTerm (prevAccepted t\<^sub>1 q\<^sub>1))"
      using p prevAccepted_proposed by auto

    have "t\<^sub>2 \<le> t\<^sub>2'"
      by (meson \<open>accepted n t\<^sub>2\<close> less.prems(3) not_le promised\<^sub>b_max t\<^sub>2')
    also have "t\<^sub>2' \<le> maxTerm (prevAccepted t\<^sub>1 q\<^sub>1)"
      using n\<^sub>1 prevAccepted_def t\<^sub>2' prevAccepted_finite by (intro maxTerm_max, auto)
    finally show "t\<^sub>2 \<le> maxTerm (prevAccepted t\<^sub>1 q\<^sub>1)" .
  qed

  finally show ?case .
qed

text \<open>From this, it follows that any two committed values are equal as desired.\<close>

lemma (in oneSlot) consistent:
  assumes "committed t\<^sub>1" and "committed t\<^sub>2"
  shows "v t\<^sub>1 = v t\<^sub>2"
  using assms by (metis Q_nonempty accepted all_not_in_conv committed not_less_iff_gr_or_eq p2b)

text \<open>It will be useful later to know the conditions under which a value in a term can be committed,
which is spelled out here:\<close>

lemma (in oneSlot) commit:
  assumes q_quorum: "q \<in> Q t\<^sub>0"
  assumes q_accepted: "\<And>n. n \<in> q \<Longrightarrow> accepted n t\<^sub>0"
  assumes intersects: "\<And>t. proposed t \<Longrightarrow> t\<^sub>0 \<le> t \<Longrightarrow> Q t \<frown> Q t\<^sub>0"
  defines "committed' t \<equiv> committed t \<or> t = t\<^sub>0"
  shows "oneSlot Q v promised\<^sub>f promised\<^sub>b proposed accepted committed'"
  by (smt committed'_def intersects oneSlot_axioms oneSlot_def q_accepted q_quorum)

section \<open>Zen\<close>

text \<open>Zen is the protocol used to replicate chosen values, including reconfigurations. The
proven-safe core of the protocol works by sending messages as follows. The remainder of the
protocol may send other messages too, and may drop or reorder any of these messages, but
must not send these messages itself to ensure safety. The @{type nat} parameter to each
message refers to a slot number.\<close>

datatype PreviousApplyResponse
  = NoApplyResponseSent
  | ApplyResponseSent Term Value

datatype Message
  = JoinRequest Term
  | JoinResponse nat Term PreviousApplyResponse
  | ApplyRequest nat Term Value
  | ApplyResponse nat Term
  | ApplyCommit nat Term

text \<open>Some prose descriptions of these messages follows, in order to give a bit more of an
intuitive understanding of their purposes. A precise description of the conditions under which each
kind of message can be sent is further below.\<close>

text \<open>The message @{term "JoinRequest t"} may be sent by any node to attempt to start a master
election in the given term @{term t}.\<close>

text \<open>The message @{term "JoinResponse i t a"} may be sent by a node in response
to a @{term JoinRequest} message. It indicates that the sender knows all committed values for slots
strictly below @{term i}, and that the sender will no longer vote (i.e. send an @{term
ApplyResponse}) in any term prior to @{term t}. The field @{term a} is either @{term
NoApplyResponseSent} or @{term "ApplyResponseSent t' x'"}. In the former case this indicates that
the node has not yet sent any @{term ApplyResponse} message in slot @{term i}, and in the latter
case it indicates that the largest term in which it has previously sent an @{term ApplyResponse}
message is @{term t'} and the value in the corresponding @{term ApplyRequest} was @{term x'}.  All
nodes must avoid sending a @{term JoinResponse} message to two different masters in the same term.
The trigger for sending this message is solely a liveness concern and therefore is out of the scope
of this model.\<close>

text \<open>The message @{term "ApplyRequest i t v"} may be sent by the elected master of term
@{term t} to request the other master-eligible nodes to vote for value @{term v} to be committed in
slot @{term i}.\<close>

text \<open>The message @{term "ApplyResponse i t"} may be sent by node in response to
the corresponding @{term ApplyRequest} message, indicating that the sender votes for the value
proposed by the master of term @{term t} to be committed in slot @{term i}.\<close>

text \<open>The message @{term "ApplyCommit i t"} indicates that the value proposed by the master of
term @{term t} in slot @{term i} received a quorum of votes and is therefore committed.\<close>

text \<open>The abstract model of Zen keeps track of the set of all messages that have ever been
sent, and asserts that this set obeys certain invariants, listed below. Further below, it will be
shown that these invariants imply that each slot obeys the @{term oneSlot} invariants above and
hence that each slot cannot see inconsistent committed values.\<close>

datatype Destination = Broadcast | OneNode Node

record RoutedMessage =
  sender :: Node
  destination :: Destination
  payload :: Message

locale zen =
  fixes messages :: "RoutedMessage set"
  fixes isMessageFromTo :: "Node \<Rightarrow> Message \<Rightarrow> Destination \<Rightarrow> bool" ("_ \<midarrow>\<langle> _ \<rangle>\<rightarrow> _" [55])
  defines "s \<midarrow>\<langle> m \<rangle>\<rightarrow> d \<equiv> \<lparr> sender = s, destination = d, payload = m \<rparr> \<in> messages"
  fixes isMessageFrom :: "Node \<Rightarrow> Message \<Rightarrow> bool" ("_ \<midarrow>\<langle> _ \<rangle>\<leadsto>" [55])
  defines "s \<midarrow>\<langle> m \<rangle>\<leadsto> \<equiv> \<exists> d. s \<midarrow>\<langle> m \<rangle>\<rightarrow> d"
  fixes isMessageTo :: "Message \<Rightarrow> Destination \<Rightarrow> bool" ("\<langle> _ \<rangle>\<rightarrow> _" [55])
  defines "\<langle> m \<rangle>\<rightarrow> d \<equiv> \<exists> s. s \<midarrow>\<langle> m \<rangle>\<rightarrow> d"
  fixes isMessage :: "Message \<Rightarrow> bool" ("\<langle> _ \<rangle>\<leadsto>" [55])
  defines "\<langle> m \<rangle>\<leadsto> \<equiv> \<exists> s. s \<midarrow>\<langle> m \<rangle>\<leadsto>"
    (* value proposed in a slot & a term *)
  fixes v :: "nat \<Rightarrow> Term \<Rightarrow> Value"
  defines "v i t \<equiv> THE x. \<langle> ApplyRequest i t x \<rangle>\<leadsto>"
    (* whether a slot is committed *)
  fixes isCommitted :: "nat \<Rightarrow> bool"
  defines "isCommitted i \<equiv> \<exists> t. \<langle> ApplyCommit i t \<rangle>\<leadsto>"
    (* whether all preceding slots are committed *)
  fixes committedTo :: "nat \<Rightarrow> bool" ("committed\<^sub><")
  defines "committed\<^sub>< i \<equiv> \<forall> j < i. isCommitted j" 
    (* the committed value in a slot *)
  fixes v\<^sub>c :: "nat \<Rightarrow> Value"
  defines "v\<^sub>c i \<equiv> v i (SOME t. \<langle> ApplyCommit i t \<rangle>\<leadsto>)"
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
  fixes promised :: "nat \<Rightarrow> Node \<Rightarrow> Node \<Rightarrow> Term \<Rightarrow> bool"
  defines "promised i s dn t \<equiv> \<exists> i' \<le> i. \<exists> a. s \<midarrow>\<langle> JoinResponse i' t a \<rangle>\<rightarrow> (OneNode dn)"
    (* set of previously-accepted terms *)
  fixes prevAccepted :: "nat \<Rightarrow> Term \<Rightarrow> Node set \<Rightarrow> Term set"
  defines "prevAccepted i t senders
      \<equiv> {t'. \<exists> s \<in> senders. \<exists> x'. s \<midarrow>\<langle> JoinResponse i t (ApplyResponseSent t' x') \<rangle>\<leadsto> }"
    (* ASSUMPTIONS *)
  assumes JoinResponse_future:
    "\<And>i i' s t t' a.
        \<lbrakk> s \<midarrow>\<langle> JoinResponse i t a \<rangle>\<leadsto>; i < i'; t' < t \<rbrakk>
            \<Longrightarrow> \<not> s \<midarrow>\<langle> ApplyResponse i' t' \<rangle>\<leadsto>"
  assumes JoinResponse_None:
    "\<And>i s t t'.
        \<lbrakk> s \<midarrow>\<langle> JoinResponse i t NoApplyResponseSent \<rangle>\<leadsto>; t' < t \<rbrakk>
            \<Longrightarrow> \<not> s \<midarrow>\<langle> ApplyResponse i t' \<rangle>\<leadsto>"
  assumes JoinResponse_Some_lt:
    "\<And>i s t t' x'. s \<midarrow>\<langle> JoinResponse i t (ApplyResponseSent t' x') \<rangle>\<leadsto>
      \<Longrightarrow> t' < t"
  assumes JoinResponse_Some_ApplyResponse:
    "\<And>i s t t' x'. s \<midarrow>\<langle> JoinResponse i t (ApplyResponseSent t' x') \<rangle>\<leadsto>
      \<Longrightarrow> s \<midarrow>\<langle> ApplyResponse i t' \<rangle>\<leadsto>"
  assumes JoinResponse_Some_ApplyRequest:
    "\<And>i s t t' x'. s \<midarrow>\<langle> JoinResponse i t (ApplyResponseSent t' x') \<rangle>\<leadsto>
      \<Longrightarrow> \<langle> ApplyRequest i t' x' \<rangle>\<leadsto>"
  assumes JoinResponse_Some_max:
    "\<And>i s t t' t'' x'. \<lbrakk> s \<midarrow>\<langle> JoinResponse i t (ApplyResponseSent t' x') \<rangle>\<leadsto>; t' < t''; t'' < t \<rbrakk>
      \<Longrightarrow> \<not> s \<midarrow>\<langle> ApplyResponse i t'' \<rangle>\<leadsto>"
  assumes JoinResponse_era:
    "\<And>i s t a. s \<midarrow>\<langle> JoinResponse i t a \<rangle>\<leadsto>
      \<Longrightarrow> \<exists> i' \<le> i. committedTo i' \<and> era\<^sub>t t \<le> era\<^sub>i i'"
  assumes JoinResponse_not_broadcast:
    "\<And>i t a d. \<langle> JoinResponse i t a \<rangle>\<rightarrow> d \<Longrightarrow> d \<noteq> Broadcast"
  assumes JoinResponse_unique_destination:
    "\<And>i s t a a' d d'. \<lbrakk> s \<midarrow>\<langle> JoinResponse i t a \<rangle>\<rightarrow> d; s \<midarrow>\<langle> JoinResponse i' t a' \<rangle>\<rightarrow> d' \<rbrakk>
      \<Longrightarrow> d = d'"
  assumes ApplyRequest_era:
    "\<And>i t x. \<langle> ApplyRequest i t x \<rangle>\<leadsto> \<Longrightarrow> era\<^sub>i i = era\<^sub>t t"
  assumes ApplyRequest_committedTo:
    "\<And>i t x. \<langle> ApplyRequest i t x \<rangle>\<leadsto> \<Longrightarrow> committedTo i"
  assumes ApplyRequest_quorum:
    "\<And>i s t x. s \<midarrow>\<langle> ApplyRequest i t x \<rangle>\<leadsto>
      \<Longrightarrow> \<exists> q \<in> Q (era\<^sub>t t). (\<forall> n \<in> q. promised i n s t) \<and>
            (prevAccepted i t q = {}
                \<or> v i t = v i (maxTerm (prevAccepted i t q)))"
  assumes ApplyRequest_function:
    "\<And>i t x x'. \<lbrakk> \<langle> ApplyRequest i t x \<rangle>\<leadsto>; \<langle> ApplyRequest i t x' \<rangle>\<leadsto> \<rbrakk>
       \<Longrightarrow> x = x'"
  assumes finite_messages:
    "finite messages"
  assumes ApplyResponse_ApplyRequest:
    "\<And>i s t. s \<midarrow>\<langle> ApplyResponse i t \<rangle>\<leadsto> \<Longrightarrow> \<exists> x. \<langle> ApplyRequest i t x \<rangle>\<leadsto>"
  assumes ApplyCommit_quorum:
    "\<And>i t. \<langle> ApplyCommit i t \<rangle>\<leadsto>
                        \<Longrightarrow> \<exists> q \<in> Q (era\<^sub>t t). \<forall> s \<in> q. s \<midarrow>\<langle> ApplyResponse i t \<rangle>\<leadsto>"

declare [[goals_limit = 20]]

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
  assumes "\<langle> ApplyCommit i t \<rangle>\<leadsto>"
  obtains s where "s \<midarrow>\<langle> ApplyResponse i t \<rangle>\<leadsto>"
  by (meson ApplyCommit_quorum Q_member_member assms)

lemma (in zen) ApplyCommit_ApplyRequest:
  assumes "\<langle> ApplyCommit i t \<rangle>\<leadsto>"
  shows "\<langle> ApplyRequest i t (v i t) \<rangle>\<leadsto>"
  by (metis ApplyCommit_ApplyResponse ApplyResponse_ApplyRequest assms the_equality v_def ApplyRequest_function)

lemma (in zen) ApplyRequest_JoinResponse:
  assumes "s \<midarrow>\<langle> ApplyRequest i t x \<rangle>\<leadsto>"
  obtains i' n a where "i' \<le> i" "n \<midarrow>\<langle> JoinResponse i' t a \<rangle>\<rightarrow> (OneNode s)"
  by (meson ApplyRequest_quorum Q_member_member assms isMessage_def promised_def)

lemma (in zen) finite_prevAccepted: "finite (prevAccepted i t ns)"
proof -
  fix t\<^sub>0
  define f :: "RoutedMessage \<Rightarrow> Term" where "f \<equiv> \<lambda> m. case payload m of JoinResponse _ _ (ApplyResponseSent t' _) \<Rightarrow> t' | _ \<Rightarrow> t\<^sub>0"
  have "prevAccepted i t ns \<subseteq> f ` messages"
    apply (simp add: prevAccepted_def f_def isMessageFrom_def isMessageFromTo_def, intro subsetI)
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
      using era\<^sub>i_step less_eq_Era_def by auto
    finally show ?thesis .
  qed simp
qed simp

lemma (in zen) era\<^sub>i_contiguous:
  assumes "e \<le> era\<^sub>i i"
  shows "\<exists> i' \<le> i. era\<^sub>i i' = e"
  using assms
proof (induct i)
  case 0
  then show ?case
    apply (auto simp add: era\<^sub>i_def less_eq_Era_def)
    using natOfEra_inj by fastforce
next
  case (Suc i)
  then show ?case
    by (metis antisym_conv1 era\<^sub>i_step le_SucI less_Era_def less_Suc_eq_le less_eq_Era_def natOfEra.simps(2))
qed

lemma (in zen) ApplyResponse_era:
  assumes "s \<midarrow>\<langle> ApplyResponse i t \<rangle>\<leadsto>"
  shows "era\<^sub>t t = era\<^sub>i i"
  using assms ApplyRequest_era ApplyResponse_ApplyRequest by metis

lemma (in zen) ApplyCommit_era:
  assumes "\<langle> ApplyCommit i t \<rangle>\<leadsto>"
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
      by (metis Suc.prems(1) dual_order.antisym era\<^sub>i_step leI less_Era_def natOfEra.simps(2) not_less_less_Suc_eq)
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
  using assms
  by (metis era\<^sub>i_mono era\<^sub>i_step lessI less_Era_def less_antisym less_eq_Suc_le natOfEra.simps(2) not_less reconfig_era reconfig_isReconfiguration)

lemma (in zen) promised_long_def: "\<exists>d. promised i s d t
     \<equiv> (s \<midarrow>\<langle> JoinResponse i t NoApplyResponseSent \<rangle>\<leadsto>
           \<or> (\<exists>i'<i. \<exists>a. s \<midarrow>\<langle> JoinResponse i' t a \<rangle>\<leadsto>))
           \<or> (\<exists>t'. \<exists> x'. s \<midarrow>\<langle> JoinResponse i t (ApplyResponseSent t' x') \<rangle>\<leadsto>)"
 (is "?LHS == ?RHS")
proof -
  have "?LHS = ?RHS"
    apply (intro iffI)
     apply (metis PreviousApplyResponse.exhaust isMessageFrom_def leI le_antisym promised_def)
    by (metis Destination.exhaust JoinResponse_not_broadcast isMessageFrom_def isMessageTo_def nat_less_le not_le promised_def)
  thus "?LHS == ?RHS" by simp
qed

lemma (in zen) JoinResponse_func:
  assumes "s \<midarrow>\<langle> JoinResponse i t a\<^sub>1 \<rangle>\<leadsto>" and "s \<midarrow>\<langle> JoinResponse i t a\<^sub>2 \<rangle>\<leadsto>"
  shows "a\<^sub>1 = a\<^sub>2"
proof (cases a\<^sub>1)
  case NoApplyResponseSent
  with assms show ?thesis
    by (metis JoinResponse_None JoinResponse_Some_ApplyResponse JoinResponse_Some_lt PreviousApplyResponse.exhaust)
next
  case (ApplyResponseSent t\<^sub>1 x\<^sub>1)
  with assms have "a\<^sub>2 \<noteq> NoApplyResponseSent"
    using JoinResponse_None JoinResponse_Some_ApplyResponse JoinResponse_Some_lt by blast
  then obtain t\<^sub>2 x\<^sub>2 where a\<^sub>2: "a\<^sub>2 = ApplyResponseSent t\<^sub>2 x\<^sub>2"
    using PreviousApplyResponse.exhaust by blast

  from ApplyResponseSent a\<^sub>2 assms
  have t: "t\<^sub>1 = t\<^sub>2"
    by (meson JoinResponse_Some_ApplyResponse JoinResponse_Some_lt less_linear JoinResponse_Some_max)

  from assms
  have x: "x\<^sub>1 = x\<^sub>2" 
    apply (intro ApplyRequest_function JoinResponse_Some_ApplyRequest)
    by (unfold ApplyResponseSent a\<^sub>2 t)

  show ?thesis
    by (simp add: ApplyResponseSent a\<^sub>2 t x)
qed

lemma (in zen) shows finite_messages_insert: "finite (insert m messages)"
  using finite_messages by auto

lemma (in zen) isCommitted_committedTo:
  assumes "isCommitted i"
  shows "committed\<^sub>< i"
  using ApplyCommit_ApplyRequest ApplyRequest_committedTo assms isCommitted_def by blast

lemma (in zen) promised_unique:
  assumes "promised i s d t" and "promised i' s d' t"
  shows "d = d'"
  by (meson Destination.inject JoinResponse_unique_destination assms promised_def)

subsection \<open>Relationship to @{term oneSlot}\<close>

text \<open>This shows that each slot @{term i} in Zen satisfies the assumptions of the @{term
oneSlot} model above.\<close>

lemma (in zen) zen_is_oneSlot:
  fixes i
  shows "oneSlot (Q \<circ> era\<^sub>t) (v i)
    (\<lambda> s t. s \<midarrow>\<langle> JoinResponse i t NoApplyResponseSent \<rangle>\<leadsto>
        \<or> (\<exists> i' < i. \<exists> a. s \<midarrow>\<langle> JoinResponse i' t a \<rangle>\<leadsto>))
    (\<lambda> s t t'. \<exists> x'. s \<midarrow>\<langle> JoinResponse i t (ApplyResponseSent t' x') \<rangle>\<leadsto>)
    (\<lambda> t. \<exists> x. \<langle> ApplyRequest i t x \<rangle>\<leadsto>)
    (\<lambda> s t. s \<midarrow>\<langle> ApplyResponse i t \<rangle>\<leadsto>)
    (\<lambda> t. \<langle> ApplyCommit i t \<rangle>\<leadsto>)"
proof (unfold_locales, fold prevAccepted_def promised_long_def)
  fix t\<^sub>1 t\<^sub>2
  assume "\<exists>x. \<langle> ApplyRequest i t\<^sub>1 x \<rangle>\<leadsto>"
  then obtain x where t\<^sub>1: "\<langle> ApplyRequest i t\<^sub>1 x \<rangle>\<leadsto>" ..
  assume t\<^sub>2: "\<langle> ApplyCommit i t\<^sub>2 \<rangle>\<leadsto>"
  assume t\<^sub>2\<^sub>1: "t\<^sub>2 \<le> t\<^sub>1" hence "era\<^sub>t t\<^sub>2 \<le> era\<^sub>t t\<^sub>1"
    by (simp add: era\<^sub>t_mono)

  from t\<^sub>1 ApplyRequest_era have "era\<^sub>t t\<^sub>1 = era\<^sub>i i" by simp
  also from t\<^sub>2 have "... = era\<^sub>t t\<^sub>2" using ApplyCommit_era by auto
  finally show "(Q \<circ> era\<^sub>t) t\<^sub>1 \<frown> (Q \<circ> era\<^sub>t) t\<^sub>2" by (simp add: Q_intersects)
next
  fix q t assume "q \<in> (Q \<circ> era\<^sub>t) t" thus "q \<noteq> {}" by (simp add: Q_members_nonempty)
next
  fix s t t'
  assume "t' < t" "s \<midarrow>\<langle> JoinResponse i t NoApplyResponseSent \<rangle>\<leadsto> \<or> (\<exists>i'<i. \<exists>a. s \<midarrow>\<langle> JoinResponse i' t a \<rangle>\<leadsto>)"
  thus "\<not> s \<midarrow>\<langle> ApplyResponse i t' \<rangle>\<leadsto>"
    using JoinResponse_None JoinResponse_future by auto
next
  fix s t t'
  assume j: "\<exists> x'. s \<midarrow>\<langle> JoinResponse i t (ApplyResponseSent t' x') \<rangle>\<leadsto>"
  from j show "t' < t" using JoinResponse_Some_lt by blast
  from j show "s \<midarrow>\<langle> ApplyResponse i t' \<rangle>\<leadsto>" using JoinResponse_Some_ApplyResponse by blast

  fix t'' assume "t' < t''" "t'' < t"
  with j show "\<not> s \<midarrow>\<langle> ApplyResponse i t'' \<rangle>\<leadsto>" using JoinResponse_Some_max by blast
next
  fix t
  assume "\<exists>x. \<langle> ApplyRequest i t x \<rangle>\<leadsto>"
  then obtain x s where "s \<midarrow>\<langle> ApplyRequest i t x \<rangle>\<leadsto>" by (auto simp add: isMessage_def)
  from ApplyRequest_quorum [OF this]
  show "\<exists>q\<in>(Q \<circ> era\<^sub>t) t. (\<forall>n\<in>q. \<exists> d. promised i n d t) \<and> (prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q)))"
    by auto
next
  fix s t assume "s \<midarrow>\<langle> ApplyResponse i t \<rangle>\<leadsto>"
  thus "\<exists>x. \<langle> ApplyRequest i t x \<rangle>\<leadsto>"
    by (simp add: ApplyResponse_ApplyRequest)
next
  fix t assume "\<langle> ApplyCommit i t \<rangle>\<leadsto>"
  thus "\<exists>q\<in>(Q \<circ> era\<^sub>t) t. \<forall>s\<in>q. s \<midarrow>\<langle> ApplyResponse i t \<rangle>\<leadsto>"
    by (simp add: ApplyCommit_quorum)
next
  fix t\<^sub>0
  define f :: "RoutedMessage \<Rightarrow> Term"
    where "f \<equiv> \<lambda> m. case payload m of ApplyRequest i t x \<Rightarrow> t | _ \<Rightarrow> t\<^sub>0"

  have "{t. \<exists>x. \<langle> ApplyRequest i t x \<rangle>\<leadsto>} \<subseteq> f ` messages"
    apply (unfold isMessage_def isMessageFrom_def isMessageFromTo_def)
    using f_def image_iff by fastforce

  moreover have "finite (f ` messages)"
    by (simp add: finite_messages)

  ultimately show "finite {t. \<exists>x. \<langle> ApplyRequest i t x \<rangle>\<leadsto>}"
    using finite_subset by blast
qed

text \<open>From this it follows that all committed values are equal.\<close>

lemma (in zen) consistent:
  assumes "\<langle> ApplyCommit  i t\<^sub>1 \<rangle>\<leadsto>"
  assumes "\<langle> ApplyCommit  i t\<^sub>2 \<rangle>\<leadsto>"
  assumes "\<langle> ApplyRequest i t\<^sub>1 v\<^sub>1 \<rangle>\<leadsto>"
  assumes "\<langle> ApplyRequest i t\<^sub>2 v\<^sub>2 \<rangle>\<leadsto>"
  shows "v\<^sub>1 = v\<^sub>2"
proof -
  from oneSlot.consistent [OF zen_is_oneSlot] assms
  have "v i t\<^sub>1 = v i t\<^sub>2" by blast
  moreover have "v\<^sub>1 = v i t\<^sub>1" using ApplyCommit_ApplyRequest assms ApplyRequest_function by blast
  moreover have "v\<^sub>2 = v i t\<^sub>2" using ApplyCommit_ApplyRequest assms ApplyRequest_function by blast
  ultimately show ?thesis by simp
qed

subsection \<open>Preserving invariants\<close>

text \<open>The statement @{term "zen M"} indicates that the set @{term M} of messages satisfies the
invariants of @{term zen}, and therefore all committed values are equal. Lemmas that are proven ``in
zen'' include the variable @{term messages} along with a silent assumption @{term "zen messages"}
and show from this that some modified set of messages also satisfies the invariants.\<close>

subsubsection \<open>Initial state\<close>

text \<open>When no messages have been sent, the invariants hold:\<close>

lemma zen_initial_state: "zen {}" by (unfold_locales, auto)

subsubsection \<open>Sending @{term JoinRequest} messages\<close>

text \<open>Any node may send a @{term JoinRequest} message for any term at any time.\<close>

lemma (in zen) send_JoinRequest:
  shows "zen (insert \<lparr> sender = s\<^sub>0, destination = d\<^sub>0, payload = JoinRequest t\<^sub>0 \<rparr> messages)" (is "zen ?messages'")
proof -
  define isMessageFromTo' :: "Node \<Rightarrow> Message \<Rightarrow> Destination \<Rightarrow> bool" ("_ \<midarrow>\<langle> _ \<rangle>\<rightarrow>' _" [55]) where
    "\<And>s m d. s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d \<equiv> \<lparr> sender = s, destination = d, payload = m \<rparr> \<in> ?messages'"

  define isMessageFrom' :: "Node \<Rightarrow> Message \<Rightarrow> bool" ("_ \<midarrow>\<langle> _ \<rangle>\<leadsto>'" [55]) where
    "\<And>s m. s \<midarrow>\<langle> m \<rangle>\<leadsto>' \<equiv> \<exists> d. s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d"

  define isMessageTo' :: "Message \<Rightarrow> Destination \<Rightarrow> bool" ("\<langle> _ \<rangle>\<rightarrow>' _" [55]) where
    "\<And>m d. \<langle> m \<rangle>\<rightarrow>' d \<equiv> \<exists> s. s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d"

  define isMessage' :: "Message \<Rightarrow> bool" ("\<langle> _ \<rangle>\<leadsto>'" [55]) where
    "\<And>m. \<langle> m \<rangle>\<leadsto>' \<equiv> \<exists> s. s \<midarrow>\<langle> m \<rangle>\<leadsto>'"

  have messages_simps:
    "\<And>i s d t a. (s \<midarrow>\<langle> JoinResponse i t a \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> JoinResponse i t a \<rangle>\<rightarrow> d)"
    "\<And>i s d t x. (s \<midarrow>\<langle> ApplyRequest i t x \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>i s d t. (s \<midarrow>\<langle> ApplyResponse i t\<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyResponse i t \<rangle>\<rightarrow> d)"
    "\<And>i s d t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)"
    by (auto simp add: isMessageFrom_def isMessageFromTo_def isMessage_def
        isMessageFromTo'_def isMessageFrom'_def isMessage'_def)

  show ?thesis
    apply (unfold_locales)
                   apply (fold isMessageFromTo'_def)
                   apply (unfold messages_simps)
                   apply (fold isMessageFrom_def isMessageTo_def)
                   apply (fold isMessage_def)
                   apply (fold isCommitted_def)
                   apply (fold committedTo_def)
                   apply (fold v_def)
                   apply (fold v\<^sub>c_def)
                   apply (fold era\<^sub>i_def)
                   apply (fold reconfig_def)
                   apply (fold Q_def)
                   apply (fold promised_def)
                   apply (fold prevAccepted_def)
    using ApplyResponse_ApplyRequest ApplyRequest_era ApplyRequest_quorum ApplyRequest_function
      ApplyRequest_committedTo JoinResponse_Some_lt JoinResponse_Some_ApplyResponse
      JoinResponse_Some_max finite_messages_insert JoinResponse_None JoinResponse_era
      JoinResponse_future ApplyCommit_quorum JoinResponse_Some_ApplyRequest
      JoinResponse_not_broadcast JoinResponse_unique_destination
    by (simp_all)
qed

subsubsection \<open>Sending @{term JoinResponse} messages\<close>

text \<open>A node @{term n\<^sub>0} can send a @{term JoinResponse} message for slot @{term
i\<^sub>0} only if \begin{itemize} \item all previous slots are committed, \item the eras of the
term and the slot are equal, and \item it has sent no @{term ApplyResponse} message for any later
slot. \end{itemize}.\<close>

text \<open>@{term "JoinResponse i\<^sub>0 t\<^sub>0 NoApplyResponseSent"} can be sent by node @{term n\<^sub>0} if,
additionally, no @{term ApplyResponse} message has been sent for slot @{term i\<^sub>0}:\<close>

lemma (in zen) send_JoinResponse_None:
  assumes "\<forall> i \<ge> i\<^sub>0. \<forall> t. \<not> s\<^sub>0 \<midarrow>\<langle> ApplyResponse i t \<rangle>\<leadsto>"
    (* first-uncommitted slot, the era is ok, and not already sent*)
  assumes "\<forall> i < i\<^sub>0. \<exists> t. \<langle> ApplyCommit i t \<rangle>\<leadsto>"
  assumes "era\<^sub>t t\<^sub>0 = era\<^sub>i i\<^sub>0"
  assumes "\<forall> i a. \<not> s\<^sub>0 \<midarrow>\<langle> JoinResponse i t\<^sub>0 a \<rangle>\<leadsto>"
    (* *)
  shows   "zen (insert \<lparr> sender = s\<^sub>0, destination = OneNode d\<^sub>0,
                         payload = JoinResponse i\<^sub>0 t\<^sub>0 NoApplyResponseSent \<rparr> messages)"
          (is "zen ?messages'")
proof -
  define isMessageFromTo' :: "Node \<Rightarrow> Message \<Rightarrow> Destination \<Rightarrow> bool" ("_ \<midarrow>\<langle> _ \<rangle>\<rightarrow>' _" [55]) where
    "\<And>s m d. s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d \<equiv> \<lparr> sender = s, destination = d, payload = m \<rparr> \<in> ?messages'"

  define isMessageFrom' :: "Node \<Rightarrow> Message \<Rightarrow> bool" ("_ \<midarrow>\<langle> _ \<rangle>\<leadsto>'" [55]) where
    "\<And>s m. s \<midarrow>\<langle> m \<rangle>\<leadsto>' \<equiv> \<exists> d. s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d"

  define isMessageTo' :: "Message \<Rightarrow> Destination \<Rightarrow> bool" ("\<langle> _ \<rangle>\<rightarrow>' _" [55]) where
    "\<And>m d. \<langle> m \<rangle>\<rightarrow>' d \<equiv> \<exists> s. s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d"

  define isMessage' :: "Message \<Rightarrow> bool" ("\<langle> _ \<rangle>\<leadsto>'" [55]) where
    "\<And>m. \<langle> m \<rangle>\<leadsto>' \<equiv> \<exists> s. s \<midarrow>\<langle> m \<rangle>\<leadsto>'"

  have isMessageFromTo'_eq [simp]:
    "\<And>s m d. (s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d) = ((s \<midarrow>\<langle> m \<rangle>\<rightarrow> d) \<or> (s, m, d) = (s\<^sub>0, JoinResponse i\<^sub>0 t\<^sub>0 NoApplyResponseSent, OneNode d\<^sub>0))"
    by (auto simp add: isMessageFromTo'_def isMessageFromTo_def)

  have isMessageFrom'_eq [simp]:
    "\<And>s m. (s \<midarrow>\<langle> m \<rangle>\<leadsto>') = ((s \<midarrow>\<langle> m \<rangle>\<leadsto>) \<or> (s, m) = (s\<^sub>0, JoinResponse i\<^sub>0 t\<^sub>0 NoApplyResponseSent))"
    by (auto simp add: isMessageFrom'_def isMessageFrom_def)

  have isMessageTo'_eq [simp]:
    "\<And>m d. (\<langle> m \<rangle>\<rightarrow>' d) = ((\<langle> m \<rangle>\<rightarrow> d) \<or> (m, d) = (JoinResponse i\<^sub>0 t\<^sub>0 NoApplyResponseSent, OneNode d\<^sub>0))"
    by (auto simp add: isMessageTo'_def isMessageTo_def)

  have isMessage'_eq [simp]:
    "\<And>m. (\<langle> m \<rangle>\<leadsto>') = ((\<langle> m \<rangle>\<leadsto>) \<or> m = JoinResponse i\<^sub>0 t\<^sub>0 NoApplyResponseSent)"
    by (auto simp add: isMessage'_def isMessage_def)

  have messages_simps:
    "\<And>i s d t t' x'. (s \<midarrow>\<langle> JoinResponse i t (ApplyResponseSent t' x') \<rangle>\<rightarrow>' d)
        = (s \<midarrow>\<langle> JoinResponse i t (ApplyResponseSent t' x') \<rangle>\<rightarrow> d)"
    "\<And>i s d t x. (s \<midarrow>\<langle> ApplyRequest i t x \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>i s d t x. (s \<midarrow>\<langle> ApplyRequest i t x \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>i s d t. (s \<midarrow>\<langle> ApplyResponse i t\<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyResponse i t \<rangle>\<rightarrow> d)"
    "\<And>i s d t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)"
    by auto

  define promised' where "\<And>i s d t. promised' i s d t \<equiv> \<exists>i'\<le>i. \<exists>a. s \<midarrow>\<langle> JoinResponse i' t a \<rangle>\<rightarrow>' (OneNode d)"
  have promised'I: "\<And>i s d t. promised i s d t \<Longrightarrow> promised' i s d t" 
    by (auto simp add: promised'_def promised_def)

  show ?thesis
    apply (unfold_locales)
                   apply (fold isMessageFromTo'_def)
                   apply (unfold messages_simps)
                   apply (fold isMessageFrom_def isMessageTo_def)
                   apply (fold isMessageFrom'_def isMessageTo'_def)
                   apply (fold isMessage_def isMessage'_def)
                   apply (fold isCommitted_def)
                   apply (fold committedTo_def)
                   apply (fold v_def)
                   apply (fold v\<^sub>c_def)
                   apply (fold era\<^sub>i_def)
                   apply (fold reconfig_def)
                   apply (fold Q_def)
                   apply (fold promised'_def)
                   apply (fold prevAccepted_def)
    using ApplyResponse_ApplyRequest ApplyRequest_era ApplyCommit_quorum ApplyRequest_function
      ApplyRequest_committedTo JoinResponse_Some_lt JoinResponse_Some_ApplyResponse
      JoinResponse_Some_max finite_messages_insert JoinResponse_Some_ApplyRequest
  proof -
    show "\<And>i i' s t t' a. s \<midarrow>\<langle> JoinResponse i t a \<rangle>\<leadsto>' \<Longrightarrow> i < i' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> ApplyResponse i' t' \<rangle>\<leadsto>"
      using JoinResponse_future assms by auto
    show "\<And>i s t t'. s \<midarrow>\<langle> JoinResponse i t NoApplyResponseSent \<rangle>\<leadsto>' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> ApplyResponse i t' \<rangle>\<leadsto>"
      using JoinResponse_None assms by auto
    show "\<And>i t a d. \<langle> JoinResponse i t a \<rangle>\<rightarrow>' d \<Longrightarrow> d \<noteq> Broadcast"
      using JoinResponse_not_broadcast by auto
    show "\<And>i' i s t a a' d d'. s \<midarrow>\<langle> JoinResponse i t a \<rangle>\<rightarrow>' d \<Longrightarrow> s \<midarrow>\<langle> JoinResponse i' t a' \<rangle>\<rightarrow>' d' \<Longrightarrow> d = d'"
      using JoinResponse_unique_destination assms isMessageFrom_def by auto
    show "\<And>i s t a. s \<midarrow>\<langle> JoinResponse i t a \<rangle>\<leadsto>' \<Longrightarrow> \<exists>i'\<le>i. committed\<^sub>< i' \<and> era\<^sub>t t \<le> era\<^sub>i i'"
      using JoinResponse_era assms committedTo_def isCommitted_def by auto
    show "\<And>i s t x. s \<midarrow>\<langle> ApplyRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>Q (era\<^sub>t t). (\<forall>n\<in>q. promised' i n s t) \<and> (prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q)))"
      by (meson ApplyRequest_quorum promised'I)
  qed
qed

text \<open>In contrast, @{term "JoinResponse i\<^sub>0 t\<^sub>0 (ApplyRequestSent t\<^sub>0'
x\<^sub>0')"} can be sent if an @{term ApplyResponse} message has been sent for slot @{term
i\<^sub>0}, in which case @{term t\<^sub>0'} must be the greatest term of any such message
previously sent by node @{term n\<^sub>0} and @{term x\<^sub>0'} is the corresponding
value.}:\<close>

lemma (in zen) send_JoinResponse_Some:
  assumes "\<forall> i > i\<^sub>0. \<forall> t. \<not> s\<^sub>0 \<midarrow>\<langle> ApplyResponse i t \<rangle>\<leadsto>"
  assumes "s\<^sub>0 \<midarrow>\<langle> ApplyResponse i\<^sub>0 t\<^sub>0' \<rangle>\<leadsto>"
  assumes "\<langle> ApplyRequest i\<^sub>0 t\<^sub>0' x\<^sub>0' \<rangle>\<leadsto>"
  assumes "t\<^sub>0' < t\<^sub>0"
  assumes "\<forall> t'. s\<^sub>0 \<midarrow>\<langle> ApplyResponse i\<^sub>0 t' \<rangle>\<leadsto> \<longrightarrow> t' \<le> t\<^sub>0'"
    (* first-uncommitted slot, the era is ok, and not already sent*)
  assumes "\<forall> i < i\<^sub>0. \<exists> t. \<langle> ApplyCommit i t \<rangle>\<leadsto>"
  assumes "era\<^sub>t t\<^sub>0 = era\<^sub>i i\<^sub>0"
  assumes "\<forall> i a. \<not> s\<^sub>0 \<midarrow>\<langle> JoinResponse i t\<^sub>0 a \<rangle>\<leadsto>"
    (* *)
  shows   "zen (insert \<lparr> sender = s\<^sub>0, destination = OneNode d\<^sub>0,
                         payload = JoinResponse i\<^sub>0 t\<^sub>0 (ApplyResponseSent t\<^sub>0' x\<^sub>0') \<rparr> messages)" (is "zen ?messages'")
proof -
  define isMessageFromTo' :: "Node \<Rightarrow> Message \<Rightarrow> Destination \<Rightarrow> bool" ("_ \<midarrow>\<langle> _ \<rangle>\<rightarrow>' _" [55]) where
    "\<And>s m d. s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d \<equiv> \<lparr> sender = s, destination = d, payload = m \<rparr> \<in> ?messages'"

  define isMessageFrom' :: "Node \<Rightarrow> Message \<Rightarrow> bool" ("_ \<midarrow>\<langle> _ \<rangle>\<leadsto>'" [55]) where
    "\<And>s m. s \<midarrow>\<langle> m \<rangle>\<leadsto>' \<equiv> \<exists> d. s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d"

  define isMessageTo' :: "Message \<Rightarrow> Destination \<Rightarrow> bool" ("\<langle> _ \<rangle>\<rightarrow>' _" [55]) where
    "\<And>m d. \<langle> m \<rangle>\<rightarrow>' d \<equiv> \<exists> s. s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d"

  define isMessage' :: "Message \<Rightarrow> bool" ("\<langle> _ \<rangle>\<leadsto>'" [55]) where
    "\<And>m. \<langle> m \<rangle>\<leadsto>' \<equiv> \<exists> s. s \<midarrow>\<langle> m \<rangle>\<leadsto>'"

  have isMessageFromTo'_eq [simp]:
    "\<And>s m d. (s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d) = ((s \<midarrow>\<langle> m \<rangle>\<rightarrow> d) \<or> (s, m, d) = (s\<^sub>0, JoinResponse i\<^sub>0 t\<^sub>0 (ApplyResponseSent t\<^sub>0' x\<^sub>0'), OneNode d\<^sub>0))"
    by (auto simp add: isMessageFromTo'_def isMessageFromTo_def)

  have isMessageFrom'_eq [simp]:
    "\<And>s m. (s \<midarrow>\<langle> m \<rangle>\<leadsto>') = ((s \<midarrow>\<langle> m \<rangle>\<leadsto>) \<or> (s, m) = (s\<^sub>0, JoinResponse i\<^sub>0 t\<^sub>0 (ApplyResponseSent t\<^sub>0' x\<^sub>0')))"
    by (auto simp add: isMessageFrom'_def isMessageFrom_def)

  have isMessageTo'_eq [simp]:
    "\<And>m d. (\<langle> m \<rangle>\<rightarrow>' d) = ((\<langle> m \<rangle>\<rightarrow> d) \<or> (m, d) = (JoinResponse i\<^sub>0 t\<^sub>0 (ApplyResponseSent t\<^sub>0' x\<^sub>0'), OneNode d\<^sub>0))"
    by (auto simp add: isMessageTo'_def isMessageTo_def)

  have isMessage'_eq [simp]:
    "\<And>m. (\<langle> m \<rangle>\<leadsto>') = ((\<langle> m \<rangle>\<leadsto>) \<or> m = JoinResponse i\<^sub>0 t\<^sub>0 (ApplyResponseSent t\<^sub>0' x\<^sub>0'))"
    by (auto simp add: isMessage'_def isMessage_def)

  have messages_simps:
    "\<And>i s d t. (s \<midarrow>\<langle> JoinResponse i t NoApplyResponseSent \<rangle>\<rightarrow>' d)
        = (s \<midarrow>\<langle> JoinResponse i t NoApplyResponseSent \<rangle>\<rightarrow> d)"
    "\<And>i s d t x. (s \<midarrow>\<langle> ApplyRequest i t x \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>i s d t. (s \<midarrow>\<langle> ApplyResponse i t\<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyResponse i t \<rangle>\<rightarrow> d)"
    "\<And>i s d t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)"
    by auto

  define promised' where "\<And>i s d t. promised' i s d t \<equiv> \<exists>i'\<le>i. \<exists>a. s \<midarrow>\<langle> JoinResponse i' t a \<rangle>\<rightarrow>' (OneNode d)"
  have promised'I: "\<And>i s d t. promised i s d t \<Longrightarrow> promised' i s d t" 
    by (auto simp add: promised'_def promised_def)

  define prevAccepted' where "\<And>i t senders. prevAccepted' i t senders
      \<equiv> {t'. \<exists>s\<in>senders. \<exists>x'. s \<midarrow>\<langle> JoinResponse i t (ApplyResponseSent t' x') \<rangle>\<leadsto>'}"

  show ?thesis
    apply (unfold_locales)
                   apply (fold isMessageFromTo'_def)
                   apply (unfold messages_simps)
                   apply (fold isMessageFrom_def isMessageTo_def)
                   apply (fold isMessageFrom'_def isMessageTo'_def)
                   apply (fold isMessage_def isMessage'_def)
                   apply (fold isCommitted_def)
                   apply (fold committedTo_def)
                   apply (fold v_def)
                   apply (fold v\<^sub>c_def)
                   apply (fold era\<^sub>i_def)
                   apply (fold reconfig_def)
                   apply (fold Q_def)
                   apply (fold promised'_def)
                   apply (fold prevAccepted'_def)
   using JoinResponse_None ApplyRequest_committedTo ApplyRequest_function finite_messages_insert
      ApplyResponse_ApplyRequest ApplyRequest_era  ApplyCommit_quorum
  proof -

    from assms JoinResponse_future
    show "\<And>i i' s t t' a. s \<midarrow>\<langle> JoinResponse i t a \<rangle>\<leadsto>'
      \<Longrightarrow> i < i' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> ApplyResponse i' t' \<rangle>\<leadsto>" by auto

    from assms JoinResponse_era
    show "\<And>i s t a. s \<midarrow>\<langle> JoinResponse i t a \<rangle>\<leadsto>' \<Longrightarrow> \<exists>i'\<le>i. committed\<^sub>< i' \<and> era\<^sub>t t \<le> era\<^sub>i i'"
      by (auto simp add: committedTo_def isCommitted_def)

    from assms JoinResponse_Some_lt
    show "\<And>i s t t' x'. s \<midarrow>\<langle> JoinResponse i t (ApplyResponseSent t' x') \<rangle>\<leadsto>' \<Longrightarrow> t' < t" by auto

    from assms JoinResponse_Some_ApplyResponse
    show "\<And>i s t t' x'. s \<midarrow>\<langle> JoinResponse i t (ApplyResponseSent t' x') \<rangle>\<leadsto>' \<Longrightarrow> s \<midarrow>\<langle> ApplyResponse i t' \<rangle>\<leadsto>" by auto

    from assms JoinResponse_Some_ApplyRequest
    show "\<And>i s t t' x'. s \<midarrow>\<langle> JoinResponse i t (ApplyResponseSent t' x') \<rangle>\<leadsto>' \<Longrightarrow> \<langle> ApplyRequest i t' x' \<rangle>\<leadsto>" by auto

    from assms JoinResponse_Some_max
    show "\<And>i s t t' t'' x'. s \<midarrow>\<langle> JoinResponse i t (ApplyResponseSent t' x') \<rangle>\<leadsto>' \<Longrightarrow> t' < t'' \<Longrightarrow> t'' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> ApplyResponse i t'' \<rangle>\<leadsto>"
      by auto

    show "\<And>i t a d. \<langle> JoinResponse i t a \<rangle>\<rightarrow>' d \<Longrightarrow> d \<noteq> Broadcast"
      using JoinResponse_not_broadcast isMessageTo'_eq by blast
    show "\<And>i' i s t a a' d d'. s \<midarrow>\<langle> JoinResponse i t a \<rangle>\<rightarrow>' d \<Longrightarrow> s \<midarrow>\<langle> JoinResponse i' t a' \<rangle>\<rightarrow>' d' \<Longrightarrow> d = d'"
      using JoinResponse_unique_destination assms isMessageFrom_def by auto
  next
    fix i s t x assume "s \<midarrow>\<langle> ApplyRequest i t x \<rangle>\<leadsto>"
    from ApplyRequest_quorum [OF this]
    obtain q
      where q: "q\<in>Q (era\<^sub>t t)" "\<forall>n\<in>q. promised i n s t"
        "prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q))" by blast

    have "prevAccepted i t q \<subseteq> prevAccepted' i t q"
      by (auto simp add: prevAccepted'_def prevAccepted_def)

    moreover have "prevAccepted' i t q \<subseteq> prevAccepted i t q"
    proof
      fix t' assume "t' \<in> prevAccepted' i t q"
      then obtain s' x' where s': "s' \<in> q" "s' \<midarrow>\<langle> JoinResponse i t (ApplyResponseSent t' x') \<rangle>\<leadsto>'" 
        by (unfold prevAccepted'_def, blast)
      from s' have "s' \<midarrow>\<langle> JoinResponse i t (ApplyResponseSent t' x') \<rangle>\<leadsto> \<or> (s', i, t, t', x') = (s\<^sub>0, i\<^sub>0, t\<^sub>0, t\<^sub>0', x\<^sub>0')"
        by simp
      with assms q s' have "s' \<midarrow>\<langle> JoinResponse i t (ApplyResponseSent t' x') \<rangle>\<leadsto>"
        by (metis prod.inject promised_long_def)
      with s' show "t' \<in> prevAccepted i t q" 
        by (auto simp add: prevAccepted_def)
    qed

    ultimately have prevAccepted_eq: "prevAccepted' i t q = prevAccepted i t q" by simp

    from q
    show "\<exists>q\<in>Q (era\<^sub>t t). (\<forall>n\<in>q. promised' i n s t) \<and> (prevAccepted' i t q = {} \<or> v i t = v i (maxTerm (prevAccepted' i t q)))"
      by (intro bexI [where x = q] conjI ballI promised'I, simp_all add: prevAccepted_eq)
  qed
qed

subsubsection \<open>Sending @{term ApplyRequest} messages\<close>

text \<open>@{term "ApplyRequest i\<^sub>0 t\<^sub>0 x\<^sub>0"} can be sent if \begin{itemize}
\item no other value has previously been sent for this $\langle \mathrm{slot}, \mathrm{term}
\rangle$ pair, \item all slots below @{term i\<^sub>0} are committed, \item a quorum of nodes have
sent @{term JoinResponse} messages for term @{term t\<^sub>0}, and \item the value proposed is the
value accepted in the greatest term amongst all @{term JoinResponse} messages, if any.
\end{itemize} \<close>

lemma (in zen) send_ApplyRequest:
  assumes "\<forall> x. \<not> s\<^sub>0 \<midarrow>\<langle> ApplyRequest i\<^sub>0 t\<^sub>0 x \<rangle>\<leadsto>"
  assumes "\<forall> i < i\<^sub>0. \<exists> t. \<langle> ApplyCommit i t \<rangle>\<leadsto>"
  assumes "era\<^sub>t t\<^sub>0 = era\<^sub>i i\<^sub>0"
  assumes "q \<in> Q (era\<^sub>t t\<^sub>0)"
  assumes "\<forall> s \<in> q. \<exists> i \<le> i\<^sub>0. \<exists> a. s \<midarrow>\<langle> JoinResponse i t\<^sub>0 a \<rangle>\<rightarrow> (OneNode s\<^sub>0)"
  assumes "prevAccepted i\<^sub>0 t\<^sub>0 q \<noteq> {}
    \<longrightarrow> x\<^sub>0 = v i\<^sub>0 (maxTerm (prevAccepted i\<^sub>0 t\<^sub>0 q))"
  shows "zen (insert \<lparr> sender = s\<^sub>0, destination = d\<^sub>0,
                       payload = ApplyRequest i\<^sub>0 t\<^sub>0 x\<^sub>0 \<rparr> messages)" (is "zen ?messages'")
proof -
  have quorum_promised: "\<forall>n\<in>q. promised i\<^sub>0 n s\<^sub>0 t\<^sub>0"
    by (simp add: assms promised_def)

  have nobody_proposed: "\<forall> x. \<not> \<langle> ApplyRequest i\<^sub>0 t\<^sub>0 x \<rangle>\<leadsto>"
  proof (intro allI notI)
    fix x assume "\<langle> ApplyRequest i\<^sub>0 t\<^sub>0 x \<rangle>\<leadsto>"
    then obtain s where s: "s \<midarrow>\<langle> ApplyRequest i\<^sub>0 t\<^sub>0 x \<rangle>\<leadsto>" by (unfold isMessage_def, blast)
    from ApplyRequest_quorum [OF this]
    obtain q' where q'_quorum: "q' \<in> Q (era\<^sub>t t\<^sub>0)"
      and q'_promised: "\<And>n. n \<in> q' \<Longrightarrow> promised i\<^sub>0 n s t\<^sub>0" by auto

    from q'_quorum `q \<in> Q (era\<^sub>t t\<^sub>0)` obtain n where "n \<in> q" "n \<in> q'"
      using Q_intersects intersects_def by force

    from `n \<in> q` quorum_promised have "promised i\<^sub>0 n s\<^sub>0 t\<^sub>0" by simp
    moreover from `n \<in> q'` q'_promised have "promised i\<^sub>0 n s t\<^sub>0" by simp

    ultimately have "s = s\<^sub>0" by (intro promised_unique)
    with assms s show False by simp
  qed

  define isMessageFromTo' :: "Node \<Rightarrow> Message \<Rightarrow> Destination \<Rightarrow> bool" ("_ \<midarrow>\<langle> _ \<rangle>\<rightarrow>' _" [55]) where
    "\<And>s m d. s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d \<equiv> \<lparr> sender = s, destination = d, payload = m \<rparr> \<in> ?messages'"

  define isMessageFrom' :: "Node \<Rightarrow> Message \<Rightarrow> bool" ("_ \<midarrow>\<langle> _ \<rangle>\<leadsto>'" [55]) where
    "\<And>s m. s \<midarrow>\<langle> m \<rangle>\<leadsto>' \<equiv> \<exists> d. s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d"

  define isMessageTo' :: "Message \<Rightarrow> Destination \<Rightarrow> bool" ("\<langle> _ \<rangle>\<rightarrow>' _" [55]) where
    "\<And>m d. \<langle> m \<rangle>\<rightarrow>' d \<equiv> \<exists> s. s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d"

  define isMessage' :: "Message \<Rightarrow> bool" ("\<langle> _ \<rangle>\<leadsto>'" [55]) where
    "\<And>m. \<langle> m \<rangle>\<leadsto>' \<equiv> \<exists> s. s \<midarrow>\<langle> m \<rangle>\<leadsto>'"

  have isMessageFromTo'_eq [simp]:
    "\<And>s m d. (s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d) = ((s \<midarrow>\<langle> m \<rangle>\<rightarrow> d) \<or> (s, m, d) = (s\<^sub>0, ApplyRequest i\<^sub>0 t\<^sub>0 x\<^sub>0, d\<^sub>0))"
    by (auto simp add: isMessageFromTo'_def isMessageFromTo_def)

  have isMessageFrom'_eq [simp]:
    "\<And>s m. (s \<midarrow>\<langle> m \<rangle>\<leadsto>') = ((s \<midarrow>\<langle> m \<rangle>\<leadsto>) \<or> (s, m) = (s\<^sub>0, ApplyRequest i\<^sub>0 t\<^sub>0 x\<^sub>0))"
    by (auto simp add: isMessageFrom'_def isMessageFrom_def)

  have isMessageTo'_eq [simp]:
    "\<And>m d. (\<langle> m \<rangle>\<rightarrow>' d) = ((\<langle> m \<rangle>\<rightarrow> d) \<or> (m, d) = (ApplyRequest i\<^sub>0 t\<^sub>0 x\<^sub>0, d\<^sub>0))"
    by (auto simp add: isMessageTo'_def isMessageTo_def)

  have isMessage'_eq [simp]:
    "\<And>m. (\<langle> m \<rangle>\<leadsto>') = ((\<langle> m \<rangle>\<leadsto>) \<or> m = ApplyRequest i\<^sub>0 t\<^sub>0 x\<^sub>0)"
    by (auto simp add: isMessage'_def isMessage_def)

  have messages_simps:
    "\<And>i s d t a. (s \<midarrow>\<langle> JoinResponse i t a \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> JoinResponse i t a \<rangle>\<rightarrow> d)"
    "\<And>i s d t. (s \<midarrow>\<langle> ApplyResponse i t\<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyResponse i t \<rangle>\<rightarrow> d)"
    "\<And>i s d t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)"
    by auto

  define v' where "\<And>i t. v' i t \<equiv> THE x. \<langle> ApplyRequest i t x \<rangle>\<leadsto>'"
  define v\<^sub>c' where "\<And>i. v\<^sub>c' i \<equiv> v' i (SOME t. \<langle> ApplyCommit i t \<rangle>\<leadsto>)"
  define era\<^sub>i' where "\<And>i. era\<^sub>i' i \<equiv> eraOfNat (card {j. j < i \<and> isReconfiguration (v\<^sub>c' j)})"
  define reconfig' where "\<And>e. reconfig' e \<equiv> THE i. isCommitted i \<and> isReconfiguration (v\<^sub>c' i) \<and> era\<^sub>i' i = e"
  define Q' where "\<And>e. Q' e \<equiv> case e of e\<^sub>0 \<Rightarrow> Q\<^sub>0 | nextEra e' \<Rightarrow> getConf (v\<^sub>c' (reconfig' e'))"

  have v_eq: "\<And>i t. v' i t = (if (i, t) = (i\<^sub>0, t\<^sub>0) then x\<^sub>0 else v i t)"
  proof -
    fix i t
    show "?thesis i t"
    proof (cases "(i, t) = (i\<^sub>0, t\<^sub>0)")
      case False
      hence eq: "\<And>x. \<langle> ApplyRequest i t x \<rangle>\<leadsto>' = \<langle> ApplyRequest i t x \<rangle>\<leadsto>" by auto
      from False show ?thesis by (unfold v'_def eq, auto simp add: v_def)
    next
      case True with nobody_proposed have eq: "\<And>x. \<langle> ApplyRequest i t x \<rangle>\<leadsto>' = (x = x\<^sub>0)" by auto
      from True show ?thesis using eq by (unfold v'_def eq, auto)
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
      with v_eq assms nobody_proposed show ?thesis apply (simp add: v\<^sub>c_def v\<^sub>c'_def)
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
            by (simp add: less_Era_def nextEra)
          from Suc.prems show "committed\<^sub>< (Suc i)" .
        qed
      qed
    qed
  qed

  show ?thesis
    apply (unfold_locales)
                   apply (fold isMessageFromTo'_def)
                   apply (unfold messages_simps)
                   apply (fold isMessageFrom_def isMessageTo_def)
                   apply (fold isMessageFrom'_def isMessageTo'_def)
                   apply (fold isMessage_def isMessage'_def)
                   apply (fold isCommitted_def)
                   apply (fold committedTo_def)
                   apply (fold v'_def)
                   apply (fold v\<^sub>c'_def)
                   apply (fold era\<^sub>i'_def)
                   apply (fold reconfig'_def)
                   apply (fold Q'_def)
                   apply (fold promised_def)
                   apply (fold prevAccepted_def)
    using  JoinResponse_future JoinResponse_None  JoinResponse_Some_lt JoinResponse_Some_ApplyResponse
            JoinResponse_Some_max  finite_messages_insert JoinResponse_not_broadcast
            JoinResponse_unique_destination
  proof -
    from assms ApplyRequest_committedTo show committedTo: "\<And>i t x. \<langle> ApplyRequest i t x \<rangle>\<leadsto>' \<Longrightarrow> committed\<^sub>< i" 
      by (auto simp add: committedTo_def isCommitted_def)

    from nobody_proposed ApplyRequest_function show "\<And>i t x x'. \<langle> ApplyRequest i t x \<rangle>\<leadsto>' \<Longrightarrow> \<langle> ApplyRequest i t x' \<rangle>\<leadsto>' \<Longrightarrow> x = x'"
      by auto

    from ApplyResponse_ApplyRequest show "\<And>i s t. s \<midarrow>\<langle> ApplyResponse i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>x. \<langle> ApplyRequest i t x \<rangle>\<leadsto>'"
      using isMessage'_eq by blast

    from ApplyRequest_era era\<^sub>i_eq have "\<And>i t x. \<langle> ApplyRequest i t x \<rangle>\<leadsto> \<Longrightarrow> era\<^sub>i' i = era\<^sub>t t"
      by (simp add: ApplyRequest_committedTo)

    with assms committedTo show "\<And>i t x. \<langle> ApplyRequest i t x \<rangle>\<leadsto>' \<Longrightarrow> era\<^sub>i' i = era\<^sub>t t"
      by (metis Message.inject(3) era\<^sub>i_eq isMessage'_eq)

    show "\<And>i s t a. s \<midarrow>\<langle> JoinResponse i t a \<rangle>\<leadsto> \<Longrightarrow> \<exists>i'\<le>i. committed\<^sub>< i' \<and> era\<^sub>t t \<le> era\<^sub>i' i'"
      using JoinResponse_era era\<^sub>i_eq by force

    from JoinResponse_Some_ApplyRequest
    show "\<And>i s t t' x'. s \<midarrow>\<langle> JoinResponse i t (ApplyResponseSent t' x') \<rangle>\<leadsto> \<Longrightarrow> \<langle> ApplyRequest i t' x' \<rangle>\<leadsto>'" by auto

  next
    fix i t
    assume a: "\<langle> ApplyCommit i t \<rangle>\<leadsto>"
    hence "committed\<^sub>< i" using ApplyCommit_ApplyRequest ApplyRequest_committedTo by blast
    hence "Q' (era\<^sub>i i) = Q (era\<^sub>i i)" by (simp add: Q'_eq)
    moreover from a have "era\<^sub>t t = era\<^sub>i i"
      using ApplyCommit_era by auto
    moreover note ApplyCommit_quorum [OF a]
    ultimately show "\<exists>q\<in>Q' (era\<^sub>t t). \<forall>s\<in>q. s \<midarrow>\<langle> ApplyResponse i t \<rangle>\<leadsto>" by simp
  next
    fix i s t x
    assume "s \<midarrow>\<langle> ApplyRequest i t x \<rangle>\<leadsto>'"
    hence "s \<midarrow>\<langle> ApplyRequest i t x \<rangle>\<leadsto> \<or> (s, i, t, x) = (s\<^sub>0, i\<^sub>0, t\<^sub>0, x\<^sub>0)" by simp
    thus "\<exists>q\<in>Q' (era\<^sub>t t). (\<forall>n\<in>q. promised i n s t) \<and> (prevAccepted i t q = {} \<or> v' i t = v' i (maxTerm (prevAccepted i t q)))"
    proof (elim disjE)
      assume a': "s \<midarrow>\<langle> ApplyRequest i t x \<rangle>\<leadsto>"
      hence a: "\<langle> ApplyRequest i t x \<rangle>\<leadsto>" by (auto simp add: isMessage_def)

      from ApplyRequest_quorum [OF a']
      obtain q where q: "q \<in> Q (era\<^sub>t t)" "\<forall> n \<in> q. promised i n s t"
        and disj: "prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q))" by blast

      from era\<^sub>i_contiguous ApplyRequest_era a
      obtain i' where "era\<^sub>i i' = era\<^sub>t t" and i':"i' \<le> i" by blast
      hence era_eq: "era\<^sub>t t = era\<^sub>i i'" by simp

      have Q_eq: "Q' (era\<^sub>t t) = Q (era\<^sub>t t)"
        using i' ApplyRequest_committedTo [OF a]
        by (unfold era_eq, intro Q'_eq, auto simp add: committedTo_def)

      have v_eq1: "v' i t = v i t" using a assms v_eq
        using nobody_proposed by auto

      show ?thesis
      proof (cases "prevAccepted i t q = {}")
        case True with q show ?thesis by (intro bexI [of _ q], simp_all add: Q_eq v_eq1)
      next
        case False
        have "maxTerm (prevAccepted i t q) \<in> prevAccepted i t q"
          by (intro maxTerm_mem finite_prevAccepted False)
        hence v_eq2: "v' i (maxTerm (prevAccepted i t q)) = v i (maxTerm (prevAccepted i t q))"
          apply (unfold v_eq, simp)
          using JoinResponse_Some_ApplyRequest nobody_proposed prevAccepted_def by fastforce
        from q disj show ?thesis
          by (intro bexI [of _ q], simp_all add: Q_eq v_eq1 v_eq2)
      qed
    next
      assume "(s, i, t, x) = (s\<^sub>0, i\<^sub>0, t\<^sub>0, x\<^sub>0)"
      hence fixed_simps: "s = s\<^sub>0" "i = i\<^sub>0" "t = t\<^sub>0" "x = x\<^sub>0" "v' i\<^sub>0 t\<^sub>0 = x\<^sub>0" by (simp_all add: v_eq)

      obtain i' where era_eq: "era\<^sub>t t\<^sub>0 = era\<^sub>i i'" "i' \<le> i"
        using assms fixed_simps by blast
      hence "Q' (era\<^sub>t t\<^sub>0) = Q (era\<^sub>t t\<^sub>0)"
        apply (unfold era_eq, intro Q'_eq)
        by (simp add: assms committedTo_def fixed_simps isCommitted_def)
      note fixed_simps = fixed_simps this

      show "\<exists>q\<in>Q' (era\<^sub>t t). (\<forall>n\<in>q. promised i n s t) \<and> (prevAccepted i t q = {} \<or> v' i t = v' i (maxTerm (prevAccepted i t q)))"
      proof (unfold fixed_simps, intro bexI [where x = q] conjI quorum_promised assms)

        from assms
        show "prevAccepted i\<^sub>0 t\<^sub>0 q = {} \<or> x\<^sub>0 = v' i\<^sub>0 (maxTerm (prevAccepted i\<^sub>0 t\<^sub>0 q))"
          by (cases "maxTerm (prevAccepted i\<^sub>0 t\<^sub>0 q) = t\<^sub>0", auto simp add: v_eq)
      qed
    qed
  qed
qed

subsubsection \<open>Sending @{term ApplyResponse} messages\<close>

text \<open>@{term "ApplyResponse i\<^sub>0 t\<^sub>0"} can be sent in response to an @{term ApplyRequest}
as long as a @{term JoinResponse} for a later term has not been sent:\<close>

lemma (in zen) send_ApplyResponse:
  assumes "\<langle> ApplyRequest i\<^sub>0 t\<^sub>0 x\<^sub>0 \<rangle>\<leadsto>"
  assumes "\<forall> i t a. s\<^sub>0 \<midarrow>\<langle> JoinResponse i t a \<rangle>\<leadsto> \<longrightarrow> t \<le> t\<^sub>0"
  shows "zen (insert \<lparr> sender = s\<^sub>0, destination = d\<^sub>0,
                       payload = ApplyResponse i\<^sub>0 t\<^sub>0 \<rparr> messages)" (is "zen ?messages'")
proof -
  define isMessageFromTo' :: "Node \<Rightarrow> Message \<Rightarrow> Destination \<Rightarrow> bool" ("_ \<midarrow>\<langle> _ \<rangle>\<rightarrow>' _" [55]) where
    "\<And>s m d. s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d \<equiv> \<lparr> sender = s, destination = d, payload = m \<rparr> \<in> ?messages'"

  define isMessageFrom' :: "Node \<Rightarrow> Message \<Rightarrow> bool" ("_ \<midarrow>\<langle> _ \<rangle>\<leadsto>'" [55]) where
    "\<And>s m. s \<midarrow>\<langle> m \<rangle>\<leadsto>' \<equiv> \<exists> d. s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d"

  define isMessageTo' :: "Message \<Rightarrow> Destination \<Rightarrow> bool" ("\<langle> _ \<rangle>\<rightarrow>' _" [55]) where
    "\<And>m d. \<langle> m \<rangle>\<rightarrow>' d \<equiv> \<exists> s. s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d"

  define isMessage' :: "Message \<Rightarrow> bool" ("\<langle> _ \<rangle>\<leadsto>'" [55]) where
    "\<And>m. \<langle> m \<rangle>\<leadsto>' \<equiv> \<exists> s. s \<midarrow>\<langle> m \<rangle>\<leadsto>'"

  have isMessageFromTo'_eq [simp]:
    "\<And>s m d. (s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d) = ((s \<midarrow>\<langle> m \<rangle>\<rightarrow> d) \<or> (s, m, d) = (s\<^sub>0, ApplyResponse i\<^sub>0 t\<^sub>0, d\<^sub>0))"
    by (auto simp add: isMessageFromTo'_def isMessageFromTo_def)

  have isMessageFrom'_eq [simp]:
    "\<And>s m. (s \<midarrow>\<langle> m \<rangle>\<leadsto>') = ((s \<midarrow>\<langle> m \<rangle>\<leadsto>) \<or> (s, m) = (s\<^sub>0, ApplyResponse i\<^sub>0 t\<^sub>0))"
    by (auto simp add: isMessageFrom'_def isMessageFrom_def)

  have isMessageTo'_eq [simp]:
    "\<And>m d. (\<langle> m \<rangle>\<rightarrow>' d) = ((\<langle> m \<rangle>\<rightarrow> d) \<or> (m, d) = (ApplyResponse i\<^sub>0 t\<^sub>0, d\<^sub>0))"
    by (auto simp add: isMessageTo'_def isMessageTo_def)

  have isMessage'_eq [simp]:
    "\<And>m. (\<langle> m \<rangle>\<leadsto>') = ((\<langle> m \<rangle>\<leadsto>) \<or> m = ApplyResponse i\<^sub>0 t\<^sub>0)"
    by (auto simp add: isMessage'_def isMessage_def)

  have messages_simps:
    "\<And>i s d t a. (s \<midarrow>\<langle> JoinResponse i t a \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> JoinResponse i t a \<rangle>\<rightarrow> d)"
    "\<And>i s d t x. (s \<midarrow>\<langle> ApplyRequest i t x\<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>i s d t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)"
    by auto

  show ?thesis
    apply (unfold_locales)
                   apply (fold isMessageFromTo'_def)
                   apply (unfold messages_simps)
                   apply (fold isMessageFrom_def isMessageTo_def)
                   apply (fold isMessageFrom'_def isMessageTo'_def)
                   apply (fold isMessage_def isMessage'_def)
                   apply (fold isCommitted_def)
                   apply (fold committedTo_def)
                   apply (fold v_def)
                   apply (fold v\<^sub>c_def)
                   apply (fold era\<^sub>i_def)
                   apply (fold reconfig_def)
                   apply (fold Q_def)
                   apply (fold promised_def)
                   apply (fold prevAccepted_def)
    using JoinResponse_Some_lt JoinResponse_era ApplyRequest_committedTo ApplyRequest_quorum
      ApplyRequest_function finite_messages_insert ApplyRequest_era JoinResponse_Some_ApplyRequest
      JoinResponse_unique_destination JoinResponse_not_broadcast
  proof -
    show "\<And>i i' s t t' a. s \<midarrow>\<langle> JoinResponse i t a \<rangle>\<leadsto> \<Longrightarrow> i < i' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> ApplyResponse i' t' \<rangle>\<leadsto>'"
      using JoinResponse_future assms(2) by fastforce
    show "\<And>i s t t'. s \<midarrow>\<langle> JoinResponse i t NoApplyResponseSent \<rangle>\<leadsto> \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> ApplyResponse i t' \<rangle>\<leadsto>'" 
      using JoinResponse_None assms(2) by fastforce
    show "\<And>i s t t' x'. s \<midarrow>\<langle> JoinResponse i t (ApplyResponseSent t' x') \<rangle>\<leadsto> \<Longrightarrow> s \<midarrow>\<langle> ApplyResponse i t' \<rangle>\<leadsto>'"
      using JoinResponse_Some_ApplyResponse by fastforce
    show "\<And>i s t t' t'' x'. s \<midarrow>\<langle> JoinResponse i t (ApplyResponseSent t' x') \<rangle>\<leadsto> \<Longrightarrow> t' < t'' \<Longrightarrow> t'' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> ApplyResponse i t'' \<rangle>\<leadsto>'"
      using JoinResponse_Some_max assms(2) by fastforce
    show "\<And>i s t. s \<midarrow>\<langle> ApplyResponse i t \<rangle>\<leadsto>' \<Longrightarrow> \<exists>x. \<langle> ApplyRequest i t x \<rangle>\<leadsto>"
      using ApplyResponse_ApplyRequest assms(1) by fastforce
    show "\<And>i t. \<langle> ApplyCommit i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>Q (era\<^sub>t t). \<forall>s\<in>q. s \<midarrow>\<langle> ApplyResponse i t \<rangle>\<leadsto>'"
      by (meson ApplyCommit_quorum isMessageFrom'_eq)
  qed
qed

subsubsection \<open>Sending @{term ApplyCommit} messages\<close>

text \<open>@{term "ApplyCommit i\<^sub>0 t\<^sub>0"} can be sent on receipt of a quorum of corresponding
@{term ApplyResponse} messages, where \textit{quorum} is defined in terms of the current
configuration:\<close>

lemma (in zen) send_ApplyCommit:
  assumes "q \<in> Q (era\<^sub>t t\<^sub>0)"
  assumes "\<forall> s \<in> q. s \<midarrow>\<langle> ApplyResponse i\<^sub>0 t\<^sub>0 \<rangle>\<leadsto>"
  shows "zen (insert \<lparr> sender = s\<^sub>0, destination = d\<^sub>0, payload = ApplyCommit i\<^sub>0 t\<^sub>0 \<rparr> messages)" (is "zen ?messages'")
proof -
  have era: "era\<^sub>i i\<^sub>0 = era\<^sub>t t\<^sub>0"
    by (metis ApplyResponse_era Q_member_member assms(1) assms(2))

  define isMessageFromTo' :: "Node \<Rightarrow> Message \<Rightarrow> Destination \<Rightarrow> bool" ("_ \<midarrow>\<langle> _ \<rangle>\<rightarrow>' _" [55]) where
    "\<And>s m d. s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d \<equiv> \<lparr> sender = s, destination = d, payload = m \<rparr> \<in> ?messages'"

  define isMessageFrom' :: "Node \<Rightarrow> Message \<Rightarrow> bool" ("_ \<midarrow>\<langle> _ \<rangle>\<leadsto>'" [55]) where
    "\<And>s m. s \<midarrow>\<langle> m \<rangle>\<leadsto>' \<equiv> \<exists> d. s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d"

  define isMessageTo' :: "Message \<Rightarrow> Destination \<Rightarrow> bool" ("\<langle> _ \<rangle>\<rightarrow>' _" [55]) where
    "\<And>m d. \<langle> m \<rangle>\<rightarrow>' d \<equiv> \<exists> s. s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d"

  define isMessage' :: "Message \<Rightarrow> bool" ("\<langle> _ \<rangle>\<leadsto>'" [55]) where
    "\<And>m. \<langle> m \<rangle>\<leadsto>' \<equiv> \<exists> s. s \<midarrow>\<langle> m \<rangle>\<leadsto>'"

  have isMessageFromTo'_eq [simp]:
    "\<And>s m d. (s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d) = ((s \<midarrow>\<langle> m \<rangle>\<rightarrow> d) \<or> (s, m, d) = (s\<^sub>0, ApplyCommit i\<^sub>0 t\<^sub>0, d\<^sub>0))"
    by (auto simp add: isMessageFromTo'_def isMessageFromTo_def)

  have isMessageFrom'_eq [simp]:
    "\<And>s m. (s \<midarrow>\<langle> m \<rangle>\<leadsto>') = ((s \<midarrow>\<langle> m \<rangle>\<leadsto>) \<or> (s, m) = (s\<^sub>0, ApplyCommit i\<^sub>0 t\<^sub>0))"
    by (auto simp add: isMessageFrom'_def isMessageFrom_def)

  have isMessageTo'_eq [simp]:
    "\<And>m d. (\<langle> m \<rangle>\<rightarrow>' d) = ((\<langle> m \<rangle>\<rightarrow> d) \<or> (m, d) = (ApplyCommit i\<^sub>0 t\<^sub>0, d\<^sub>0))"
    by (auto simp add: isMessageTo'_def isMessageTo_def)

  have isMessage'_eq [simp]:
    "\<And>m. (\<langle> m \<rangle>\<leadsto>') = ((\<langle> m \<rangle>\<leadsto>) \<or> m = ApplyCommit i\<^sub>0 t\<^sub>0)"
    by (auto simp add: isMessage'_def isMessage_def)

  have messages_simps:
    "\<And>i s d t a. (s \<midarrow>\<langle> JoinResponse i t a \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> JoinResponse i t a \<rangle>\<rightarrow> d)"
    "\<And>i s d t x. (s \<midarrow>\<langle> ApplyRequest i t x\<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>i s d t. (s \<midarrow>\<langle> ApplyResponse i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyResponse i t \<rangle>\<rightarrow> d)"
    by auto

  define isCommitted' where "\<And>i. isCommitted' i \<equiv> \<exists>t. \<langle> ApplyCommit i t \<rangle>\<leadsto>'"
  define committedTo' ("committed\<^sub><'") where "\<And>i. committed\<^sub><' i \<equiv> \<forall>j < i. isCommitted' j"
  define v\<^sub>c' where "\<And>i. v\<^sub>c' i \<equiv> v i (SOME t. \<langle> ApplyCommit i t \<rangle>\<leadsto>')"
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

  have v\<^sub>c_eq: "\<And>i. isCommitted i \<Longrightarrow> v\<^sub>c' i = v\<^sub>c i"
  proof -
    fix i assume i: "isCommitted i"
    show "?thesis i"
    proof (cases "i = i\<^sub>0")
      case False thus ?thesis by (simp add: v\<^sub>c_def v\<^sub>c'_def)
    next
      case True
      define t  where "t  \<equiv> SOME t. \<langle> ApplyCommit i\<^sub>0 t \<rangle>\<leadsto>"
      define t' where "t' \<equiv> SOME t. \<langle> ApplyCommit i\<^sub>0 t \<rangle>\<leadsto>'"

      have eq:  "v\<^sub>c  i\<^sub>0 = v i\<^sub>0 t"  by (simp add: v\<^sub>c_def t_def)
      have eq': "v\<^sub>c' i\<^sub>0 = v i\<^sub>0 t'" by (simp add: v\<^sub>c'_def t'_def)

      show ?thesis
        apply (unfold True eq eq')
      proof (intro oneSlot.consistent [OF oneSlot.commit [OF zen_is_oneSlot]])
        from assms show "q \<in> (Q \<circ> era\<^sub>t) t\<^sub>0" "\<And>s. s \<in> q \<Longrightarrow> s \<midarrow>\<langle> ApplyResponse i\<^sub>0 t\<^sub>0 \<rangle>\<leadsto>"
          by simp_all

        from i have "\<langle> ApplyCommit i\<^sub>0 t \<rangle>\<leadsto>" by (metis True isCommitted_def someI_ex t_def)
        thus "\<langle> ApplyCommit i\<^sub>0 t \<rangle>\<leadsto> \<or> t = t\<^sub>0" by simp
        from i have t': "\<langle> ApplyCommit i\<^sub>0 t' \<rangle>\<leadsto>'" 
          by (metis isMessage'_eq someI_ex t'_def)
        thus "\<langle> ApplyCommit i\<^sub>0 t' \<rangle>\<leadsto> \<or> t' = t\<^sub>0" by simp

        fix t assume le: "t\<^sub>0 \<le> t"
        assume "\<exists>x. \<langle> ApplyRequest i\<^sub>0 t x \<rangle>\<leadsto>"
        then obtain x where "\<langle> ApplyRequest i\<^sub>0 t x \<rangle>\<leadsto>" by blast

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
      by (metis Era.simps(5) Q_def lessI less_eq_Era_def less_le_trans natOfEra.simps(2) not_less reconfig'_eq reconfig_isCommitted v\<^sub>c_eq)
  qed

  show ?thesis
    apply (unfold_locales)
                  apply (fold isMessageFromTo'_def)
                   apply (unfold messages_simps)
                   apply (fold isMessageFrom_def isMessageTo_def)
                   apply (fold isMessageFrom'_def isMessageTo'_def)
                   apply (fold isMessage_def isMessage'_def)
                   apply (fold isCommitted'_def)
                   apply (fold committedTo'_def)
                   apply (fold v_def)
                   apply (fold v\<^sub>c'_def)
                   apply (fold era\<^sub>i'_def)
                   apply (fold reconfig'_def)
                   apply (fold Q'_def)
                   apply (fold promised_def)
                   apply (fold prevAccepted_def)
    using JoinResponse_future JoinResponse_None JoinResponse_Some_lt JoinResponse_Some_ApplyResponse
      JoinResponse_Some_max ApplyRequest_function finite_messages_insert ApplyResponse_ApplyRequest
      JoinResponse_Some_ApplyRequest JoinResponse_unique_destination JoinResponse_not_broadcast
  proof -
    from ApplyRequest_committedTo show "\<And>i t x. \<langle> ApplyRequest i t x \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub><' i" by (simp add: committedTo_eq)

    from JoinResponse_era era\<^sub>i_eq committedTo_eq
    show "\<And>i s t a. s \<midarrow>\<langle> JoinResponse i t a \<rangle>\<leadsto> \<Longrightarrow> \<exists>i'\<le>i. committed\<^sub><' i' \<and> era\<^sub>t t \<le> era\<^sub>i' i'"
      by force

    from era\<^sub>i_eq show "\<And>i t x. \<langle> ApplyRequest i t x \<rangle>\<leadsto> \<Longrightarrow> era\<^sub>i' i = era\<^sub>t t"
      using ApplyCommit_era era committedTo_current isCommitted_committedTo isCommitted_def 
      by (simp add: ApplyRequest_committedTo ApplyRequest_era)

    show "\<And>i s t x. s \<midarrow>\<langle> ApplyRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>Q' (era\<^sub>t t). (\<forall>n\<in>q. promised i n s t) \<and> (prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q)))"
      by (metis ApplyRequest_committedTo ApplyRequest_era ApplyRequest_quorum Q'_eq isMessage_def order_refl)

    show "\<And>i t. \<langle> ApplyCommit i t \<rangle>\<leadsto>' \<Longrightarrow> \<exists>q\<in>Q' (era\<^sub>t t). \<forall>s\<in>q. s \<midarrow>\<langle> ApplyResponse i t \<rangle>\<leadsto>"
      by (metis (mono_tags, hide_lams) ApplyCommit_era ApplyCommit_quorum Message.inject(5) Q'_eq assms(1) assms(2) committedTo_current era isCommitted'_def isCommitted_committedTo isCommitted_eq isMessage'_eq order_refl)
  qed
qed

section \<open>Per-node model\<close>

record NodeData =
  currentNode :: Node (* identity of this node *)
  localCheckpoint :: nat (* all slots strictly below this one are committed *)
  currentEra :: Era (* era of the localCheckpoint slot *)
  currentConfiguration :: Configuration (* configuration of the currentEra *)
  currentClusterState :: ClusterState (* last-committed cluster state *)
  (* acceptor data *)
  lastAccepted :: PreviousApplyResponse (* term and value that were last accepted in this slot, if any *)
  minimumAcceptableTerm :: Term (* greatest term for which a promise was sent *)
  (* election data *)
  electionTerm :: Term (* term of JoinResponses being collected *)
  electionVotes :: "Node set"
  electionWon :: bool
  electionValue :: PreviousApplyResponse
  (* learner data *)
  applyRequestedInCurrentSlot :: bool
  applyTerm :: Term
  applyVotes :: "Node set"

definition applyValue :: "Value \<Rightarrow> NodeData \<Rightarrow> NodeData"
  where
    "applyValue x nd \<equiv> case x of
        NoOp \<Rightarrow> nd
      | Reconfigure Q \<Rightarrow> nd \<lparr> currentEra := nextEra (currentEra nd)
                            , currentConfiguration := Q \<rparr>
      | SetClusterState s \<Rightarrow> nd \<lparr> currentClusterState := s \<rparr>"

definition lastAcceptedGreaterTermThan :: "Term \<Rightarrow> NodeData \<Rightarrow> bool"
  where
    "lastAcceptedGreaterTermThan t nd \<equiv> case lastAccepted nd of
      NoApplyResponseSent \<Rightarrow> False
      | ApplyResponseSent t' _ \<Rightarrow> t' < t"

definition isQuorum :: "NodeData \<Rightarrow> Node set \<Rightarrow> bool"
  where "isQuorum nd q \<equiv> q \<in> Rep_Configuration (currentConfiguration nd)"

fun combineApplyResponses :: "PreviousApplyResponse \<Rightarrow> PreviousApplyResponse \<Rightarrow> PreviousApplyResponse"
  where
    "combineApplyResponses NoApplyResponseSent par = par"
  | "combineApplyResponses par NoApplyResponseSent = par"
  | "combineApplyResponses (ApplyResponseSent t\<^sub>1 x\<^sub>1) (ApplyResponseSent t\<^sub>2 x\<^sub>2)
        = (if t\<^sub>1 < t\<^sub>2 then ApplyResponseSent t\<^sub>2 x\<^sub>2 else ApplyResponseSent t\<^sub>1 x\<^sub>1)"

definition HandleClientRequest :: "NodeData \<Rightarrow> Value \<Rightarrow> (NodeData * RoutedMessage list)"
  where "HandleClientRequest nd x \<equiv>
    if electionWon nd \<and> \<not> applyRequestedInCurrentSlot nd
    then ( nd \<lparr> applyRequestedInCurrentSlot := True \<rparr>
         , [ \<lparr> sender = currentNode nd, destination = Broadcast,
               payload = ApplyRequest (localCheckpoint nd) (electionTerm nd) x \<rparr> ] )
    else (nd, [])"

definition ProcessMessage :: "NodeData \<Rightarrow> RoutedMessage \<Rightarrow> (NodeData * RoutedMessage list)"
  where
    "ProcessMessage nd msg \<equiv>
      let respond   = (\<lambda> m. [\<lparr> sender = currentNode nd, destination = OneNode (sender msg), payload = m \<rparr>]);
          broadcast = (\<lambda> m. [\<lparr> sender = currentNode nd, destination = Broadcast, payload = m \<rparr>])
          
      in if destination msg \<in> { Broadcast, OneNode (currentNode nd) } then case payload msg of

      JoinRequest t \<Rightarrow>
          if minimumAcceptableTerm nd < t
          then ( nd \<lparr> minimumAcceptableTerm := t \<rparr>
               , respond (JoinResponse (localCheckpoint nd)
                                       t
                                       (lastAccepted nd)))
          else (nd, [])

      | JoinResponse i t a \<Rightarrow>
          if localCheckpoint nd < i
             \<or> t < electionTerm nd
             \<or> (t = electionTerm nd \<and> electionWon nd)
          then (nd, [])
          else let newVotes = if electionTerm nd = t
                                then insert (sender msg) (electionVotes nd)
                                else { sender msg };

                   nd1 = nd \<lparr> electionVotes := newVotes
                            , electionValue := combineApplyResponses (electionValue nd) a
                            , electionWon := isQuorum nd newVotes
                            , electionTerm := t
                            , applyRequestedInCurrentSlot := False \<rparr>

                in (case electionValue nd1 of
                      ApplyResponseSent _ x \<Rightarrow> HandleClientRequest nd1 x
                      | _ \<Rightarrow> (nd1, []))

      | ApplyRequest i t x \<Rightarrow>
          if minimumAcceptableTerm nd \<le> t
                \<and> \<not> lastAcceptedGreaterTermThan t nd
                \<and> localCheckpoint nd = i
          then ( nd \<lparr> lastAccepted := ApplyResponseSent t x \<rparr>
               , respond (ApplyResponse i t))
          else (nd, [])

      | ApplyResponse i t \<Rightarrow>
          if localCheckpoint nd = i
          then (nd, [])
          else (nd, [])

      | ApplyCommit i t \<Rightarrow> let
          nd' = if i = localCheckpoint nd
                then case lastAccepted nd of
                    ApplyResponseSent t' x' \<Rightarrow>
                      if t = t'
                      then applyValue x'
                              nd \<lparr> localCheckpoint := i + 1
                                 , lastAccepted := NoApplyResponseSent
                                 , applyRequestedInCurrentSlot := False \<rparr>
                      else nd
                  | NoApplyResponseSent \<Rightarrow> nd
                else nd
          in (nd', [])

      else (nd, [])"

locale zenImpl = zen +
  fixes nodeState :: "Node \<Rightarrow> NodeData"
  assumes nodesIdentified: "\<And>n. currentNode (nodeState n) = n"
  assumes committedToLocalCheckpoint: "\<And>n. committed\<^sub>< (localCheckpoint (nodeState n))"
  assumes eraMatchesLocalCheckpoint: "\<And>n. currentEra (nodeState n) = era\<^sub>i (localCheckpoint (nodeState n))"
  assumes lastAcceptedInEarlierTerm: "\<And>n. case lastAccepted (nodeState n) of
      NoApplyResponseSent \<Rightarrow> True
    | ApplyResponseSent t' _ \<Rightarrow> t' \<le> minimumAcceptableTerm (nodeState n)"

lemma (in zenImpl)
  shows "zenImpl (insert \<lparr> sender = anySender, destination = Broadcast, payload = JoinRequest t \<rparr> messages) nodeState"
  sorry

lemma (in zenImpl)
  fixes n\<^sub>0
  assumes "m \<in> messages"
  defines "nd \<equiv> nodeState n\<^sub>0"
  defines "result \<equiv> ProcessMessage nd m"
  defines "nodeState' \<equiv> \<lambda>n. if n = n\<^sub>0 then (fst result) else nodeState n"
  defines "messages' \<equiv> messages \<union> set (snd result)"
  shows "zenImpl messages' nodeState'"
proof (cases m)
  case (JoinResponse i n t a)
  have [simp]: "result = (nd, [])"
    by (simp add: result_def JoinResponse ProcessMessage_def)
  have [simp]: "nodeState' = nodeState"
    by (auto simp add: nodeState'_def nd_def)
  have [simp]: "messages' = messages"
    by (auto simp add: messages'_def)
  from zenImpl_axioms show ?thesis by simp
next
  case (ApplyRequest i t x)
  then show ?thesis sorry
next
  case (ApplyResponse i n t)
  then show ?thesis sorry
next
  case (ApplyCommit i t)

  have [simp]: "messages' = messages"
    by (simp add: messages'_def result_def ApplyCommit ProcessMessage_def)

  show ?thesis
  proof (cases "i < localCheckpoint nd")
    case True
    have [simp]: "result = (nd, [])"
      by (simp add: True result_def ApplyCommit ProcessMessage_def)
    have [simp]: "nodeState' = nodeState"
      by (auto simp add: nodeState'_def nd_def)
    from zenImpl_axioms show ?thesis by simp
  next
    case False
    from zenImpl.axioms [OF zenImpl_axioms] have "zen messages'" by simp
    then show ?thesis proof (intro zenImpl.intro)
  qed


  then show ?thesis sorry
qed

end
