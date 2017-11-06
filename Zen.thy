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

datatype PreviousPublishResponse
  = NoPublishResponseSent
  | PublishResponseSent Term Value

datatype Message
  = StartJoin Term
  | JoinRequest nat Term PreviousPublishResponse
  | ClientValue Value
  | PublishRequest nat Term Value
  | PublishResponse nat Term
  | ApplyCommit nat Term
  | Reboot

text \<open>Some prose descriptions of these messages follows, in order to give a bit more of an
intuitive understanding of their purposes. A precise description of the conditions under which each
kind of message can be sent is further below.\<close>

text \<open>The message @{term "StartJoin t"} may be sent by any node to attempt to start a master
election in the given term @{term t}.\<close>

text \<open>The message @{term "JoinRequest i t a"} may be sent by a node in response
to a @{term StartJoin} message. It indicates that the sender knows all committed values for slots
strictly below @{term i}, and that the sender will no longer vote (i.e. send an @{term
PublishResponse}) in any term prior to @{term t}. The field @{term a} is either @{term
NoPublishResponseSent} or @{term "PublishResponseSent t' x'"}. In the former case this indicates that
the node has not yet sent any @{term PublishResponse} message in slot @{term i}, and in the latter
case it indicates that the largest term in which it has previously sent an @{term PublishResponse}
message is @{term t'} and the value in the corresponding @{term PublishRequest} was @{term x'}.  All
nodes must avoid sending a @{term JoinRequest} message to two different masters in the same term.
The trigger for sending this message is solely a liveness concern and therefore is out of the scope
of this model.\<close>

text \<open>The message @{term "ClientValue x"} may be sent by any node and indicates an attempt to
reach consensus on the value @{term x}.\<close>

text \<open>The message @{term "PublishRequest i t v"} may be sent by the elected master of term
@{term t} to request the other master-eligible nodes to vote for value @{term v} to be committed in
slot @{term i}.\<close>

text \<open>The message @{term "PublishResponse i t"} may be sent by node in response to
the corresponding @{term PublishRequest} message, indicating that the sender votes for the value
proposed by the master of term @{term t} to be committed in slot @{term i}.\<close>

text \<open>The message @{term "ApplyCommit i t"} indicates that the value proposed by the master of
term @{term t} in slot @{term i} received a quorum of votes and is therefore committed.\<close>

text \<open>The message @{term Reboot} may be sent by any node to represent the restart of a node, which
loses any ephemeral state.\<close>

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
  fixes isMessageFromTo :: "Node \<Rightarrow> Message \<Rightarrow> Destination \<Rightarrow> bool" ("(_) \<midarrow>\<langle> _ \<rangle>\<rightarrow> (_)" [55])
  defines "s \<midarrow>\<langle> m \<rangle>\<rightarrow> d \<equiv> \<lparr> sender = s, destination = d, payload = m \<rparr> \<in> messages"
  fixes isMessageFrom :: "Node \<Rightarrow> Message \<Rightarrow> bool" ("(_) \<midarrow>\<langle> _ \<rangle>\<leadsto>" [55])
  defines "s \<midarrow>\<langle> m \<rangle>\<leadsto> \<equiv> \<exists> d. s \<midarrow>\<langle> m \<rangle>\<rightarrow> d"
  fixes isMessageTo :: "Message \<Rightarrow> Destination \<Rightarrow> bool" ("\<langle> _ \<rangle>\<rightarrow> (_)" [55])
  defines "\<langle> m \<rangle>\<rightarrow> d \<equiv> \<exists> s. s \<midarrow>\<langle> m \<rangle>\<rightarrow> d"
  fixes isMessage :: "Message \<Rightarrow> bool" ("\<langle> _ \<rangle>\<leadsto>" [55])
  defines "\<langle> m \<rangle>\<leadsto> \<equiv> \<exists> s. s \<midarrow>\<langle> m \<rangle>\<leadsto>"
    (* value proposed in a slot & a term *)
  fixes v :: "nat \<Rightarrow> Term \<Rightarrow> Value"
  defines "v i t \<equiv> THE x. \<langle> PublishRequest i t x \<rangle>\<leadsto>"
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
    (* predicate to say whether an applicable JoinRequest has been sent *)
  fixes promised :: "nat \<Rightarrow> Node \<Rightarrow> Node \<Rightarrow> Term \<Rightarrow> bool"
  defines "promised i s dn t \<equiv> \<exists> i' \<le> i. \<exists> a. s \<midarrow>\<langle> JoinRequest i' t a \<rangle>\<rightarrow> (OneNode dn)"
    (* set of previously-accepted terms *)
  fixes prevAccepted :: "nat \<Rightarrow> Term \<Rightarrow> Node set \<Rightarrow> Term set"
  defines "prevAccepted i t senders
      \<equiv> {t'. \<exists> s \<in> senders. \<exists> x'. s \<midarrow>\<langle> JoinRequest i t (PublishResponseSent t' x') \<rangle>\<leadsto> }"
    (* ASSUMPTIONS *)
  assumes JoinRequest_future:
    "\<And>i i' s t t' a.
        \<lbrakk> s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>; i < i'; t' < t \<rbrakk>
            \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i' t' \<rangle>\<leadsto>"
  assumes JoinRequest_None:
    "\<And>i s t t'.
        \<lbrakk> s \<midarrow>\<langle> JoinRequest i t NoPublishResponseSent \<rangle>\<leadsto>; t' < t \<rbrakk>
            \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>"
  assumes JoinRequest_Some_lt:
    "\<And>i s t t' x'. s \<midarrow>\<langle> JoinRequest i t (PublishResponseSent t' x') \<rangle>\<leadsto>
      \<Longrightarrow> t' < t"
  assumes JoinRequest_Some_PublishResponse:
    "\<And>i s t t' x'. s \<midarrow>\<langle> JoinRequest i t (PublishResponseSent t' x') \<rangle>\<leadsto>
      \<Longrightarrow> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>"
  assumes JoinRequest_Some_PublishRequest:
    "\<And>i s t t' x'. s \<midarrow>\<langle> JoinRequest i t (PublishResponseSent t' x') \<rangle>\<leadsto>
      \<Longrightarrow> \<langle> PublishRequest i t' x' \<rangle>\<leadsto>"
  assumes JoinRequest_Some_max:
    "\<And>i s t t' t'' x'. \<lbrakk> s \<midarrow>\<langle> JoinRequest i t (PublishResponseSent t' x') \<rangle>\<leadsto>; t' < t''; t'' < t \<rbrakk>
      \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t'' \<rangle>\<leadsto>"
  assumes JoinRequest_era:
    "\<And>i s t a. s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>
      \<Longrightarrow> \<exists> i' \<le> i. committedTo i' \<and> era\<^sub>t t \<le> era\<^sub>i i'"
  assumes JoinRequest_not_broadcast:
    "\<And>i t a d. \<langle> JoinRequest i t a \<rangle>\<rightarrow> d \<Longrightarrow> d \<noteq> Broadcast"
  assumes JoinRequest_unique_destination:
    "\<And>i s t a a' d d'. \<lbrakk> s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<rightarrow> d; s \<midarrow>\<langle> JoinRequest i' t a' \<rangle>\<rightarrow> d' \<rbrakk>
      \<Longrightarrow> d = d'"
  assumes PublishRequest_era:
    "\<And>i t x. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> era\<^sub>i i = era\<^sub>t t"
  assumes PublishRequest_committedTo:
    "\<And>i t x. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> committedTo i"
  assumes PublishRequest_quorum:
    "\<And>i s t x. s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>
      \<Longrightarrow> \<exists> q \<in> Q (era\<^sub>t t). (\<forall> n \<in> q. promised i n s t) \<and>
            (prevAccepted i t q = {}
                \<or> v i t = v i (maxTerm (prevAccepted i t q)))"
  assumes PublishRequest_function:
    "\<And>i t x x'. \<lbrakk> \<langle> PublishRequest i t x \<rangle>\<leadsto>; \<langle> PublishRequest i t x' \<rangle>\<leadsto> \<rbrakk>
       \<Longrightarrow> x = x'"
  assumes finite_messages:
    "finite messages"
  assumes PublishResponse_PublishRequest:
    "\<And>i s t. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto> \<Longrightarrow> \<exists> x. \<langle> PublishRequest i t x \<rangle>\<leadsto>"
  assumes ApplyCommit_quorum:
    "\<And>i t. \<langle> ApplyCommit i t \<rangle>\<leadsto>
                        \<Longrightarrow> \<exists> q \<in> Q (era\<^sub>t t). \<forall> s \<in> q. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>"

declare [[goals_limit = 30]]

subsection \<open>Utility lemmas\<close>

text \<open>Some results that are useful later:\<close>

lemma (in zen) Q_intersects: "Q e \<frown> Q e"
  by (cases e, simp_all add: Q_def Q\<^sub>0_intersects getConf_intersects)

lemma (in zen) Q_members_nonempty: assumes "q \<in> Q e" shows "q \<noteq> {}"
  using assms Q_intersects 
  by (auto simp add: intersects_def)

lemma (in zen) Q_member_member: assumes "q \<in> Q e" obtains n where "n \<in> q"
  using Q_members_nonempty assms by fastforce

lemma (in zen) ApplyCommit_PublishResponse:
  assumes "\<langle> ApplyCommit i t \<rangle>\<leadsto>"
  obtains s where "s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>"
  by (meson ApplyCommit_quorum Q_member_member assms)

lemma (in zen) ApplyCommit_PublishRequest:
  assumes "\<langle> ApplyCommit i t \<rangle>\<leadsto>"
  shows "\<langle> PublishRequest i t (v i t) \<rangle>\<leadsto>"
  by (metis ApplyCommit_PublishResponse PublishResponse_PublishRequest assms the_equality v_def PublishRequest_function)

lemma (in zen) PublishRequest_JoinRequest:
  assumes "s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>"
  obtains i' n a where "i' \<le> i" "n \<midarrow>\<langle> JoinRequest i' t a \<rangle>\<rightarrow> (OneNode s)"
  by (meson PublishRequest_quorum Q_member_member assms isMessage_def promised_def)

lemma (in zen) finite_prevAccepted: "finite (prevAccepted i t ns)"
proof -
  fix t\<^sub>0
  define f :: "RoutedMessage \<Rightarrow> Term" where "f \<equiv> \<lambda> m. case payload m of JoinRequest _ _ (PublishResponseSent t' _) \<Rightarrow> t' | _ \<Rightarrow> t\<^sub>0"
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

lemma (in zen) PublishResponse_era:
  assumes "s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>"
  shows "era\<^sub>t t = era\<^sub>i i"
  using assms PublishRequest_era PublishResponse_PublishRequest by metis

lemma (in zen) ApplyCommit_era:
  assumes "\<langle> ApplyCommit i t \<rangle>\<leadsto>"
  shows "era\<^sub>t t = era\<^sub>i i"
  by (meson PublishResponse_era assms ApplyCommit_PublishResponse)

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
     \<equiv> (s \<midarrow>\<langle> JoinRequest i t NoPublishResponseSent \<rangle>\<leadsto>
           \<or> (\<exists>i'<i. \<exists>a. s \<midarrow>\<langle> JoinRequest i' t a \<rangle>\<leadsto>))
           \<or> (\<exists>t'. \<exists> x'. s \<midarrow>\<langle> JoinRequest i t (PublishResponseSent t' x') \<rangle>\<leadsto>)"
 (is "?LHS == ?RHS")
proof -
  have "?LHS = ?RHS"
    apply (intro iffI)
     apply (metis PreviousPublishResponse.exhaust isMessageFrom_def leI le_antisym promised_def)
    by (metis Destination.exhaust JoinRequest_not_broadcast isMessageFrom_def isMessageTo_def nat_less_le not_le promised_def)
  thus "?LHS == ?RHS" by simp
qed

lemma (in zen) JoinRequest_value_function:
  assumes "s \<midarrow>\<langle> JoinRequest i t a\<^sub>1 \<rangle>\<leadsto>" and "s \<midarrow>\<langle> JoinRequest i t a\<^sub>2 \<rangle>\<leadsto>"
  shows "a\<^sub>1 = a\<^sub>2"
proof (cases a\<^sub>1)
  case NoPublishResponseSent
  with assms show ?thesis
    by (metis JoinRequest_None JoinRequest_Some_PublishResponse JoinRequest_Some_lt PreviousPublishResponse.exhaust)
next
  case (PublishResponseSent t\<^sub>1 x\<^sub>1)
  with assms have "a\<^sub>2 \<noteq> NoPublishResponseSent"
    using JoinRequest_None JoinRequest_Some_PublishResponse JoinRequest_Some_lt by blast
  then obtain t\<^sub>2 x\<^sub>2 where a\<^sub>2: "a\<^sub>2 = PublishResponseSent t\<^sub>2 x\<^sub>2"
    using PreviousPublishResponse.exhaust by blast

  from PublishResponseSent a\<^sub>2 assms
  have t: "t\<^sub>1 = t\<^sub>2"
    by (meson JoinRequest_Some_PublishResponse JoinRequest_Some_lt less_linear JoinRequest_Some_max)

  from assms
  have x: "x\<^sub>1 = x\<^sub>2" 
    apply (intro PublishRequest_function JoinRequest_Some_PublishRequest)
    by (unfold PublishResponseSent a\<^sub>2 t)

  show ?thesis
    by (simp add: PublishResponseSent a\<^sub>2 t x)
qed

lemma (in zen) shows finite_messages_insert: "finite (insert m messages)"
  using finite_messages by auto

lemma (in zen) isCommitted_committedTo:
  assumes "isCommitted i"
  shows "committed\<^sub>< i"
  using ApplyCommit_PublishRequest PublishRequest_committedTo assms isCommitted_def by blast

lemma (in zen) promised_unique:
  assumes "promised i s d t" and "promised i' s d' t"
  shows "d = d'"
  by (meson Destination.inject JoinRequest_unique_destination assms promised_def)

subsection \<open>Relationship to @{term oneSlot}\<close>

text \<open>This shows that each slot @{term i} in Zen satisfies the assumptions of the @{term
oneSlot} model above.\<close>

lemma (in zen) zen_is_oneSlot:
  fixes i
  shows "oneSlot (Q \<circ> era\<^sub>t) (v i)
    (\<lambda> s t. s \<midarrow>\<langle> JoinRequest i t NoPublishResponseSent \<rangle>\<leadsto>
        \<or> (\<exists> i' < i. \<exists> a. s \<midarrow>\<langle> JoinRequest i' t a \<rangle>\<leadsto>))
    (\<lambda> s t t'. \<exists> x'. s \<midarrow>\<langle> JoinRequest i t (PublishResponseSent t' x') \<rangle>\<leadsto>)
    (\<lambda> t. \<exists> x. \<langle> PublishRequest i t x \<rangle>\<leadsto>)
    (\<lambda> s t. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>)
    (\<lambda> t. \<langle> ApplyCommit i t \<rangle>\<leadsto>)"
proof (unfold_locales, fold prevAccepted_def promised_long_def)
  fix t\<^sub>1 t\<^sub>2
  assume "\<exists>x. \<langle> PublishRequest i t\<^sub>1 x \<rangle>\<leadsto>"
  then obtain x where t\<^sub>1: "\<langle> PublishRequest i t\<^sub>1 x \<rangle>\<leadsto>" ..
  assume t\<^sub>2: "\<langle> ApplyCommit i t\<^sub>2 \<rangle>\<leadsto>"
  assume t\<^sub>2\<^sub>1: "t\<^sub>2 \<le> t\<^sub>1" hence "era\<^sub>t t\<^sub>2 \<le> era\<^sub>t t\<^sub>1"
    by (simp add: era\<^sub>t_mono)

  from t\<^sub>1 PublishRequest_era have "era\<^sub>t t\<^sub>1 = era\<^sub>i i" by simp
  also from t\<^sub>2 have "... = era\<^sub>t t\<^sub>2" using ApplyCommit_era by auto
  finally show "(Q \<circ> era\<^sub>t) t\<^sub>1 \<frown> (Q \<circ> era\<^sub>t) t\<^sub>2" by (simp add: Q_intersects)
next
  fix q t assume "q \<in> (Q \<circ> era\<^sub>t) t" thus "q \<noteq> {}" by (simp add: Q_members_nonempty)
next
  fix s t t'
  assume "t' < t" "s \<midarrow>\<langle> JoinRequest i t NoPublishResponseSent \<rangle>\<leadsto> \<or> (\<exists>i'<i. \<exists>a. s \<midarrow>\<langle> JoinRequest i' t a \<rangle>\<leadsto>)"
  thus "\<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>"
    using JoinRequest_None JoinRequest_future by auto
next
  fix s t t'
  assume j: "\<exists> x'. s \<midarrow>\<langle> JoinRequest i t (PublishResponseSent t' x') \<rangle>\<leadsto>"
  from j show "t' < t" using JoinRequest_Some_lt by blast
  from j show "s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>" using JoinRequest_Some_PublishResponse by blast

  fix t'' assume "t' < t''" "t'' < t"
  with j show "\<not> s \<midarrow>\<langle> PublishResponse i t'' \<rangle>\<leadsto>" using JoinRequest_Some_max by blast
next
  fix t
  assume "\<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>"
  then obtain x s where "s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>" by (auto simp add: isMessage_def)
  from PublishRequest_quorum [OF this]
  show "\<exists>q\<in>(Q \<circ> era\<^sub>t) t. (\<forall>n\<in>q. \<exists> d. promised i n d t) \<and> (prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q)))"
    by auto
next
  fix s t assume "s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>"
  thus "\<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>"
    by (simp add: PublishResponse_PublishRequest)
next
  fix t assume "\<langle> ApplyCommit i t \<rangle>\<leadsto>"
  thus "\<exists>q\<in>(Q \<circ> era\<^sub>t) t. \<forall>s\<in>q. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>"
    by (simp add: ApplyCommit_quorum)
next
  fix t\<^sub>0
  define f :: "RoutedMessage \<Rightarrow> Term"
    where "f \<equiv> \<lambda> m. case payload m of PublishRequest i t x \<Rightarrow> t | _ \<Rightarrow> t\<^sub>0"

  have "{t. \<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>} \<subseteq> f ` messages"
    apply (unfold isMessage_def isMessageFrom_def isMessageFromTo_def)
    using f_def image_iff by fastforce

  moreover have "finite (f ` messages)"
    by (simp add: finite_messages)

  ultimately show "finite {t. \<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>}"
    using finite_subset by blast
qed

text \<open>From this it follows that all committed values are equal.\<close>

lemma (in zen) consistent:
  assumes "\<langle> ApplyCommit  i t\<^sub>1 \<rangle>\<leadsto>"
  assumes "\<langle> ApplyCommit  i t\<^sub>2 \<rangle>\<leadsto>"
  assumes "\<langle> PublishRequest i t\<^sub>1 v\<^sub>1 \<rangle>\<leadsto>"
  assumes "\<langle> PublishRequest i t\<^sub>2 v\<^sub>2 \<rangle>\<leadsto>"
  shows "v\<^sub>1 = v\<^sub>2"
proof -
  from oneSlot.consistent [OF zen_is_oneSlot] assms
  have "v i t\<^sub>1 = v i t\<^sub>2" by blast
  moreover have "v\<^sub>1 = v i t\<^sub>1" using ApplyCommit_PublishRequest assms PublishRequest_function by blast
  moreover have "v\<^sub>2 = v i t\<^sub>2" using ApplyCommit_PublishRequest assms PublishRequest_function by blast
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

subsubsection \<open>Sending @{term StartJoin} messages\<close>

text \<open>Any node may send a @{term StartJoin} message for any term at any time.\<close>

lemma (in zen) send_StartJoin:
  shows "zen (insert \<lparr> sender = s\<^sub>0, destination = d\<^sub>0, payload = StartJoin t\<^sub>0 \<rparr> messages)" (is "zen ?messages'")
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
    "\<And>i s d t a. (s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<rightarrow> d)"
    "\<And>i s d t x. (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>i s d t. (s \<midarrow>\<langle> PublishResponse i t\<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<rightarrow> d)"
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
    using PublishResponse_PublishRequest PublishRequest_era PublishRequest_quorum PublishRequest_function
      PublishRequest_committedTo JoinRequest_Some_lt JoinRequest_Some_PublishResponse
      JoinRequest_Some_max finite_messages_insert JoinRequest_None JoinRequest_era
      JoinRequest_future ApplyCommit_quorum JoinRequest_Some_PublishRequest
      JoinRequest_not_broadcast JoinRequest_unique_destination
    by (simp_all)
qed

subsubsection \<open>Sending @{term JoinRequest} messages\<close>

text \<open>A node @{term n\<^sub>0} can send a @{term JoinRequest} message for slot @{term
i\<^sub>0} only if \begin{itemize} \item all previous slots are committed, \item the eras of the
term and the slot are equal, and \item it has sent no @{term PublishResponse} message for any later
slot. \end{itemize}.\<close>

text \<open>@{term "JoinRequest i\<^sub>0 t\<^sub>0 NoPublishResponseSent"} can be sent by node @{term n\<^sub>0} if,
additionally, no @{term PublishResponse} message has been sent for slot @{term i\<^sub>0}:\<close>

lemma (in zen) send_JoinRequest_None:
  assumes "\<forall> i \<ge> i\<^sub>0. \<forall> t. \<not> s\<^sub>0 \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>"
    (* first-uncommitted slot, the era is ok, and not already sent*)
  assumes "\<forall> i < i\<^sub>0. \<exists> t. \<langle> ApplyCommit i t \<rangle>\<leadsto>"
  assumes "era\<^sub>t t\<^sub>0 = era\<^sub>i i\<^sub>0"
  assumes "\<forall> i a. \<not> s\<^sub>0 \<midarrow>\<langle> JoinRequest i t\<^sub>0 a \<rangle>\<leadsto>"
    (* *)
  shows   "zen (insert \<lparr> sender = s\<^sub>0, destination = OneNode d\<^sub>0,
                         payload = JoinRequest i\<^sub>0 t\<^sub>0 NoPublishResponseSent \<rparr> messages)"
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
    "\<And>s m d. (s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d) = ((s \<midarrow>\<langle> m \<rangle>\<rightarrow> d) \<or> (s, m, d) = (s\<^sub>0, JoinRequest i\<^sub>0 t\<^sub>0 NoPublishResponseSent, OneNode d\<^sub>0))"
    by (auto simp add: isMessageFromTo'_def isMessageFromTo_def)

  have isMessageFrom'_eq [simp]:
    "\<And>s m. (s \<midarrow>\<langle> m \<rangle>\<leadsto>') = ((s \<midarrow>\<langle> m \<rangle>\<leadsto>) \<or> (s, m) = (s\<^sub>0, JoinRequest i\<^sub>0 t\<^sub>0 NoPublishResponseSent))"
    by (auto simp add: isMessageFrom'_def isMessageFrom_def)

  have isMessageTo'_eq [simp]:
    "\<And>m d. (\<langle> m \<rangle>\<rightarrow>' d) = ((\<langle> m \<rangle>\<rightarrow> d) \<or> (m, d) = (JoinRequest i\<^sub>0 t\<^sub>0 NoPublishResponseSent, OneNode d\<^sub>0))"
    by (auto simp add: isMessageTo'_def isMessageTo_def)

  have isMessage'_eq [simp]:
    "\<And>m. (\<langle> m \<rangle>\<leadsto>') = ((\<langle> m \<rangle>\<leadsto>) \<or> m = JoinRequest i\<^sub>0 t\<^sub>0 NoPublishResponseSent)"
    by (auto simp add: isMessage'_def isMessage_def)

  have messages_simps:
    "\<And>i s d t t' x'. (s \<midarrow>\<langle> JoinRequest i t (PublishResponseSent t' x') \<rangle>\<rightarrow>' d)
        = (s \<midarrow>\<langle> JoinRequest i t (PublishResponseSent t' x') \<rangle>\<rightarrow> d)"
    "\<And>i s d t x. (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>i s d t x. (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>i s d t. (s \<midarrow>\<langle> PublishResponse i t\<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<rightarrow> d)"
    "\<And>i s d t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)"
    by auto

  define promised' where "\<And>i s d t. promised' i s d t \<equiv> \<exists>i'\<le>i. \<exists>a. s \<midarrow>\<langle> JoinRequest i' t a \<rangle>\<rightarrow>' (OneNode d)"
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
    using PublishResponse_PublishRequest PublishRequest_era ApplyCommit_quorum PublishRequest_function
      PublishRequest_committedTo JoinRequest_Some_lt JoinRequest_Some_PublishResponse
      JoinRequest_Some_max finite_messages_insert JoinRequest_Some_PublishRequest
  proof -
    show "\<And>i i' s t t' a. s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>' \<Longrightarrow> i < i' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i' t' \<rangle>\<leadsto>"
      using JoinRequest_future assms by auto
    show "\<And>i s t t'. s \<midarrow>\<langle> JoinRequest i t NoPublishResponseSent \<rangle>\<leadsto>' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>"
      using JoinRequest_None assms by auto
    show "\<And>i t a d. \<langle> JoinRequest i t a \<rangle>\<rightarrow>' d \<Longrightarrow> d \<noteq> Broadcast"
      using JoinRequest_not_broadcast by auto
    show "\<And>i' i s t a a' d d'. s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<rightarrow>' d \<Longrightarrow> s \<midarrow>\<langle> JoinRequest i' t a' \<rangle>\<rightarrow>' d' \<Longrightarrow> d = d'"
      using JoinRequest_unique_destination assms isMessageFrom_def by auto
    show "\<And>i s t a. s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>' \<Longrightarrow> \<exists>i'\<le>i. committed\<^sub>< i' \<and> era\<^sub>t t \<le> era\<^sub>i i'"
      using JoinRequest_era assms committedTo_def isCommitted_def by auto
    show "\<And>i s t x. s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>Q (era\<^sub>t t). (\<forall>n\<in>q. promised' i n s t) \<and> (prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q)))"
      by (meson PublishRequest_quorum promised'I)
  qed
qed

text \<open>In contrast, @{term "JoinRequest i\<^sub>0 t\<^sub>0 (PublishRequestSent t\<^sub>0'
x\<^sub>0')"} can be sent if an @{term PublishResponse} message has been sent for slot @{term
i\<^sub>0}, in which case @{term t\<^sub>0'} must be the greatest term of any such message
previously sent by node @{term n\<^sub>0} and @{term x\<^sub>0'} is the corresponding
value.}:\<close>

lemma (in zen) send_JoinRequest_Some:
  assumes "\<forall> i > i\<^sub>0. \<forall> t. \<not> s\<^sub>0 \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>"
  assumes "s\<^sub>0 \<midarrow>\<langle> PublishResponse i\<^sub>0 t\<^sub>0' \<rangle>\<leadsto>"
  assumes "\<langle> PublishRequest i\<^sub>0 t\<^sub>0' x\<^sub>0' \<rangle>\<leadsto>"
  assumes "t\<^sub>0' < t\<^sub>0"
  assumes "\<forall> t'. s\<^sub>0 \<midarrow>\<langle> PublishResponse i\<^sub>0 t' \<rangle>\<leadsto> \<longrightarrow> t' \<le> t\<^sub>0'"
    (* first-uncommitted slot, the era is ok, and not already sent*)
  assumes "\<forall> i < i\<^sub>0. \<exists> t. \<langle> ApplyCommit i t \<rangle>\<leadsto>"
  assumes "era\<^sub>t t\<^sub>0 = era\<^sub>i i\<^sub>0"
  assumes "\<forall> i a. \<not> s\<^sub>0 \<midarrow>\<langle> JoinRequest i t\<^sub>0 a \<rangle>\<leadsto>"
    (* *)
  shows   "zen (insert \<lparr> sender = s\<^sub>0, destination = OneNode d\<^sub>0,
                         payload = JoinRequest i\<^sub>0 t\<^sub>0 (PublishResponseSent t\<^sub>0' x\<^sub>0') \<rparr> messages)" (is "zen ?messages'")
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
    "\<And>s m d. (s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d) = ((s \<midarrow>\<langle> m \<rangle>\<rightarrow> d) \<or> (s, m, d) = (s\<^sub>0, JoinRequest i\<^sub>0 t\<^sub>0 (PublishResponseSent t\<^sub>0' x\<^sub>0'), OneNode d\<^sub>0))"
    by (auto simp add: isMessageFromTo'_def isMessageFromTo_def)

  have isMessageFrom'_eq [simp]:
    "\<And>s m. (s \<midarrow>\<langle> m \<rangle>\<leadsto>') = ((s \<midarrow>\<langle> m \<rangle>\<leadsto>) \<or> (s, m) = (s\<^sub>0, JoinRequest i\<^sub>0 t\<^sub>0 (PublishResponseSent t\<^sub>0' x\<^sub>0')))"
    by (auto simp add: isMessageFrom'_def isMessageFrom_def)

  have isMessageTo'_eq [simp]:
    "\<And>m d. (\<langle> m \<rangle>\<rightarrow>' d) = ((\<langle> m \<rangle>\<rightarrow> d) \<or> (m, d) = (JoinRequest i\<^sub>0 t\<^sub>0 (PublishResponseSent t\<^sub>0' x\<^sub>0'), OneNode d\<^sub>0))"
    by (auto simp add: isMessageTo'_def isMessageTo_def)

  have isMessage'_eq [simp]:
    "\<And>m. (\<langle> m \<rangle>\<leadsto>') = ((\<langle> m \<rangle>\<leadsto>) \<or> m = JoinRequest i\<^sub>0 t\<^sub>0 (PublishResponseSent t\<^sub>0' x\<^sub>0'))"
    by (auto simp add: isMessage'_def isMessage_def)

  have messages_simps:
    "\<And>i s d t. (s \<midarrow>\<langle> JoinRequest i t NoPublishResponseSent \<rangle>\<rightarrow>' d)
        = (s \<midarrow>\<langle> JoinRequest i t NoPublishResponseSent \<rangle>\<rightarrow> d)"
    "\<And>i s d t x. (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>i s d t. (s \<midarrow>\<langle> PublishResponse i t\<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<rightarrow> d)"
    "\<And>i s d t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)"
    by auto

  define promised' where "\<And>i s d t. promised' i s d t \<equiv> \<exists>i'\<le>i. \<exists>a. s \<midarrow>\<langle> JoinRequest i' t a \<rangle>\<rightarrow>' (OneNode d)"
  have promised'I: "\<And>i s d t. promised i s d t \<Longrightarrow> promised' i s d t" 
    by (auto simp add: promised'_def promised_def)

  define prevAccepted' where "\<And>i t senders. prevAccepted' i t senders
      \<equiv> {t'. \<exists>s\<in>senders. \<exists>x'. s \<midarrow>\<langle> JoinRequest i t (PublishResponseSent t' x') \<rangle>\<leadsto>'}"

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
   using JoinRequest_None PublishRequest_committedTo PublishRequest_function finite_messages_insert
      PublishResponse_PublishRequest PublishRequest_era  ApplyCommit_quorum
  proof -

    from assms JoinRequest_future
    show "\<And>i i' s t t' a. s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>'
      \<Longrightarrow> i < i' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i' t' \<rangle>\<leadsto>" by auto

    from assms JoinRequest_era
    show "\<And>i s t a. s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>' \<Longrightarrow> \<exists>i'\<le>i. committed\<^sub>< i' \<and> era\<^sub>t t \<le> era\<^sub>i i'"
      by (auto simp add: committedTo_def isCommitted_def)

    from assms JoinRequest_Some_lt
    show "\<And>i s t t' x'. s \<midarrow>\<langle> JoinRequest i t (PublishResponseSent t' x') \<rangle>\<leadsto>' \<Longrightarrow> t' < t" by auto

    from assms JoinRequest_Some_PublishResponse
    show "\<And>i s t t' x'. s \<midarrow>\<langle> JoinRequest i t (PublishResponseSent t' x') \<rangle>\<leadsto>' \<Longrightarrow> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>" by auto

    from assms JoinRequest_Some_PublishRequest
    show "\<And>i s t t' x'. s \<midarrow>\<langle> JoinRequest i t (PublishResponseSent t' x') \<rangle>\<leadsto>' \<Longrightarrow> \<langle> PublishRequest i t' x' \<rangle>\<leadsto>" by auto

    from assms JoinRequest_Some_max
    show "\<And>i s t t' t'' x'. s \<midarrow>\<langle> JoinRequest i t (PublishResponseSent t' x') \<rangle>\<leadsto>' \<Longrightarrow> t' < t'' \<Longrightarrow> t'' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t'' \<rangle>\<leadsto>"
      by auto

    show "\<And>i t a d. \<langle> JoinRequest i t a \<rangle>\<rightarrow>' d \<Longrightarrow> d \<noteq> Broadcast"
      using JoinRequest_not_broadcast isMessageTo'_eq by blast
    show "\<And>i' i s t a a' d d'. s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<rightarrow>' d \<Longrightarrow> s \<midarrow>\<langle> JoinRequest i' t a' \<rangle>\<rightarrow>' d' \<Longrightarrow> d = d'"
      using JoinRequest_unique_destination assms isMessageFrom_def by auto
  next
    fix i s t x assume "s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>"
    from PublishRequest_quorum [OF this]
    obtain q
      where q: "q\<in>Q (era\<^sub>t t)" "\<forall>n\<in>q. promised i n s t"
        "prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q))" by blast

    have "prevAccepted i t q \<subseteq> prevAccepted' i t q"
      by (auto simp add: prevAccepted'_def prevAccepted_def)

    moreover have "prevAccepted' i t q \<subseteq> prevAccepted i t q"
    proof
      fix t' assume "t' \<in> prevAccepted' i t q"
      then obtain s' x' where s': "s' \<in> q" "s' \<midarrow>\<langle> JoinRequest i t (PublishResponseSent t' x') \<rangle>\<leadsto>'" 
        by (unfold prevAccepted'_def, blast)
      from s' have "s' \<midarrow>\<langle> JoinRequest i t (PublishResponseSent t' x') \<rangle>\<leadsto> \<or> (s', i, t, t', x') = (s\<^sub>0, i\<^sub>0, t\<^sub>0, t\<^sub>0', x\<^sub>0')"
        by simp
      with assms q s' have "s' \<midarrow>\<langle> JoinRequest i t (PublishResponseSent t' x') \<rangle>\<leadsto>"
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

subsubsection \<open>Sending @{term ClientValue} messages\<close>

text \<open>Any node may send a @{term ClientValue} message for any value at any time.\<close>

lemma (in zen) send_ClientValue:
  shows "zen (insert \<lparr> sender = s\<^sub>0, destination = d\<^sub>0, payload = ClientValue x\<^sub>0 \<rparr> messages)" (is "zen ?messages'")
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
    "\<And>i s d t a. (s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<rightarrow> d)"
    "\<And>i s d t x. (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>i s d t. (s \<midarrow>\<langle> PublishResponse i t\<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<rightarrow> d)"
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
    using PublishResponse_PublishRequest PublishRequest_era PublishRequest_quorum PublishRequest_function
      PublishRequest_committedTo JoinRequest_Some_lt JoinRequest_Some_PublishResponse
      JoinRequest_Some_max finite_messages_insert JoinRequest_None JoinRequest_era
      JoinRequest_future ApplyCommit_quorum JoinRequest_Some_PublishRequest
      JoinRequest_not_broadcast JoinRequest_unique_destination
    by (simp_all)
qed

subsubsection \<open>Sending @{term PublishRequest} messages\<close>

text \<open>@{term "PublishRequest i\<^sub>0 t\<^sub>0 x\<^sub>0"} can be sent if \begin{itemize}
\item no other value has previously been sent for this $\langle \mathrm{slot}, \mathrm{term}
\rangle$ pair, \item all slots below @{term i\<^sub>0} are committed, \item a quorum of nodes have
sent @{term JoinRequest} messages for term @{term t\<^sub>0}, and \item the value proposed is the
value accepted in the greatest term amongst all @{term JoinRequest} messages, if any.
\end{itemize} \<close>

lemma (in zen) send_PublishRequest:
  assumes "\<forall> x. \<not> s\<^sub>0 \<midarrow>\<langle> PublishRequest i\<^sub>0 t\<^sub>0 x \<rangle>\<leadsto>"
  assumes "\<forall> i < i\<^sub>0. \<exists> t. \<langle> ApplyCommit i t \<rangle>\<leadsto>"
  assumes "era\<^sub>t t\<^sub>0 = era\<^sub>i i\<^sub>0"
  assumes "q \<in> Q (era\<^sub>t t\<^sub>0)"
  assumes "\<forall> s \<in> q. \<exists> i \<le> i\<^sub>0. \<exists> a. s \<midarrow>\<langle> JoinRequest i t\<^sub>0 a \<rangle>\<rightarrow> (OneNode s\<^sub>0)"
  assumes "prevAccepted i\<^sub>0 t\<^sub>0 q \<noteq> {}
    \<longrightarrow> x\<^sub>0 = v i\<^sub>0 (maxTerm (prevAccepted i\<^sub>0 t\<^sub>0 q))"
  shows "zen (insert \<lparr> sender = s\<^sub>0, destination = d\<^sub>0,
                       payload = PublishRequest i\<^sub>0 t\<^sub>0 x\<^sub>0 \<rparr> messages)" (is "zen ?messages'")
proof -
  have quorum_promised: "\<forall>n\<in>q. promised i\<^sub>0 n s\<^sub>0 t\<^sub>0"
    by (simp add: assms promised_def)

  have nobody_proposed: "\<forall> x. \<not> \<langle> PublishRequest i\<^sub>0 t\<^sub>0 x \<rangle>\<leadsto>"
  proof (intro allI notI)
    fix x assume "\<langle> PublishRequest i\<^sub>0 t\<^sub>0 x \<rangle>\<leadsto>"
    then obtain s where s: "s \<midarrow>\<langle> PublishRequest i\<^sub>0 t\<^sub>0 x \<rangle>\<leadsto>" by (unfold isMessage_def, blast)
    from PublishRequest_quorum [OF this]
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
    "\<And>s m d. (s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d) = ((s \<midarrow>\<langle> m \<rangle>\<rightarrow> d) \<or> (s, m, d) = (s\<^sub>0, PublishRequest i\<^sub>0 t\<^sub>0 x\<^sub>0, d\<^sub>0))"
    by (auto simp add: isMessageFromTo'_def isMessageFromTo_def)

  have isMessageFrom'_eq [simp]:
    "\<And>s m. (s \<midarrow>\<langle> m \<rangle>\<leadsto>') = ((s \<midarrow>\<langle> m \<rangle>\<leadsto>) \<or> (s, m) = (s\<^sub>0, PublishRequest i\<^sub>0 t\<^sub>0 x\<^sub>0))"
    by (auto simp add: isMessageFrom'_def isMessageFrom_def)

  have isMessageTo'_eq [simp]:
    "\<And>m d. (\<langle> m \<rangle>\<rightarrow>' d) = ((\<langle> m \<rangle>\<rightarrow> d) \<or> (m, d) = (PublishRequest i\<^sub>0 t\<^sub>0 x\<^sub>0, d\<^sub>0))"
    by (auto simp add: isMessageTo'_def isMessageTo_def)

  have isMessage'_eq [simp]:
    "\<And>m. (\<langle> m \<rangle>\<leadsto>') = ((\<langle> m \<rangle>\<leadsto>) \<or> m = PublishRequest i\<^sub>0 t\<^sub>0 x\<^sub>0)"
    by (auto simp add: isMessage'_def isMessage_def)

  have messages_simps:
    "\<And>i s d t a. (s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<rightarrow> d)"
    "\<And>i s d t. (s \<midarrow>\<langle> PublishResponse i t\<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<rightarrow> d)"
    "\<And>i s d t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)"
    by auto

  define v' where "\<And>i t. v' i t \<equiv> THE x. \<langle> PublishRequest i t x \<rangle>\<leadsto>'"
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
      hence eq: "\<And>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>' = \<langle> PublishRequest i t x \<rangle>\<leadsto>" by auto
      from False show ?thesis by (unfold v'_def eq, auto simp add: v_def)
    next
      case True with nobody_proposed have eq: "\<And>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>' = (x = x\<^sub>0)" by auto
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
        by (metis ApplyCommit_PublishRequest i isCommitted_def someI_ex)
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
    using  JoinRequest_future JoinRequest_None  JoinRequest_Some_lt JoinRequest_Some_PublishResponse
            JoinRequest_Some_max  finite_messages_insert JoinRequest_not_broadcast
            JoinRequest_unique_destination
  proof -
    from assms PublishRequest_committedTo show committedTo: "\<And>i t x. \<langle> PublishRequest i t x \<rangle>\<leadsto>' \<Longrightarrow> committed\<^sub>< i" 
      by (auto simp add: committedTo_def isCommitted_def)

    from nobody_proposed PublishRequest_function show "\<And>i t x x'. \<langle> PublishRequest i t x \<rangle>\<leadsto>' \<Longrightarrow> \<langle> PublishRequest i t x' \<rangle>\<leadsto>' \<Longrightarrow> x = x'"
      by auto

    from PublishResponse_PublishRequest show "\<And>i s t. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>'"
      using isMessage'_eq by blast

    from PublishRequest_era era\<^sub>i_eq have "\<And>i t x. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> era\<^sub>i' i = era\<^sub>t t"
      by (simp add: PublishRequest_committedTo)

    with assms committedTo show "\<And>i t x. \<langle> PublishRequest i t x \<rangle>\<leadsto>' \<Longrightarrow> era\<^sub>i' i = era\<^sub>t t"
      by (metis Message.inject(4) era\<^sub>i_eq isMessage'_eq)

    show "\<And>i s t a. s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto> \<Longrightarrow> \<exists>i'\<le>i. committed\<^sub>< i' \<and> era\<^sub>t t \<le> era\<^sub>i' i'"
      using JoinRequest_era era\<^sub>i_eq by force

    from JoinRequest_Some_PublishRequest
    show "\<And>i s t t' x'. s \<midarrow>\<langle> JoinRequest i t (PublishResponseSent t' x') \<rangle>\<leadsto> \<Longrightarrow> \<langle> PublishRequest i t' x' \<rangle>\<leadsto>'" by auto

  next
    fix i t
    assume a: "\<langle> ApplyCommit i t \<rangle>\<leadsto>"
    hence "committed\<^sub>< i" using ApplyCommit_PublishRequest PublishRequest_committedTo by blast
    hence "Q' (era\<^sub>i i) = Q (era\<^sub>i i)" by (simp add: Q'_eq)
    moreover from a have "era\<^sub>t t = era\<^sub>i i"
      using ApplyCommit_era by auto
    moreover note ApplyCommit_quorum [OF a]
    ultimately show "\<exists>q\<in>Q' (era\<^sub>t t). \<forall>s\<in>q. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>" by simp
  next
    fix i s t x
    assume "s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>'"
    hence "s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto> \<or> (s, i, t, x) = (s\<^sub>0, i\<^sub>0, t\<^sub>0, x\<^sub>0)" by simp
    thus "\<exists>q\<in>Q' (era\<^sub>t t). (\<forall>n\<in>q. promised i n s t) \<and> (prevAccepted i t q = {} \<or> v' i t = v' i (maxTerm (prevAccepted i t q)))"
    proof (elim disjE)
      assume a': "s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>"
      hence a: "\<langle> PublishRequest i t x \<rangle>\<leadsto>" by (auto simp add: isMessage_def)

      from PublishRequest_quorum [OF a']
      obtain q where q: "q \<in> Q (era\<^sub>t t)" "\<forall> n \<in> q. promised i n s t"
        and disj: "prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q))" by blast

      from era\<^sub>i_contiguous PublishRequest_era a
      obtain i' where "era\<^sub>i i' = era\<^sub>t t" and i':"i' \<le> i" by blast
      hence era_eq: "era\<^sub>t t = era\<^sub>i i'" by simp

      have Q_eq: "Q' (era\<^sub>t t) = Q (era\<^sub>t t)"
        using i' PublishRequest_committedTo [OF a]
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
          using JoinRequest_Some_PublishRequest nobody_proposed prevAccepted_def by fastforce
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

subsubsection \<open>Sending @{term PublishResponse} messages\<close>

text \<open>@{term "PublishResponse i\<^sub>0 t\<^sub>0"} can be sent in response to an @{term PublishRequest}
as long as a @{term JoinRequest} for a later term has not been sent:\<close>

lemma (in zen) send_PublishResponse:
  assumes "\<langle> PublishRequest i\<^sub>0 t\<^sub>0 x\<^sub>0 \<rangle>\<leadsto>"
  assumes "\<forall> i t a. s\<^sub>0 \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto> \<longrightarrow> t \<le> t\<^sub>0"
  shows "zen (insert \<lparr> sender = s\<^sub>0, destination = d\<^sub>0,
                       payload = PublishResponse i\<^sub>0 t\<^sub>0 \<rparr> messages)" (is "zen ?messages'")
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
    "\<And>s m d. (s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d) = ((s \<midarrow>\<langle> m \<rangle>\<rightarrow> d) \<or> (s, m, d) = (s\<^sub>0, PublishResponse i\<^sub>0 t\<^sub>0, d\<^sub>0))"
    by (auto simp add: isMessageFromTo'_def isMessageFromTo_def)

  have isMessageFrom'_eq [simp]:
    "\<And>s m. (s \<midarrow>\<langle> m \<rangle>\<leadsto>') = ((s \<midarrow>\<langle> m \<rangle>\<leadsto>) \<or> (s, m) = (s\<^sub>0, PublishResponse i\<^sub>0 t\<^sub>0))"
    by (auto simp add: isMessageFrom'_def isMessageFrom_def)

  have isMessageTo'_eq [simp]:
    "\<And>m d. (\<langle> m \<rangle>\<rightarrow>' d) = ((\<langle> m \<rangle>\<rightarrow> d) \<or> (m, d) = (PublishResponse i\<^sub>0 t\<^sub>0, d\<^sub>0))"
    by (auto simp add: isMessageTo'_def isMessageTo_def)

  have isMessage'_eq [simp]:
    "\<And>m. (\<langle> m \<rangle>\<leadsto>') = ((\<langle> m \<rangle>\<leadsto>) \<or> m = PublishResponse i\<^sub>0 t\<^sub>0)"
    by (auto simp add: isMessage'_def isMessage_def)

  have messages_simps:
    "\<And>i s d t a. (s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<rightarrow> d)"
    "\<And>i s d t x. (s \<midarrow>\<langle> PublishRequest i t x\<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow> d)"
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
    using JoinRequest_Some_lt JoinRequest_era PublishRequest_committedTo PublishRequest_quorum
      PublishRequest_function finite_messages_insert PublishRequest_era JoinRequest_Some_PublishRequest
      JoinRequest_unique_destination JoinRequest_not_broadcast
  proof -
    show "\<And>i i' s t t' a. s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto> \<Longrightarrow> i < i' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i' t' \<rangle>\<leadsto>'"
      using JoinRequest_future assms(2) by fastforce
    show "\<And>i s t t'. s \<midarrow>\<langle> JoinRequest i t NoPublishResponseSent \<rangle>\<leadsto> \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>'" 
      using JoinRequest_None assms(2) by fastforce
    show "\<And>i s t t' x'. s \<midarrow>\<langle> JoinRequest i t (PublishResponseSent t' x') \<rangle>\<leadsto> \<Longrightarrow> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>'"
      using JoinRequest_Some_PublishResponse by fastforce
    show "\<And>i s t t' t'' x'. s \<midarrow>\<langle> JoinRequest i t (PublishResponseSent t' x') \<rangle>\<leadsto> \<Longrightarrow> t' < t'' \<Longrightarrow> t'' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t'' \<rangle>\<leadsto>'"
      using JoinRequest_Some_max assms(2) by fastforce
    show "\<And>i s t. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>' \<Longrightarrow> \<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>"
      using PublishResponse_PublishRequest assms(1) by fastforce
    show "\<And>i t. \<langle> ApplyCommit i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>Q (era\<^sub>t t). \<forall>s\<in>q. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>'"
      by (meson ApplyCommit_quorum isMessageFrom'_eq)
  qed
qed

subsubsection \<open>Sending @{term ApplyCommit} messages\<close>

text \<open>@{term "ApplyCommit i\<^sub>0 t\<^sub>0"} can be sent on receipt of a quorum of corresponding
@{term PublishResponse} messages, where \textit{quorum} is defined in terms of the current
configuration:\<close>

lemma (in zen) send_ApplyCommit:
  assumes "q \<in> Q (era\<^sub>t t\<^sub>0)"
  assumes "\<forall> s \<in> q. s \<midarrow>\<langle> PublishResponse i\<^sub>0 t\<^sub>0 \<rangle>\<leadsto>"
  shows "zen (insert \<lparr> sender = s\<^sub>0, destination = d\<^sub>0, payload = ApplyCommit i\<^sub>0 t\<^sub>0 \<rparr> messages)" (is "zen ?messages'")
proof -
  have era: "era\<^sub>i i\<^sub>0 = era\<^sub>t t\<^sub>0"
    by (metis PublishResponse_era Q_member_member assms(1) assms(2))

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
    "\<And>i s d t a. (s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<rightarrow> d)"
    "\<And>i s d t x. (s \<midarrow>\<langle> PublishRequest i t x\<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>i s d t. (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<rightarrow> d)"
    by auto

  define isCommitted' where "\<And>i. isCommitted' i \<equiv> \<exists>t. \<langle> ApplyCommit i t \<rangle>\<leadsto>'"
  define committedTo' ("committed\<^sub><'") where "\<And>i. committed\<^sub><' i \<equiv> \<forall>j < i. isCommitted' j"
  define v\<^sub>c' where "\<And>i. v\<^sub>c' i \<equiv> v i (SOME t. \<langle> ApplyCommit i t \<rangle>\<leadsto>')"
  define era\<^sub>i' where "\<And>i. era\<^sub>i' i \<equiv> eraOfNat (card {j. j < i \<and> isReconfiguration (v\<^sub>c' j)})"
  define reconfig' where "\<And>e. reconfig' e \<equiv> THE i. isCommitted' i \<and> isReconfiguration (v\<^sub>c' i) \<and> era\<^sub>i' i = e"
  define Q' where "\<And>e. Q' e \<equiv> case e of e\<^sub>0 \<Rightarrow> Q\<^sub>0 | nextEra e' \<Rightarrow> getConf (v\<^sub>c' (reconfig' e'))"

  have committedTo_current: "committed\<^sub>< i\<^sub>0"
    using assms by (metis PublishRequest_committedTo Q_member_member PublishResponse_PublishRequest)

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
        from assms show "q \<in> (Q \<circ> era\<^sub>t) t\<^sub>0" "\<And>s. s \<in> q \<Longrightarrow> s \<midarrow>\<langle> PublishResponse i\<^sub>0 t\<^sub>0 \<rangle>\<leadsto>"
          by simp_all

        from i have "\<langle> ApplyCommit i\<^sub>0 t \<rangle>\<leadsto>" by (metis True isCommitted_def someI_ex t_def)
        thus "\<langle> ApplyCommit i\<^sub>0 t \<rangle>\<leadsto> \<or> t = t\<^sub>0" by simp
        from i have t': "\<langle> ApplyCommit i\<^sub>0 t' \<rangle>\<leadsto>'" 
          by (metis isMessage'_eq someI_ex t'_def)
        thus "\<langle> ApplyCommit i\<^sub>0 t' \<rangle>\<leadsto> \<or> t' = t\<^sub>0" by simp

        fix t assume le: "t\<^sub>0 \<le> t"
        assume "\<exists>x. \<langle> PublishRequest i\<^sub>0 t x \<rangle>\<leadsto>"
        then obtain x where "\<langle> PublishRequest i\<^sub>0 t x \<rangle>\<leadsto>" by blast

        hence "era\<^sub>t t \<le> era\<^sub>i i\<^sub>0" using PublishRequest_era by simp
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
    using JoinRequest_future JoinRequest_None JoinRequest_Some_lt JoinRequest_Some_PublishResponse
      JoinRequest_Some_max PublishRequest_function finite_messages_insert PublishResponse_PublishRequest
      JoinRequest_Some_PublishRequest JoinRequest_unique_destination JoinRequest_not_broadcast
  proof -
    from PublishRequest_committedTo show "\<And>i t x. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub><' i" by (simp add: committedTo_eq)

    from JoinRequest_era era\<^sub>i_eq committedTo_eq
    show "\<And>i s t a. s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto> \<Longrightarrow> \<exists>i'\<le>i. committed\<^sub><' i' \<and> era\<^sub>t t \<le> era\<^sub>i' i'"
      by force

    from era\<^sub>i_eq show "\<And>i t x. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> era\<^sub>i' i = era\<^sub>t t"
      using ApplyCommit_era era committedTo_current isCommitted_committedTo isCommitted_def 
      by (simp add: PublishRequest_committedTo PublishRequest_era)

    show "\<And>i s t x. s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>Q' (era\<^sub>t t). (\<forall>n\<in>q. promised i n s t) \<and> (prevAccepted i t q = {} \<or> v i t = v i (maxTerm (prevAccepted i t q)))"
      by (metis PublishRequest_committedTo PublishRequest_era PublishRequest_quorum Q'_eq isMessage_def order_refl)

    show "\<And>i t. \<langle> ApplyCommit i t \<rangle>\<leadsto>' \<Longrightarrow> \<exists>q\<in>Q' (era\<^sub>t t). \<forall>s\<in>q. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>"
      by (metis (mono_tags, hide_lams) ApplyCommit_era ApplyCommit_quorum Message.inject(6) Q'_eq assms(1) assms(2) committedTo_current era isCommitted'_def isCommitted_committedTo isCommitted_eq isMessage'_eq order_refl)
  qed
qed

subsubsection \<open>Sending @{term Reboot} messages\<close>

text \<open>Any node may send a @{term Reboot} message at any time.\<close>

lemma (in zen) send_Reboot:
  shows "zen (insert \<lparr> sender = s\<^sub>0, destination = d\<^sub>0, payload = Reboot \<rparr> messages)" (is "zen ?messages'")
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
    "\<And>i s d t a. (s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<rightarrow> d)"
    "\<And>i s d t x. (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>i s d t. (s \<midarrow>\<langle> PublishResponse i t\<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<rightarrow> d)"
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
    using PublishResponse_PublishRequest PublishRequest_era PublishRequest_quorum PublishRequest_function
      PublishRequest_committedTo JoinRequest_Some_lt JoinRequest_Some_PublishResponse
      JoinRequest_Some_max finite_messages_insert JoinRequest_None JoinRequest_era
      JoinRequest_future ApplyCommit_quorum JoinRequest_Some_PublishRequest
      JoinRequest_not_broadcast JoinRequest_unique_destination
    by (simp_all)
qed

section \<open>Per-node model\<close>

record NodeData =
  currentNode :: Node (* identity of this node *)
  firstUncommittedSlot :: nat (* all slots strictly below this one are committed *)
  currentEra :: Era (* era of the firstUncommittedSlot slot *)
  currentConfiguration :: Configuration (* configuration of the currentEra *)
  currentClusterState :: ClusterState (* last-committed cluster state *)
  (* acceptor data *)
  lastAccepted :: PreviousPublishResponse (* term and value that were last accepted in this slot, if any *)
  currentTerm :: Term (* greatest term for which a promise was sent *)
  (* election data *)
  electionTerm :: Term (* term of JoinRequests being collected *)
  electionVotes :: "Node set" (* set of nodes that have sent a JoinRequest for the current electionTerm *)
  electionWon :: bool
  electionValue :: PreviousPublishResponse
  (* learner data *)
  applyRequested :: bool (* whether an PublishRequest has been sent with slot=firstUncommittedSlot and term=electionTerm *)
  applyTerm :: Term
  applyVotes :: "Node set"

definition applyValue :: "Value \<Rightarrow> NodeData \<Rightarrow> NodeData"
  where
    "applyValue x nd \<equiv> case x of
        NoOp \<Rightarrow> nd
      | Reconfigure Q \<Rightarrow> nd \<lparr> currentEra := nextEra (currentEra nd)
                            , currentConfiguration := Q
                            , electionVotes := {}
                            , electionWon := False
                            , electionValue := NoPublishResponseSent \<rparr>
      | SetClusterState s \<Rightarrow> nd \<lparr> currentClusterState := s \<rparr>"

definition lastAcceptedGreaterTermThan :: "Term \<Rightarrow> NodeData \<Rightarrow> bool"
  where
    "lastAcceptedGreaterTermThan t nd \<equiv> case lastAccepted nd of
      NoPublishResponseSent \<Rightarrow> False
      | PublishResponseSent t' _ \<Rightarrow> t' < t"

definition isQuorum :: "NodeData \<Rightarrow> Node set \<Rightarrow> bool"
  where "isQuorum nd q \<equiv> q \<in> Rep_Configuration (currentConfiguration nd)"

fun combinePublishResponses :: "PreviousPublishResponse \<Rightarrow> PreviousPublishResponse \<Rightarrow> PreviousPublishResponse"
  where
    "combinePublishResponses NoPublishResponseSent par = par"
  | "combinePublishResponses par NoPublishResponseSent = par"
  | "combinePublishResponses (PublishResponseSent t\<^sub>1 x\<^sub>1) (PublishResponseSent t\<^sub>2 x\<^sub>2)
        = (if t\<^sub>1 < t\<^sub>2 then PublishResponseSent t\<^sub>2 x\<^sub>2 else PublishResponseSent t\<^sub>1 x\<^sub>1)"

lemma combinePublishResponses_p_none[simp]:
  "combinePublishResponses par NoPublishResponseSent = par"
  by (cases par, auto)

lemma combinePublishResponses_eq_NoPublishResponseSent_1:
  assumes "combinePublishResponses p1 p2 = NoPublishResponseSent"
  shows "p1 = NoPublishResponseSent"
  using assms
  by (metis PreviousPublishResponse.exhaust combinePublishResponses.simps(3) combinePublishResponses_p_none)

lemma combinePublishResponses_eq_NoPublishResponseSent_2:
  assumes "combinePublishResponses p1 p2 = NoPublishResponseSent"
  shows "p2 = NoPublishResponseSent"
  using assms
  by (metis combinePublishResponses.simps(1) combinePublishResponses_eq_NoPublishResponseSent_1)

lemma combinePublishResponses_range: "combinePublishResponses p1 p2 \<in> {p1, p2}"
  by (cases p1, simp, cases p2, simp_all)

definition publishValue :: "Value \<Rightarrow> NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "publishValue x nd \<equiv>
        if electionWon nd \<and> \<not> applyRequested nd
              then ( nd \<lparr> applyRequested := True \<rparr>
                   , Some (PublishRequest (firstUncommittedSlot nd) (electionTerm nd) x) )
              else (nd, None)"

definition handleClientValue :: "Value \<Rightarrow> NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "handleClientValue x nd \<equiv>
      if electionValue nd = NoPublishResponseSent then publishValue x nd else (nd, None)"

definition handleStartJoin :: "Term \<Rightarrow> NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "handleStartJoin t nd \<equiv> if currentTerm nd < t \<and> era\<^sub>t t = currentEra nd
          then ( nd \<lparr> currentTerm := t \<rparr>
               , Some (JoinRequest (firstUncommittedSlot nd)
                                     t
                                    (lastAccepted nd)))
          else (nd, None)"

definition ensureElectionTerm :: "Term \<Rightarrow> NodeData \<Rightarrow> NodeData"
  where
    "ensureElectionTerm t nd \<equiv> if electionTerm nd = t
                                then nd
                                else nd \<lparr> electionVotes := {}
                                        , electionTerm := t
                                        , electionWon := False
                                        , electionValue := NoPublishResponseSent
                                        , applyRequested := False
                                        \<rparr>"

definition addElectionVote :: "Node \<Rightarrow> nat => PreviousPublishResponse \<Rightarrow> NodeData \<Rightarrow> NodeData"
  where
    "addElectionVote s i a nd \<equiv> let newVotes = insert s (electionVotes nd)
      in nd \<lparr> electionVotes := newVotes
            , electionValue := combinePublishResponses (electionValue nd)
                                                     (if i = firstUncommittedSlot nd
                                                        then a
                                                        else NoPublishResponseSent)
            , electionWon := isQuorum nd newVotes \<rparr>"

definition sendElectionValueIfAppropriate :: "NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "sendElectionValueIfAppropriate nd
      \<equiv> case electionValue nd of
          PublishResponseSent _ x \<Rightarrow> publishValue x nd
          | _ \<Rightarrow> (nd, None)"

definition handleJoinRequest :: "Node \<Rightarrow> nat \<Rightarrow> Term \<Rightarrow> PreviousPublishResponse \<Rightarrow> NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "handleJoinRequest s i t a nd \<equiv>
         if firstUncommittedSlot nd < i
             \<or> t < electionTerm nd
             \<or> (t = electionTerm nd \<and> electionWon nd)
             \<or> era\<^sub>t t \<noteq> currentEra nd
          then (nd, None)
          else let nd1 = ensureElectionTerm t nd;
                   nd2 = addElectionVote s i a nd1
               in sendElectionValueIfAppropriate nd2"

definition handlePublishRequest :: "nat \<Rightarrow> Term \<Rightarrow> Value \<Rightarrow> NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "handlePublishRequest i t x nd \<equiv>
          if currentTerm nd \<le> t
                \<and> \<not> lastAcceptedGreaterTermThan t nd
                \<and> firstUncommittedSlot nd = i
          then ( nd \<lparr> lastAccepted := PublishResponseSent t x \<rparr>
               , Some (PublishResponse i t))
          else (nd, None)"

definition handlePublishResponse :: "Node \<Rightarrow> nat \<Rightarrow> Term \<Rightarrow> NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "handlePublishResponse s i t nd \<equiv>
        if firstUncommittedSlot nd = i \<and> applyTerm nd \<le> t
        then let oldVotes = if applyTerm nd = t then applyVotes nd else {};
                 newVotes = insert s oldVotes
             in (nd \<lparr> applyTerm := t, applyVotes := newVotes \<rparr>,
                 if isQuorum nd newVotes then Some (ApplyCommit i t) else None)
        else (nd, None)"

definition handleApplyCommit :: "nat \<Rightarrow> Term \<Rightarrow> NodeData \<Rightarrow> NodeData"
  where
    "handleApplyCommit i t nd \<equiv> 
        if i = firstUncommittedSlot nd
        then case lastAccepted nd of
            PublishResponseSent t' x' \<Rightarrow>
              if t = t'
              then applyValue x'
                      nd \<lparr> firstUncommittedSlot := i + 1
                         , lastAccepted := NoPublishResponseSent
                         , applyRequested := False
                         , electionValue := NoPublishResponseSent \<rparr>
              else nd
          | NoPublishResponseSent \<Rightarrow> nd
        else nd"

definition handleReboot :: "NodeData \<Rightarrow> NodeData"
  where
    "handleReboot nd \<equiv> 
      \<lparr> currentNode = currentNode nd
      , firstUncommittedSlot = firstUncommittedSlot nd
      , currentEra = currentEra nd
      , currentConfiguration = currentConfiguration nd
      , currentClusterState = currentClusterState nd
      , lastAccepted = lastAccepted nd
      , currentTerm = currentTerm nd
      , electionTerm = SOME t. False
      , electionVotes = {}
      , electionWon = False
      , electionValue = NoPublishResponseSent
      , applyRequested = True
      , applyTerm = SOME t. False
      , applyVotes = {}
      \<rparr>"

definition ProcessMessage :: "NodeData \<Rightarrow> RoutedMessage \<Rightarrow> (NodeData * RoutedMessage option)"
  where
    "ProcessMessage nd msg \<equiv>
      let respondTo = (\<lambda> d (nd, mmsg). case mmsg of None \<Rightarrow> (nd, None) | Some msg \<Rightarrow> (nd, Some
                          \<lparr> sender = currentNode nd, destination = d, payload = msg \<rparr>));
          respondToSender = respondTo (OneNode (sender msg));
          respondToAll    = respondTo Broadcast
      in
        if destination msg \<in> { Broadcast, OneNode (currentNode nd) }
        then case payload msg of
          StartJoin t \<Rightarrow> respondToSender (handleStartJoin t nd)
          | JoinRequest i t a \<Rightarrow> respondToAll (handleJoinRequest (sender msg) i t a nd)
          | ClientValue x \<Rightarrow> respondToAll (handleClientValue x nd)
          | PublishRequest i t x \<Rightarrow> respondToSender (handlePublishRequest i t x nd)
          | PublishResponse i t \<Rightarrow> respondToAll (handlePublishResponse (sender msg) i t nd)
          | ApplyCommit i t \<Rightarrow> (handleApplyCommit i t nd, None)
          | Reboot \<Rightarrow> (handleReboot nd, None)
        else (nd, None)"

locale zenImpl = zen +
  fixes nodeState :: "Node \<Rightarrow> NodeData"
  assumes nodesIdentified: "\<And>n. currentNode (nodeState n) = n"
  assumes committedToLocalCheckpoint: "\<And>n. committed\<^sub>< (firstUncommittedSlot (nodeState n))"
  assumes eraMatchesLocalCheckpoint: "\<And>n. currentEra (nodeState n) = era\<^sub>i (firstUncommittedSlot (nodeState n))"
  assumes isQuorum_firstUncommittedSlot:
    "\<And>n. { q. isQuorum (nodeState n) q } = Q (era\<^sub>i (firstUncommittedSlot (nodeState n)))"
  assumes nothingAcceptedInLaterSlots:
    "\<And>i n t. firstUncommittedSlot (nodeState n) < i
    \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>"
  assumes lastAccepted_None: "\<And>n t. lastAccepted (nodeState n) = NoPublishResponseSent
    \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>"
  assumes lastAccepted_Some_term: "\<And>n t' x'. lastAccepted (nodeState n) = PublishResponseSent t' x'
  \<Longrightarrow> t' \<le> currentTerm (nodeState n)"
  assumes lastAccepted_Some_sent: "\<And>n t' x'. lastAccepted (nodeState n) = PublishResponseSent t' x'
  \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t' \<rangle>\<leadsto>"
  assumes lastAccepted_Some_value: "\<And>n t' x'. lastAccepted (nodeState n) = PublishResponseSent t' x'
  \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t' x' \<rangle>\<leadsto>"
  assumes lastAccepted_Some_max: "\<And>n t' x' t''. lastAccepted (nodeState n) = PublishResponseSent t' x'
  \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t'' \<rangle>\<leadsto>
  \<Longrightarrow> t'' \<le> t'"
  assumes JoinRequest_currentTerm:
    "\<And>n i t a. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)"
  assumes JoinRequest_slot_function:
    "\<And>n i i' t a a'. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto> \<Longrightarrow> n \<midarrow>\<langle> JoinRequest i' t a' \<rangle>\<leadsto> \<Longrightarrow> i = i'"
  
  assumes PublishRequest_electionTerm:
    "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto>
        \<Longrightarrow> t \<le> electionTerm (nodeState n)"
  assumes PublishRequest_electionTerm_applyRequested:
    "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto>
        \<Longrightarrow> \<not> applyRequested (nodeState n)
        \<Longrightarrow> t < electionTerm (nodeState n)"
  assumes applyRequested_electionWon:
    "\<And>n. applyRequested (nodeState n) \<Longrightarrow> electionWon (nodeState n)"
  assumes electionVotes:
    "\<And> n n'. n' \<in> electionVotes (nodeState n)
      \<Longrightarrow> \<exists> i \<le> firstUncommittedSlot (nodeState n). \<exists> a.
        n' \<midarrow>\<langle> JoinRequest i (electionTerm (nodeState n)) a \<rangle>\<rightarrow> (OneNode n)"
  assumes electionWon_isQuorum:
    "\<And>n. electionWon (nodeState n) \<Longrightarrow> isQuorum (nodeState n) (electionVotes (nodeState n))"
  assumes electionWon_era:
    "\<And>n. electionWon (nodeState n) \<Longrightarrow> era\<^sub>t (electionTerm (nodeState n)) = era\<^sub>i (firstUncommittedSlot (nodeState n))"

  assumes electionValue_None: "\<And>n n'.
    \<lbrakk> electionValue (nodeState n) = NoPublishResponseSent; n' \<in> electionVotes (nodeState n) \<rbrakk>
    \<Longrightarrow> (n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n))
                           (electionTerm (nodeState n))
                           NoPublishResponseSent \<rangle>\<rightarrow> (OneNode n))
    \<or> (\<exists> i < firstUncommittedSlot (nodeState n). \<exists> a.
        n' \<midarrow>\<langle> JoinRequest i (electionTerm (nodeState n)) a \<rangle>\<rightarrow> (OneNode n))"
  assumes electionValue_Some: "\<And>n t' x'.
    \<lbrakk> electionValue (nodeState n) = PublishResponseSent t' x' \<rbrakk>
    \<Longrightarrow> \<exists> n' \<in> electionVotes (nodeState n).
         (n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n))
                               (electionTerm (nodeState n))
                               (PublishResponseSent t' x') \<rangle>\<rightarrow> (OneNode n))"
  assumes electionValue_Some_max: "\<And>n t' x' n'' t'' x''.
    \<lbrakk> electionValue (nodeState n) = PublishResponseSent t' x';
      n'' \<in> electionVotes (nodeState n);
      n'' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n))
                                (electionTerm (nodeState n))
                                (PublishResponseSent t'' x'') \<rangle>\<rightarrow> (OneNode n) \<rbrakk>
    \<Longrightarrow> t'' \<le> t'"

locale zenStep = zenImpl +
  fixes n\<^sub>0 :: Node
  fixes nd' :: NodeData
  fixes messages' :: "RoutedMessage set"
  fixes message :: RoutedMessage
  assumes message: "message \<in> messages"
  assumes messages_subset: "messages \<subseteq> messages'"

definition (in zenStep) nd :: NodeData
  where "nd \<equiv> nodeState n\<^sub>0"
definition (in zenStep) nodeState' :: "Node \<Rightarrow> NodeData"
  where "nodeState' n \<equiv> if n = n\<^sub>0 then nd' else nodeState n"
    (* updated definitions from zen *)
definition (in zenStep) isMessageFromTo' :: "Node \<Rightarrow> Message \<Rightarrow> Destination \<Rightarrow> bool" ("_ \<midarrow>\<langle> _ \<rangle>\<rightarrow>' _" [55])
  where "s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d \<equiv> \<lparr> sender = s, destination = d, payload = m \<rparr> \<in> messages'"
definition (in zenStep) isMessageFrom' :: "Node \<Rightarrow> Message \<Rightarrow> bool" ("_ \<midarrow>\<langle> _ \<rangle>\<leadsto>'" [55])
  where "s \<midarrow>\<langle> m \<rangle>\<leadsto>' \<equiv> \<exists> d. s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d"
definition (in zenStep) isMessageTo' :: "Message \<Rightarrow> Destination \<Rightarrow> bool" ("\<langle> _ \<rangle>\<rightarrow>' _" [55])
  where "\<langle> m \<rangle>\<rightarrow>' d \<equiv> \<exists> s. s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d"
definition (in zenStep) isMessage' :: "Message \<Rightarrow> bool" ("\<langle> _ \<rangle>\<leadsto>'" [55])
  where "\<langle> m \<rangle>\<leadsto>' \<equiv> \<exists> s. s \<midarrow>\<langle> m \<rangle>\<leadsto>'"
    (* value proposed in a slot & a term *)
definition (in zenStep) v' :: "nat \<Rightarrow> Term \<Rightarrow> Value"
  where "v' i t \<equiv> THE x. \<langle> PublishRequest i t x \<rangle>\<leadsto>'"
    (* whether a slot is committed *)
definition (in zenStep) isCommitted' :: "nat \<Rightarrow> bool"
  where "isCommitted' i \<equiv> \<exists> t. \<langle> ApplyCommit i t \<rangle>\<leadsto>'"
    (* whether all preceding slots are committed *)
definition (in zenStep) committedTo' :: "nat \<Rightarrow> bool" ("committed\<^sub><'")
  where "committed\<^sub><' i \<equiv> \<forall> j < i. isCommitted' j" 
    (* the committed value in a slot *)
definition (in zenStep) v\<^sub>c' :: "nat \<Rightarrow> Value"
  where "v\<^sub>c' i \<equiv> v' i (SOME t. \<langle> ApplyCommit i t \<rangle>\<leadsto>')"
    (* the era of a slot *)
definition (in zenStep) era\<^sub>i' :: "nat \<Rightarrow> Era"
  where "era\<^sub>i' i \<equiv> eraOfNat (card { j. j < i \<and> isReconfiguration (v\<^sub>c' j) })"
    (* the (unique) slot in an era containing a reconfiguration *)
definition (in zenStep) reconfig' :: "Era \<Rightarrow> nat"
  where "reconfig' e
      \<equiv> THE i. isCommitted' i \<and> isReconfiguration (v\<^sub>c' i) \<and> era\<^sub>i' i = e"
    (* the configuration of an era *)
definition (in zenStep) Q' :: "Era \<Rightarrow> Node set set"
  where "Q' e \<equiv> case e of e\<^sub>0 \<Rightarrow> Q\<^sub>0 | nextEra e' \<Rightarrow> getConf (v\<^sub>c' (reconfig' e'))"
    (* predicate to say whether an applicable JoinRequest has been sent *)
definition (in zenStep) promised' :: "nat \<Rightarrow> Node \<Rightarrow> Node \<Rightarrow> Term \<Rightarrow> bool"
  where "promised' i s dn t \<equiv> \<exists> i' \<le> i. \<exists> a. s \<midarrow>\<langle> JoinRequest i' t a \<rangle>\<rightarrow>' (OneNode dn)"
    (* set of previously-accepted terms *)
definition (in zenStep) prevAccepted' :: "nat \<Rightarrow> Term \<Rightarrow> Node set \<Rightarrow> Term set"
  where "prevAccepted' i t senders
      \<equiv> {t'. \<exists> s \<in> senders. \<exists> x'. s \<midarrow>\<langle> JoinRequest i t (PublishResponseSent t' x') \<rangle>\<leadsto>' }"

lemma (in zenStep)
  assumes "zen messages'"
  assumes "\<And>n. currentNode (nodeState' n) = n"
  assumes "\<And>n. committed\<^sub><' (firstUncommittedSlot (nodeState' n))"
  assumes "\<And>n. currentEra (nodeState' n) = era\<^sub>i' (firstUncommittedSlot (nodeState' n))"
  assumes "\<And>n. {q. isQuorum (nodeState' n) q} = Q' (era\<^sub>i' (firstUncommittedSlot (nodeState' n)))"
  assumes "\<And>i n t. firstUncommittedSlot (nodeState' n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>'"
  assumes "\<And>n t. lastAccepted (nodeState' n) = NoPublishResponseSent \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t \<rangle>\<leadsto>'"
  assumes "\<And>n t' x'. lastAccepted (nodeState' n) = PublishResponseSent t' x' \<Longrightarrow> t' \<le> currentTerm (nodeState' n)"
  assumes "\<And>n t' x'. lastAccepted (nodeState' n) = PublishResponseSent t' x' \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t' \<rangle>\<leadsto>'"
  assumes "\<And>n t' x'. lastAccepted (nodeState' n) = PublishResponseSent t' x' \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t' x' \<rangle>\<leadsto>'"
  assumes "\<And>n t' x' t''. lastAccepted (nodeState' n) = PublishResponseSent t' x' \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t'' \<rangle>\<leadsto>' \<Longrightarrow> t'' \<le> t'"
  assumes "\<And>n i t a. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>' \<Longrightarrow> t \<le> currentTerm (nodeState' n)"
  assumes "\<And>n i i' t a a'. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>' \<Longrightarrow> n \<midarrow>\<langle> JoinRequest i' t a' \<rangle>\<leadsto>' \<Longrightarrow> i = i'"
  assumes "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t x \<rangle>\<leadsto>' \<Longrightarrow> t \<le> electionTerm (nodeState' n)"
  assumes "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t x \<rangle>\<leadsto>' \<Longrightarrow> \<not> applyRequested (nodeState' n) \<Longrightarrow> t < electionTerm (nodeState' n)"
  assumes "\<And>n. applyRequested (nodeState' n) \<Longrightarrow> electionWon (nodeState' n)"
  assumes "\<And>n n'. n' \<in> electionVotes (nodeState' n) \<Longrightarrow> promised' (firstUncommittedSlot (nodeState' n)) n' n (electionTerm (nodeState' n))"
  assumes "\<And>n. electionWon (nodeState' n) \<Longrightarrow> isQuorum (nodeState' n) (electionVotes (nodeState' n))"
  assumes "\<And>n. electionWon (nodeState' n) \<Longrightarrow> era\<^sub>t (electionTerm (nodeState' n)) = era\<^sub>i' (firstUncommittedSlot (nodeState' n))"
  assumes "\<And>n n'. electionValue (nodeState' n) = NoPublishResponseSent \<Longrightarrow> n' \<in> electionVotes (nodeState' n) \<Longrightarrow> (n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState' n)) (electionTerm (nodeState' n)) NoPublishResponseSent \<rangle>\<rightarrow>' (OneNode n)) \<or> (\<exists>i<firstUncommittedSlot (nodeState' n). \<exists>a. n' \<midarrow>\<langle> JoinRequest i (electionTerm (nodeState' n)) a \<rangle>\<rightarrow>' (OneNode n))"
  assumes "\<And>n t' x'. electionValue (nodeState' n) = PublishResponseSent t' x' \<Longrightarrow> \<exists>n'\<in>electionVotes (nodeState' n). n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState' n)) (electionTerm (nodeState' n)) (PublishResponseSent t' x') \<rangle>\<rightarrow>' (OneNode n)"
  assumes "\<And>n t' x' n'' t'' x''. electionValue (nodeState' n) = PublishResponseSent t' x' \<Longrightarrow> n'' \<in> electionVotes (nodeState' n) \<Longrightarrow> n'' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState' n)) (electionTerm (nodeState' n)) (PublishResponseSent t'' x'') \<rangle>\<rightarrow>' (OneNode n) \<Longrightarrow> t'' \<le> t'"
  shows zenImplI: "zenImpl messages' nodeState'"
  apply (intro_locales, intro assms, intro zenImpl_axioms.intro)
                 apply (fold isMessageFromTo'_def)
                 apply (fold isMessageFrom'_def)
                 apply (fold isMessage'_def)
                 apply (fold v'_def)
                 apply (fold isCommitted'_def)
                 apply (fold committedTo'_def)
                 apply (fold v\<^sub>c'_def)
                 apply (fold era\<^sub>i'_def)
                 apply (fold reconfig'_def)
                 apply (fold Q'_def)
                 apply (fold promised'_def)
  using assms proof - qed

definition (in zenStep) response :: "Message \<Rightarrow> RoutedMessage"
  where
    "\<And>msg. response msg \<equiv>  \<lparr>sender = n\<^sub>0,
                             destination = OneNode (sender message),
                             payload = msg \<rparr>"

definition (in zenStep) broadcast :: "Message \<Rightarrow> RoutedMessage"
  where
    "\<And>msg. broadcast msg \<equiv>  \<lparr>sender = n\<^sub>0,
                             destination = Broadcast,
                             payload = msg \<rparr>"

fun (in zenStep) send :: "(Message \<Rightarrow> RoutedMessage) \<Rightarrow> ('a * Message option) \<Rightarrow> RoutedMessage set"
  where
    "send f (_, None) = messages"
  | "send f (_, Some m) = insert (f m) messages"

lemma (in zenStep)
  assumes "zenImpl messages' nodeState'"
  shows zenStepI: "zenStep messages' nodeState' messages' message"
proof (intro_locales)
  from assms
  show "zen messages'" "zenImpl_axioms messages' nodeState'"
    by (simp_all add: zenImpl_def)

  from message messages_subset
  show "zenStep_axioms messages' messages' message"
    by (intro zenStep_axioms.intro, auto)
qed

lemma (in zenStep) publishValue_invariants:
  fixes x
  defines "result \<equiv> publishValue x nd"
  assumes nd': "nd' = fst result"
  assumes messages': "messages' = send broadcast result"
  assumes x: "\<And> t' x'. electionValue nd = PublishResponseSent t' x' \<Longrightarrow> x = x'"
  shows "zenImpl messages' nodeState'"
proof (cases "electionWon nd \<and> \<not> applyRequested nd")
  case False
  hence result: "result = (nd, None)" by (simp add: result_def publishValue_def)
  have "messages' = messages" by (auto simp add: messages' result)
  moreover
  have "nodeState' = nodeState" by (intro ext, unfold nodeState'_def, simp add: nd' result nd_def)
  moreover note zenImpl_axioms
  ultimately show ?thesis by simp
next
  case True note won = this
  hence result: "result = (nd \<lparr>applyRequested := True\<rparr>,
                           Some (PublishRequest (firstUncommittedSlot nd) (electionTerm nd) x))"
    by (simp add: result_def publishValue_def)

  have messages': "messages' = insert \<lparr>sender = n\<^sub>0, destination = Broadcast, payload = PublishRequest (firstUncommittedSlot nd) (electionTerm nd) x\<rparr> messages"
    by (simp add: messages' result broadcast_def)

  have message_simps:
    "\<And>s d i t a. (s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<rightarrow> d)"
    "\<And>s d i t. (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<rightarrow> d)"
    "\<And>s d i t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)"
    "\<And>d i t a. (\<langle> JoinRequest i t a \<rangle>\<rightarrow>' d) = (\<langle> JoinRequest i t a \<rangle>\<rightarrow> d)"
    "\<And>d i t. (\<langle> PublishResponse i t \<rangle>\<rightarrow>' d) = (\<langle> PublishResponse i t \<rangle>\<rightarrow> d)"
    "\<And>d i t. (\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = (\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)"
    "\<And>s d i t a. (s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>') = (s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>)"
    "\<And>s d i t. (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>') = (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>)"
    "\<And>s d i t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<leadsto>') = (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<leadsto>)"
    "\<And>d i t a. (\<langle> JoinRequest i t a \<rangle>\<leadsto>') = (\<langle> JoinRequest i t a \<rangle>\<leadsto>)"
    "\<And>d i t. (\<langle> PublishResponse i t \<rangle>\<leadsto>') = (\<langle> PublishResponse i t \<rangle>\<leadsto>)"
    "\<And>d i t. (\<langle> ApplyCommit i t \<rangle>\<leadsto>') = (\<langle> ApplyCommit i t \<rangle>\<leadsto>)"
    by (auto simp add: isMessageFromTo'_def isMessageTo'_def isMessage'_def isMessageFrom'_def,
        auto simp add: isMessageFromTo_def isMessageTo_def isMessage_def isMessageFrom_def messages')

  from electionWon_era True eraMatchesLocalCheckpoint
  have era_eq:
    "era\<^sub>t (electionTerm nd) = currentEra nd" 
    "era\<^sub>i (firstUncommittedSlot nd) = currentEra nd" by (simp_all add: nd_def)

  have PublishRequest': "\<And>s d i t x'. (s \<midarrow>\<langle> PublishRequest i t x' \<rangle>\<rightarrow>' d) = ((s \<midarrow>\<langle> PublishRequest i t x' \<rangle>\<rightarrow> d)
          \<or> (s, d, i, t, x') = (n\<^sub>0, Broadcast, firstUncommittedSlot nd, electionTerm nd, x))"
    by (auto simp add: isMessageFromTo'_def, auto simp add: messages' isMessageFromTo_def)

  have fresh_request: "\<And>x. \<not> \<langle> PublishRequest (firstUncommittedSlot nd) (electionTerm nd) x \<rangle>\<leadsto>"
  proof (intro notI)
    fix x'
    assume "\<langle> PublishRequest (firstUncommittedSlot nd) (electionTerm nd) x' \<rangle>\<leadsto>"
    with True obtain s d where
      s: "s \<midarrow>\<langle> PublishRequest (firstUncommittedSlot nd) (electionTerm nd) x' \<rangle>\<rightarrow> d"
      by (auto simp add: isMessage_def isMessageFrom_def)

    with PublishRequest_quorum [where s = s and i = "firstUncommittedSlot nd" and t = "electionTerm nd" and x = x']
    obtain q where q: "q \<in> Q (currentEra nd)" and promised: "\<And>n. n \<in> q \<Longrightarrow> promised (firstUncommittedSlot nd) n s (electionTerm nd)"
      by (auto simp add: era_eq isMessageFrom_def, blast)

    from won have "isQuorum nd (electionVotes nd)"
      by (unfold nd_def, intro electionWon_isQuorum, simp)
    with isQuorum_firstUncommittedSlot [of n\<^sub>0]
    have "electionVotes nd \<in> Q (currentEra nd)" using nd_def era_eq by auto

    from q this Q_intersects have "q \<inter> electionVotes nd \<noteq> {}"
      by (auto simp add: intersects_def)
    then obtain n where n: "n \<in> q" "n \<in> electionVotes nd" by auto

    from promised [OF `n \<in> q`]
    obtain i' a' where "n \<midarrow>\<langle> JoinRequest i' (electionTerm nd) a' \<rangle>\<rightarrow> (OneNode s)"
      by (auto simp add: promised_def)

    moreover from electionVotes n
    obtain i'' a'' where "n \<midarrow>\<langle> JoinRequest i'' (electionTerm nd) a'' \<rangle>\<rightarrow> (OneNode n\<^sub>0)"
      by (auto simp add: nd_def, blast)

    ultimately have "OneNode s = OneNode n\<^sub>0"
      by (intro JoinRequest_unique_destination)

    with s have "n\<^sub>0 \<midarrow>\<langle> PublishRequest (firstUncommittedSlot nd) (electionTerm nd) x' \<rangle>\<leadsto>"
      by (auto simp add: isMessageFrom_def)

    hence "electionTerm nd < electionTerm (nodeState n\<^sub>0)"
    proof (intro PublishRequest_electionTerm_applyRequested, fold nd_def)
      from won show "\<not> applyRequested nd" by (simp add: nd_def)
    qed
    thus False by (simp add: nd_def)
  qed

  have v_eq: "\<And>i t. v' i t = (if (i, t) = (firstUncommittedSlot nd, electionTerm nd) then x else v i t)"
  proof -
    fix i t
    show "?thesis i t"
    proof (cases "(i, t) = (firstUncommittedSlot nd, electionTerm nd)")
      case False
      with PublishRequest'
      show ?thesis
        by (unfold v'_def v_def isMessage'_def isMessageFrom'_def isMessage_def isMessageFrom_def, auto)
    next
      case True
      have "v' i t = x"
      proof (unfold v'_def, intro the_equality)
        from True
        show p1: "\<langle> PublishRequest i t x \<rangle>\<leadsto>'"
          by (auto simp add: isMessage'_def isMessageFrom'_def PublishRequest')

        fix x'
        assume "\<langle> PublishRequest i t x' \<rangle>\<leadsto>'"
        with True have "\<langle> PublishRequest (firstUncommittedSlot nd) (electionTerm nd) x' \<rangle>\<leadsto> \<or> x' = x"
          by (auto simp add: isMessage'_def isMessage_def isMessageFrom'_def isMessageFrom_def PublishRequest')
        with fresh_request show "x' = x" by simp
      qed
      with True show ?thesis by simp
    qed
  qed

  have isCommitted_eq: "isCommitted' = isCommitted"
    by (intro ext, simp add: isCommitted_def isCommitted'_def message_simps)

  have committedTo_eq: "committed\<^sub><' = committed\<^sub><"
    by (intro ext, simp add: committedTo_def committedTo'_def isCommitted_eq)

  have v\<^sub>c_eq: "\<And>i. isCommitted i \<Longrightarrow> v\<^sub>c' i = v\<^sub>c i"
  proof -
    fix i assume i: "isCommitted i"
    define t where "t \<equiv> SOME t. \<langle> ApplyCommit i t \<rangle>\<leadsto>"
    have t: "\<langle> ApplyCommit i t \<rangle>\<leadsto>"
    proof -
      from i obtain t where t: "\<langle> ApplyCommit i t \<rangle>\<leadsto>" by (auto simp add: isCommitted_def)
      thus ?thesis by (unfold t_def, intro someI)
    qed
    from ApplyCommit_PublishRequest [OF this] fresh_request
    have ne: "(i, t) \<noteq> (firstUncommittedSlot nd, electionTerm nd)" by (intro notI, simp)

    have "v\<^sub>c' i = v' i t" by (simp add: v\<^sub>c'_def t_def message_simps)
    also from ne have "... = v i t" by (auto simp add: v_eq)
    also have "... = v\<^sub>c i" by (simp add: v\<^sub>c_def t_def)
    finally show "?thesis i" by simp
  qed

  have era\<^sub>i_eq: "\<And>i. committed\<^sub>< i \<Longrightarrow> era\<^sub>i' i = era\<^sub>i i"
  proof -
    fix i
    assume i: "committed\<^sub>< i"
    with v\<^sub>c_eq have "{j. j < i \<and> isReconfiguration (v\<^sub>c' j)} = {j. j < i \<and> isReconfiguration (v\<^sub>c j)}"
      by (auto simp add: committedTo_def)
    thus "?thesis i" by (simp add: era\<^sub>i'_def era\<^sub>i_def)
  qed

  have reconfig_eq: "\<And>e. reconfig' e = reconfig e"
  proof -
    fix e
    have "\<And>i. (isCommitted' i \<and> isReconfiguration (v\<^sub>c' i) \<and> era\<^sub>i' i = e)
            = (isCommitted i \<and> isReconfiguration (v\<^sub>c  i) \<and> era\<^sub>i  i = e)"
      using era\<^sub>i_eq isCommitted_committedTo v\<^sub>c_eq isCommitted_eq by auto
    thus "?thesis e" by (simp add: reconfig'_def reconfig_def)
  qed

  have Q_eq: "\<And> i. committed\<^sub>< i \<Longrightarrow> Q' (era\<^sub>i i) = Q (era\<^sub>i i)"
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
        proof (unfold nextEra, simp add: Q_def Q'_def reconfig_eq,
            intro cong [OF refl, where f = getConf] v\<^sub>c_eq reconfig_isCommitted)
          show "era\<^sub>i i < era\<^sub>i (Suc i)"
            by (simp add: less_Era_def nextEra)
          from Suc.prems show "committed\<^sub>< (Suc i)" .
        qed
      qed
    qed
  qed

  have nd': "nd' = nd \<lparr> applyRequested := True \<rparr>" by (simp add: nd' result)

  have firstUncommittedSlot: "\<And>n. firstUncommittedSlot (nodeState' n) = firstUncommittedSlot (nodeState n)"
    by (unfold nodeState'_def, auto simp add: nd' nd_def)

  have era_firstUncommittedSlot: "\<And>n. era\<^sub>i' (firstUncommittedSlot (nodeState n)) = era\<^sub>i (firstUncommittedSlot (nodeState n))"
    by (intro era\<^sub>i_eq committedToLocalCheckpoint)

  show ?thesis
  proof (intro zenImplI)
    show "zen messages'"
    proof (unfold messages', intro send_PublishRequest allI impI notI ballI)
      from PublishRequest_electionTerm_applyRequested True
      show "\<And>x. n\<^sub>0 \<midarrow>\<langle> PublishRequest (firstUncommittedSlot nd) (electionTerm nd) x \<rangle>\<leadsto> \<Longrightarrow> False"
        by (auto simp add: isMessageFrom_def isMessageFromTo_def nd_def)

      from committedToLocalCheckpoint [where n = n\<^sub>0]
      show "\<And>i. i < firstUncommittedSlot nd \<Longrightarrow> \<exists>t. \<langle> ApplyCommit i t \<rangle>\<leadsto>"
        by (auto simp add: isMessage_def isMessageFrom_def isMessageFromTo_def nd_def committedTo_def isCommitted_def)

      from electionWon_era True
      show era_eq: "era\<^sub>t (electionTerm nd) = era\<^sub>i (firstUncommittedSlot nd)" by (simp add: nd_def)

      from True electionWon_isQuorum
      have "isQuorum nd (electionVotes nd)"
        by (simp add: nd_def)
      with isQuorum_firstUncommittedSlot era_eq
      show "electionVotes nd \<in> Q (era\<^sub>t (electionTerm nd))"
        by (auto simp add: nd_def)

      from electionVotes
      show "\<And>s. s \<in> electionVotes nd \<Longrightarrow> \<exists>i\<le>firstUncommittedSlot nd. \<exists>a. s \<midarrow>\<langle> JoinRequest i (electionTerm nd) a \<rangle>\<rightarrow> (OneNode n\<^sub>0)"
        by (auto simp add: nd_def)

      assume nonempty: "prevAccepted (firstUncommittedSlot nd) (electionTerm nd) (electionVotes nd) \<noteq> {}" (is "?T \<noteq> {}")

      define t' where "t' = maxTerm ?T"
      have t'_mem: "t' \<in> ?T"
        by (unfold t'_def, intro maxTerm_mem finite_prevAccepted nonempty)

      have t'_max: "\<And>t''. t'' \<in> ?T \<Longrightarrow> t'' \<le> t'"
        by (unfold t'_def, intro maxTerm_max finite_prevAccepted)

      from t'_mem obtain s x' where s_vote: "s \<in> electionVotes nd"
        and s_send: "s \<midarrow>\<langle> JoinRequest (firstUncommittedSlot nd) (electionTerm nd) (PublishResponseSent t' x') \<rangle>\<leadsto>"
        by (auto simp add: prevAccepted_def)

      obtain t where electionValue: "electionValue nd = PublishResponseSent t x"
      proof (cases "electionValue nd")
        case NoPublishResponseSent
        with s_vote
        have "electionValue (nodeState n\<^sub>0) = NoPublishResponseSent" "s \<in> electionVotes (nodeState n\<^sub>0)"
          by (simp_all add: nd_def)
        from electionValue_None [OF this]
        show ?thesis
        proof (elim disjE exE conjE)
          assume "s \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n\<^sub>0)) (electionTerm (nodeState n\<^sub>0)) NoPublishResponseSent \<rangle>\<rightarrow> (OneNode n\<^sub>0)"
          hence "PublishResponseSent t' x' = NoPublishResponseSent"
            by (intro JoinRequest_value_function [OF s_send], auto simp add: nd_def isMessageFrom_def)
          thus ?thesis by simp
        next
          fix i' a'
          assume "s \<midarrow>\<langle> JoinRequest i' (electionTerm (nodeState n\<^sub>0)) a' \<rangle>\<rightarrow> (OneNode n\<^sub>0)"
          hence "firstUncommittedSlot nd = i'"
            by (intro JoinRequest_slot_function [OF s_send], auto simp add: nd_def isMessageFrom_def)
          moreover assume "i' < firstUncommittedSlot (nodeState n\<^sub>0)"
          ultimately show ?thesis by (simp add: nd_def)
        qed
      next
        case (PublishResponseSent t' x')
        from this x [OF this] show ?thesis
          by (intro that, simp)
      qed

      show "x = v (firstUncommittedSlot nd) t'"
      proof (intro PublishRequest_function)
        define P where "\<And>x. P x \<equiv> \<langle> PublishRequest (firstUncommittedSlot nd) t' x \<rangle>\<leadsto>"
        have v_The: "v (firstUncommittedSlot nd) t' = (THE x. P x)"
          by (simp add: P_def v_def)

        have "P (v (firstUncommittedSlot nd) t')"
        proof (unfold v_The, intro theI [of P], unfold P_def)
          from JoinRequest_Some_PublishRequest [OF s_send]
          show a1: "\<langle> PublishRequest (firstUncommittedSlot nd) t' x' \<rangle>\<leadsto>" .
          fix x''
          assume a2: "\<langle> PublishRequest (firstUncommittedSlot nd) t' x'' \<rangle>\<leadsto>"
          show "x'' = x'"
            by (intro PublishRequest_function [OF a2 a1])
        qed

        thus "\<langle> PublishRequest (firstUncommittedSlot nd) t' (v (firstUncommittedSlot nd) t') \<rangle>\<leadsto>"
          by (simp add: P_def)

        from electionValue_Some [where n = n\<^sub>0] electionValue
        obtain s' where s'_vote: "s' \<in> electionVotes nd"
          and s'_send: "s' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot nd) (electionTerm nd) (PublishResponseSent t x) \<rangle>\<rightarrow> (OneNode n\<^sub>0)"
          by (auto simp add: nd_def)

        from s'_vote s'_send have "t \<le> t'"
          by (intro t'_max, auto simp add: prevAccepted_def isMessageFrom_def)
        moreover have "t' \<le> t"
        proof (intro electionValue_Some_max [where n = n\<^sub>0])
          from electionValue
          show "electionValue (nodeState n\<^sub>0) = PublishResponseSent t x"
            by (simp add: nd_def)

          from s_vote show "s \<in> electionVotes (nodeState n\<^sub>0)" by (simp add: nd_def)

          from electionVotes [OF this]
          obtain i' a' where s1: "s \<midarrow>\<langle> JoinRequest i' (electionTerm nd) a' \<rangle>\<rightarrow> (OneNode n\<^sub>0)"
            by (auto simp add: isMessageFromTo_def nd_def)

          from s_send obtain d where
            s2: "s \<midarrow>\<langle> JoinRequest (firstUncommittedSlot nd) (electionTerm nd) (PublishResponseSent t' x') \<rangle>\<rightarrow> d" by (auto simp add: isMessageFrom_def)

          have "d = OneNode n\<^sub>0"
            by (intro JoinRequest_unique_destination [OF s2 s1])

          with s2 show "s \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n\<^sub>0)) (electionTerm (nodeState n\<^sub>0)) (PublishResponseSent t' x') \<rangle>\<rightarrow> (OneNode n\<^sub>0)"
            by (auto simp add: isMessageFromTo_def nd_def)
        qed
        ultimately have t_eq: "t' = t" by simp

        show "\<langle> PublishRequest (firstUncommittedSlot nd) t' x \<rangle>\<leadsto>"
        proof (intro JoinRequest_Some_PublishRequest, unfold t_eq)
          from s'_send show "s' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot nd) (electionTerm nd) (PublishResponseSent t x) \<rangle>\<leadsto>"
            by (auto simp add: isMessageFrom_def)
        qed
      qed
    qed

    from nodesIdentified nd'
    show "\<And>n. currentNode (nodeState' n) = n"
      by (unfold nodeState'_def, auto simp add: nd_def)

    from committedToLocalCheckpoint nd'
    show "\<And>n. committed\<^sub><' (firstUncommittedSlot (nodeState' n))"
      by (unfold nodeState'_def, auto simp add: nd_def committedTo_eq)

    from era\<^sub>i_eq committedToLocalCheckpoint nd' era_eq eraMatchesLocalCheckpoint
    show "\<And>n. currentEra (nodeState' n) = era\<^sub>i' (firstUncommittedSlot (nodeState' n))"
      by (unfold nodeState'_def, auto simp add: nd_def nd')

  next
    fix n
    have "{q. isQuorum (nodeState' n) q} = {q. isQuorum (nodeState n) q}"
      by (unfold nodeState'_def, simp add: isQuorum_def nd' nd_def)
    also note isQuorum_firstUncommittedSlot
    also have "Q (era\<^sub>i (firstUncommittedSlot (nodeState n))) = Q' (era\<^sub>i' (firstUncommittedSlot (nodeState' n)))"
      by (unfold firstUncommittedSlot era_firstUncommittedSlot, intro sym [OF Q_eq] committedToLocalCheckpoint)
    finally show "{q. isQuorum (nodeState' n) q} = Q' (era\<^sub>i' (firstUncommittedSlot (nodeState' n)))".

    from nothingAcceptedInLaterSlots
    show "\<And>i t. firstUncommittedSlot (nodeState' n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>'"
      by (cases "n = n\<^sub>0", unfold nodeState'_def message_simps, auto simp add: nd' nd_def)

  next
    from lastAccepted_None
    show "\<And>n t. lastAccepted (nodeState' n) = NoPublishResponseSent \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t \<rangle>\<leadsto>'"
      by (unfold nodeState'_def message_simps, auto simp add: nd' nd_def)

    from lastAccepted_Some_term
    show "\<And>n t' x'. lastAccepted (nodeState' n) = PublishResponseSent t' x' \<Longrightarrow> t' \<le> currentTerm (nodeState' n)"
      by (unfold nodeState'_def message_simps, auto simp add: nd' nd_def)

    from lastAccepted_Some_sent
    show "\<And>n t' x'. lastAccepted (nodeState' n) = PublishResponseSent t' x' \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t' \<rangle>\<leadsto>'"
      by (unfold nodeState'_def message_simps, auto simp add: nd' nd_def)

    from lastAccepted_Some_value nodeState'_def isMessage'_def isMessageFrom'_def PublishRequest' isMessage_def isMessageFrom_def nd' nd_def
    show "\<And>n t' x'. lastAccepted (nodeState' n) = PublishResponseSent t' x' \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t' x' \<rangle>\<leadsto>'"
      by (auto, meson, meson)      

  next
    fix n
    from lastAccepted_Some_max
    show "\<And>t' x' t''. lastAccepted (nodeState' n) = PublishResponseSent t' x' \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t'' \<rangle>\<leadsto>' \<Longrightarrow> t'' \<le> t'"
      by (unfold nodeState'_def, cases "n = n\<^sub>0", auto simp add: nd' message_simps nd_def)

  next
    from JoinRequest_currentTerm
    show "\<And>n i t a. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>' \<Longrightarrow> t \<le> currentTerm (nodeState' n)"
      by (unfold nodeState'_def message_simps, auto simp add: nd' nd_def)

    from JoinRequest_slot_function
    show "\<And>n i i' t a a'. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>' \<Longrightarrow> n \<midarrow>\<langle> JoinRequest i' t a' \<rangle>\<leadsto>' \<Longrightarrow> i = i'"
      by (unfold nodeState'_def message_simps, auto simp add: nd' nd_def)

    from PublishRequest_electionTerm
    show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t x \<rangle>\<leadsto>' \<Longrightarrow> t \<le> electionTerm (nodeState' n)"
      by (unfold nodeState'_def isMessageFrom'_def PublishRequest', auto simp add: nd' nd_def isMessageFrom_def, blast, blast)

    from PublishRequest_electionTerm_applyRequested
    show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t x \<rangle>\<leadsto>' \<Longrightarrow> \<not> applyRequested (nodeState' n) \<Longrightarrow> t < electionTerm (nodeState' n)"
      by (unfold nodeState'_def isMessageFrom'_def PublishRequest', auto simp add: nd' nd_def isMessageFrom_def, blast)

    from applyRequested_electionWon won
    show "\<And>n. applyRequested (nodeState' n) \<Longrightarrow> electionWon (nodeState' n)"
      by (unfold nodeState'_def, auto simp add: nd_def nd')

    from electionVotes
    show "\<And>n n'. n' \<in> electionVotes (nodeState' n) \<Longrightarrow> promised' (firstUncommittedSlot (nodeState' n)) n' n (electionTerm (nodeState' n))"
      by (unfold nodeState'_def, auto simp add: nd_def nd' promised'_def message_simps)

    from electionWon_isQuorum
    show "\<And>n. electionWon (nodeState' n) \<Longrightarrow> isQuorum (nodeState' n) (electionVotes (nodeState' n))"
      by (unfold nodeState'_def, auto simp add: nd_def nd' isQuorum_def)

    from electionWon_era era_firstUncommittedSlot
    show "\<And>n. electionWon (nodeState' n) \<Longrightarrow> era\<^sub>t (electionTerm (nodeState' n)) = era\<^sub>i' (firstUncommittedSlot (nodeState' n))"
      by (unfold nodeState'_def, auto simp add: nd_def nd')

    from electionValue_None
    show "\<And>n n'. electionValue (nodeState' n) = NoPublishResponseSent \<Longrightarrow> n' \<in> electionVotes (nodeState' n)
      \<Longrightarrow> (n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState' n)) (electionTerm (nodeState' n)) NoPublishResponseSent \<rangle>\<rightarrow>' (OneNode n))
        \<or> (\<exists>i<firstUncommittedSlot (nodeState' n). \<exists>a. (n' \<midarrow>\<langle> JoinRequest i (electionTerm (nodeState' n)) a \<rangle>\<rightarrow>' (OneNode n)))"
      by (unfold nodeState'_def, auto simp add: nd' nd_def message_simps, blast, blast)

    from electionValue_Some
    show "\<And>n t' x'. electionValue (nodeState' n) = PublishResponseSent t' x'
      \<Longrightarrow> \<exists>n'\<in>electionVotes (nodeState' n). n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState' n)) (electionTerm (nodeState' n)) (PublishResponseSent t' x') \<rangle>\<rightarrow>' (OneNode n)"
      by (unfold nodeState'_def, auto simp add: nd' nd_def message_simps)

    fix n
    from electionValue_Some_max
    show "\<And>t' x' n'' t'' x''. electionValue (nodeState' n) = PublishResponseSent t' x'
      \<Longrightarrow> n'' \<in> electionVotes (nodeState' n) \<Longrightarrow> n'' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState' n)) (electionTerm (nodeState' n)) (PublishResponseSent t'' x'') \<rangle>\<rightarrow>' (OneNode n)
      \<Longrightarrow> t'' \<le> t'"
      by (unfold nodeState'_def, cases "n = n\<^sub>0", auto simp add: nd' nd_def message_simps)
  qed
qed


lemma (in zenStep) handleStartJoin_invariants:
  fixes t
  defines "result \<equiv> handleStartJoin t nd"
  assumes nd': "nd' = fst result"
  assumes messages': "messages' = send response result"
  shows "zenImpl messages' nodeState'"
proof (cases "currentTerm nd < t \<and> era\<^sub>t t = currentEra nd")
  case False
  hence result: "result = (nd, None)" by (simp add: result_def handleStartJoin_def)
  have "messages' = messages" by (auto simp add: messages' result)
  moreover
  have "nodeState' = nodeState" by (intro ext, unfold nodeState'_def, simp add: nd' result nd_def)
  moreover note zenImpl_axioms
  ultimately show ?thesis by simp
next
  case True
  hence new_term: "currentTerm nd < t" 
    and era_eq: "era\<^sub>t t = currentEra nd" by simp_all

  have result: "result = (nd \<lparr>currentTerm := t\<rparr>, Some (JoinRequest (firstUncommittedSlot nd) t (lastAccepted nd)))"
    by (simp add: result_def handleStartJoin_def True)

  have messages': "messages' = insert \<lparr>sender = n\<^sub>0, destination = OneNode (sender message),
                                               payload = JoinRequest (firstUncommittedSlot nd) t (lastAccepted nd)\<rparr> messages"
    by (simp add: messages' result response_def)

  from result
  have property_simps[simp]:
    "\<And>n. currentNode (nodeState' n) = currentNode (nodeState n)"
    "\<And>n. firstUncommittedSlot (nodeState' n) = firstUncommittedSlot (nodeState n)"
    "\<And>n. currentEra (nodeState' n) = currentEra (nodeState n)"
    "\<And>n q. isQuorum (nodeState' n) q = isQuorum (nodeState n) q"
    "\<And>n. lastAccepted (nodeState' n) = lastAccepted (nodeState n)"
    "\<And>n. electionTerm (nodeState' n) = electionTerm (nodeState n)"
    "\<And>n. electionWon (nodeState' n) = electionWon (nodeState n)"
    "\<And>n. electionVotes (nodeState' n) = electionVotes (nodeState n)"
    "\<And>n. electionValue (nodeState' n) = electionValue (nodeState n)"
    "\<And>n. applyRequested (nodeState' n) = applyRequested (nodeState n)"
    by (unfold nodeState'_def, auto simp add: nd_def isQuorum_def nd')

  have message_simps[simp]:
    "\<And>s d i t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)"
    "\<And>s d i t x. (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>s d i t. (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<rightarrow> d)"
    "\<And>d i t. (\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = (\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)"
    "\<And>d i t x. (\<langle> PublishRequest i t x \<rangle>\<rightarrow>' d) = (\<langle> PublishRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>d i t. (\<langle> PublishResponse i t \<rangle>\<rightarrow>' d) = (\<langle> PublishResponse i t \<rangle>\<rightarrow> d)"
    "\<And>s i t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<leadsto>') = (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<leadsto>)"
    "\<And>s i t x. (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>') = (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>)"
    "\<And>s i t. (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>') = (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>)"
    "\<And>i t. (\<langle> ApplyCommit i t \<rangle>\<leadsto>') = (\<langle> ApplyCommit i t \<rangle>\<leadsto>)"
    "\<And>i t x. (\<langle> PublishRequest i t x \<rangle>\<leadsto>') = (\<langle> PublishRequest i t x \<rangle>\<leadsto>)"
    "\<And>i t. (\<langle> PublishResponse i t \<rangle>\<leadsto>') = (\<langle> PublishResponse i t \<rangle>\<leadsto>)"
    by (unfold isMessageFromTo'_def isMessageTo'_def isMessageFrom'_def isMessage'_def,
        auto simp add: messages' isMessageFromTo_def isMessageTo_def isMessageFrom_def isMessage_def)

  have JoinRequest': "\<And>s d i t' a. (s \<midarrow>\<langle> JoinRequest i t' a \<rangle>\<rightarrow>' d) =
    ((s \<midarrow>\<langle> JoinRequest i t' a \<rangle>\<rightarrow> d)
      \<or> (s, i, t', a, d) = (n\<^sub>0, firstUncommittedSlot nd, t, lastAccepted nd, OneNode (sender message)))"
    by (unfold isMessageFromTo'_def isMessageFromTo_def, auto simp add: messages')

  have v_eq[simp]: "v' = v" by (intro ext, auto simp add: v'_def v_def)
  have v\<^sub>c_eq[simp]: "v\<^sub>c' = v\<^sub>c" by (intro ext, auto simp add: v\<^sub>c'_def v\<^sub>c_def)
  have isCommitted_eq[simp]: "isCommitted' = isCommitted" by (intro ext, auto simp add: isCommitted'_def isCommitted_def)
  have committedTo_eq[simp]: "committed\<^sub><' = committed\<^sub><" by (intro ext, auto simp add: committedTo'_def committedTo_def)
  have era\<^sub>i_eq[simp]: "era\<^sub>i' = era\<^sub>i" by (intro ext, auto simp add: era\<^sub>i'_def era\<^sub>i_def)
  have reconfig_eq[simp]: "reconfig' = reconfig" by (intro ext, auto simp add: reconfig'_def reconfig_def)
  have Q_eq[simp]: "Q' = Q" using reconfig_eq v\<^sub>c_eq Q'_def Q_def by blast

  show ?thesis
  proof (intro zenImplI)
    show "zen messages'"
    proof (cases "lastAccepted nd")
      case NoPublishResponseSent
      hence messages': "messages' = insert \<lparr>sender = n\<^sub>0, destination = OneNode (sender message),
                                               payload = JoinRequest (firstUncommittedSlot nd) t NoPublishResponseSent\<rparr> messages"
        by (simp add: messages')

      show ?thesis
      proof (unfold messages', intro send_JoinRequest_None)
        from committedToLocalCheckpoint
        show "\<forall>i<firstUncommittedSlot nd. \<exists>t. \<langle> ApplyCommit i t \<rangle>\<leadsto>"
          by (simp add: nd_def committedTo_def isCommitted_def)

        from True eraMatchesLocalCheckpoint
        show "era\<^sub>t t = era\<^sub>i (firstUncommittedSlot nd)"
          by (simp add: nd_def)

        show "\<forall>i\<ge>firstUncommittedSlot nd. \<forall>t. \<not> n\<^sub>0 \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>"
        proof (intro allI impI)
          fix i t
          assume le: "firstUncommittedSlot nd \<le> i"
          show "\<not> n\<^sub>0 \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>"
          proof (cases "i \<le> firstUncommittedSlot nd")
            case False
            with le have lt: "firstUncommittedSlot nd < i" by simp
            with nothingAcceptedInLaterSlots show ?thesis by (simp add: nd_def nodesIdentified)
          next
            case True with le have eq: "i = firstUncommittedSlot nd" by simp
            from lastAccepted_None [of n\<^sub>0] NoPublishResponseSent show ?thesis
              by (simp add: nd_def eq nodesIdentified)
          qed
        qed

        from JoinRequest_currentTerm new_term
        show "\<forall>i a. \<not> n\<^sub>0 \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>"
          using nd_def nodesIdentified by fastforce
      qed

    next
      case (PublishResponseSent t' x')
      hence messages': "messages' = insert \<lparr>sender = n\<^sub>0, destination = OneNode (sender message),
                                               payload = JoinRequest (firstUncommittedSlot nd) t (PublishResponseSent t' x')\<rparr> messages"
        by (simp add: messages')

      show ?thesis
      proof (unfold messages', intro send_JoinRequest_Some)
        from committedToLocalCheckpoint
        show "\<forall>i<firstUncommittedSlot nd. \<exists>t. \<langle> ApplyCommit i t \<rangle>\<leadsto>"
          by (simp add: nd_def committedTo_def isCommitted_def)

        from nothingAcceptedInLaterSlots
        show "\<forall>i>firstUncommittedSlot nd. \<forall>t. \<not> n\<^sub>0 \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>"
          by (simp add: nd_def nodesIdentified)

        from JoinRequest_currentTerm new_term
        show "\<forall>i a. \<not> n\<^sub>0 \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>"
          using nd_def nodesIdentified by fastforce

        from lastAccepted_Some_sent [of n\<^sub>0] lastAccepted_Some_value [of n\<^sub>0] lastAccepted_Some_max [of n\<^sub>0] PublishResponseSent
        show "n\<^sub>0 \<midarrow>\<langle> PublishResponse (firstUncommittedSlot nd) t' \<rangle>\<leadsto>"
          "\<langle> PublishRequest (firstUncommittedSlot nd) t' x' \<rangle>\<leadsto>"
          "\<forall>t''. n\<^sub>0 \<midarrow>\<langle> PublishResponse (firstUncommittedSlot nd) t'' \<rangle>\<leadsto> \<longrightarrow> t'' \<le> t'"
          by (simp_all add: nd_def)

        from lastAccepted_Some_term [of n\<^sub>0] PublishResponseSent new_term
        show "t' < t" by (auto simp add: nd_def, fastforce)

        from True eraMatchesLocalCheckpoint
        show "era\<^sub>t t = era\<^sub>i (firstUncommittedSlot nd)"
          by (simp add: nd_def)
      qed
    qed

    from nodesIdentified show "\<And>n. currentNode (nodeState' n) = n" by simp
    from committedToLocalCheckpoint show "\<And>n. committed\<^sub><' (firstUncommittedSlot (nodeState' n))" by simp
    from eraMatchesLocalCheckpoint show "\<And>n. currentEra (nodeState' n) = era\<^sub>i' (firstUncommittedSlot (nodeState' n))" by simp
    from nothingAcceptedInLaterSlots show "\<And>i n t. firstUncommittedSlot (nodeState' n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>'" by simp
    from PublishRequest_electionTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t x \<rangle>\<leadsto>' \<Longrightarrow> t \<le> electionTerm (nodeState' n)" by simp
    from PublishRequest_electionTerm_applyRequested show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t x \<rangle>\<leadsto>' \<Longrightarrow> \<not> applyRequested (nodeState' n) \<Longrightarrow> t < electionTerm (nodeState' n)" by simp
    from applyRequested_electionWon show "\<And>n. applyRequested (nodeState' n) \<Longrightarrow> electionWon (nodeState' n)" by simp
    from isQuorum_firstUncommittedSlot show "\<And>n. {q. isQuorum (nodeState' n) q} = Q' (era\<^sub>i' (firstUncommittedSlot (nodeState' n)))" by simp
    from electionWon_isQuorum show "\<And>n. electionWon (nodeState' n) \<Longrightarrow> isQuorum (nodeState' n) (electionVotes (nodeState' n))" by simp
    from lastAccepted_None show "\<And>n t. lastAccepted (nodeState' n) = NoPublishResponseSent \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t \<rangle>\<leadsto>'" by simp
    from lastAccepted_Some_sent show "\<And>n t' x'. lastAccepted (nodeState' n) = PublishResponseSent t' x' \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t' \<rangle>\<leadsto>'" by simp
    from lastAccepted_Some_value show "\<And>n t' x'. lastAccepted (nodeState' n) = PublishResponseSent t' x' \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t' x' \<rangle>\<leadsto>'" by simp
    from lastAccepted_Some_max show "\<And>n t' x' t''. lastAccepted (nodeState' n) = PublishResponseSent t' x' \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t'' \<rangle>\<leadsto>' \<Longrightarrow> t'' \<le> t'" by simp
    from electionWon_era show "\<And>n. electionWon (nodeState' n) \<Longrightarrow> era\<^sub>t (electionTerm (nodeState' n)) = era\<^sub>i' (firstUncommittedSlot (nodeState' n))" by simp

    from electionVotes show "\<And>n n'. n' \<in> electionVotes (nodeState' n) \<Longrightarrow> promised' (firstUncommittedSlot (nodeState' n)) n' n (electionTerm (nodeState' n))"
      by (auto simp add: promised'_def JoinRequest', blast)

    from electionValue_None
    show "\<And>n n'. electionValue (nodeState' n) = NoPublishResponseSent \<Longrightarrow>
            n' \<in> electionVotes (nodeState' n) \<Longrightarrow>
            (n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState' n)) (electionTerm (nodeState' n)) NoPublishResponseSent \<rangle>\<rightarrow>' (OneNode n))
         \<or> (\<exists>i<firstUncommittedSlot (nodeState' n). \<exists>a. (n' \<midarrow>\<langle> JoinRequest i (electionTerm (nodeState' n)) a \<rangle>\<rightarrow>' (OneNode n)))"
      by (auto simp add: JoinRequest')

    from electionValue_Some JoinRequest' property_simps message_simps
    show "\<And>n t' x'. electionValue (nodeState' n) = PublishResponseSent t' x' \<Longrightarrow> \<exists>n'\<in>electionVotes (nodeState' n). n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState' n)) (electionTerm (nodeState' n)) (PublishResponseSent t' x') \<rangle>\<rightarrow>' (OneNode n)"
      by metis

  next
    fix n t' x'
    assume lastAccepted: "lastAccepted (nodeState' n) = PublishResponseSent t' x'"
    show "t' \<le> currentTerm (nodeState' n)"
    proof (cases "n = n\<^sub>0")
      case False
      with lastAccepted_Some_term lastAccepted show ?thesis by (unfold nodeState'_def, simp)
    next
      case True
      with lastAccepted_Some_term lastAccepted
      have "t' \<le> currentTerm (nodeState n\<^sub>0)" by simp
      also from new_term have "... < currentTerm (nodeState' n)"
        by (unfold nodeState'_def, simp add: True nd' result nd_def)
      finally show ?thesis by simp
    qed

  next
    fix n i t' a
    assume sent: "n \<midarrow>\<langle> JoinRequest i t' a \<rangle>\<leadsto>'"
    show "t' \<le> currentTerm (nodeState' n)"
    proof (cases "n = n\<^sub>0")
      case False
      with JoinRequest_currentTerm sent
      show ?thesis by (auto simp add: nodeState'_def isMessageFrom_def isMessageFrom'_def JoinRequest')
    next
      case True
      from sent show ?thesis
      proof (unfold isMessageFrom'_def JoinRequest' True, elim exE disjE)
        fix d
        assume "n\<^sub>0 \<midarrow>\<langle> JoinRequest i t' a \<rangle>\<rightarrow> d"
        hence "t' \<le> currentTerm (nodeState n\<^sub>0)"
          using JoinRequest_currentTerm isMessageFrom_def by blast     
        also from new_term have "... < currentTerm (nodeState' n\<^sub>0)"
          by (unfold nodeState'_def, simp add: True nd' result nd_def)
        finally show "t' \<le> ..." by simp
      next
        fix d assume "(n\<^sub>0, i, t', a, d) = (n\<^sub>0, firstUncommittedSlot nd, t, lastAccepted nd, OneNode (sender message))"
        thus "t' \<le> currentTerm (nodeState' n\<^sub>0)"
          by (unfold nodeState'_def, simp add: nd' result)
      qed
    qed

  next
    fix n i i' t' a a'
    assume "n \<midarrow>\<langle> JoinRequest i t' a \<rangle>\<leadsto>'"
    then obtain d where d: "(n \<midarrow>\<langle> JoinRequest i t' a \<rangle>\<rightarrow> d) \<or> (n, i, t') = (n\<^sub>0, firstUncommittedSlot nd, t)"
      by (auto simp add: JoinRequest' isMessageFrom'_def)
    assume "n \<midarrow>\<langle> JoinRequest i' t' a' \<rangle>\<leadsto>'"
    then obtain d' where d': "(n \<midarrow>\<langle> JoinRequest i' t' a' \<rangle>\<rightarrow> d') \<or> (n, i', t') = (n\<^sub>0, firstUncommittedSlot nd, t)"
      by (auto simp add: JoinRequest' isMessageFrom'_def)

    from d d'
    show "i = i'"
    proof (elim disjE)
      show "n \<midarrow>\<langle> JoinRequest i t' a \<rangle>\<rightarrow> d \<Longrightarrow> n \<midarrow>\<langle> JoinRequest i' t' a' \<rangle>\<rightarrow> d' \<Longrightarrow> i = i'"
        by (intro JoinRequest_slot_function, auto simp add: isMessageFrom_def)

      show "(n, i, t') = (n\<^sub>0, firstUncommittedSlot nd, t)
              \<Longrightarrow> (n, i', t') = (n\<^sub>0, firstUncommittedSlot nd, t)
              \<Longrightarrow> i = i'" by simp

    next
      assume "n \<midarrow>\<langle> JoinRequest i t' a \<rangle>\<rightarrow> d" "(n, i', t') = (n\<^sub>0, firstUncommittedSlot nd, t)"
      hence "n\<^sub>0 \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>" by (auto simp add: isMessageFrom_def)
      from JoinRequest_currentTerm [OF this] new_term
      show ?thesis by (simp add: nd_def)
    next
      assume "n \<midarrow>\<langle> JoinRequest i' t' a' \<rangle>\<rightarrow> d'" "(n, i, t') = (n\<^sub>0, firstUncommittedSlot nd, t)"
      hence "n\<^sub>0 \<midarrow>\<langle> JoinRequest i' t a' \<rangle>\<leadsto>" by (auto simp add: isMessageFrom_def)
      from JoinRequest_currentTerm [OF this] new_term
      show ?thesis by (simp add: nd_def)
    qed

  next
    fix n t' x'
    assume "electionValue (nodeState' n) = PublishResponseSent t' x'"
    hence a: "electionValue (nodeState n) = PublishResponseSent t' x'" by simp
    from electionValue_Some [OF a]
    obtain n' where n': "n' \<in> electionVotes (nodeState n)"
      "n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (electionTerm (nodeState n)) (PublishResponseSent t' x') \<rangle>\<rightarrow> (OneNode n)" by auto

    fix n'' t'' x''
    assume "n'' \<in> electionVotes (nodeState' n)" hence n'': "n'' \<in> electionVotes (nodeState n)" by simp
    assume n''_msg: "n'' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState' n)) (electionTerm (nodeState' n)) (PublishResponseSent t'' x'') \<rangle>\<rightarrow>' (OneNode n)"

    from n''_msg have "(n'' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (electionTerm (nodeState n)) (PublishResponseSent t'' x'') \<rangle>\<rightarrow> (OneNode n))
              \<or> (n'', firstUncommittedSlot (nodeState n), electionTerm (nodeState n), PublishResponseSent t'' x'', OneNode n) = 
                (n\<^sub>0, firstUncommittedSlot nd, t, lastAccepted nd, OneNode (sender message))"
      (is "?D1 \<or> ?D2")
      by (simp add: JoinRequest')

    thus "t'' \<le> t'"
    proof (elim disjE)
      assume ?D1
      with electionValue_Some_max a n'' show ?thesis by blast
    next
      assume eq: "?D2"
      from n'' eq have "n\<^sub>0 \<in> electionVotes (nodeState (sender message))" by simp
      from electionVotes [OF this] eq
      obtain i a where a: "n\<^sub>0 \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>"
        by (auto simp add: isMessageFrom_def)
      from JoinRequest_currentTerm [OF this] new_term
      show ?thesis by (simp add: nd_def)
    qed
  qed
qed

lemma (in zenStep) ensureElectionTerm_invariants:
  assumes t: "electionTerm nd \<le> t"
  assumes nd': "nd' = ensureElectionTerm t nd"
  assumes messages': "messages' = messages"
  shows "zenImpl messages' nodeState'"
proof (cases "electionTerm nd = t")
  case True
  hence "nodeState' = nodeState"
    by (intro ext, unfold nodeState'_def, auto simp add: nd' ensureElectionTerm_def nd_def)
  with zenImpl_axioms messages' show ?thesis by simp
next
  case False

  have message_simps[simp]:
    "\<And>s p d. (s \<midarrow>\<langle> p \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> p \<rangle>\<rightarrow> d)"
    "\<And>p d. (\<langle> p \<rangle>\<rightarrow>' d) = (\<langle> p \<rangle>\<rightarrow> d)"
    "\<And>s p. (s \<midarrow>\<langle> p \<rangle>\<leadsto>') = (s \<midarrow>\<langle> p \<rangle>\<leadsto>)"
    "\<And>p. (\<langle> p \<rangle>\<leadsto>') = (\<langle> p \<rangle>\<leadsto>)"
    by (unfold isMessageFromTo'_def isMessageTo'_def isMessageFrom'_def isMessage'_def,
        auto simp add: messages' isMessageFromTo_def isMessageTo_def isMessageFrom_def isMessage_def)

  have property_simps[simp]:
    "\<And>n. currentNode (nodeState' n) = currentNode (nodeState n)"
    "\<And>n. firstUncommittedSlot (nodeState' n) = firstUncommittedSlot (nodeState n)"
    "\<And>n. currentEra (nodeState' n) = currentEra (nodeState n)"
    "\<And>n q. isQuorum (nodeState' n) q = isQuorum (nodeState n) q"
    "\<And>n. lastAccepted (nodeState' n) = lastAccepted (nodeState n)"
    "\<And>n. currentTerm (nodeState' n) = currentTerm (nodeState n)"
    "electionTerm (nodeState' n\<^sub>0) = t"
    "electionWon (nodeState' n\<^sub>0) = False"
    "electionVotes (nodeState' n\<^sub>0) = {}"
    "electionValue (nodeState' n\<^sub>0) = NoPublishResponseSent"
    "applyRequested (nodeState' n\<^sub>0) = False"
    using False
    by (unfold nodeState'_def, auto simp add: nd_def isQuorum_def nd' ensureElectionTerm_def)

  have v_eq[simp]: "v' = v" by (intro ext, auto simp add: v'_def v_def)
  have v\<^sub>c_eq[simp]: "v\<^sub>c' = v\<^sub>c" by (intro ext, auto simp add: v\<^sub>c'_def v\<^sub>c_def)
  have isCommitted_eq[simp]: "isCommitted' = isCommitted" by (intro ext, auto simp add: isCommitted'_def isCommitted_def)
  have committedTo_eq[simp]: "committed\<^sub><' = committed\<^sub><" by (intro ext, auto simp add: committedTo'_def committedTo_def)
  have era\<^sub>i_eq[simp]: "era\<^sub>i' = era\<^sub>i" by (intro ext, auto simp add: era\<^sub>i'_def era\<^sub>i_def)
  have reconfig_eq[simp]: "reconfig' = reconfig" by (intro ext, auto simp add: reconfig'_def reconfig_def)
  have Q_eq[simp]: "Q' = Q" using reconfig_eq v\<^sub>c_eq Q'_def Q_def by blast

  show "zenImpl messages' nodeState'"
    apply (intro zenImplI)
                        apply (unfold message_simps property_simps committedTo_eq era\<^sub>i_eq Q_eq)
      (*      using nodesIdentified committedToLocalCheckpoint eraMatchesLocalCheckpoint
              isQuorum_firstUncommittedSlot JoinRequest_slot_function
              nothingAcceptedInLaterSlots JoinRequest_currentTerm *)
  proof -
    from zen_axioms show "zen messages'" by (simp add: messages')
    from nodesIdentified show "\<And>n. currentNode (nodeState n) = n".
    from committedToLocalCheckpoint show "\<And>n. committed\<^sub>< (firstUncommittedSlot (nodeState n))".
    from eraMatchesLocalCheckpoint show "\<And>n. currentEra (nodeState n) = era\<^sub>i (firstUncommittedSlot (nodeState n))".
    from isQuorum_firstUncommittedSlot show "\<And>n. {q. isQuorum (nodeState n) q} = Q (era\<^sub>i (firstUncommittedSlot (nodeState n)))".
    from nothingAcceptedInLaterSlots show "\<And>i n t. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>" .
    from lastAccepted_None show "\<And>n t. lastAccepted (nodeState n) = NoPublishResponseSent \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>" .
    from lastAccepted_Some_term show "\<And>n t' x'. lastAccepted (nodeState n) = PublishResponseSent t' x' \<Longrightarrow> t' \<le> currentTerm (nodeState n)" .
    from lastAccepted_Some_sent show "\<And>n t' x'. lastAccepted (nodeState n) = PublishResponseSent t' x' \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t' \<rangle>\<leadsto>" .
    from lastAccepted_Some_value show "\<And>n t' x'. lastAccepted (nodeState n) = PublishResponseSent t' x' \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t' x' \<rangle>\<leadsto>" .
    from lastAccepted_Some_max show "\<And>n t' x' t''. lastAccepted (nodeState n) = PublishResponseSent t' x' \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t'' \<rangle>\<leadsto> \<Longrightarrow> t'' \<le> t'" .
    from JoinRequest_currentTerm show "\<And>n i t a. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)" .
    from JoinRequest_slot_function show "\<And>n i i' t a a'. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto> \<Longrightarrow> n \<midarrow>\<langle> JoinRequest i' t a' \<rangle>\<leadsto> \<Longrightarrow> i = i'" .

    from applyRequested_electionWon show "\<And>n. applyRequested (nodeState' n) \<Longrightarrow> electionWon (nodeState' n)"
      by (unfold nodeState'_def, auto simp add: nd' ensureElectionTerm_def nd_def)

    from electionVotes False show "\<And>n n'. n' \<in> electionVotes (nodeState' n) \<Longrightarrow> promised' (firstUncommittedSlot (nodeState n)) n' n (electionTerm (nodeState' n))"
      by (unfold nodeState'_def, auto simp add: nd' ensureElectionTerm_def nd_def promised'_def)

    from electionWon_isQuorum show "\<And>n. electionWon (nodeState' n) \<Longrightarrow> isQuorum (nodeState n) (electionVotes (nodeState' n))"
      by (unfold nodeState'_def, auto simp add: nd' ensureElectionTerm_def nd_def)

    from electionWon_era False show "\<And>n. electionWon (nodeState' n) \<Longrightarrow> era\<^sub>t (electionTerm (nodeState' n)) = era\<^sub>i (firstUncommittedSlot (nodeState n))"
      by (unfold nodeState'_def, auto simp add: nd' ensureElectionTerm_def nd_def)

    from electionValue_None False show " \<And>n n'. electionValue (nodeState' n) = NoPublishResponseSent \<Longrightarrow>
            n' \<in> electionVotes (nodeState' n) \<Longrightarrow>
            (n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (electionTerm (nodeState' n)) NoPublishResponseSent \<rangle>\<rightarrow> (OneNode n))
                \<or> (\<exists>i<firstUncommittedSlot (nodeState n). \<exists>a. n' \<midarrow>\<langle> JoinRequest i (electionTerm (nodeState' n)) a \<rangle>\<rightarrow> (OneNode n))"
      by (unfold nodeState'_def, auto simp add: nd' ensureElectionTerm_def nd_def, blast)

    from electionValue_Some show "\<And>n t' x'. electionValue (nodeState' n) = PublishResponseSent t' x'
      \<Longrightarrow> \<exists>n'\<in>electionVotes (nodeState' n). n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (electionTerm (nodeState' n)) (PublishResponseSent t' x') \<rangle>\<rightarrow> (OneNode n)"
      by (unfold nodeState'_def, auto simp add: nd' ensureElectionTerm_def nd_def)

    fix n
    from electionValue_Some_max False show "\<And>t' x' n'' t'' x''. electionValue (nodeState' n) = PublishResponseSent t' x'
      \<Longrightarrow> n'' \<in> electionVotes (nodeState' n)
      \<Longrightarrow> n'' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (electionTerm (nodeState' n)) (PublishResponseSent t'' x'') \<rangle>\<rightarrow> (OneNode n)
      \<Longrightarrow> t'' \<le> t'"
      by (cases "n = n\<^sub>0", unfold nodeState'_def, auto simp add: nd' ensureElectionTerm_def nd_def)

    fix t' x'
    assume sent: "n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t' x' \<rangle>\<leadsto>"

    show "t' \<le> electionTerm (nodeState' n)"
    proof (cases "n = n\<^sub>0")
      case False
      with PublishRequest_electionTerm sent show ?thesis
        by (unfold nodeState'_def, auto)
    next
      case True
      with PublishRequest_electionTerm sent have "t' \<le> electionTerm nd" by (simp add: nd_def)
      also note t
      also have "t = electionTerm (nodeState' n)" by (simp add: True)
      finally show ?thesis .
    qed

    assume not_requested: "\<not> applyRequested (nodeState' n)"
    show "t' < electionTerm (nodeState' n)"
    proof (cases "n = n\<^sub>0")
      case False
      with PublishRequest_electionTerm_applyRequested sent not_requested show ?thesis
        by (unfold nodeState'_def, auto)
    next
      case True
      with PublishRequest_electionTerm sent have "t' \<le> electionTerm nd" by (simp add: nd_def)
      also from t False have "... < t" by simp
      also have "t = electionTerm (nodeState' n)" by (simp add: True)
      finally show ?thesis .
    qed
  qed
qed

lemma (in zenStep) addElectionVote_invariants:
  assumes nd': "nd' = addElectionVote s i a nd"
  assumes messages': "messages' = messages"
  assumes not_won: "\<not> electionWon nd"
  assumes sent: "s \<midarrow>\<langle> JoinRequest i (electionTerm nd) a \<rangle>\<rightarrow> (OneNode n\<^sub>0)"
  assumes era: "era\<^sub>t (electionTerm nd) = currentEra nd"
  assumes slot: "i \<le> firstUncommittedSlot nd"
  shows "zenImpl messages' nodeState'"
proof -
  have message_simps[simp]:
    "\<And>s p d. (s \<midarrow>\<langle> p \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> p \<rangle>\<rightarrow> d)"
    "\<And>p d. (\<langle> p \<rangle>\<rightarrow>' d) = (\<langle> p \<rangle>\<rightarrow> d)"
    "\<And>s p. (s \<midarrow>\<langle> p \<rangle>\<leadsto>') = (s \<midarrow>\<langle> p \<rangle>\<leadsto>)"
    "\<And>p. (\<langle> p \<rangle>\<leadsto>') = (\<langle> p \<rangle>\<leadsto>)"
    by (unfold isMessageFromTo'_def isMessageTo'_def isMessageFrom'_def isMessage'_def,
        auto simp add: messages' isMessageFromTo_def isMessageTo_def isMessageFrom_def isMessage_def)

  have property_simps[simp]:
    "\<And>n. currentNode (nodeState' n) = currentNode (nodeState n)"
    "\<And>n. firstUncommittedSlot (nodeState' n) = firstUncommittedSlot (nodeState n)"
    "\<And>n. currentEra (nodeState' n) = currentEra (nodeState n)"
    "\<And>n q. isQuorum (nodeState' n) q = isQuorum (nodeState n) q"
    "\<And>n. lastAccepted (nodeState' n) = lastAccepted (nodeState n)"
    "\<And>n. currentTerm (nodeState' n) = currentTerm (nodeState n)"
    "\<And>n. electionTerm (nodeState' n) = electionTerm (nodeState n)"
    "\<And>n. applyRequested (nodeState' n) = applyRequested (nodeState n)"
    by (unfold nodeState'_def, auto simp add: nd_def isQuorum_def nd' addElectionVote_def Let_def)

  have v_eq[simp]: "v' = v" by (intro ext, auto simp add: v'_def v_def)
  have v\<^sub>c_eq[simp]: "v\<^sub>c' = v\<^sub>c" by (intro ext, auto simp add: v\<^sub>c'_def v\<^sub>c_def)
  have isCommitted_eq[simp]: "isCommitted' = isCommitted" by (intro ext, auto simp add: isCommitted'_def isCommitted_def)
  have committedTo_eq[simp]: "committed\<^sub><' = committed\<^sub><" by (intro ext, auto simp add: committedTo'_def committedTo_def)
  have era\<^sub>i_eq[simp]: "era\<^sub>i' = era\<^sub>i" by (intro ext, auto simp add: era\<^sub>i'_def era\<^sub>i_def)
  have reconfig_eq[simp]: "reconfig' = reconfig" by (intro ext, auto simp add: reconfig'_def reconfig_def)
  have Q_eq[simp]: "Q' = Q" using reconfig_eq v\<^sub>c_eq Q'_def Q_def by blast
  have promised_eq[simp]: "promised' = promised" by (intro ext, auto simp add: promised'_def promised_def)

  show "zenImpl messages' nodeState'"
    apply (intro zenImplI)
                        apply (unfold message_simps property_simps committedTo_eq era\<^sub>i_eq Q_eq promised_eq)
      (*      using nodesIdentified committedToLocalCheckpoint eraMatchesLocalCheckpoint
              isQuorum_firstUncommittedSlot JoinRequest_slot_function
              nothingAcceptedInLaterSlots JoinRequest_currentTerm *)
  proof -
    from zen_axioms show "zen messages'" by (simp add: messages')
    from nodesIdentified show "\<And>n. currentNode (nodeState n) = n".
    from committedToLocalCheckpoint show "\<And>n. committed\<^sub>< (firstUncommittedSlot (nodeState n))".
    from eraMatchesLocalCheckpoint show "\<And>n. currentEra (nodeState n) = era\<^sub>i (firstUncommittedSlot (nodeState n))".
    from isQuorum_firstUncommittedSlot show "\<And>n. {q. isQuorum (nodeState n) q} = Q (era\<^sub>i (firstUncommittedSlot (nodeState n)))".
    from nothingAcceptedInLaterSlots show "\<And>i n t. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>" .
    from lastAccepted_None show "\<And>n t. lastAccepted (nodeState n) = NoPublishResponseSent \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>" .
    from lastAccepted_Some_term show "\<And>n t' x'. lastAccepted (nodeState n) = PublishResponseSent t' x' \<Longrightarrow> t' \<le> currentTerm (nodeState n)" .
    from lastAccepted_Some_sent show "\<And>n t' x'. lastAccepted (nodeState n) = PublishResponseSent t' x' \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t' \<rangle>\<leadsto>" .
    from lastAccepted_Some_value show "\<And>n t' x'. lastAccepted (nodeState n) = PublishResponseSent t' x' \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t' x' \<rangle>\<leadsto>" .
    from lastAccepted_Some_max show "\<And>n t' x' t''. lastAccepted (nodeState n) = PublishResponseSent t' x' \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t'' \<rangle>\<leadsto> \<Longrightarrow> t'' \<le> t'" .
    from JoinRequest_currentTerm show "\<And>n i t a. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)" .
    from JoinRequest_slot_function show "\<And>n i i' t a a'. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto> \<Longrightarrow> n \<midarrow>\<langle> JoinRequest i' t a' \<rangle>\<leadsto> \<Longrightarrow> i = i'" .
    from PublishRequest_electionTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> t \<le> electionTerm (nodeState n)" .
    from PublishRequest_electionTerm_applyRequested show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> \<not> applyRequested (nodeState n) \<Longrightarrow> t < electionTerm (nodeState n)" .

    from applyRequested_electionWon not_won
    show "\<And>n. applyRequested (nodeState n) \<Longrightarrow> electionWon (nodeState' n)"
      by (unfold nodeState'_def, auto simp add: nd_def)

    from electionWon_isQuorum
    show "\<And>n. electionWon (nodeState' n) \<Longrightarrow> isQuorum (nodeState n) (electionVotes (nodeState' n))"
      by (unfold nodeState'_def, auto simp add: nd_def nd' addElectionVote_def Let_def)

    fix n
    from electionWon_era era eraMatchesLocalCheckpoint
    show "electionWon (nodeState' n) \<Longrightarrow> era\<^sub>t (electionTerm (nodeState n)) = era\<^sub>i (firstUncommittedSlot (nodeState n))"
      by (cases "n = n\<^sub>0", unfold nodeState'_def, auto simp add: nd_def nd' addElectionVote_def Let_def)

    from electionVotes slot sent
    show "\<And>n'. n' \<in> electionVotes (nodeState' n) \<Longrightarrow> promised (firstUncommittedSlot (nodeState n)) n' n (electionTerm (nodeState n))"
      by (cases "n = n\<^sub>0", unfold nodeState'_def, auto simp add: promised_def nd' addElectionVote_def Let_def nd_def)

    fix n'
    assume electionValue': "electionValue (nodeState' n) = NoPublishResponseSent"
    assume n'_vote: "n' \<in> electionVotes (nodeState' n)"

    show "(n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (electionTerm (nodeState n)) NoPublishResponseSent \<rangle>\<rightarrow> (OneNode n))
               \<or> (\<exists>i<firstUncommittedSlot (nodeState n). \<exists>a. n' \<midarrow>\<langle> JoinRequest i (electionTerm (nodeState n)) a \<rangle>\<rightarrow> (OneNode n))"
    proof (cases "n = n\<^sub>0")
      case False with electionValue_None electionValue' n'_vote show ?thesis
        by (unfold nodeState'_def, auto)
    next
      case True note n_eq = this

      from electionValue'
      have combine_None: "combinePublishResponses (electionValue nd) (if i = firstUncommittedSlot nd then a else NoPublishResponseSent) = NoPublishResponseSent"
        by (unfold nodeState'_def, simp add: n_eq nd' addElectionVote_def Let_def)

      from combinePublishResponses_eq_NoPublishResponseSent_1 [OF this]
      have electionValue: "electionValue nd = NoPublishResponseSent" .

      from n'_vote have "n' \<in> electionVotes nd \<or> n' = s"
        by (unfold nodeState'_def, auto simp add: n_eq nd' addElectionVote_def Let_def)
      thus ?thesis
      proof (elim disjE)
        assume n'_vote: "n' \<in> electionVotes nd"
        with electionValue_None electionValue
        show ?thesis by (auto simp add: nd_def n_eq)
      next
        assume n': "n' = s"
        show ?thesis
        proof (cases "i = firstUncommittedSlot nd")
          case False with sent slot show ?thesis by (auto simp add: n_eq nd_def n')
        next
          case True
          from combinePublishResponses_eq_NoPublishResponseSent_2 [OF combine_None]
          have a: "a = NoPublishResponseSent" by (simp add: True)
          from sent slot show ?thesis by (auto simp add: n_eq nd_def n' a True)
        qed
      qed
    qed

  next
    fix n t' x'
    assume electionValue': "electionValue (nodeState' n) = PublishResponseSent t' x'"

    show "\<exists>n'\<in>electionVotes (nodeState' n). n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (electionTerm (nodeState n)) (PublishResponseSent t' x') \<rangle>\<rightarrow> (OneNode n)"
    proof (cases "n = n\<^sub>0")
      case False
      with electionValue_Some electionValue' show ?thesis by (unfold nodeState'_def, auto)
    next
      case True note n_eq = this
      show ?thesis
      proof (cases "electionValue nd = PublishResponseSent t' x'")
        case True with electionValue_Some show ?thesis
          by (unfold nodeState'_def, auto simp add: nd_def n_eq nd' addElectionVote_def Let_def)
      next
        case False

        from electionValue'
        have combine_Some: "combinePublishResponses (electionValue nd) (if i = firstUncommittedSlot nd then a else NoPublishResponseSent) = PublishResponseSent t' x'"
          by (unfold nodeState'_def, simp add: n_eq nd' addElectionVote_def Let_def)

        have "PublishResponseSent t' x' \<in> { electionValue nd, if i = firstUncommittedSlot nd then a else NoPublishResponseSent }"
          by (fold combine_Some, intro combinePublishResponses_range)

        with False have eqs: "i = firstUncommittedSlot nd" "a = PublishResponseSent t' x'"
          by (cases "i = firstUncommittedSlot nd", auto)

        from sent show ?thesis
          by (unfold nodeState'_def, auto simp add: n_eq nd' addElectionVote_def Let_def eqs nd_def)
      qed
    qed

  next
    fix n t' x' n'' t'' x''
    assume electionValue': "electionValue (nodeState' n) = PublishResponseSent t' x'"
    assume n''_vote: "n'' \<in> electionVotes (nodeState' n)"
    assume n''_sent: "n'' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (electionTerm (nodeState n)) (PublishResponseSent t'' x'') \<rangle>\<rightarrow> (OneNode n)"

    show "t'' \<le> t'"
    proof (cases "n = n\<^sub>0")
      case False
      with electionValue_Some_max electionValue' n''_vote n''_sent show ?thesis by (unfold nodeState'_def, auto)
    next
      case True note n_eq = this

      from n''_vote have n''_vote: "n'' \<in> electionVotes nd \<or> n'' = s"
        unfolding nodeState'_def by (auto simp add: n_eq nd' addElectionVote_def Let_def)

      from electionValue'
      have combine_Some: "combinePublishResponses (electionValue nd) (if i = firstUncommittedSlot nd then a else NoPublishResponseSent) = PublishResponseSent t' x'"
        by (unfold nodeState'_def, simp add: n_eq nd' addElectionVote_def Let_def)

      have PublishResponseSent_mem: "PublishResponseSent t' x' \<in> { electionValue nd, if i = firstUncommittedSlot nd then a else NoPublishResponseSent }"
        by (fold combine_Some, intro combinePublishResponses_range)

      show ?thesis
      proof (cases "electionValue nd = PublishResponseSent t' x'")
        case True

        from n''_vote
        show ?thesis
        proof (elim disjE)
          assume "n'' \<in> electionVotes nd" with True electionValue_Some_max n''_vote n''_sent show ?thesis
            unfolding nodeState'_def by (auto simp add: nd_def n_eq nd' addElectionVote_def Let_def)
        next
          assume n'': "n'' = s"
          with sent n''_sent
          have i: "i = firstUncommittedSlot nd"
            by (intro JoinRequest_slot_function, auto simp add: n_eq isMessageFrom_def nd_def)
          from n'' i sent n''_sent have a: "a = PublishResponseSent t'' x''"
            by (intro JoinRequest_value_function, auto simp add: n_eq isMessageFrom_def nd_def)
          from combine_Some show ?thesis by (cases "t' < t''", auto simp add: True i a)
        qed
      next
        case False

        from PublishResponseSent_mem False have eqs: "i = firstUncommittedSlot nd" "a = PublishResponseSent t' x'"
          by (cases "i = firstUncommittedSlot nd", auto)

        from n''_vote show ?thesis
        proof (elim disjE)
          assume n'': "n'' = s"
          from n''_sent sent have "a = PublishResponseSent t'' x''"
            by (intro JoinRequest_value_function, auto simp add: n'' eqs nd_def n_eq isMessageFrom_def)
          with eqs show ?thesis by auto
        next
          assume n''_vote: "n'' \<in> electionVotes nd"
          show ?thesis
          proof (cases "electionValue nd")
            case NoPublishResponseSent
            with n''_vote
            have "electionValue (nodeState n\<^sub>0) = NoPublishResponseSent" "n'' \<in> electionVotes (nodeState n\<^sub>0)"
              by (simp_all add: nd_def)

            from electionValue_None [OF this] show ?thesis
            proof (elim disjE exE conjE)
              assume "n'' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n\<^sub>0)) (electionTerm (nodeState n\<^sub>0)) NoPublishResponseSent \<rangle>\<rightarrow> (OneNode n\<^sub>0)"
              with n''_sent have "NoPublishResponseSent = PublishResponseSent t'' x''"
                by (intro JoinRequest_value_function, auto simp add: n_eq isMessageFrom_def)
              thus ?thesis by simp
            next
              fix i' a'
              assume "n'' \<midarrow>\<langle> JoinRequest i' (electionTerm (nodeState n\<^sub>0)) a' \<rangle>\<rightarrow> (OneNode n\<^sub>0)"
              with n''_sent have "i' = i" by (intro JoinRequest_slot_function, auto simp add: n_eq isMessageFrom_def eqs nd_def)
              moreover assume "i' < firstUncommittedSlot (nodeState n\<^sub>0)"
              ultimately show ?thesis by (simp add: eqs nd_def)
            qed

          next
            case (PublishResponseSent t''' x''')
            with n''_vote n''_sent have "t'' \<le> t'''"
              by (intro electionValue_Some_max, auto simp add: n_eq nd_def)
            also from combine_Some have "t''' \<le> t'"
              by (cases "t''' < t'", auto simp add: eqs PublishResponseSent)
            finally show ?thesis .
          qed
        qed
      qed
    qed
  qed
qed

fun insertOption :: "RoutedMessage option \<Rightarrow> RoutedMessage set \<Rightarrow> RoutedMessage set"
  where
    "insertOption None = id"
  | "insertOption (Some m) = insert m"

lemma (in zenImpl)
  fixes n\<^sub>0
  assumes "m \<in> messages"
  defines "nd \<equiv> nodeState n\<^sub>0"
  defines "result \<equiv> ProcessMessage nd m"
  defines "nodeState' \<equiv> \<lambda>n. if n = n\<^sub>0 then (fst result) else nodeState n"
  defines "messages' \<equiv> insertOption (snd result) messages"
  shows "zenImpl messages' nodeState'"
proof -
  {
    assume r: "result = (nd, None)"
    from r have "nodeState' = nodeState"
      by (auto simp add: nodeState'_def nd_def)
    moreover from r have "messages' = messages" by (simp add: messages'_def)
    ultimately have "zenImpl messages' nodeState'"
      using zenImpl_axioms by blast
  }
  note noop = this

  from `m \<in> messages`
  have m: "(sender m) \<midarrow>\<langle> payload m \<rangle>\<rightarrow> (destination m)"
    by (cases m, auto simp add: isMessageFromTo_def)

  have currentNode[simp]: "currentNode nd = n\<^sub>0" "\<And>n. currentNode (nodeState n) = n"
    by (simp_all add: nd_def nodesIdentified)

  from `m \<in> messages`
  have zenStepI: "\<And>nodeState. zenImpl messages nodeState \<Longrightarrow> zenStep messages nodeState messages' m"
  proof (intro_locales, simp add: zenImpl_def, intro zenStep_axioms.intro)
    show "messages \<subseteq> messages'"
      by (cases "snd result", auto simp add: messages'_def)
  qed

  from zenImpl_axioms have zenStep: "zenStep messages nodeState messages' m" by (intro zenStepI)

  have [simp]: "nodeState n\<^sub>0 = nd" by (simp add: nd_def)

  define broadcast' :: "(NodeData * Message option) \<Rightarrow> (NodeData * RoutedMessage option)" where
    "\<And>p. broadcast' p \<equiv> case p of
            (nd, Some m') \<Rightarrow> (nd, Some \<lparr>sender = currentNode nd,
                                   destination = Broadcast,
                                   payload = m' \<rparr>)
            | (nd, None) \<Rightarrow> (nd, None)"

  show ?thesis
  proof (cases "destination m = Broadcast \<or> destination m = OneNode (currentNode nd)")
    case False
    hence "result = (nd, None)"
      unfolding result_def ProcessMessage_def Let_def by simp
    thus ?thesis by (intro noop)
  next
    case True note dest_ok = this
    have dest_True: "destination m \<in> {Broadcast, OneNode (currentNode nd)} = True"
      using dest_ok by simp
    show ?thesis
    proof (cases "payload m")
      case (StartJoin t)
      show ?thesis
      proof (cases "currentTerm nd < t \<and> era\<^sub>t t = currentEra nd")
        case False
        hence "result = (nd, None)"
          unfolding result_def ProcessMessage_def Let_def dest_True StartJoin
          by (simp add: handleStartJoin_def)
        thus ?thesis by (intro noop)
      next
        case True
        hence new_term: "currentTerm nd < t" and era_eq: "era\<^sub>t t = currentEra nd" by simp_all

        have handleStartJoin[simp]: "handleStartJoin t nd = (nd \<lparr>currentTerm := t\<rparr>, Some (JoinRequest (firstUncommittedSlot nd) t (lastAccepted nd)))"
          by (simp add: handleStartJoin_def True)

        hence result: "result = (nd \<lparr>currentTerm := t\<rparr>, Some \<lparr> sender = n\<^sub>0, destination = OneNode (sender m), payload = JoinRequest (firstUncommittedSlot nd) t (lastAccepted nd) \<rparr>)"
          unfolding result_def ProcessMessage_def Let_def dest_True StartJoin by simp

        note zenStep.nodeState'_def zenStep.response_def zenStep.send.simps zenStep.nd_def
        note [simp] = this [OF zenStep]

        have "zenImpl messages' (zenStep.nodeState' nodeState n\<^sub>0 (nd \<lparr>currentTerm := t\<rparr>))"
          by (intro zenStep.handleStartJoin_invariants [OF zenStep, where t = t], simp_all add: messages'_def result)
        moreover have "zenStep.nodeState' nodeState n\<^sub>0 (nd \<lparr>currentTerm := t\<rparr>) = nodeState'"
          by (auto simp add: nodeState'_def result)
        ultimately show ?thesis by simp
      qed
    next

      case (JoinRequest i t a)

      from JoinRequest_not_broadcast m JoinRequest dest_ok
      have dest_m: "destination m = OneNode n\<^sub>0"
        apply (cases "destination m")
        using isMessageTo_def apply fastforce
        by auto

      from JoinRequest_not_broadcast m JoinRequest dest_ok
      have m: "(sender m) \<midarrow>\<langle> JoinRequest i t a \<rangle>\<rightarrow> (OneNode n\<^sub>0)"
        apply (cases "destination m")
        using isMessageTo_def apply fastforce
        by auto

      show ?thesis
      proof (cases "firstUncommittedSlot nd < i
             \<or> t < electionTerm nd
             \<or> (t = electionTerm nd \<and> electionWon nd)
             \<or> era\<^sub>t t \<noteq> currentEra nd")
        case True
        have "result = (nd, None)"
        unfolding result_def ProcessMessage_def dest_True JoinRequest
          by (simp add: handleJoinRequest_def True)
        thus ?thesis by (intro noop)
      next
        case False
        hence False': "i \<le> firstUncommittedSlot nd" "electionTerm nd \<le> t"
                      "electionTerm nd = t \<Longrightarrow> \<not> electionWon nd"
                      "era\<^sub>t t = currentEra nd"
          by auto
        hence False_eq: "(firstUncommittedSlot nd < i \<or> t < electionTerm nd \<or> t = electionTerm nd \<and> electionWon nd \<or> era\<^sub>t t \<noteq> currentEra nd) = False"
          by auto

        define nd1 where "nd1 \<equiv> ensureElectionTerm t nd"
        define nodeState1 where "\<And>n. nodeState1 n \<equiv> if n = n\<^sub>0 then nd1 else nodeState n"

        have nodeState1: "nodeState1 = zenStep.nodeState' nodeState n\<^sub>0 nd1"
          by (intro ext, simp add: zenStep.nodeState'_def [OF zenStep] nodeState1_def)

        have nd[simp]: "zenStep.nd nodeState n\<^sub>0 = nd"
          by (simp add: zenStep.nd_def [OF zenStep])

        have zenImpl1: "zenImpl messages nodeState1"
          unfolding nodeState1
        proof (intro zenStep.ensureElectionTerm_invariants)
          from `m \<in> messages`
          show "zenStep messages nodeState messages m"
            by (intro_locales, intro zenStep_axioms.intro, simp_all)

          from `electionTerm nd \<le> t` show "electionTerm (zenStep.nd nodeState n\<^sub>0) \<le> t"
            by (simp add: zenStep.nd_def [OF zenStep])

          show "nd1 = ensureElectionTerm t (zenStep.nd nodeState n\<^sub>0)"
            by (simp add: zenStep.nd_def [OF zenStep] nd1_def)
        qed simp

        from zenImpl1
        have zenStep1: "zenStep messages nodeState1 messages' m" by (intro zenStepI)

        define newVotes where "newVotes \<equiv> insert (sender m) (electionVotes nd1)"
        define nd2 where "nd2 \<equiv> addElectionVote (sender m) i a nd1"
        define nodeState2 where "\<And>n. nodeState2 n \<equiv> if n = n\<^sub>0 then nd2 else nodeState1 n"

        have nodeState2: "nodeState2 = zenStep.nodeState' nodeState1 n\<^sub>0 nd2"
          by (intro ext, simp add: zenStep.nodeState'_def [OF zenStep1] nodeState2_def)

        have nd1[simp]: "zenStep.nd nodeState1 n\<^sub>0 = nd1"
          by (simp add: zenStep.nd_def [OF zenStep1] nodeState1_def)

        have electionTerm_nd1[simp]: "electionTerm nd1 = t"
          by (simp add: nd1_def ensureElectionTerm_def)

        have currentEra_nd1[simp]: "currentEra nd1 = currentEra nd"
          by (simp add: nd1_def ensureElectionTerm_def)

        have firstUncommittedSlot_nd1[simp]: "firstUncommittedSlot nd1 = firstUncommittedSlot nd"
          by (simp add: nd1_def ensureElectionTerm_def)

        from False'
        have electionWon_nd1[simp]: "\<not> electionWon nd1"
          by (simp add: nd1_def ensureElectionTerm_def)

        have zenImpl2: "zenImpl messages nodeState2"
          unfolding nodeState2
          using `era\<^sub>t t = currentEra nd` `i \<le> firstUncommittedSlot nd`
        proof (intro zenStep.addElectionVote_invariants)
          from `m \<in> messages` zenImpl1
          show "zenStep messages nodeState1 messages m"
            by (intro_locales, simp add: zenImpl_def, intro zenStep_axioms.intro, simp_all)

          show "nd2 = addElectionVote (sender m) i a (zenStep.nd nodeState1 n\<^sub>0)" by (simp add: nd2_def)

          from m
          show "\<lparr>sender = sender m, destination = OneNode n\<^sub>0, payload = JoinRequest i (electionTerm (zenStep.nd nodeState1 n\<^sub>0)) a\<rparr> \<in> messages"
            by (simp add: isMessageFromTo_def)
        qed simp_all

        from zenImpl2
        have zenStep2: "zenStep messages nodeState2 messages' m" by (intro zenStepI)

        from False'
        have "handleJoinRequest (sender m) i t a nd = sendElectionValueIfAppropriate nd2"
          by (auto simp add: handleJoinRequest_def nd2_def nd1_def)
        hence result: "result = broadcast' (sendElectionValueIfAppropriate nd2)"
          unfolding result_def ProcessMessage_def dest_True JoinRequest broadcast'_def by simp

        have no_message: "result = (nd2, None) \<Longrightarrow> ?thesis"
        proof -
          assume result: "result = (nd2, None)"
          moreover from result have "messages' = messages" by (simp add: messages'_def)
          moreover from result have "nodeState' = nodeState2" by (auto simp add: nodeState'_def nodeState2_def nodeState1_def)
          moreover note zenImpl2
          ultimately show ?thesis by simp
        qed

        have not_requested: "\<not> applyRequested nd2"
        proof
          assume "applyRequested nd2"
          hence "applyRequested nd1" by (simp add: nd2_def addElectionVote_def Let_def)
          with zenImpl.applyRequested_electionWon [OF zenImpl1, of n\<^sub>0]
          have "electionWon nd1" by (simp add: nodeState1_def)
          moreover have "\<not>electionWon nd1" by simp
          ultimately show False by simp
        qed

        show ?thesis
        proof (cases "electionValue nd2")
          case NoPublishResponseSent
          hence result: "result = (nd2, None)"
            by (simp add: result handleJoinRequest_def sendElectionValueIfAppropriate_def broadcast'_def)
          thus ?thesis by (intro no_message)
        next
          case (PublishResponseSent t' x')
          hence result: "result = broadcast' (publishValue x' nd2)"
            by (simp add: result handleJoinRequest_def sendElectionValueIfAppropriate_def PublishResponseSent)

          show ?thesis
          proof (cases "electionWon nd2")
            case False
            hence result: "result = (nd2, None)"
              by (simp add: result publishValue_def broadcast'_def)
            thus ?thesis by (intro no_message)
          next
            case True

            have publishValue_nd2: "publishValue x' nd2 = (nd2\<lparr>applyRequested := True\<rparr>, Some (PublishRequest (firstUncommittedSlot nd2) (electionTerm nd2) x'))"
              by (simp add: publishValue_def True not_requested)

            have result': "result = (nd2\<lparr>applyRequested := True\<rparr>, Some \<lparr>sender = currentNode nd2, destination = Broadcast, payload = PublishRequest (firstUncommittedSlot nd2) (electionTerm nd2) x'\<rparr>)"
              by (simp add: result publishValue_nd2 broadcast'_def)

            have nd2[simp]: "zenStep.nd nodeState2 n\<^sub>0 = nd2"
              by (simp add: zenStep.nd_def [OF zenStep2] nodeState2_def)

            have nodeState': "nodeState' = zenStep.nodeState' nodeState2 n\<^sub>0 (nd2\<lparr>applyRequested := True\<rparr>)"
              by (intro ext, simp add: nodeState'_def result' zenStep.nodeState'_def [OF zenStep2] nodeState2_def nodeState1_def)

            have currentNode2[simp]: "currentNode nd2 = currentNode nd1"
              by (simp add: nd2_def addElectionVote_def Let_def)
            have currentNode1[simp]: "currentNode nd1 = currentNode nd"
              by (simp add: nd1_def ensureElectionTerm_def)

            show ?thesis
              unfolding nodeState'
            proof (intro zenStep.publishValue_invariants [OF zenStep2])

              from result result' show "nd2\<lparr>applyRequested := True\<rparr> = fst (publishValue x' (zenStep.nd nodeState2 n\<^sub>0))"
                unfolding broadcast'_def
                by (simp add: True publishValue_def not_requested)

              from result' show "messages' = zenStep.send messages (zenStep.broadcast n\<^sub>0) (publishValue x' (zenStep.nd nodeState2 n\<^sub>0))"
                using   publishValue_nd2
                unfolding broadcast'_def messages'_def result zenStep.broadcast_def [OF zenStep2]
                by (simp add: zenStep.send.simps [OF zenStep2])

              fix t'' x''
              assume "electionValue (zenStep.nd nodeState2 n\<^sub>0) = PublishResponseSent t'' x''"
              with PublishResponseSent show "x' = x''" by simp
            qed
          qed
        qed
      qed

    next
      case (ClientValue x)

      have result: "result = broadcast' (handleClientValue x nd)"
        unfolding result_def ProcessMessage_def ClientValue dest_True broadcast'_def by simp
     
      show ?thesis
      proof (cases "electionWon nd \<and> \<not> applyRequested nd \<and> electionValue nd = NoPublishResponseSent")
        case False
        hence "handleClientValue x nd = (nd, None)"
          by (auto simp add: handleClientValue_def publishValue_def)
        hence "result = (nd, None)"
          by (simp add: result broadcast'_def)
        thus ?thesis by (intro noop)
      next
        case True
        hence handleClientValue_eq: "handleClientValue x nd = (nd \<lparr> applyRequested := True \<rparr>, Some (PublishRequest (firstUncommittedSlot nd) (electionTerm nd) x))"
          by (simp add: publishValue_def handleClientValue_def)
        hence result: "result = (nd \<lparr> applyRequested := True \<rparr>, Some \<lparr>sender = n\<^sub>0, destination = Broadcast, payload = PublishRequest (firstUncommittedSlot nd) (electionTerm nd) x\<rparr>)"
          by (simp add: result broadcast'_def)

        from handleClientValue_eq True
        have publishValue: "publishValue x nd = (nd \<lparr> applyRequested := True \<rparr>, Some (PublishRequest (firstUncommittedSlot nd) (electionTerm nd) x))"
          by (simp add: handleClientValue_def)

        note zenStep.nodeState'_def [OF zenStep]

        have nodeState': "nodeState' = zenStep.nodeState' nodeState n\<^sub>0 (nd \<lparr> applyRequested := True \<rparr>)"
          unfolding zenStep.nodeState'_def [OF zenStep] nodeState'_def
          by (auto simp add: result)

        have nd[simp]: "zenStep.nd nodeState n\<^sub>0 = nd"
          unfolding zenStep.nd_def [OF zenStep] nd_def by simp

        show ?thesis
          unfolding nodeState'
        proof (intro zenStep.publishValue_invariants [OF zenStep])
          from publishValue handleClientValue_eq
          show "nd\<lparr>applyRequested := True\<rparr> = fst (publishValue x (zenStep.nd nodeState n\<^sub>0))"
            by simp

          show "messages' = zenStep.send messages (zenStep.broadcast n\<^sub>0) (publishValue x (zenStep.nd nodeState n\<^sub>0))"
            by (simp add: messages'_def result publishValue zenStep.send.simps [OF zenStep] zenStep.broadcast_def [OF zenStep])

          fix t' x'
          assume "electionValue (zenStep.nd nodeState n\<^sub>0) = PublishResponseSent t' x'"
          with True show "x = x'" by simp
        qed
      qed

    next
