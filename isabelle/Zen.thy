section \<open>Safety Properties\<close>

text \<open>This section describes the invariants that hold in the system, shows that the implementation
preserves the invariants, and shows that the invariants imply the required safety properties.\<close>

theory Zen
  imports Implementation OneSlot
begin

subsection \<open>Invariants on messages\<close>

text \<open>Firstly, a set of invariants that hold on the set of messages that have ever been sent,
without considering the state of any individual node.\<close>

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
      \<equiv> {t'. \<exists> s \<in> senders. s \<midarrow>\<langle> JoinRequest i t (Some t') \<rangle>\<leadsto> }"
    (* ASSUMPTIONS *)
  assumes JoinRequest_future:
    "\<And>i i' s t t' a.
        \<lbrakk> s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>; i < i'; t' < t \<rbrakk>
            \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i' t' \<rangle>\<leadsto>"
  assumes JoinRequest_None:
    "\<And>i s t t'.
        \<lbrakk> s \<midarrow>\<langle> JoinRequest i t None \<rangle>\<leadsto>; t' < t \<rbrakk>
            \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>"
  assumes JoinRequest_Some_lt:
    "\<And>i s t t'. s \<midarrow>\<langle> JoinRequest i t (Some t') \<rangle>\<leadsto>
      \<Longrightarrow> t' < t"
  assumes JoinRequest_Some_PublishResponse:
    "\<And>i s t t'. s \<midarrow>\<langle> JoinRequest i t (Some t') \<rangle>\<leadsto>
      \<Longrightarrow> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>"
  assumes JoinRequest_Some_max:
    "\<And>i s t t' t''. \<lbrakk> s \<midarrow>\<langle> JoinRequest i t (Some t') \<rangle>\<leadsto>; t' < t''; t'' < t \<rbrakk>
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

subsubsection \<open>Utility lemmas\<close>

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
  define f :: "RoutedMessage \<Rightarrow> Term" where "f \<equiv> \<lambda> m. case payload m of JoinRequest _ _ (Some t') \<Rightarrow> t' | _ \<Rightarrow> t\<^sub>0"
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
     \<equiv> (s \<midarrow>\<langle> JoinRequest i t None \<rangle>\<leadsto>
           \<or> (\<exists>i'<i. \<exists>a. s \<midarrow>\<langle> JoinRequest i' t a \<rangle>\<leadsto>))
           \<or> (\<exists>t'. s \<midarrow>\<langle> JoinRequest i t (Some t') \<rangle>\<leadsto>)"
 (is "?LHS == ?RHS")
proof -
  have "?LHS = ?RHS"
    apply (intro iffI)
     apply (metis option.exhaust isMessageFrom_def leI le_antisym promised_def)
    by (metis Destination.exhaust JoinRequest_not_broadcast isMessageFrom_def isMessageTo_def nat_less_le not_le promised_def)
  thus "?LHS == ?RHS" by simp
qed

lemma (in zen) JoinRequest_value_function:
  assumes "s \<midarrow>\<langle> JoinRequest i t a\<^sub>1 \<rangle>\<leadsto>" and "s \<midarrow>\<langle> JoinRequest i t a\<^sub>2 \<rangle>\<leadsto>"
  shows "a\<^sub>1 = a\<^sub>2"
proof (cases a\<^sub>1)
  case None
  with assms show ?thesis
    by (metis JoinRequest_None JoinRequest_Some_PublishResponse JoinRequest_Some_lt option.exhaust)
next
  case (Some t\<^sub>1)
  with assms obtain t\<^sub>2 where a\<^sub>2: "a\<^sub>2 = Some t\<^sub>2"
    using JoinRequest_None JoinRequest_Some_PublishResponse JoinRequest_Some_lt option.exhaust by metis

  from Some a\<^sub>2 assms show ?thesis
    by (metis JoinRequest_Some_PublishResponse JoinRequest_Some_lt less_linear JoinRequest_Some_max)
qed

lemma (in zen) shows finite_messages_insert: "finite (insert m messages)"
  using finite_messages by auto

lemma (in zen) isCommitted_committedTo:
  assumes "isCommitted i"
  shows "committed\<^sub>< i"
  using ApplyCommit_PublishRequest PublishRequest_committedTo assms isCommitted_def by blast

lemma (in zen) isCommitted_committedTo_Suc:
  assumes "isCommitted i"
  shows "committed\<^sub>< (Suc i)"
  using assms committedTo_def isCommitted_committedTo less_antisym by blast

lemma (in zen) promised_unique:
  assumes "promised i s d t" and "promised i' s d' t"
  shows "d = d'"
  by (meson Destination.inject JoinRequest_unique_destination assms promised_def)

subsubsection \<open>Relationship to @{term oneSlot}\<close>

text \<open>This shows that each slot @{term i} in Zen satisfies the assumptions of the @{term
oneSlot} model above.\<close>

lemma (in zen) zen_is_oneSlot:
  fixes i
  shows "oneSlot (Q \<circ> era\<^sub>t) (v i)
    (\<lambda> s t. s \<midarrow>\<langle> JoinRequest i t None \<rangle>\<leadsto>
        \<or> (\<exists> i' < i. \<exists> a. s \<midarrow>\<langle> JoinRequest i' t a \<rangle>\<leadsto>))
    (\<lambda> s t t'. s \<midarrow>\<langle> JoinRequest i t (Some t') \<rangle>\<leadsto>)
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
  assume "t' < t" "s \<midarrow>\<langle> JoinRequest i t None \<rangle>\<leadsto> \<or> (\<exists>i'<i. \<exists>a. s \<midarrow>\<langle> JoinRequest i' t a \<rangle>\<leadsto>)"
  thus "\<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>"
    using JoinRequest_None JoinRequest_future by auto
next
  fix s t t'
  assume j: "s \<midarrow>\<langle> JoinRequest i t (Some t') \<rangle>\<leadsto>"
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

theorem (in zen) consistent:
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

lemma (in zen) ApplyCommit_v\<^sub>c:
  assumes "\<langle> ApplyCommit i t \<rangle>\<leadsto>"
  shows "v\<^sub>c i = v i t"
proof (unfold v\<^sub>c_def, intro someI2 [where Q = "\<lambda>t'. v i t' = v i t"])
  from assms show "\<langle> ApplyCommit i t \<rangle>\<leadsto>" .
  fix t' assume "\<langle> ApplyCommit i t' \<rangle>\<leadsto>"
  thus "v i t' = v i t" by (intro oneSlot.consistent [OF zen_is_oneSlot] assms)
qed

lemma (in zen) ApplyCommit_PublishRequest_v\<^sub>c:
  assumes "\<langle> ApplyCommit i t \<rangle>\<leadsto>"
  shows "\<langle> PublishRequest i t (v\<^sub>c i) \<rangle>\<leadsto>"
  unfolding ApplyCommit_v\<^sub>c [OF assms]
  using ApplyCommit_PublishRequest assms .

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
      JoinRequest_future ApplyCommit_quorum
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
                         payload = JoinRequest i\<^sub>0 t\<^sub>0 None \<rparr> messages)"
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
    "\<And>s m d. (s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d) = ((s \<midarrow>\<langle> m \<rangle>\<rightarrow> d) \<or> (s, m, d) = (s\<^sub>0, JoinRequest i\<^sub>0 t\<^sub>0 None, OneNode d\<^sub>0))"
    by (auto simp add: isMessageFromTo'_def isMessageFromTo_def)

  have isMessageFrom'_eq [simp]:
    "\<And>s m. (s \<midarrow>\<langle> m \<rangle>\<leadsto>') = ((s \<midarrow>\<langle> m \<rangle>\<leadsto>) \<or> (s, m) = (s\<^sub>0, JoinRequest i\<^sub>0 t\<^sub>0 None))"
    by (auto simp add: isMessageFrom'_def isMessageFrom_def)

  have isMessageTo'_eq [simp]:
    "\<And>m d. (\<langle> m \<rangle>\<rightarrow>' d) = ((\<langle> m \<rangle>\<rightarrow> d) \<or> (m, d) = (JoinRequest i\<^sub>0 t\<^sub>0 None, OneNode d\<^sub>0))"
    by (auto simp add: isMessageTo'_def isMessageTo_def)

  have isMessage'_eq [simp]:
    "\<And>m. (\<langle> m \<rangle>\<leadsto>') = ((\<langle> m \<rangle>\<leadsto>) \<or> m = JoinRequest i\<^sub>0 t\<^sub>0 None)"
    by (auto simp add: isMessage'_def isMessage_def)

  have messages_simps:
    "\<And>i s d t t' x'. (s \<midarrow>\<langle> JoinRequest i t (Some t') \<rangle>\<rightarrow>' d)
        = (s \<midarrow>\<langle> JoinRequest i t (Some t') \<rangle>\<rightarrow> d)"
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
      JoinRequest_Some_max finite_messages_insert
  proof -
    show "\<And>i i' s t t' a. s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>' \<Longrightarrow> i < i' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i' t' \<rangle>\<leadsto>"
      using JoinRequest_future assms by auto
    show "\<And>i s t t'. s \<midarrow>\<langle> JoinRequest i t None \<rangle>\<leadsto>' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>"
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

text \<open>In contrast, @{term "JoinRequest i\<^sub>0 t\<^sub>0 (Some t\<^sub>0')"} can be sent if an @{term PublishResponse}
message has been sent for slot @{term
i\<^sub>0}, in which case @{term t\<^sub>0'} must be the greatest term of any such message
previously sent by node @{term n\<^sub>0} and @{term x\<^sub>0'} is the corresponding
value.}:\<close>

lemma (in zen) send_JoinRequest_Some:
  assumes "\<forall> i > i\<^sub>0. \<forall> t. \<not> s\<^sub>0 \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>"
  assumes "s\<^sub>0 \<midarrow>\<langle> PublishResponse i\<^sub>0 t\<^sub>0' \<rangle>\<leadsto>"
  assumes "t\<^sub>0' < t\<^sub>0"
  assumes "\<forall> t'. s\<^sub>0 \<midarrow>\<langle> PublishResponse i\<^sub>0 t' \<rangle>\<leadsto> \<longrightarrow> t' \<le> t\<^sub>0'"
    (* first-uncommitted slot, the era is ok, and not already sent*)
  assumes "\<forall> i < i\<^sub>0. \<exists> t. \<langle> ApplyCommit i t \<rangle>\<leadsto>"
  assumes "era\<^sub>t t\<^sub>0 = era\<^sub>i i\<^sub>0"
  assumes "\<forall> i a. \<not> s\<^sub>0 \<midarrow>\<langle> JoinRequest i t\<^sub>0 a \<rangle>\<leadsto>"
    (* *)
  shows   "zen (insert \<lparr> sender = s\<^sub>0, destination = OneNode d\<^sub>0,
                         payload = JoinRequest i\<^sub>0 t\<^sub>0 (Some t\<^sub>0') \<rparr> messages)" (is "zen ?messages'")
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
    "\<And>s m d. (s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d) = ((s \<midarrow>\<langle> m \<rangle>\<rightarrow> d) \<or> (s, m, d) = (s\<^sub>0, JoinRequest i\<^sub>0 t\<^sub>0 (Some t\<^sub>0'), OneNode d\<^sub>0))"
    by (auto simp add: isMessageFromTo'_def isMessageFromTo_def)

  have isMessageFrom'_eq [simp]:
    "\<And>s m. (s \<midarrow>\<langle> m \<rangle>\<leadsto>') = ((s \<midarrow>\<langle> m \<rangle>\<leadsto>) \<or> (s, m) = (s\<^sub>0, JoinRequest i\<^sub>0 t\<^sub>0 (Some t\<^sub>0')))"
    by (auto simp add: isMessageFrom'_def isMessageFrom_def)

  have isMessageTo'_eq [simp]:
    "\<And>m d. (\<langle> m \<rangle>\<rightarrow>' d) = ((\<langle> m \<rangle>\<rightarrow> d) \<or> (m, d) = (JoinRequest i\<^sub>0 t\<^sub>0 (Some t\<^sub>0'), OneNode d\<^sub>0))"
    by (auto simp add: isMessageTo'_def isMessageTo_def)

  have isMessage'_eq [simp]:
    "\<And>m. (\<langle> m \<rangle>\<leadsto>') = ((\<langle> m \<rangle>\<leadsto>) \<or> m = JoinRequest i\<^sub>0 t\<^sub>0 (Some t\<^sub>0'))"
    by (auto simp add: isMessage'_def isMessage_def)

  have messages_simps:
    "\<And>i s d t. (s \<midarrow>\<langle> JoinRequest i t None \<rangle>\<rightarrow>' d)
        = (s \<midarrow>\<langle> JoinRequest i t None \<rangle>\<rightarrow> d)"
    "\<And>i s d t x. (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>i s d t. (s \<midarrow>\<langle> PublishResponse i t\<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<rightarrow> d)"
    "\<And>i s d t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)"
    by auto

  define promised' where "\<And>i s d t. promised' i s d t \<equiv> \<exists>i'\<le>i. \<exists>a. s \<midarrow>\<langle> JoinRequest i' t a \<rangle>\<rightarrow>' (OneNode d)"
  have promised'I: "\<And>i s d t. promised i s d t \<Longrightarrow> promised' i s d t" 
    by (auto simp add: promised'_def promised_def)

  define prevAccepted' where "\<And>i t senders. prevAccepted' i t senders
      \<equiv> {t'. \<exists>s\<in>senders. s \<midarrow>\<langle> JoinRequest i t (Some t') \<rangle>\<leadsto>'}"

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
      PublishResponse_PublishRequest PublishRequest_era ApplyCommit_quorum
  proof -

    from assms JoinRequest_future
    show "\<And>i i' s t t' a. s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>'
      \<Longrightarrow> i < i' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i' t' \<rangle>\<leadsto>" by auto

    from assms JoinRequest_era
    show "\<And>i s t a. s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>' \<Longrightarrow> \<exists>i'\<le>i. committed\<^sub>< i' \<and> era\<^sub>t t \<le> era\<^sub>i i'"
      by (auto simp add: committedTo_def isCommitted_def)

    from assms JoinRequest_Some_lt
    show "\<And>i s t t' x'. s \<midarrow>\<langle> JoinRequest i t (Some t') \<rangle>\<leadsto>' \<Longrightarrow> t' < t" by auto

    from assms JoinRequest_Some_PublishResponse
    show "\<And>i s t t' x'. s \<midarrow>\<langle> JoinRequest i t (Some t') \<rangle>\<leadsto>' \<Longrightarrow> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>" by auto

    from assms JoinRequest_Some_max
    show "\<And>i s t t' t'' x'. s \<midarrow>\<langle> JoinRequest i t (Some t') \<rangle>\<leadsto>' \<Longrightarrow> t' < t'' \<Longrightarrow> t'' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t'' \<rangle>\<leadsto>"
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
      then obtain s' where s': "s' \<in> q" "s' \<midarrow>\<langle> JoinRequest i t (Some t') \<rangle>\<leadsto>'" 
        by (unfold prevAccepted'_def, blast)
      from s' have "s' \<midarrow>\<langle> JoinRequest i t (Some t') \<rangle>\<leadsto> \<or> (s', i, t, t') = (s\<^sub>0, i\<^sub>0, t\<^sub>0, t\<^sub>0')"
        by simp
      with assms q s' have "s' \<midarrow>\<langle> JoinRequest i t (Some t') \<rangle>\<leadsto>"
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
      JoinRequest_future ApplyCommit_quorum
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
        have 1: "maxTerm (prevAccepted i t q) \<in> prevAccepted i t q"
          by (intro maxTerm_mem finite_prevAccepted False)
        have 2: "\<nexists>n. n \<in> q \<and> n \<midarrow>\<langle> JoinRequest i\<^sub>0 t (Some t\<^sub>0) \<rangle>\<leadsto>"
          by (meson JoinRequest_Some_PublishResponse PublishResponse_PublishRequest nobody_proposed)
        from 1 2 have v_eq2: "v' i (maxTerm (prevAccepted i t q)) = v i (maxTerm (prevAccepted i t q))"
          apply (unfold v_eq) using prevAccepted_def by auto
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
      PublishRequest_function finite_messages_insert PublishRequest_era
      JoinRequest_unique_destination JoinRequest_not_broadcast
  proof -
    show "\<And>i i' s t t' a. s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto> \<Longrightarrow> i < i' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i' t' \<rangle>\<leadsto>'"
      using JoinRequest_future assms(2) by fastforce
    show "\<And>i s t t'. s \<midarrow>\<langle> JoinRequest i t None \<rangle>\<leadsto> \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>'" 
      using JoinRequest_None assms(2) by fastforce
    show "\<And>i s t t' x'. s \<midarrow>\<langle> JoinRequest i t (Some t') \<rangle>\<leadsto> \<Longrightarrow> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>'"
      using JoinRequest_Some_PublishResponse by fastforce
    show "\<And>i s t t' t'' x'. s \<midarrow>\<langle> JoinRequest i t (Some t') \<rangle>\<leadsto> \<Longrightarrow> t' < t'' \<Longrightarrow> t'' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t'' \<rangle>\<leadsto>'"
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
      JoinRequest_unique_destination JoinRequest_not_broadcast
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
      JoinRequest_future ApplyCommit_quorum
      JoinRequest_not_broadcast JoinRequest_unique_destination
    by (simp_all)
qed

subsection \<open>Invariants on node states\<close>

text \<open>A set of invariants which relate the states of the individual nodes to the set of messages sent.\<close>

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
  assumes lastAccepted_None: "\<And>n t. lastAcceptedTerm (nodeState n) = None
    \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>"
  assumes lastAccepted_Some_sent: "\<And>n t. lastAcceptedTerm (nodeState n) = Some t
    \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>"
  assumes lastAccepted_Some_max: "\<And>n t t'. lastAcceptedTerm (nodeState n) = Some t
    \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t' \<rangle>\<leadsto>
    \<Longrightarrow> t' \<le> t"
  assumes lastAccepted_Some_value: "lastAcceptedTerm (nodeState n) = Some t
    \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t (lastAcceptedValue (nodeState n)) \<rangle>\<leadsto>"
  assumes JoinRequest_currentTerm:
    "\<And>n i t a. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)"
  assumes JoinRequest_slot_function:
    "\<And>n i i' t a a'. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto> \<Longrightarrow> n \<midarrow>\<langle> JoinRequest i' t a' \<rangle>\<leadsto> \<Longrightarrow> i = i'"
  assumes PublishRequest_currentTerm:
    "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto>
        \<Longrightarrow> t \<le> currentTerm (nodeState n)"
  assumes PublishRequest_currentTerm_applyRequested:
    "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto>
        \<Longrightarrow> publishPermitted (nodeState n)
        \<Longrightarrow> t < currentTerm (nodeState n)"
  assumes joinVotes:
    "\<And> n n'. n' \<in> joinVotes (nodeState n)
      \<Longrightarrow> \<exists> i \<le> firstUncommittedSlot (nodeState n). \<exists> a.
        n' \<midarrow>\<langle> JoinRequest i (currentTerm (nodeState n)) a \<rangle>\<rightarrow> (OneNode n)"
  assumes electionWon_isQuorum:
    "\<And>n. electionWon (nodeState n) \<Longrightarrow> isQuorum (nodeState n) (joinVotes (nodeState n))"
  assumes electionWon_era:
    "\<And>n. electionWon (nodeState n) \<Longrightarrow> era\<^sub>t (currentTerm (nodeState n)) = era\<^sub>i (firstUncommittedSlot (nodeState n))"
  assumes electionValue_Free: "\<And>n n'.
    \<lbrakk> electionValueState (nodeState n) = ElectionValueFree; n' \<in> joinVotes (nodeState n) \<rbrakk>
    \<Longrightarrow> (n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n))
                           (currentTerm (nodeState n))
                           None \<rangle>\<rightarrow> (OneNode n))
    \<or> (\<exists> i < firstUncommittedSlot (nodeState n). \<exists> a.
        n' \<midarrow>\<langle> JoinRequest i (currentTerm (nodeState n)) a \<rangle>\<rightarrow> (OneNode n))"
  assumes electionValue_not_Free: "\<And>n.
    \<lbrakk> electionValueState (nodeState n) \<noteq> ElectionValueFree \<rbrakk>
    \<Longrightarrow> \<exists> n' \<in> joinVotes (nodeState n). \<exists> t t'. lastAcceptedTerm (nodeState n) = Some t \<and> t' \<le> t \<and>
         n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n))
                               (currentTerm (nodeState n))
                               (Some t') \<rangle>\<rightarrow> (OneNode n)"
  assumes electionValue_not_Free_max: "\<And>n n' a'.
    \<lbrakk> electionValueState (nodeState n) \<noteq> ElectionValueFree;
      n' \<in> joinVotes (nodeState n);
      n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n))
                                (currentTerm (nodeState n))
                                a' \<rangle>\<rightarrow> (OneNode n) \<rbrakk>
    \<Longrightarrow> maxTermOption a' (lastAcceptedTerm (nodeState n)) = lastAcceptedTerm (nodeState n)"
  assumes electionValue_Forced: "\<And>n.
    electionValueState (nodeState n) = ElectionValueForced
    \<Longrightarrow> \<exists> n' \<in> joinVotes (nodeState n).
         (n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n))
                               (currentTerm (nodeState n))
                               (lastAcceptedTerm (nodeState n)) \<rangle>\<rightarrow> (OneNode n))"
  assumes publishVotes: "\<And>n n'. n' \<in> publishVotes (nodeState n)
    \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) \<rangle>\<leadsto>"

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
      \<equiv> {t'. \<exists> s \<in> senders. s \<midarrow>\<langle> JoinRequest i t (Some t') \<rangle>\<leadsto>' }"


lemma currentTerm_ensureCurrentTerm[simp]: "currentTerm (ensureCurrentTerm t nd) = t"
  by (auto simp add: ensureCurrentTerm_def)

lemma (in zenStep)
  assumes "zen messages'"
  assumes "\<And>n. currentNode (nodeState' n) = n"
  assumes "\<And>n. committed\<^sub><' (firstUncommittedSlot (nodeState' n))"
  assumes "\<And>n. currentEra (nodeState' n) = era\<^sub>i' (firstUncommittedSlot (nodeState' n))"
  assumes "\<And>n. {q. isQuorum (nodeState' n) q} = Q' (era\<^sub>i' (firstUncommittedSlot (nodeState' n)))"
  assumes "\<And>i n t. firstUncommittedSlot (nodeState' n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>'"
  assumes "\<And>n t. lastAcceptedTerm (nodeState' n) = None \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t \<rangle>\<leadsto>'"
  assumes "\<And>n t. lastAcceptedTerm (nodeState' n) = Some t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t \<rangle>\<leadsto>'"
  assumes "\<And>n t t'. lastAcceptedTerm (nodeState' n) = Some t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t' \<rangle>\<leadsto>' \<Longrightarrow> t' \<le> t"
  assumes "\<And>n t. lastAcceptedTerm (nodeState' n) = Some t \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t (lastAcceptedValue (nodeState' n)) \<rangle>\<leadsto>'"
  assumes "\<And>n i t a. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>' \<Longrightarrow> t \<le> currentTerm (nodeState' n)"
  assumes "\<And>n i i' t a a'. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>' \<Longrightarrow> n \<midarrow>\<langle> JoinRequest i' t a' \<rangle>\<leadsto>' \<Longrightarrow> i = i'"
  assumes "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t x \<rangle>\<leadsto>' \<Longrightarrow> t \<le> currentTerm (nodeState' n)"
  assumes "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t x \<rangle>\<leadsto>' \<Longrightarrow> publishPermitted (nodeState' n) \<Longrightarrow> t < currentTerm (nodeState' n)"
  assumes "\<And>n n'. n' \<in> joinVotes (nodeState' n) \<Longrightarrow> promised' (firstUncommittedSlot (nodeState' n)) n' n (currentTerm (nodeState' n))"
  assumes "\<And>n. electionWon (nodeState' n) \<Longrightarrow> isQuorum (nodeState' n) (joinVotes (nodeState' n))"
  assumes "\<And>n. electionWon (nodeState' n) \<Longrightarrow> era\<^sub>t (currentTerm (nodeState' n)) = era\<^sub>i' (firstUncommittedSlot (nodeState' n))"
  assumes "\<And>n n'. electionValueState (nodeState' n) = ElectionValueFree \<Longrightarrow> n' \<in> joinVotes (nodeState' n) \<Longrightarrow> (n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState' n)) None \<rangle>\<rightarrow>' (OneNode n)) \<or> (\<exists>i<firstUncommittedSlot (nodeState' n). \<exists>a. n' \<midarrow>\<langle> JoinRequest i (currentTerm (nodeState' n)) a \<rangle>\<rightarrow>' (OneNode n))"
  assumes "\<And>n. electionValueState (nodeState' n) \<noteq> ElectionValueFree \<Longrightarrow> \<exists>n'\<in>joinVotes (nodeState' n).  \<exists>t t'. lastAcceptedTerm (nodeState' n) = Some t \<and> t' \<le> t \<and> n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState' n)) (Some t') \<rangle>\<rightarrow>' (OneNode n)"
  assumes "\<And>n n' a'. electionValueState (nodeState' n) \<noteq> ElectionValueFree \<Longrightarrow> n' \<in> joinVotes (nodeState' n) \<Longrightarrow> n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState' n)) a' \<rangle>\<rightarrow>' (OneNode n) \<Longrightarrow> maxTermOption a' (lastAcceptedTerm (nodeState' n)) = lastAcceptedTerm (nodeState' n)"
  assumes "\<And>n. electionValueState (nodeState' n) = ElectionValueForced \<Longrightarrow> \<exists>n'\<in>joinVotes (nodeState' n). n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState' n)) (lastAcceptedTerm (nodeState' n)) \<rangle>\<rightarrow>' (OneNode n)"
  assumes "\<And>n n'. n' \<in> publishVotes (nodeState' n) \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState' n)) \<rangle>\<leadsto>'"
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
  assumes x: "electionValueState nd = ElectionValueForced \<Longrightarrow> x = lastAcceptedValue nd"
  shows "zenImpl messages' nodeState'"
proof (cases "electionWon nd \<and> publishPermitted nd \<and> electionValueState nd \<noteq> ElectionValueUnknown")
  case False
  hence result: "result = (nd, None)" by (simp add: result_def publishValue_def)
  have "messages' = messages" by (auto simp add: messages' result)
  moreover
  have "nodeState' = nodeState" by (intro ext, unfold nodeState'_def, simp add: nd' result nd_def)
  moreover note zenImpl_axioms
  ultimately show ?thesis by simp
next
  case True note won = this
  hence result: "result = (nd \<lparr> publishPermitted := False \<rparr>,
                           Some (PublishRequest (firstUncommittedSlot nd) (currentTerm nd) x))"
    by (simp add: result_def publishValue_def)

  have messages': "messages' = insert \<lparr>sender = n\<^sub>0, destination = Broadcast, payload = PublishRequest (firstUncommittedSlot nd) (currentTerm nd) x\<rparr> messages"
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
    "era\<^sub>t (currentTerm nd) = currentEra nd" 
    "era\<^sub>i (firstUncommittedSlot nd) = currentEra nd" by (simp_all add: nd_def)

  have PublishRequest': "\<And>s d i t x'. (s \<midarrow>\<langle> PublishRequest i t x' \<rangle>\<rightarrow>' d) = ((s \<midarrow>\<langle> PublishRequest i t x' \<rangle>\<rightarrow> d)
          \<or> (s, d, i, t, x') = (n\<^sub>0, Broadcast, firstUncommittedSlot nd, currentTerm nd, x))"
    by (auto simp add: isMessageFromTo'_def, auto simp add: messages' isMessageFromTo_def)

  have fresh_request: "\<And>x. \<not> \<langle> PublishRequest (firstUncommittedSlot nd) (currentTerm nd) x \<rangle>\<leadsto>"
  proof (intro notI)
    fix x'
    assume "\<langle> PublishRequest (firstUncommittedSlot nd) (currentTerm nd) x' \<rangle>\<leadsto>"
    with True obtain s d where
      s: "s \<midarrow>\<langle> PublishRequest (firstUncommittedSlot nd) (currentTerm nd) x' \<rangle>\<rightarrow> d"
      by (auto simp add: isMessage_def isMessageFrom_def)

    with PublishRequest_quorum [where s = s and i = "firstUncommittedSlot nd" and t = "currentTerm nd" and x = x']
    obtain q where q: "q \<in> Q (currentEra nd)" and promised: "\<And>n. n \<in> q \<Longrightarrow> promised (firstUncommittedSlot nd) n s (currentTerm nd)"
      by (auto simp add: era_eq isMessageFrom_def, blast)

    from won have "isQuorum nd (joinVotes nd)"
      by (unfold nd_def, intro electionWon_isQuorum, simp)
    with isQuorum_firstUncommittedSlot [of n\<^sub>0]
    have "joinVotes nd \<in> Q (currentEra nd)" using nd_def era_eq by auto

    from q this Q_intersects have "q \<inter> joinVotes nd \<noteq> {}"
      by (auto simp add: intersects_def)
    then obtain n where n: "n \<in> q" "n \<in> joinVotes nd" by auto

    from promised [OF `n \<in> q`]
    obtain i' a' where "n \<midarrow>\<langle> JoinRequest i' (currentTerm nd) a' \<rangle>\<rightarrow> (OneNode s)"
      by (auto simp add: promised_def)

    moreover from joinVotes n
    obtain i'' a'' where "n \<midarrow>\<langle> JoinRequest i'' (currentTerm nd) a'' \<rangle>\<rightarrow> (OneNode n\<^sub>0)"
      by (auto simp add: nd_def, blast)

    ultimately have "OneNode s = OneNode n\<^sub>0"
      by (intro JoinRequest_unique_destination)

    with s have "n\<^sub>0 \<midarrow>\<langle> PublishRequest (firstUncommittedSlot nd) (currentTerm nd) x' \<rangle>\<leadsto>"
      by (auto simp add: isMessageFrom_def)

    hence "currentTerm nd < currentTerm (nodeState n\<^sub>0)"
    proof (intro PublishRequest_currentTerm_applyRequested, fold nd_def)
      from won show "publishPermitted nd" by (simp add: nd_def)
    qed
    thus False by (simp add: nd_def)
  qed

  have v_eq: "\<And>i t. v' i t = (if (i, t) = (firstUncommittedSlot nd, currentTerm nd) then x else v i t)"
  proof -
    fix i t
    show "?thesis i t"
    proof (cases "(i, t) = (firstUncommittedSlot nd, currentTerm nd)")
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
        with True have "\<langle> PublishRequest (firstUncommittedSlot nd) (currentTerm nd) x' \<rangle>\<leadsto> \<or> x' = x"
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
    have ne: "(i, t) \<noteq> (firstUncommittedSlot nd, currentTerm nd)" by (intro notI, simp)

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

  have nd': "nd' = nd \<lparr> publishPermitted := False \<rparr>" by (simp add: nd' result)

  have firstUncommittedSlot: "\<And>n. firstUncommittedSlot (nodeState' n) = firstUncommittedSlot (nodeState n)"
    by (unfold nodeState'_def, auto simp add: nd' nd_def)

  have era_firstUncommittedSlot: "\<And>n. era\<^sub>i' (firstUncommittedSlot (nodeState n)) = era\<^sub>i (firstUncommittedSlot (nodeState n))"
    by (intro era\<^sub>i_eq committedToLocalCheckpoint)

  have currentEra: "\<And>n. currentEra (nodeState' n) = currentEra (nodeState n)"
    by (unfold nodeState'_def, auto simp add: nd' nd_def)

  have publishVotes_eq: "\<And>n. publishVotes (nodeState' n) = publishVotes (nodeState n)"
    by (unfold nodeState'_def, auto simp add: nd' nd_def)

  have currentTerm: "\<And>n. currentTerm (nodeState' n) = currentTerm (nodeState n)"
    by (unfold nodeState'_def, auto simp add: nd' nd_def)

  show ?thesis
  proof (intro zenImplI)
    show "zen messages'"
    proof (unfold messages', intro send_PublishRequest allI impI notI ballI)
      from PublishRequest_currentTerm_applyRequested True
      show "\<And>x. n\<^sub>0 \<midarrow>\<langle> PublishRequest (firstUncommittedSlot nd) (currentTerm nd) x \<rangle>\<leadsto> \<Longrightarrow> False"
        by (auto simp add: isMessageFrom_def isMessageFromTo_def nd_def)

      from committedToLocalCheckpoint [where n = n\<^sub>0]
      show "\<And>i. i < firstUncommittedSlot nd \<Longrightarrow> \<exists>t. \<langle> ApplyCommit i t \<rangle>\<leadsto>"
        by (auto simp add: isMessage_def isMessageFrom_def isMessageFromTo_def nd_def committedTo_def isCommitted_def)

      from electionWon_era True
      show era_eq: "era\<^sub>t (currentTerm nd) = era\<^sub>i (firstUncommittedSlot nd)" by (simp add: nd_def)

      from True electionWon_isQuorum
      have "isQuorum nd (joinVotes nd)"
        by (simp add: nd_def)
      with isQuorum_firstUncommittedSlot era_eq
      show "joinVotes nd \<in> Q (era\<^sub>t (currentTerm nd))"
        by (auto simp add: nd_def)

      from joinVotes
      show "\<And>s. s \<in> joinVotes nd \<Longrightarrow> \<exists>i\<le>firstUncommittedSlot nd. \<exists>a. s \<midarrow>\<langle> JoinRequest i (currentTerm nd) a \<rangle>\<rightarrow> (OneNode n\<^sub>0)"
        by (auto simp add: nd_def)

      assume nonempty: "prevAccepted (firstUncommittedSlot nd) (currentTerm nd) (joinVotes nd) \<noteq> {}" (is "?T \<noteq> {}")

      define t' where "t' = maxTerm ?T"
      have t'_mem: "t' \<in> ?T"
        by (unfold t'_def, intro maxTerm_mem finite_prevAccepted nonempty)

      have t'_max: "\<And>t''. t'' \<in> ?T \<Longrightarrow> t'' \<le> t'"
        by (unfold t'_def, intro maxTerm_max finite_prevAccepted)

      from t'_mem obtain s where s_vote: "s \<in> joinVotes nd"
        and s_send: "s \<midarrow>\<langle> JoinRequest (firstUncommittedSlot nd) (currentTerm nd) (Some t') \<rangle>\<leadsto>"
        by (auto simp add: prevAccepted_def)

      have electionValueForced: "electionValueState nd = ElectionValueForced"
      proof (cases "electionValueState nd")
        case ElectionValueForced thus ?thesis by simp
      next
        case ElectionValueUnknown with won show ?thesis by simp
      next
        case ElectionValueFree
        with s_vote have "electionValueState (nodeState n\<^sub>0) = ElectionValueFree" "s \<in> joinVotes (nodeState n\<^sub>0)"
          by (simp_all add: nd_def)
        from electionValue_Free[OF this]
        show ?thesis
        proof (elim disjE exE conjE)
          assume "s \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n\<^sub>0)) (currentTerm (nodeState n\<^sub>0)) None \<rangle>\<rightarrow> (OneNode n\<^sub>0)"
          hence "Some t' = None"
            by (intro JoinRequest_value_function [OF s_send], auto simp add: nd_def isMessageFrom_def)
          thus ?thesis by simp
        next
          fix i' a'
          assume "s \<midarrow>\<langle> JoinRequest i' (currentTerm (nodeState n\<^sub>0)) a' \<rangle>\<rightarrow> (OneNode n\<^sub>0)"
          hence "firstUncommittedSlot nd = i'"
            by (intro JoinRequest_slot_function [OF s_send], auto simp add: nd_def isMessageFrom_def)
          moreover assume "i' < firstUncommittedSlot (nodeState n\<^sub>0)"
          ultimately show ?thesis by (simp add: nd_def)
        qed
      qed

      have s_send_to: "s \<midarrow>\<langle> JoinRequest (firstUncommittedSlot nd) (currentTerm nd) (Some t') \<rangle>\<rightarrow> (OneNode n\<^sub>0)"
      proof -
        from s_send obtain d where d: "s \<midarrow>\<langle> JoinRequest (firstUncommittedSlot nd) (currentTerm nd) (Some t') \<rangle>\<rightarrow> d"
          by (auto simp add: isMessageFrom_def)

        from joinVotes s_vote obtain i a where ia: "s \<midarrow>\<langle> JoinRequest i (currentTerm nd) a \<rangle>\<rightarrow> (OneNode n\<^sub>0)"
          by (unfold nd_def, blast)

        have i: "i = firstUncommittedSlot nd"
        proof (intro JoinRequest_slot_function)
          from ia d show
            "s \<midarrow>\<langle> JoinRequest i (currentTerm nd) a \<rangle>\<leadsto>" 
            "s \<midarrow>\<langle> JoinRequest (firstUncommittedSlot nd) (currentTerm nd) (Some t') \<rangle>\<leadsto>"
            by (auto simp add: isMessageFrom_def)
        qed

        have a: "a = Some t'"
        proof (intro JoinRequest_value_function)
          from ia d show
            "s \<midarrow>\<langle> JoinRequest i (currentTerm nd) a \<rangle>\<leadsto>" 
            "s \<midarrow>\<langle> JoinRequest i (currentTerm nd) (Some t') \<rangle>\<leadsto>"
            by (auto simp add: isMessageFrom_def i)
        qed

        from ia show ?thesis by (simp add: i a)
      qed

      from electionValueForced s_vote s_send_to
      have maxTermOption_eq: "maxTermOption (Some t') (lastAcceptedTerm nd) = lastAcceptedTerm nd"
        by (unfold nd_def, intro electionValue_not_Free_max, auto)

      obtain t where t: "lastAcceptedTerm nd = Some t" and tt': "t' \<le> t"
      proof (cases "lastAcceptedTerm (nodeState n\<^sub>0)")
        case (Some t) with maxTermOption_eq show ?thesis by (intro that, auto simp add: nd_def max_def, cases "t' \<le> t", auto)
      next
        case None
        with maxTermOption_eq show ?thesis by (auto simp add: nd_def)
      qed

      show "x = v (firstUncommittedSlot nd) t'"
      proof (intro PublishRequest_function)
        define P where "\<And>x. P x \<equiv> \<langle> PublishRequest (firstUncommittedSlot nd) t' x \<rangle>\<leadsto>"
        have v_The: "v (firstUncommittedSlot nd) t' = (THE x. P x)"
          by (simp add: P_def v_def)

        have "P (v (firstUncommittedSlot nd) t')"
        proof (unfold v_The, intro theI' [of P] ex_ex1I, unfold P_def)
          from s_send PublishResponse_PublishRequest JoinRequest_Some_PublishResponse
          show "\<exists>x. \<langle> PublishRequest (firstUncommittedSlot nd) t' x \<rangle>\<leadsto>" by metis

          fix x\<^sub>1 x\<^sub>2
          assume "\<langle> PublishRequest (firstUncommittedSlot nd) t' x\<^sub>1 \<rangle>\<leadsto>"
            "\<langle> PublishRequest (firstUncommittedSlot nd) t' x\<^sub>2 \<rangle>\<leadsto>"
          thus "x\<^sub>1 = x\<^sub>2" by (intro PublishRequest_function)
        qed

        thus "\<langle> PublishRequest (firstUncommittedSlot nd) t' (v (firstUncommittedSlot nd) t') \<rangle>\<leadsto>"
          by (simp add: P_def)

        from electionValue_Forced [where n = n\<^sub>0] electionValueForced
        obtain s' where s'_vote: "s' \<in> joinVotes nd"
          and s'_send: "s' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot nd) (currentTerm nd) (lastAcceptedTerm nd) \<rangle>\<rightarrow> (OneNode n\<^sub>0)"
          by (auto simp add: nd_def)

        from s'_vote s'_send t have "t \<le> t'"
          by (intro t'_max, auto simp add: prevAccepted_def isMessageFrom_def)
        with tt' have t_eq: "t' = t" by simp

        have x: "x = lastAcceptedValue nd"
          using electionValueForced x by blast

        from lastAccepted_Some_value x t t_eq
        show "\<langle> PublishRequest (firstUncommittedSlot nd) t' x \<rangle>\<leadsto>"
          by (auto simp add: nd_def)
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
    show "\<And>n t. lastAcceptedTerm (nodeState' n) = None \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t \<rangle>\<leadsto>'"
      by (unfold nodeState'_def message_simps, auto simp add: nd' nd_def)

    from lastAccepted_Some_sent
    show "\<And>n t. lastAcceptedTerm (nodeState' n) = Some t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t \<rangle>\<leadsto>'"
      by (unfold nodeState'_def message_simps, auto simp add: nd' nd_def)

  next
    fix n
    from lastAccepted_Some_max
    show "\<And>t t'. lastAcceptedTerm (nodeState' n) = Some t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t' \<rangle>\<leadsto>' \<Longrightarrow> t' \<le> t"
    by (unfold nodeState'_def, cases "n = n\<^sub>0", auto simp add: nd' message_simps nd_def)

  next
    from lastAccepted_Some_value nodeState'_def isMessage'_def isMessageFrom'_def PublishRequest' isMessage_def isMessageFrom_def nd' nd_def
    show "\<And>n t. lastAcceptedTerm (nodeState' n) = Some t \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t (lastAcceptedValue (nodeState' n)) \<rangle>\<leadsto>'"
      by (auto, meson, meson)      

    from JoinRequest_currentTerm
    show "\<And>n i t a. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>' \<Longrightarrow> t \<le> currentTerm (nodeState' n)"
      by (unfold nodeState'_def message_simps, auto simp add: nd' nd_def)

    from JoinRequest_slot_function
    show "\<And>n i i' t a a'. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>' \<Longrightarrow> n \<midarrow>\<langle> JoinRequest i' t a' \<rangle>\<leadsto>' \<Longrightarrow> i = i'"
      by (unfold nodeState'_def message_simps, auto simp add: nd' nd_def)

    from PublishRequest_currentTerm
    show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t x \<rangle>\<leadsto>' \<Longrightarrow> t \<le> currentTerm (nodeState' n)"
      by (unfold nodeState'_def isMessageFrom'_def PublishRequest', auto simp add: nd' nd_def isMessageFrom_def, blast, blast)

    from PublishRequest_currentTerm_applyRequested
    show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t x \<rangle>\<leadsto>' \<Longrightarrow> publishPermitted (nodeState' n) \<Longrightarrow> t < currentTerm (nodeState' n)"
      by (unfold nodeState'_def isMessageFrom'_def PublishRequest', auto simp add: nd' nd_def isMessageFrom_def, blast)

    from joinVotes
    show "\<And>n n'. n' \<in> joinVotes (nodeState' n) \<Longrightarrow> promised' (firstUncommittedSlot (nodeState' n)) n' n (currentTerm (nodeState' n))"
      by (unfold nodeState'_def, auto simp add: nd_def nd' promised'_def message_simps)

    from electionWon_isQuorum
    show "\<And>n. electionWon (nodeState' n) \<Longrightarrow> isQuorum (nodeState' n) (joinVotes (nodeState' n))"
      by (unfold nodeState'_def, auto simp add: nd_def nd' isQuorum_def)

    from electionWon_era era_firstUncommittedSlot
    show "\<And>n. electionWon (nodeState' n) \<Longrightarrow> era\<^sub>t (currentTerm (nodeState' n)) = era\<^sub>i' (firstUncommittedSlot (nodeState' n))"
      by (unfold nodeState'_def, auto simp add: nd_def nd')

    from electionValue_Free
    show "\<And>n n'. electionValueState (nodeState' n) = ElectionValueFree \<Longrightarrow>
            n' \<in> joinVotes (nodeState' n) \<Longrightarrow>
            (n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState' n)) None \<rangle>\<rightarrow>' (OneNode n)) \<or>
            ((\<exists>i<firstUncommittedSlot (nodeState' n). \<exists>a. n' \<midarrow>\<langle> JoinRequest i (currentTerm (nodeState' n)) a \<rangle>\<rightarrow>' (OneNode n)))"
      by (unfold nodeState'_def, auto simp add: nd' nd_def message_simps, blast, blast)

    from electionValue_not_Free
    show "\<And>n. electionValueState (nodeState' n) \<noteq> ElectionValueFree \<Longrightarrow>
            \<exists>n'\<in>joinVotes (nodeState' n).
               \<exists>t t'. lastAcceptedTerm (nodeState' n) = Some t \<and> t' \<le> t \<and> n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState' n)) (Some t') \<rangle>\<rightarrow>' (OneNode n)"
      by (unfold nodeState'_def, auto simp add: nd' nd_def message_simps)

    from electionValue_Forced
    show "\<And>n. electionValueState (nodeState' n) = ElectionValueForced \<Longrightarrow>
         \<exists>n'\<in>joinVotes (nodeState' n). n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState' n)) (lastAcceptedTerm (nodeState' n)) \<rangle>\<rightarrow>' (OneNode n)"
      by (unfold nodeState'_def, auto simp add: nd' nd_def message_simps)

    from electionValue_not_Free_max
    show "\<And>n n' a'. electionValueState (nodeState' n) \<noteq> ElectionValueFree \<Longrightarrow>
               n' \<in> joinVotes (nodeState' n) \<Longrightarrow>
               n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState' n)) a' \<rangle>\<rightarrow>' (OneNode n) \<Longrightarrow>
               maxTermOption a' (lastAcceptedTerm (nodeState' n)) = lastAcceptedTerm (nodeState' n)"
      by (unfold nodeState'_def, auto simp add: nd' nd_def message_simps)

  next
    from publishVotes
    show "\<And>n n'. n' \<in> publishVotes (nodeState' n) \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState' n)) \<rangle>\<leadsto>'"
      unfolding publishVotes_eq firstUncommittedSlot currentTerm message_simps .
  qed
qed

lemma (in zenStep) ensureCurrentTerm_invariants:
  assumes t: "currentTerm nd \<le> t"
  assumes nd': "nd' = ensureCurrentTerm t nd"
  assumes messages': "messages' = messages"
  shows "zenImpl messages' nodeState'"
proof (cases "currentTerm nd = t")
  case True
  hence "nodeState' = nodeState"
    by (intro ext, unfold nodeState'_def, auto simp add: nd' ensureCurrentTerm_def nd_def)
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
    "\<And>n. lastAcceptedTerm (nodeState' n) = lastAcceptedTerm (nodeState n)"
    "\<And>n. lastAcceptedValue (nodeState' n) = lastAcceptedValue (nodeState n)"
    "currentTerm (nodeState' n\<^sub>0) = t"
    "electionWon (nodeState' n\<^sub>0) = False"
    "joinVotes (nodeState' n\<^sub>0) = {}"
    "electionValueState (nodeState' n\<^sub>0) = ElectionValueFree"
    "publishPermitted (nodeState' n\<^sub>0) = True"
    "publishVotes (nodeState' n\<^sub>0) = {}"
    using False
    by (unfold nodeState'_def, auto simp add: nd_def isQuorum_def nd' ensureCurrentTerm_def)

  have currentTerm_increases: "\<And>n. currentTerm (nodeState n) \<le> currentTerm (nodeState' n)"
    using nd_def nodeState'_def property_simps t by auto

  have v_eq[simp]: "v' = v" by (intro ext, auto simp add: v'_def v_def)
  have v\<^sub>c_eq[simp]: "v\<^sub>c' = v\<^sub>c" by (intro ext, auto simp add: v\<^sub>c'_def v\<^sub>c_def)
  have isCommitted_eq[simp]: "isCommitted' = isCommitted" by (intro ext, auto simp add: isCommitted'_def isCommitted_def)
  have committedTo_eq[simp]: "committed\<^sub><' = committed\<^sub><" by (intro ext, auto simp add: committedTo'_def committedTo_def)
  have era\<^sub>i_eq[simp]: "era\<^sub>i' = era\<^sub>i" by (intro ext, auto simp add: era\<^sub>i'_def era\<^sub>i_def)
  have reconfig_eq[simp]: "reconfig' = reconfig" by (intro ext, auto simp add: reconfig'_def reconfig_def)
  have Q_eq[simp]: "Q' = Q" using reconfig_eq v\<^sub>c_eq Q'_def Q_def by blast

  show "zenImpl messages' nodeState'"
  proof (intro zenImplI, unfold message_simps property_simps committedTo_eq era\<^sub>i_eq Q_eq)
    from zen_axioms show "zen messages'" by (simp add: messages')
    from nodesIdentified show "\<And>n. currentNode (nodeState n) = n".
    from committedToLocalCheckpoint show "\<And>n. committed\<^sub>< (firstUncommittedSlot (nodeState n))".
    from eraMatchesLocalCheckpoint show "\<And>n. currentEra (nodeState n) = era\<^sub>i (firstUncommittedSlot (nodeState n))".
    from isQuorum_firstUncommittedSlot show "\<And>n. {q. isQuorum (nodeState n) q} = Q (era\<^sub>i (firstUncommittedSlot (nodeState n)))".
    from nothingAcceptedInLaterSlots show "\<And>i n t. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>" .
    from lastAccepted_None show "\<And>n t. lastAcceptedTerm (nodeState n) = None \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>".
    from lastAccepted_Some_sent show "\<And>n t. lastAcceptedTerm (nodeState n) = Some t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>" .
    from lastAccepted_Some_value show "\<And>n t. lastAcceptedTerm (nodeState n) = Some t \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t (lastAcceptedValue (nodeState n)) \<rangle>\<leadsto>" .
    from lastAccepted_Some_max show "\<And>n t t'. lastAcceptedTerm (nodeState n) = Some t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t' \<rangle>\<leadsto> \<Longrightarrow> t' \<le> t" .
    from JoinRequest_slot_function show "\<And>n i i' t a a'. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto> \<Longrightarrow> n \<midarrow>\<langle> JoinRequest i' t a' \<rangle>\<leadsto> \<Longrightarrow> i = i'" .

    from publishVotes False show "\<And>n n'. n' \<in> publishVotes (nodeState' n) \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState' n)) \<rangle>\<leadsto>"
      unfolding nodeState'_def by (auto simp add: nd' ensureCurrentTerm_def nd_def)

    from JoinRequest_currentTerm currentTerm_increases show "\<And>n i t a. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState' n)"
      using order_trans by blast

    from joinVotes False show "\<And>n n'. n' \<in> joinVotes (nodeState' n) \<Longrightarrow> promised' (firstUncommittedSlot (nodeState n)) n' n (currentTerm (nodeState' n))"
      by (unfold nodeState'_def, auto simp add: nd' ensureCurrentTerm_def nd_def promised'_def)

    from electionWon_isQuorum show "\<And>n. electionWon (nodeState' n) \<Longrightarrow> isQuorum (nodeState n) (joinVotes (nodeState' n))"
      by (unfold nodeState'_def, auto simp add: nd' ensureCurrentTerm_def nd_def)

    from electionWon_era False show "\<And>n. electionWon (nodeState' n) \<Longrightarrow> era\<^sub>t (currentTerm (nodeState' n)) = era\<^sub>i (firstUncommittedSlot (nodeState n))"
      by (unfold nodeState'_def, auto simp add: nd' ensureCurrentTerm_def nd_def)

    from electionValue_Free False show "\<And>n n'. electionValueState (nodeState' n) = ElectionValueFree \<Longrightarrow>
            n' \<in> joinVotes (nodeState' n) \<Longrightarrow>
            (n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState' n)) None \<rangle>\<rightarrow> (OneNode n)) \<or>
            (\<exists>i<firstUncommittedSlot (nodeState n). \<exists>a. n' \<midarrow>\<langle> JoinRequest i (currentTerm (nodeState' n)) a \<rangle>\<rightarrow> (OneNode n))"
      by (unfold nodeState'_def, auto simp add: nd' ensureCurrentTerm_def nd_def, blast)

    from electionValue_not_Free show "\<And>n. electionValueState (nodeState' n) \<noteq> ElectionValueFree \<Longrightarrow>
            \<exists>n'\<in>joinVotes (nodeState' n).
               \<exists>t t'. lastAcceptedTerm (nodeState n) = Some t \<and> t' \<le> t \<and> n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState' n)) (Some t') \<rangle>\<rightarrow> (OneNode n)"
      by (unfold nodeState'_def, auto simp add: nd' ensureCurrentTerm_def nd_def)

    from electionValue_Forced show "\<And>n. electionValueState (nodeState' n) = ElectionValueForced \<Longrightarrow>
         \<exists>n'\<in>joinVotes (nodeState' n). n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState' n)) (lastAcceptedTerm (nodeState n)) \<rangle>\<rightarrow> (OneNode n)"
      by (unfold nodeState'_def, auto simp add: nd' ensureCurrentTerm_def nd_def)

    fix n
    from electionValue_not_Free_max False show "\<And>n' a'. electionValueState (nodeState' n) \<noteq> ElectionValueFree \<Longrightarrow>
               n' \<in> joinVotes (nodeState' n) \<Longrightarrow>
               n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState' n)) a' \<rangle>\<rightarrow> (OneNode n) \<Longrightarrow>
               maxTermOption a' (lastAcceptedTerm (nodeState n)) = lastAcceptedTerm (nodeState n)"
      by (cases "n = n\<^sub>0", unfold nodeState'_def, auto simp add: nd' ensureCurrentTerm_def nd_def)

    fix t' x'
    assume sent: "n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t' x' \<rangle>\<leadsto>"

    show "t' \<le> currentTerm (nodeState' n)"
    proof (cases "n = n\<^sub>0")
      case False
      with PublishRequest_currentTerm sent show ?thesis
        by (unfold nodeState'_def, auto)
    next
      case True
      with PublishRequest_currentTerm sent have "t' \<le> currentTerm nd" by (simp add: nd_def)
      also note t
      also have "t = currentTerm (nodeState' n)" by (simp add: True)
      finally show ?thesis .
    qed

    assume not_requested: "publishPermitted (nodeState' n)"
    show "t' < currentTerm (nodeState' n)"
    proof (cases "n = n\<^sub>0")
      case False
      with PublishRequest_currentTerm_applyRequested sent not_requested show ?thesis
        by (unfold nodeState'_def, auto)
    next
      case True
      with PublishRequest_currentTerm sent have "t' \<le> currentTerm nd" by (simp add: nd_def)
      also from t False have "... < t" by simp
      also have "t = currentTerm (nodeState' n)" by (simp add: True)
      finally show ?thesis .
    qed
  qed
qed

lemma (in zenStep) sendJoinRequest_invariants:
  defines "result \<equiv> (nd, Some (JoinRequest (firstUncommittedSlot nd) (currentTerm nd) (lastAcceptedTerm nd)))"
  assumes messages': "messages' = send response result"
  assumes era_eq: "era\<^sub>t (currentTerm nd) = currentEra nd"
  assumes nd': "nd' = nd"
  assumes not_sent: "\<And>i a. \<not> n\<^sub>0 \<midarrow>\<langle> JoinRequest i (currentTerm nd) a \<rangle>\<leadsto>"
  assumes not_accepted: "\<And>t'. lastAcceptedTerm nd = Some t' \<Longrightarrow> t' < currentTerm nd"
  shows "zenImpl messages' nodeState'"
proof -

  have result: "result = (nd, Some (JoinRequest (firstUncommittedSlot nd) (currentTerm nd) (lastAcceptedTerm nd)))"
    by (simp add: result_def)

  have messages': "messages' = insert \<lparr>sender = n\<^sub>0, destination = OneNode (sender message),
                                               payload = JoinRequest (firstUncommittedSlot nd) (currentTerm nd) (lastAcceptedTerm nd)\<rparr> messages"
    by (simp add: messages' result response_def)

  have nodeState'[simp]: "nodeState' = nodeState"
    by (intro ext, auto simp add: nodeState'_def nd' zenStep.nodeState'_def [OF zenStep_axioms] nd_def)

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
      \<or> (s, i, t', a, d) = (n\<^sub>0, firstUncommittedSlot nd, currentTerm nd, lastAcceptedTerm nd, OneNode (sender message)))"
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
    proof (cases "lastAcceptedTerm nd")
      case None
      hence messages': "messages' = insert \<lparr>sender = n\<^sub>0, destination = OneNode (sender message),
                                               payload = JoinRequest (firstUncommittedSlot nd) (currentTerm nd) None\<rparr> messages"
        by (simp add: messages')

      show ?thesis
      proof (unfold messages', intro send_JoinRequest_None)
        from committedToLocalCheckpoint
        show "\<forall>i<firstUncommittedSlot nd. \<exists>t. \<langle> ApplyCommit i t \<rangle>\<leadsto>"
          by (simp add: nd_def committedTo_def isCommitted_def)

        from eraMatchesLocalCheckpoint era_eq
        show "era\<^sub>t (currentTerm nd) = era\<^sub>i (firstUncommittedSlot nd)"
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
            from lastAccepted_None [of n\<^sub>0] None show ?thesis
              by (simp add: nd_def eq nodesIdentified)
          qed
        qed

        from  not_sent
        show "\<forall>i a. \<not> n\<^sub>0 \<midarrow>\<langle> JoinRequest i (currentTerm nd) a \<rangle>\<leadsto>" by simp
      qed

    next
      case (Some t')
      hence messages': "messages' = insert \<lparr>sender = n\<^sub>0, destination = OneNode (sender message),
                                               payload = JoinRequest (firstUncommittedSlot nd) (currentTerm nd) (Some t')\<rparr> messages"
        by (simp add: messages')

      show ?thesis
      proof (unfold messages', intro send_JoinRequest_Some)
        from committedToLocalCheckpoint
        show "\<forall>i<firstUncommittedSlot nd. \<exists>t. \<langle> ApplyCommit i t \<rangle>\<leadsto>"
          by (simp add: nd_def committedTo_def isCommitted_def)

        from nothingAcceptedInLaterSlots
        show "\<forall>i>firstUncommittedSlot nd. \<forall>t. \<not> n\<^sub>0 \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>"
          by (simp add: nd_def nodesIdentified)

        from not_sent
        show "\<forall>i a. \<not> n\<^sub>0 \<midarrow>\<langle> JoinRequest i (currentTerm nd) a \<rangle>\<leadsto>" by simp

        from lastAccepted_Some_sent [of n\<^sub>0] lastAccepted_Some_value [of n\<^sub>0] lastAccepted_Some_max [of n\<^sub>0] Some
        show "n\<^sub>0 \<midarrow>\<langle> PublishResponse (firstUncommittedSlot nd) t' \<rangle>\<leadsto>"
          "\<forall>t''. n\<^sub>0 \<midarrow>\<langle> PublishResponse (firstUncommittedSlot nd) t'' \<rangle>\<leadsto> \<longrightarrow> t'' \<le> t'"
          by (simp_all add: nd_def)

        from not_accepted Some
        show "t' < currentTerm nd" by simp

        from eraMatchesLocalCheckpoint era_eq
        show "era\<^sub>t (currentTerm nd) = era\<^sub>i (firstUncommittedSlot nd)"
          by (simp add: nd_def)
      qed
    qed

    from nodesIdentified show "\<And>n. currentNode (nodeState' n) = n" by simp
    from committedToLocalCheckpoint show "\<And>n. committed\<^sub><' (firstUncommittedSlot (nodeState' n))" by simp
    from eraMatchesLocalCheckpoint show "\<And>n. currentEra (nodeState' n) = era\<^sub>i' (firstUncommittedSlot (nodeState' n))" by simp
    from nothingAcceptedInLaterSlots show "\<And>i n t. firstUncommittedSlot (nodeState' n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>'" by simp
    from PublishRequest_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t x \<rangle>\<leadsto>' \<Longrightarrow> t \<le> currentTerm (nodeState' n)" by simp
    from PublishRequest_currentTerm_applyRequested show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t x \<rangle>\<leadsto>' \<Longrightarrow> publishPermitted (nodeState' n) \<Longrightarrow> t < currentTerm (nodeState' n)" by simp
    from isQuorum_firstUncommittedSlot show "\<And>n. {q. isQuorum (nodeState' n) q} = Q' (era\<^sub>i' (firstUncommittedSlot (nodeState' n)))" by simp
    from electionWon_isQuorum show "\<And>n. electionWon (nodeState' n) \<Longrightarrow> isQuorum (nodeState' n) (joinVotes (nodeState' n))" by simp
    from lastAccepted_None show "\<And>n t. lastAcceptedTerm (nodeState' n) = None \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t \<rangle>\<leadsto>'" by simp
    from lastAccepted_Some_sent show "\<And>n t. lastAcceptedTerm (nodeState' n) = Some t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t \<rangle>\<leadsto>'" by simp
    from lastAccepted_Some_value show "\<And>n t. lastAcceptedTerm (nodeState' n) = Some t \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t (lastAcceptedValue (nodeState' n)) \<rangle>\<leadsto>'" by simp
    from lastAccepted_Some_max show "\<And>n t t'. lastAcceptedTerm (nodeState' n) = Some t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t' \<rangle>\<leadsto>' \<Longrightarrow> t' \<le> t" by simp
    from electionWon_era show "\<And>n. electionWon (nodeState' n) \<Longrightarrow> era\<^sub>t (currentTerm (nodeState' n)) = era\<^sub>i' (firstUncommittedSlot (nodeState' n))" by simp
    from publishVotes show "\<And>n n'. n' \<in> publishVotes (nodeState' n) \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState' n)) \<rangle>\<leadsto>'" by simp

    from joinVotes show "\<And>n n'. n' \<in> joinVotes (nodeState' n) \<Longrightarrow> promised' (firstUncommittedSlot (nodeState' n)) n' n (currentTerm (nodeState' n))"
      by (auto simp add: promised'_def JoinRequest', blast)

    from electionValue_Free
    show "\<And>n n'. electionValueState (nodeState' n) = ElectionValueFree \<Longrightarrow>
            n' \<in> joinVotes (nodeState' n) \<Longrightarrow>
            (n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState' n)) None \<rangle>\<rightarrow>' (OneNode n)) \<or>
            (\<exists>i<firstUncommittedSlot (nodeState' n). \<exists>a. n' \<midarrow>\<langle> JoinRequest i (currentTerm (nodeState' n)) a \<rangle>\<rightarrow>' (OneNode n))"
      by (auto simp add: JoinRequest')

    from electionValue_not_Free JoinRequest' message_simps nodeState'
    show "\<And>n. electionValueState (nodeState' n) \<noteq> ElectionValueFree \<Longrightarrow>
            \<exists>n'\<in>joinVotes (nodeState' n).
               \<exists>t t'. lastAcceptedTerm (nodeState' n) = Some t \<and> t' \<le> t \<and> n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState' n)) (Some t') \<rangle>\<rightarrow>' (OneNode n)"
      by metis

    from electionValue_Forced
    show "\<And>n. electionValueState (nodeState' n) = ElectionValueForced \<Longrightarrow>
         \<exists>n'\<in>joinVotes (nodeState' n). n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState' n)) (lastAcceptedTerm (nodeState' n)) \<rangle>\<rightarrow>' (OneNode n)"
      by (auto simp add: JoinRequest')

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
        thus "t' \<le> currentTerm (nodeState' n\<^sub>0)"
          unfolding nodeState'
          using JoinRequest_currentTerm isMessageFrom_def by blast     
      next
        fix d assume "(n\<^sub>0, i, t', a, d) = (n\<^sub>0, firstUncommittedSlot nd, currentTerm nd, lastAcceptedTerm nd, OneNode (sender message))"
        thus "t' \<le> currentTerm (nodeState' n\<^sub>0)"
          by (unfold nodeState'_def, simp add: nd' result)
      qed
    qed

  next
    fix n i i' t' a a'
    assume "n \<midarrow>\<langle> JoinRequest i t' a \<rangle>\<leadsto>'"
    then obtain d where d: "(n \<midarrow>\<langle> JoinRequest i t' a \<rangle>\<rightarrow> d) \<or> (n, i, t') = (n\<^sub>0, firstUncommittedSlot nd, currentTerm nd)"
      by (auto simp add: JoinRequest' isMessageFrom'_def)
    assume "n \<midarrow>\<langle> JoinRequest i' t' a' \<rangle>\<leadsto>'"
    then obtain d' where d': "(n \<midarrow>\<langle> JoinRequest i' t' a' \<rangle>\<rightarrow> d') \<or> (n, i', t') = (n\<^sub>0, firstUncommittedSlot nd, currentTerm nd)"
      by (auto simp add: JoinRequest' isMessageFrom'_def)

    from d d'
    show "i = i'"
    proof (elim disjE)
      show "n \<midarrow>\<langle> JoinRequest i t' a \<rangle>\<rightarrow> d \<Longrightarrow> n \<midarrow>\<langle> JoinRequest i' t' a' \<rangle>\<rightarrow> d' \<Longrightarrow> i = i'"
        by (intro JoinRequest_slot_function, auto simp add: isMessageFrom_def)

      show "(n, i, t') = (n\<^sub>0, firstUncommittedSlot nd, currentTerm nd)
              \<Longrightarrow> (n, i', t') = (n\<^sub>0, firstUncommittedSlot nd, currentTerm nd)
              \<Longrightarrow> i = i'" by simp

    next
      assume "n \<midarrow>\<langle> JoinRequest i t' a \<rangle>\<rightarrow> d" "(n, i', t') = (n\<^sub>0, firstUncommittedSlot nd, currentTerm nd)"
      hence "n\<^sub>0 \<midarrow>\<langle> JoinRequest i (currentTerm nd) a \<rangle>\<leadsto>" by (auto simp add: isMessageFrom_def)
      with not_sent show ?thesis by simp
    next
      assume "n \<midarrow>\<langle> JoinRequest i' t' a' \<rangle>\<rightarrow> d'" "(n, i, t') = (n\<^sub>0, firstUncommittedSlot nd, currentTerm nd)"
      hence "n\<^sub>0 \<midarrow>\<langle> JoinRequest i' (currentTerm nd) a' \<rangle>\<leadsto>" by (auto simp add: isMessageFrom_def)
      with not_sent show ?thesis by simp
    qed

  next
    fix n
    assume "electionValueState (nodeState' n) \<noteq> ElectionValueFree"
    hence a: "electionValueState (nodeState n) \<noteq> ElectionValueFree" by simp
    from electionValue_not_Free [OF a]
    obtain n' t t' where n': "n' \<in> joinVotes (nodeState n)" "lastAcceptedTerm (nodeState n) = Some t" "t' \<le> t"
      "n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) (Some t') \<rangle>\<rightarrow> (OneNode n)" by auto

    fix n' a'
    assume "n' \<in> joinVotes (nodeState' n)" hence n': "n' \<in> joinVotes (nodeState n)" by simp
    assume n'_msg: "n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState' n)) a' \<rangle>\<rightarrow>' (OneNode n)"

    from n'_msg 
    have "(n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) a' \<rangle>\<rightarrow> (OneNode n)) \<or>
                (n', firstUncommittedSlot (nodeState n), currentTerm (nodeState n), a', OneNode n) = 
                (n\<^sub>0, firstUncommittedSlot nd, currentTerm nd, lastAcceptedTerm nd, OneNode (sender message))"
      (is "?D1 \<or> ?D2")
      by (simp add: JoinRequest')

    thus "maxTermOption a' (lastAcceptedTerm (nodeState' n)) = lastAcceptedTerm (nodeState' n)"
    proof (elim disjE)
      assume ?D1
      with electionValue_not_Free_max a n' show ?thesis by auto
    next
      assume eq: "?D2"
      from n' eq have "n\<^sub>0 \<in> joinVotes (nodeState (sender message))" by simp
      from joinVotes [OF this]
      obtain i a where a: "n\<^sub>0 \<midarrow>\<langle> JoinRequest i (currentTerm (nodeState (sender message))) a \<rangle>\<leadsto>"
        by (auto simp add: isMessageFrom_def)
      with eq not_sent show ?thesis by auto
    qed
  qed
qed

lemma (in zenStep) handleStartJoin_invariants:
  fixes t
  defines "result \<equiv> handleStartJoin t nd"
  assumes nd': "nd' = fst result"
  assumes messages': "messages' = send response result"
  shows "zenImpl messages' nodeState'"
proof (cases "currentTerm nd < t \<and> era\<^sub>t t = currentEra nd \<and> (case lastAcceptedTerm nd of None \<Rightarrow> True | Some t' \<Rightarrow> t' < t)")
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

  from True have nd': "nd' = ensureCurrentTerm t nd"
    by (simp add: nd' result_def handleStartJoin_def)

  from message new_term nd'
  have zenImpl1: "zenImpl messages nodeState'"
    by (intro zenStep.ensureCurrentTerm_invariants, intro_locales, intro zenStep_axioms.intro, simp_all)

  with message messages_subset
  have zenStep1: "zenStep messages nodeState' messages' message"
    by (intro_locales, simp add: zenImpl_def, intro zenStep_axioms.intro)

  have nodeState': "nodeState' = zenStep.nodeState' nodeState' n\<^sub>0 nd'"
    by (intro ext, simp add: nodeState'_def zenStep.nodeState'_def [OF zenStep1])

  have nd'_eq: "zenStep.nd nodeState' n\<^sub>0 = nd'"
    by (simp add: zenStep.nd_def [OF zenStep1] nodeState'_def)

  have currentTerm_nd': "currentTerm nd' = t" by (simp add: nd')

  have "zenImpl messages' (zenStep.nodeState' nodeState' n\<^sub>0 nd')"
  proof (intro zenStep.sendJoinRequest_invariants [OF zenStep1], unfold nd'_eq currentTerm_nd')
    from True
    show "messages' = send response (nd', Some (JoinRequest (firstUncommittedSlot nd') t (lastAcceptedTerm nd')))"
      by (auto simp add: messages' result_def handleStartJoin_def nd' ensureCurrentTerm_def)

    from era_eq show "era\<^sub>t t = currentEra nd'"
      by (simp add: nd' ensureCurrentTerm_def)

    show "nd' = nd'" by simp

  next
    fix i a
    show "\<nexists>d. \<lparr>sender = n\<^sub>0, destination = d, payload = JoinRequest i t a\<rparr> \<in> messages"
    proof (intro notI)
      assume "\<exists> d. \<lparr>sender = n\<^sub>0, destination = d, payload = JoinRequest i t a\<rparr> \<in> messages"
      hence "n\<^sub>0 \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>" by (auto simp add: isMessageFrom_def isMessageFromTo_def)
      from JoinRequest_currentTerm [OF this]
      have "t \<le> currentTerm nd" by (simp add: nd_def)
      with new_term show False by simp
    qed

  next
    fix t'
    assume lastAccepted_Some: "lastAcceptedTerm nd' = Some t'"
    hence "lastAcceptedTerm (nodeState n\<^sub>0) =  Some t'"
      by (cases "currentTerm nd = t", auto simp add: nd' ensureCurrentTerm_def nd_def)
    with True new_term
    show "t' < t" by (simp add: nd_def)
  qed

  with nodeState' show ?thesis by simp
qed

lemma (in zenStep) addElectionVote_invariants:
  assumes nd': "nd' = addElectionVote s i a nd"
  assumes messages': "messages' = messages"
  assumes not_won: "\<not> electionWon nd"
  assumes sent: "s \<midarrow>\<langle> JoinRequest i (currentTerm nd) a \<rangle>\<rightarrow> (OneNode n\<^sub>0)"
  assumes era: "era\<^sub>t (currentTerm nd) = currentEra nd"
  assumes slot: "i \<le> firstUncommittedSlot nd"
  assumes a_lastAcceptedTerm: "maxTermOption a (lastAcceptedTerm nd) = lastAcceptedTerm nd"
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
    "\<And>n. lastAcceptedTerm (nodeState' n) = lastAcceptedTerm (nodeState n)"
    "\<And>n. lastAcceptedValue (nodeState' n) = lastAcceptedValue (nodeState n)"
    "\<And>n. currentTerm (nodeState' n) = currentTerm (nodeState n)"
    "\<And>n. publishPermitted (nodeState' n) = publishPermitted (nodeState n)"
    "\<And>n. publishVotes (nodeState' n) = publishVotes (nodeState n)"
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
  proof -
    from zen_axioms show "zen messages'" by (simp add: messages')
    from nodesIdentified show "\<And>n. currentNode (nodeState n) = n".
    from committedToLocalCheckpoint show "\<And>n. committed\<^sub>< (firstUncommittedSlot (nodeState n))".
    from eraMatchesLocalCheckpoint show "\<And>n. currentEra (nodeState n) = era\<^sub>i (firstUncommittedSlot (nodeState n))".
    from isQuorum_firstUncommittedSlot show "\<And>n. {q. isQuorum (nodeState n) q} = Q (era\<^sub>i (firstUncommittedSlot (nodeState n)))".
    from nothingAcceptedInLaterSlots show "\<And>i n t. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>" .
    from lastAccepted_None show "\<And>n t. lastAcceptedTerm (nodeState n) = None \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>" .
    from lastAccepted_Some_sent show "\<And>n t. lastAcceptedTerm (nodeState n) = Some t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>" .
    from lastAccepted_Some_value show "\<And>n t. lastAcceptedTerm (nodeState n) = Some t \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t (lastAcceptedValue (nodeState n)) \<rangle>\<leadsto>" .
    from lastAccepted_Some_max show "\<And>n t t'. lastAcceptedTerm (nodeState n) = Some t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t' \<rangle>\<leadsto> \<Longrightarrow> t' \<le> t" .
    from JoinRequest_currentTerm show "\<And>n i t a. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)" .
    from JoinRequest_slot_function show "\<And>n i i' t a a'. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto> \<Longrightarrow> n \<midarrow>\<langle> JoinRequest i' t a' \<rangle>\<leadsto> \<Longrightarrow> i = i'" .
    from PublishRequest_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)" .
    from PublishRequest_currentTerm_applyRequested show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> publishPermitted (nodeState n) \<Longrightarrow> t < currentTerm (nodeState n)" .
    from publishVotes show "\<And>n n'. n' \<in> publishVotes (nodeState n) \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) \<rangle>\<leadsto>" .

    from electionWon_isQuorum
    show "\<And>n. electionWon (nodeState' n) \<Longrightarrow> isQuorum (nodeState n) (joinVotes (nodeState' n))"
      by (unfold nodeState'_def, auto simp add: nd_def nd' addElectionVote_def Let_def)

    fix n
    from electionWon_era era eraMatchesLocalCheckpoint
    show "electionWon (nodeState' n) \<Longrightarrow> era\<^sub>t (currentTerm (nodeState n)) = era\<^sub>i (firstUncommittedSlot (nodeState n))"
      by (cases "n = n\<^sub>0", unfold nodeState'_def, auto simp add: nd_def nd' addElectionVote_def Let_def)

    from joinVotes slot sent
    show "\<And>n'. n' \<in> joinVotes (nodeState' n) \<Longrightarrow> promised (firstUncommittedSlot (nodeState n)) n' n (currentTerm (nodeState n))"
      by (cases "n = n\<^sub>0", unfold nodeState'_def, auto simp add: promised_def nd' addElectionVote_def Let_def nd_def)

    fix n'
    assume electionValueFree': "electionValueState (nodeState' n) = ElectionValueFree"
    assume n'_vote: "n' \<in> joinVotes (nodeState' n)"

    show "(n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) None \<rangle>\<rightarrow> (OneNode n))
               \<or> (\<exists>i<firstUncommittedSlot (nodeState n). \<exists>a. n' \<midarrow>\<langle> JoinRequest i (currentTerm (nodeState n)) a \<rangle>\<rightarrow> (OneNode n))"
    proof (cases "n = n\<^sub>0")
      case False with electionValue_Free electionValueFree' n'_vote show ?thesis
        by (unfold nodeState'_def, auto)
    next
      case True note n_eq = this

      from electionValueFree'
      have electionValueFree: "electionValueState (nodeState n) = ElectionValueFree"
        apply (unfold nodeState'_def)
        apply (auto simp add: nd' n_eq addElectionVote_def Let_def)
        using ElectionValueState.distinct
        by (metis nd_def)

      from n'_vote have "n' \<in> joinVotes nd \<or> n' = s"
        by (unfold nodeState'_def, auto simp add: n_eq nd' addElectionVote_def Let_def)
      thus ?thesis
      proof (elim disjE)
        assume n'_vote: "n' \<in> joinVotes nd"
        with electionValue_Free electionValueFree
        show ?thesis by (auto simp add: nd_def n_eq)
      next
        assume n': "n' = s"
        show ?thesis
        proof (cases "i = firstUncommittedSlot nd")
          case False with sent slot show ?thesis by (auto simp add: n_eq nd_def n')
        next
          case True
          with electionValueFree' have a: "a = None"
            unfolding nodeState'_def
            apply (simp add: n_eq nd' addElectionVote_def Let_def)
            using ElectionValueState.distinct
            by (metis not_None_eq)
          from sent slot show ?thesis by (auto simp add: n_eq nd_def n' a True)
        qed
      qed
    qed

  next
    fix n
    assume electionValueForced': "electionValueState (nodeState' n) \<noteq> ElectionValueFree"

    show "\<exists>n'\<in>joinVotes (nodeState' n).
            \<exists>t t'. lastAcceptedTerm (nodeState n) = Some t \<and> t' \<le> t \<and> n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) (Some t') \<rangle>\<rightarrow> (OneNode n)"
    proof (cases "n = n\<^sub>0")
      case False
      with electionValue_not_Free electionValueForced' show ?thesis by (unfold nodeState'_def, auto)
    next
      case True note n_eq = this
      show ?thesis
      proof (cases "electionValueState (nodeState n) = ElectionValueFree")
        case False with electionValue_not_Free show ?thesis
          by (unfold nodeState'_def, auto simp add: nd_def n_eq nd' addElectionVote_def Let_def)
      next
        case True
        with electionValueForced' have "i = firstUncommittedSlot nd \<and> a \<noteq> None"
          unfolding nodeState'_def
          apply (simp add: n_eq nd' addElectionVote_def Let_def nd_def)
          by presburger
        hence i: "i = firstUncommittedSlot nd" and "a \<noteq> None" by simp_all
        then obtain t' where a: "a = Some t'" by auto

        from a_lastAcceptedTerm a obtain t where t: "lastAcceptedTerm nd = Some t" and t't: "t' \<le> t"
          apply (cases "lastAcceptedTerm nd", simp_all)
          by (metis eq_iff max_def)

        have "joinVotes (nodeState' n) = insert s (joinVotes nd)"
          unfolding nodeState'_def
          by (simp add: n_eq nd' addElectionVote_def Let_def)

        show ?thesis
        proof (intro bexI exI conjI)
          show "s \<in> joinVotes (nodeState' n)"
            unfolding nodeState'_def
            by (simp add: n_eq nd' addElectionVote_def Let_def)

          from sent
          show "s \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) (Some t') \<rangle>\<rightarrow> (OneNode n)"
            by (simp add: i a n_eq nd_def)

          from t show "lastAcceptedTerm (nodeState n) = Some t" by (simp add: nd_def n_eq)
          from t't show "t' \<le> t" .
        qed
      qed
    qed

  next
    fix n
    assume electionValueForced': "electionValueState (nodeState' n) = ElectionValueForced"

    show "\<exists>n'\<in>joinVotes (nodeState' n). n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) (lastAcceptedTerm (nodeState n)) \<rangle>\<rightarrow> (OneNode n)"
    proof (cases "n = n\<^sub>0")
      case False
      with electionValueForced' electionValue_Forced
      show ?thesis
        unfolding nodeState'_def
        by (auto)
    next
      case True note n_eq = this

      show ?thesis
      proof (cases "electionValueState (nodeState n) = ElectionValueForced")
        case True
        with electionValue_Forced
        have "\<exists>n'\<in>joinVotes (nodeState n). n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) (lastAcceptedTerm (nodeState n)) \<rangle>\<rightarrow> (OneNode n)"
          by (auto simp add: n_eq)
        moreover have "joinVotes (nodeState n) \<subseteq> joinVotes (nodeState' n)"
          unfolding nodeState'_def
          unfolding nd' n_eq addElectionVote_def Let_def nd_def by auto
        ultimately show ?thesis by blast
      next
        case False

        with electionValueForced' have "i = firstUncommittedSlot nd \<and> a \<noteq> None \<and> a = lastAcceptedTerm nd"
          unfolding nodeState'_def n_eq
          unfolding nd' addElectionVote_def Let_def nd_def
          apply simp
          using ElectionValueState.distinct by presburger

        hence i: "i = firstUncommittedSlot nd" and a_Some: "a \<noteq> None" and a: "a = lastAcceptedTerm nd"
          by auto

        show ?thesis
        proof (intro bexI exI conjI)
          from sent
          show "s \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) (lastAcceptedTerm (nodeState n)) \<rangle>\<rightarrow> (OneNode n)"
            by (simp add: i a n_eq nd_def)

          show "s \<in> joinVotes (nodeState' n)"
            unfolding nodeState'_def
            by (simp add: n_eq nd' addElectionVote_def Let_def)
        qed
      qed
    qed

  next
    fix n n' a'

    assume notFree': "electionValueState (nodeState' n) \<noteq> ElectionValueFree"
    assume n'_vote: "n' \<in> joinVotes (nodeState' n)"
    assume n'_sent: "n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) a' \<rangle>\<rightarrow> (OneNode n)"

    show "maxTermOption a' (lastAcceptedTerm (nodeState n)) = lastAcceptedTerm (nodeState n)"
    proof (cases "n = n\<^sub>0")
      case False
      with electionValue_not_Free_max notFree' n'_vote n'_sent show ?thesis by (unfold nodeState'_def, auto)
    next
      case True note n_eq = this

      from n'_vote have "n' \<in> joinVotes nd \<or> n' = s"
        unfolding nodeState'_def by (auto simp add: n_eq nd' addElectionVote_def Let_def)

      thus ?thesis
      proof (elim disjE)
        assume "n' \<in> joinVotes nd" hence n'_vote: "n' \<in> joinVotes (nodeState n\<^sub>0)" by (simp add: nd_def)
        show ?thesis
        proof (cases "electionValueState (nodeState n\<^sub>0) = ElectionValueFree")
          case False
          with electionValue_not_Free_max n'_vote n'_sent
          show ?thesis by (simp add: n_eq)
        next
          case True
          from electionValue_Free [OF True n'_vote]
          show ?thesis
          proof (elim disjE exE conjE)
            assume "n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n\<^sub>0)) (currentTerm (nodeState n\<^sub>0)) None \<rangle>\<rightarrow> (OneNode n\<^sub>0)"
            with n'_sent have a': "a' = None"
              by (intro JoinRequest_value_function, auto simp add: isMessageFrom_def n_eq)
            thus ?thesis by simp
          next
            fix i'' a''
            assume ia: "n' \<midarrow>\<langle> JoinRequest i'' (currentTerm (nodeState n\<^sub>0)) a'' \<rangle>\<rightarrow> (OneNode n\<^sub>0)"

            from ia n'_sent
            have i'': "i'' = (firstUncommittedSlot (nodeState n))"
              by (intro JoinRequest_slot_function, auto simp add: isMessageFrom_def n_eq)

            assume "i'' < firstUncommittedSlot (nodeState n\<^sub>0)"
            with i'' show ?thesis by (simp add: n_eq)
          qed
        qed
      next
        assume n': "n' = s"

        from sent n'_sent have i: "i = firstUncommittedSlot nd"
          by (intro JoinRequest_slot_function, auto simp add: isMessageFrom_def n' n_eq nd_def)

        from sent n'_sent have a: "a' = a"
          by (intro JoinRequest_value_function, auto simp add: isMessageFrom_def n' n_eq nd_def i)

        from a_lastAcceptedTerm show ?thesis
          by (simp add: a nd_def n_eq)
      qed
    qed
  qed
qed

lemma (in zenStep) handlePublishRequest_invariants:
  fixes i t x
  defines "result \<equiv> handlePublishRequest i t x nd"
  assumes nd': "nd' = fst result"
  assumes messages': "messages' = send response result"
  assumes sent: "\<langle> PublishRequest i t x \<rangle>\<leadsto>"
  shows "zenImpl messages' nodeState'"
proof (cases "i = firstUncommittedSlot nd \<and> currentTerm nd \<le> t \<and> (case lastAcceptedTerm nd of None \<Rightarrow> True | Some t' \<Rightarrow> t' \<le> t)")
  case False
  hence [simp]: "result = (nd, None)"
    by (simp add: result_def handlePublishRequest_def)

  have [simp]: "messages' = messages"
    by (simp add: messages')

  have [simp]: "nodeState' = nodeState"
    unfolding nodeState'_def
    by (intro ext, simp add: nd' nd_def)

  from zenImpl_axioms show ?thesis by simp

next
  case True note precondition = this

  hence result: "result = (nd\<lparr>lastAcceptedTerm := Some t, lastAcceptedValue := x,
                    electionValueState := if lastAcceptedTerm nd \<noteq> Some t
                                            \<and> electionValueState nd = ElectionValueForced
                                            then ElectionValueUnknown
                                            else electionValueState nd\<rparr>, Some (PublishResponse i t))"
    by (simp add: result_def handlePublishRequest_def)

  have messages': "messages' = insert \<lparr> sender = n\<^sub>0, destination = OneNode (sender message), payload = PublishResponse i t \<rparr> messages"
    by (simp add: messages' result response_def)

  have message_simps[simp]:
    "\<And>s d i t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)"
    "\<And>s d i t x. (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>s d i t a. (s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<rightarrow> d)"
    "\<And>d i t. (\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = (\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)"
    "\<And>d i t x. (\<langle> PublishRequest i t x \<rangle>\<rightarrow>' d) = (\<langle> PublishRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>d i t a. (\<langle> JoinRequest i t a \<rangle>\<rightarrow>' d) = (\<langle> JoinRequest i t a \<rangle>\<rightarrow> d)"
    "\<And>s i t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<leadsto>') = (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<leadsto>)"
    "\<And>s i t x. (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>') = (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>)"
    "\<And>s i t a. (s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>') = (s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>)"
    "\<And>i t. (\<langle> ApplyCommit i t \<rangle>\<leadsto>') = (\<langle> ApplyCommit i t \<rangle>\<leadsto>)"
    "\<And>i t x. (\<langle> PublishRequest i t x \<rangle>\<leadsto>') = (\<langle> PublishRequest i t x \<rangle>\<leadsto>)"
    "\<And>i t a. (\<langle> JoinRequest i t a \<rangle>\<leadsto>') = (\<langle> JoinRequest i t a \<rangle>\<leadsto>)"
    by (unfold isMessageFromTo'_def isMessageTo'_def isMessageFrom'_def isMessage'_def,
        auto simp add: messages' isMessageFromTo_def isMessageTo_def isMessageFrom_def isMessage_def)

  have property_simps[simp]:
    "\<And>n. currentNode (nodeState' n) = currentNode (nodeState n)"
    "\<And>n. firstUncommittedSlot (nodeState' n) = firstUncommittedSlot (nodeState n)"
    "\<And>n. currentEra (nodeState' n) = currentEra (nodeState n)"
    "\<And>n q. isQuorum (nodeState' n) q = isQuorum (nodeState n) q"
    "\<And>n. currentTerm (nodeState' n) = currentTerm (nodeState n)"
    "\<And>n. publishPermitted (nodeState' n) = publishPermitted (nodeState n)"
    "\<And>n. joinVotes (nodeState' n) = joinVotes (nodeState n)"
    "\<And>n. electionWon (nodeState' n) = electionWon (nodeState n)"
    "\<And>n. publishVotes (nodeState' n) = publishVotes (nodeState n)"
    "lastAcceptedTerm nd' = Some t"
    "lastAcceptedValue nd' = x"
    by (unfold nodeState'_def, auto simp add: result nd' nd_def isQuorum_def)

  have electionValueState': "electionValueState nd'
      = (if lastAcceptedTerm nd \<noteq> Some t
          \<and> electionValueState nd = ElectionValueForced
          then ElectionValueUnknown
          else electionValueState nd)"
    by (simp add: result nd')

  hence electionValueState_simps[simp]:
    "\<And>n. (electionValueState (nodeState' n) = ElectionValueFree)
        = (electionValueState (nodeState n) = ElectionValueFree)"
    unfolding nodeState'_def
    by (simp add: electionValueState' nd_def)

  have PublishResponse'_fromTo: "\<And>s d i t'. (s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<rightarrow>' d) =
    ((s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<rightarrow> d)
      \<or> (s, i, t', d) = (n\<^sub>0, firstUncommittedSlot nd, t, OneNode (sender message)))"
    by (unfold isMessageFromTo'_def isMessageFromTo_def, auto simp add: messages' True)

  have PublishResponse'_from:
    "\<And>s i t'. (s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>') =
    ((s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>)
      \<or> (s, i, t') = (n\<^sub>0, firstUncommittedSlot nd, t))"
    by (unfold isMessageFrom'_def isMessageFrom_def, auto simp add: PublishResponse'_fromTo)

  note PublishResponse' = PublishResponse'_fromTo PublishResponse'_from

  have v_eq[simp]: "v' = v" by (intro ext, auto simp add: v'_def v_def)
  have v\<^sub>c_eq[simp]: "v\<^sub>c' = v\<^sub>c" by (intro ext, auto simp add: v\<^sub>c'_def v\<^sub>c_def)
  have isCommitted_eq[simp]: "isCommitted' = isCommitted" by (intro ext, auto simp add: isCommitted'_def isCommitted_def)
  have committedTo_eq[simp]: "committed\<^sub><' = committed\<^sub><" by (intro ext, auto simp add: committedTo'_def committedTo_def)
  have era\<^sub>i_eq[simp]: "era\<^sub>i' = era\<^sub>i" by (intro ext, auto simp add: era\<^sub>i'_def era\<^sub>i_def)
  have reconfig_eq[simp]: "reconfig' = reconfig" by (intro ext, auto simp add: reconfig'_def reconfig_def)
  have Q_eq[simp]: "Q' = Q" using reconfig_eq v\<^sub>c_eq Q'_def Q_def by blast

  show ?thesis
    apply (intro zenImplI)
                        apply (unfold message_simps property_simps committedTo_eq era\<^sub>i_eq Q_eq electionValueState_simps)
  proof -
    show "zen messages'"
    proof (unfold messages', intro send_PublishResponse [OF sent] allI impI)
      fix i' t' a'
      assume "n\<^sub>0 \<midarrow>\<langle> JoinRequest i' t' a' \<rangle>\<leadsto>"
      from JoinRequest_currentTerm [OF this] True show "t' \<le> t" using nd_def by auto
    qed

    from nodesIdentified show "\<And>n. currentNode (nodeState n) = n".
    from committedToLocalCheckpoint show "\<And>n. committed\<^sub>< (firstUncommittedSlot (nodeState n))".
    from eraMatchesLocalCheckpoint show "\<And>n. currentEra (nodeState n) = era\<^sub>i (firstUncommittedSlot (nodeState n))".
    from isQuorum_firstUncommittedSlot show "\<And>n. {q. isQuorum (nodeState n) q} = Q (era\<^sub>i (firstUncommittedSlot (nodeState n)))".
    from JoinRequest_currentTerm show "\<And>n i t a. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)" .
    from JoinRequest_slot_function show "\<And>n i i' t a a'. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto> \<Longrightarrow> n \<midarrow>\<langle> JoinRequest i' t a' \<rangle>\<leadsto> \<Longrightarrow> i = i'" .
    from PublishRequest_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)" .
    from PublishRequest_currentTerm_applyRequested show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> publishPermitted (nodeState n) \<Longrightarrow> t < currentTerm (nodeState n)" .
    from electionWon_isQuorum show "\<And>n. electionWon (nodeState n) \<Longrightarrow> isQuorum (nodeState n) (joinVotes (nodeState n))" .
    from electionWon_era show "\<And>n. electionWon (nodeState n) \<Longrightarrow> era\<^sub>t (currentTerm (nodeState n)) = era\<^sub>i (firstUncommittedSlot (nodeState n))".
    from electionValue_Free show "\<And>n n'. electionValueState (nodeState n) = ElectionValueFree \<Longrightarrow>
            n' \<in> joinVotes (nodeState n) \<Longrightarrow> (n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) None \<rangle>\<rightarrow> (OneNode n))
             \<or> (\<exists>i<firstUncommittedSlot (nodeState n). \<exists>a. n' \<midarrow>\<langle> JoinRequest i (currentTerm (nodeState n)) a \<rangle>\<rightarrow> (OneNode n))".

    from joinVotes show "\<And>n n'. n' \<in> joinVotes (nodeState n) \<Longrightarrow> promised' (firstUncommittedSlot (nodeState n)) n' n (currentTerm (nodeState n))"
      by (simp add: promised'_def)

    from publishVotes show "\<And>n n'. n' \<in> publishVotes (nodeState n) \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) \<rangle>\<leadsto>'"
      by (auto simp add: PublishResponse')

    fix n

    from nothingAcceptedInLaterSlots
    show "\<And>i t. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>'"
      by (cases "n = n\<^sub>0", simp_all add: PublishResponse' nd_def)

    from lastAccepted_None show "\<And>t. lastAcceptedTerm (nodeState' n) = None \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>'"
      by (cases "n = n\<^sub>0", simp_all add: PublishResponse' nodeState'_def)

    from lastAccepted_Some_sent sent
    show "\<And>t. lastAcceptedTerm (nodeState' n) = Some t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>'"
      by (cases "n = n\<^sub>0", auto simp add: PublishResponse' nd_def nodeState'_def)

    show "\<And>t t'. lastAcceptedTerm (nodeState' n) = Some t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t' \<rangle>\<leadsto>' \<Longrightarrow> t' \<le> t"
    proof (cases "n = n\<^sub>0")
      case False
      with lastAccepted_Some_max
      show "\<And>t t'. lastAcceptedTerm (nodeState' n) = Some t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t' \<rangle>\<leadsto>' \<Longrightarrow> t' \<le> t"
        by (auto simp add: PublishResponse' nodeState'_def)
    next
      case True note n_eq = this
      fix t' t''
      assume "lastAcceptedTerm (nodeState' n) = Some t'"
      hence t': "t' = t"
        by (simp add: n_eq nodeState'_def)

      assume "n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t'' \<rangle>\<leadsto>'"
      hence "n\<^sub>0 \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n\<^sub>0)) t'' \<rangle>\<leadsto> \<or> t'' = t"
        by (simp add: PublishResponse' n_eq nd_def t')

      thus "t'' \<le> t'"
      proof (elim disjE)
        assume "t'' = t" with t' show ?thesis by simp
      next
        assume pr: "n\<^sub>0 \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n\<^sub>0)) t'' \<rangle>\<leadsto>"
        with lastAccepted_None
        have "lastAcceptedTerm (nodeState n\<^sub>0) \<noteq> None" by metis
        then obtain t''' where t''': "lastAcceptedTerm (nodeState n\<^sub>0) = Some t'''" by blast
        from lastAccepted_Some_max [OF t''' pr] precondition t'''
        show ?thesis by (auto simp add: t' nd_def)
      qed
    qed

    from lastAccepted_Some_value sent precondition
    show "\<And>t. lastAcceptedTerm (nodeState' n) = Some t \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t (lastAcceptedValue (nodeState' n)) \<rangle>\<leadsto>"
      by (cases "n = n\<^sub>0", auto simp add: PublishResponse' nodeState'_def nd_def)

    show "electionValueState (nodeState n) \<noteq> ElectionValueFree \<Longrightarrow> \<exists>n'\<in>joinVotes (nodeState n). \<exists>t t'. lastAcceptedTerm (nodeState' n) = Some t \<and> t' \<le> t \<and> n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) (Some t') \<rangle>\<rightarrow> (OneNode n)"
      apply (cases "n = n\<^sub>0")
       apply (auto simp add: nodeState'_def nd_def)
       apply (metis dual_order.strict_implies_order dual_order.trans isMessageFromTo_def nd_def precondition zen.JoinRequest_Some_lt zenImpl.electionValue_not_Free zenImpl_axioms zen_axioms)
      using electionValue_not_Free by auto

  next
    fix n n' a'
    assume not_Free: "electionValueState (nodeState n) \<noteq> ElectionValueFree"
    assume n'_vote: "n' \<in> joinVotes (nodeState n)"
    assume n'_sent: "n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) a' \<rangle>\<rightarrow> (OneNode n)"

    show "maxTermOption a' (lastAcceptedTerm (nodeState' n)) = lastAcceptedTerm (nodeState' n)"
    proof (cases "n = n\<^sub>0")
      case False
      with not_Free n'_vote n'_sent electionValue_not_Free_max
      show ?thesis by (simp add: nodeState'_def)
    next
      case True note n_eq = this
      from not_Free n'_vote n'_sent electionValue_not_Free_max
      have 1: "maxTermOption a' (lastAcceptedTerm (nodeState n\<^sub>0)) = lastAcceptedTerm (nodeState n\<^sub>0)"
        by (simp add: n_eq)

      show ?thesis
      proof (cases "lastAcceptedTerm (nodeState n\<^sub>0)")
        case None
        with 1 show ?thesis by simp
      next
        case (Some t') note Some1 = this
        from Some precondition have t't: "t' \<le> t" by (simp add: nd_def)
        show ?thesis
        proof (cases a')
          case None thus ?thesis by simp
        next
          case (Some t'')
          from Some 1 Some1 have "t'' \<le> t'"
            by (cases "t'' \<le> t'", auto simp add: max_def)
          with t't have "t'' \<le> t" by simp
          thus ?thesis by (simp add: n_eq Some nodeState'_def max_def)
        qed
      qed
    qed

  next
    fix n
    assume forced': "electionValueState (nodeState' n) = ElectionValueForced"
    show "\<exists>n'\<in>joinVotes (nodeState n). n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) (lastAcceptedTerm (nodeState' n)) \<rangle>\<rightarrow> (OneNode n)"
    proof (cases "n = n\<^sub>0")
      case False with forced' electionValue_Forced show ?thesis by (simp add: nodeState'_def)
    next
      case True note n_eq = this
      from forced' have "electionValueState (nodeState n\<^sub>0) = ElectionValueForced
        \<and> lastAcceptedTerm nd = Some t"
        by (cases "lastAcceptedTerm nd \<noteq> Some t \<and> electionValueState nd = ElectionValueForced",
            simp_all add: n_eq nodeState'_def electionValueState', simp add: nd_def)

      hence forced: "electionValueState (nodeState n\<^sub>0) = ElectionValueForced"
        and unchanged: "lastAcceptedTerm nd = Some t"
        by auto

      with electionValue_Forced [of n\<^sub>0]
      show ?thesis
        unfolding nodeState'_def
        by (auto simp add: n_eq nd_def)
    qed
  qed
qed

lemma (in zenStep) commitIfQuorate_invariants:
  fixes s i t
  defines "result \<equiv> commitIfQuorate nd"
  assumes nd': "nd' = fst result"
  assumes messages': "messages' = send broadcast result"
  shows "zenImpl messages' nodeState'"
proof (cases "isQuorum nd (publishVotes nd)")
  case False
  hence [simp]: "result = (nd, None)"
    by (simp add: result_def commitIfQuorate_def)

  have [simp]: "messages' = messages"
    by (simp add: messages')

  have [simp]: "nodeState' = nodeState"
    unfolding nodeState'_def
    by (intro ext, simp add: nd' nd_def)

  from zenImpl_axioms show ?thesis by simp

next
  case True note isQuorum = this

  hence result: "result = (nd, Some (ApplyCommit (firstUncommittedSlot nd) (currentTerm nd)))"
    by (simp add: result_def commitIfQuorate_def)

  have nodeState': "nodeState' = nodeState"
    unfolding nodeState'_def
    by (intro ext, simp add: nd' nd_def result)

  have messages': "messages' = insert \<lparr> sender = n\<^sub>0, destination = Broadcast, payload = ApplyCommit (firstUncommittedSlot nd) (currentTerm nd) \<rparr> messages"
    by (simp add: messages' result broadcast_def)

  have message_simps[simp]:
    "\<And>s d i t. (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<rightarrow> d)"
    "\<And>s d i t x. (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>s d i t a. (s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<rightarrow> d)"
    "\<And>d i t. (\<langle> PublishResponse i t \<rangle>\<rightarrow>' d) = (\<langle> PublishResponse i t \<rangle>\<rightarrow> d)"
    "\<And>d i t x. (\<langle> PublishRequest i t x \<rangle>\<rightarrow>' d) = (\<langle> PublishRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>d i t a. (\<langle> JoinRequest i t a \<rangle>\<rightarrow>' d) = (\<langle> JoinRequest i t a \<rangle>\<rightarrow> d)"
    "\<And>s i t. (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>') = (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>)"
    "\<And>s i t x. (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>') = (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>)"
    "\<And>s i t a. (s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>') = (s \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto>)"
    "\<And>i t. (\<langle> PublishResponse i t \<rangle>\<leadsto>') = (\<langle> PublishResponse i t \<rangle>\<leadsto>)"
    "\<And>i t x. (\<langle> PublishRequest i t x \<rangle>\<leadsto>') = (\<langle> PublishRequest i t x \<rangle>\<leadsto>)"
    "\<And>i t a. (\<langle> JoinRequest i t a \<rangle>\<leadsto>') = (\<langle> JoinRequest i t a \<rangle>\<leadsto>)"
    by (unfold isMessageFromTo'_def isMessageTo'_def isMessageFrom'_def isMessage'_def,
        auto simp add: messages' isMessageFromTo_def isMessageTo_def isMessageFrom_def isMessage_def)

  have ApplyCommit_fromTo: "\<And>s d i t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = ((s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)
      \<or> (s, i, t, d) = (n\<^sub>0, firstUncommittedSlot nd, currentTerm nd, Broadcast))"
    unfolding isMessageFromTo_def isMessageFromTo'_def
    by (auto simp add: messages')

  have ApplyCommit_from: "\<And>s i t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<leadsto>') = ((s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<leadsto>)
      \<or> (s, i, t) = (n\<^sub>0, firstUncommittedSlot nd, currentTerm nd))"
    unfolding isMessageFrom_def isMessageFrom'_def by (auto simp add: ApplyCommit_fromTo)

  have ApplyCommit_to: "\<And>d i t. (\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = ((\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)
      \<or> (i, t, d) = (firstUncommittedSlot nd, currentTerm nd, Broadcast))"
    unfolding isMessageTo_def isMessageTo'_def
    by (auto simp add: ApplyCommit_fromTo)

  have ApplyCommit_any: "\<And>i t. (\<langle> ApplyCommit i t \<rangle>\<leadsto>') = ((\<langle> ApplyCommit i t \<rangle>\<leadsto>)
      \<or> (i, t) = (firstUncommittedSlot nd, currentTerm nd))"
    unfolding isMessage_def isMessage'_def by (auto simp add: ApplyCommit_from)

  note ApplyCommit' = ApplyCommit_any ApplyCommit_from ApplyCommit_fromTo ApplyCommit_to

  from committedToLocalCheckpoint
  have committedTo_current: "committed\<^sub>< (firstUncommittedSlot nd)"
    by (simp add: nd_def)

  have isCommitted_eq: "\<And>i. isCommitted' i = (isCommitted i \<or> i = firstUncommittedSlot nd)"
    using isCommitted'_def isCommitted_def by (auto simp add: ApplyCommit')

  have committedTo_eq: "\<And>i. committed\<^sub><' i = ((committed\<^sub>< i) \<or> (i = Suc (firstUncommittedSlot nd)))"
  proof -
    fix i
    show "?thesis i"
    proof (cases "isCommitted (firstUncommittedSlot nd)")
      case True with isCommitted_eq have 1: "isCommitted' = isCommitted" by (intro ext, auto)
      from True isCommitted_committedTo_Suc have 2: "committed\<^sub>< (Suc (firstUncommittedSlot nd))" by simp
      from 1 2 show ?thesis by (simp add: committedTo'_def committedTo_def, blast)
    next
      case False
      with committedTo_current isCommitted_committedTo
      have isCommitted_lt[simp]: "\<And>j. isCommitted j = (j < firstUncommittedSlot nd)"
        using committedTo_def nat_neq_iff by blast
      have isCommitted'_le[simp]: "\<And>j. isCommitted' j = (j \<le> firstUncommittedSlot nd)"
        by (auto simp add: isCommitted_eq)
      show ?thesis
        by (simp add: committedTo'_def committedTo_def, auto, presburger)
    qed
  qed

  have v_eq[simp]: "v' = v" by (intro ext, auto simp add: v'_def v_def)

  have zen': "zen messages'"
  proof (unfold messages', intro send_ApplyCommit ballI)
    from isQuorum_firstUncommittedSlot isQuorum
    have publishVotes_Q: "publishVotes nd \<in> Q (era\<^sub>i (firstUncommittedSlot nd))"
      by (auto simp add: nd_def)

    hence publishVotes_nonempty: "publishVotes nd \<noteq> {}"
      by (intro Q_members_nonempty)
    then obtain n' where n'_vote: "n' \<in> publishVotes (nodeState n\<^sub>0)" unfolding nd_def by blast

    with publishVotes
    have "n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n\<^sub>0)) (currentTerm (nodeState n\<^sub>0)) \<rangle>\<leadsto>"
      by simp

    from PublishResponse_era [OF this] publishVotes_Q
    show "publishVotes nd \<in> Q (era\<^sub>t (currentTerm nd))"
      by (simp add: nd_def)

    from publishVotes show "\<And>s. s \<in> publishVotes nd \<Longrightarrow> s \<midarrow>\<langle> PublishResponse (firstUncommittedSlot nd) (currentTerm nd) \<rangle>\<leadsto>"
      by (simp add: nd_def)
  qed

  have v\<^sub>c_eq: "\<And>i. isCommitted i \<Longrightarrow> v\<^sub>c' i = v\<^sub>c i"
  proof -
    fix i assume "isCommitted i"
    then obtain t where committed: "\<langle> ApplyCommit i t \<rangle>\<leadsto>" unfolding isCommitted_def by blast
    hence committed': "\<langle> ApplyCommit i t \<rangle>\<leadsto>'" by (simp add: ApplyCommit')

    have "v\<^sub>c i = v i t" by (intro ApplyCommit_v\<^sub>c committed)
    moreover from committed'
    have "v\<^sub>c' i = v' i t" by (unfold v\<^sub>c'_def v'_def isMessage'_def isMessageFrom'_def isMessageFromTo'_def, intro zen.ApplyCommit_v\<^sub>c [OF zen'])
    ultimately show "?thesis i" by simp
  qed

  have era\<^sub>i_eq: "\<And>i. committed\<^sub>< i \<Longrightarrow> era\<^sub>i' i = era\<^sub>i i"
  proof -
    fix i assume "committed\<^sub>< i"
    hence "\<And>j. (j < i \<and> isReconfiguration (v\<^sub>c' j)) = (j < i \<and> isReconfiguration (v\<^sub>c j))"
      unfolding committedTo_def using v\<^sub>c_eq by metis
    thus "?thesis i" by (unfold era\<^sub>i'_def era\<^sub>i_def, simp)
  qed

  from committedToLocalCheckpoint
  have era\<^sub>i_firstUncommittedSlot: "\<And>n. era\<^sub>i' (firstUncommittedSlot (nodeState n)) = era\<^sub>i (firstUncommittedSlot (nodeState n))"
    by (intro era\<^sub>i_eq)

  have reconfig_eq: "\<And>e i. committed\<^sub>< i \<Longrightarrow> e < era\<^sub>i i \<Longrightarrow> reconfig' e = reconfig e"
  proof -
    fix e i assume a: "committed\<^sub>< i" "e < era\<^sub>i i"

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

  have Q_eq: "\<And>e i. committed\<^sub>< i \<Longrightarrow> e \<le> era\<^sub>i i \<Longrightarrow> Q' e = Q e"
  proof -
    fix e i assume a: "committed\<^sub>< i" "e \<le> era\<^sub>i i"
    thus "Q' e = Q e" 
    proof (cases e)
      case e\<^sub>0 thus ?thesis by (simp add: Q_def Q'_def)
    next
      case (nextEra e')
      with a have lt: "e' < era\<^sub>i i" by (simp add: less_Era_def less_eq_Era_def)

      from a lt have reconfig_eq[simp]: "reconfig' e' = reconfig e'"
        by (intro reconfig_eq)

      from a lt
      have v\<^sub>c_eq[simp]: "v\<^sub>c' (reconfig e') = v\<^sub>c (reconfig e')"
        by (intro v\<^sub>c_eq reconfig_isCommitted)

      show ?thesis unfolding Q_def Q'_def nextEra by simp
    qed
  qed

  have Q_era_eq: "\<And>n. Q' (era\<^sub>i (firstUncommittedSlot (nodeState n))) = Q (era\<^sub>i (firstUncommittedSlot (nodeState n)))"
  proof (intro Q_eq)
    from committedToLocalCheckpoint
    show "\<And>n. committed\<^sub>< (firstUncommittedSlot (nodeState n))".
    show "\<And>n. era\<^sub>i (firstUncommittedSlot (nodeState n)) \<le> era\<^sub>i (firstUncommittedSlot (nodeState n))" by simp
  qed

  note zen.consistent [OF zen']

  show ?thesis
    apply (intro zenImplI)
                        apply (unfold nodeState' message_simps era\<^sub>i_firstUncommittedSlot Q_era_eq)
  proof -
    from zen' show "zen messages'" .
    from nodesIdentified show "\<And>n. currentNode (nodeState n) = n".
    from eraMatchesLocalCheckpoint show "\<And>n. currentEra (nodeState n) = era\<^sub>i (firstUncommittedSlot (nodeState n))".
    from isQuorum_firstUncommittedSlot show "\<And>n. {q. isQuorum (nodeState n) q} = Q (era\<^sub>i (firstUncommittedSlot (nodeState n)))".
    from nothingAcceptedInLaterSlots show "\<And>i n t. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>" .
    from lastAccepted_None show "\<And>n t. lastAcceptedTerm (nodeState n) = None \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>" .
    from lastAccepted_Some_sent show "\<And>n t. lastAcceptedTerm (nodeState n) = Some t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>" .
    from lastAccepted_Some_value show "\<And>n t. lastAcceptedTerm (nodeState n) = Some t \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t (lastAcceptedValue (nodeState n)) \<rangle>\<leadsto>" .
    from lastAccepted_Some_max show "\<And>n t t'. lastAcceptedTerm (nodeState n) = Some t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t' \<rangle>\<leadsto> \<Longrightarrow> t' \<le> t" .
    from JoinRequest_currentTerm show "\<And>n i t a. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)" .
    from JoinRequest_slot_function show "\<And>n i i' t a a'. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto> \<Longrightarrow> n \<midarrow>\<langle> JoinRequest i' t a' \<rangle>\<leadsto> \<Longrightarrow> i = i'" .
    from PublishRequest_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)" .
    from PublishRequest_currentTerm_applyRequested show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> publishPermitted (nodeState n) \<Longrightarrow> t < currentTerm (nodeState n)" .

    from joinVotes show "\<And>n n'. n' \<in> joinVotes (nodeState n) \<Longrightarrow> promised' (firstUncommittedSlot (nodeState n)) n' n (currentTerm (nodeState n))"
      by (simp add: promised'_def)

    from electionWon_isQuorum show "\<And>n. electionWon (nodeState n) \<Longrightarrow> isQuorum (nodeState n) (joinVotes (nodeState n))" .
    from electionWon_era show "\<And>n. electionWon (nodeState n) \<Longrightarrow> era\<^sub>t (currentTerm (nodeState n)) = era\<^sub>i (firstUncommittedSlot (nodeState n))" .
    from electionValue_Free show "\<And>n n'. electionValueState (nodeState n) = ElectionValueFree \<Longrightarrow>
            n' \<in> joinVotes (nodeState n) \<Longrightarrow> (n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) None \<rangle>\<rightarrow> (OneNode n))
             \<or> (\<exists>i<firstUncommittedSlot (nodeState n). \<exists>a. n' \<midarrow>\<langle> JoinRequest i (currentTerm (nodeState n)) a \<rangle>\<rightarrow> (OneNode n))".

    from electionValue_not_Free show "\<And>n. electionValueState (nodeState n) \<noteq> ElectionValueFree \<Longrightarrow> \<exists>n'\<in>joinVotes (nodeState n). \<exists>t t'. lastAcceptedTerm (nodeState n) = Some t \<and> t' \<le> t \<and> n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) (Some t') \<rangle>\<rightarrow> (OneNode n)" .
    from electionValue_not_Free_max show "\<And>n n' a'. electionValueState (nodeState n) \<noteq> ElectionValueFree \<Longrightarrow>
               n' \<in> joinVotes (nodeState n) \<Longrightarrow> n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) a' \<rangle>\<rightarrow> (OneNode n) \<Longrightarrow> maxTermOption a' (lastAcceptedTerm (nodeState n)) = lastAcceptedTerm (nodeState n)".
    from electionValue_Forced show "\<And>n. electionValueState (nodeState n) = ElectionValueForced \<Longrightarrow> \<exists>n'\<in>joinVotes (nodeState n). n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) (lastAcceptedTerm (nodeState n)) \<rangle>\<rightarrow> (OneNode n)".
    from publishVotes show "\<And>n n'. n' \<in> publishVotes (nodeState n) \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) \<rangle>\<leadsto>" .

    from committedToLocalCheckpoint show "\<And>n. committed\<^sub><' (firstUncommittedSlot (nodeState n))" by (simp add: committedTo_eq)
  qed
qed

lemma (in zenStep) addPublishVote_invariants:
  assumes nd': "nd' = nd \<lparr> publishVotes := insert s (publishVotes nd) \<rparr>"
  assumes messages': "messages' = messages"
  assumes sent: "s \<midarrow>\<langle> PublishResponse (firstUncommittedSlot nd) (currentTerm nd) \<rangle>\<leadsto>"
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
    "\<And>n. lastAcceptedTerm (nodeState' n) = lastAcceptedTerm (nodeState n)"
    "\<And>n. lastAcceptedValue (nodeState' n) = lastAcceptedValue (nodeState n)"
    "\<And>n. currentTerm (nodeState' n) = currentTerm (nodeState n)"
    "\<And>n. publishPermitted (nodeState' n) = publishPermitted (nodeState n)"
    "\<And>n. joinVotes (nodeState' n) = joinVotes (nodeState n)"
    "\<And>n. electionWon (nodeState' n) = electionWon (nodeState n)"
    "\<And>n. electionValueState (nodeState' n) = electionValueState (nodeState n)"
    by (unfold nodeState'_def, auto simp add: nd_def isQuorum_def nd' addElectionVote_def Let_def)

  have v_eq[simp]: "v' = v" by (intro ext, auto simp add: v'_def v_def)
  have v\<^sub>c_eq[simp]: "v\<^sub>c' = v\<^sub>c" by (intro ext, auto simp add: v\<^sub>c'_def v\<^sub>c_def)
  have isCommitted_eq[simp]: "isCommitted' = isCommitted" by (intro ext, auto simp add: isCommitted'_def isCommitted_def)
  have committedTo_eq[simp]: "committed\<^sub><' = committed\<^sub><" by (intro ext, auto simp add: committedTo'_def committedTo_def)
  have era\<^sub>i_eq[simp]: "era\<^sub>i' = era\<^sub>i" by (intro ext, auto simp add: era\<^sub>i'_def era\<^sub>i_def)
  have reconfig_eq[simp]: "reconfig' = reconfig" by (intro ext, auto simp add: reconfig'_def reconfig_def)
  have Q_eq[simp]: "Q' = Q" using reconfig_eq v\<^sub>c_eq Q'_def Q_def by blast
  have promised_eq[simp]: "promised' = promised" by (intro ext, auto simp add: promised'_def promised_def)

  show ?thesis
    apply (intro zenImplI)
                        apply (unfold property_simps era\<^sub>i_eq Q_eq message_simps committedTo_eq promised_eq)
  proof -
    from zen_axioms messages' show "zen messages'" by simp

    from nodesIdentified show "\<And>n. currentNode (nodeState n) = n".
    from eraMatchesLocalCheckpoint show "\<And>n. currentEra (nodeState n) = era\<^sub>i (firstUncommittedSlot (nodeState n))".
    from committedToLocalCheckpoint show "\<And>n. committed\<^sub>< (firstUncommittedSlot (nodeState n))" .
    from isQuorum_firstUncommittedSlot show "\<And>n. {q. isQuorum (nodeState n) q} = Q (era\<^sub>i (firstUncommittedSlot (nodeState n)))".
    from nothingAcceptedInLaterSlots show "\<And>i n t. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>" .
    from lastAccepted_None show "\<And>n t. lastAcceptedTerm (nodeState n) = None \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>" .
    from lastAccepted_Some_sent show "\<And>n t. lastAcceptedTerm (nodeState n) = Some t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>" .
    from lastAccepted_Some_value show "\<And>n t. lastAcceptedTerm (nodeState n) = Some t \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t (lastAcceptedValue (nodeState n)) \<rangle>\<leadsto>" .
    from lastAccepted_Some_max show "\<And>n t t'. lastAcceptedTerm (nodeState n) = Some t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t' \<rangle>\<leadsto> \<Longrightarrow> t' \<le> t" .
    from JoinRequest_currentTerm show "\<And>n i t a. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)" .
    from JoinRequest_slot_function show "\<And>n i i' t a a'. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto> \<Longrightarrow> n \<midarrow>\<langle> JoinRequest i' t a' \<rangle>\<leadsto> \<Longrightarrow> i = i'" .
    from PublishRequest_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)" .
    from PublishRequest_currentTerm_applyRequested show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> publishPermitted (nodeState n) \<Longrightarrow> t < currentTerm (nodeState n)" .

    from joinVotes show "\<And>n n'. n' \<in> joinVotes (nodeState n) \<Longrightarrow> promised (firstUncommittedSlot (nodeState n)) n' n (currentTerm (nodeState n))"
      by (auto simp add: promised_def)

    from electionWon_isQuorum show "\<And>n. electionWon (nodeState n) \<Longrightarrow> isQuorum (nodeState n) (joinVotes (nodeState n))" .
    from electionWon_era show "\<And>n. electionWon (nodeState n) \<Longrightarrow> era\<^sub>t (currentTerm (nodeState n)) = era\<^sub>i (firstUncommittedSlot (nodeState n))" .
    from electionValue_Free show "\<And>n n'. electionValueState (nodeState n) = ElectionValueFree \<Longrightarrow>
            n' \<in> joinVotes (nodeState n) \<Longrightarrow> (n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) None \<rangle>\<rightarrow> (OneNode n))
             \<or> (\<exists>i<firstUncommittedSlot (nodeState n). \<exists>a. n' \<midarrow>\<langle> JoinRequest i (currentTerm (nodeState n)) a \<rangle>\<rightarrow> (OneNode n))".

    from electionValue_not_Free show "\<And>n. electionValueState (nodeState n) \<noteq> ElectionValueFree \<Longrightarrow> \<exists>n'\<in>joinVotes (nodeState n). \<exists>t t'. lastAcceptedTerm (nodeState n) = Some t \<and> t' \<le> t \<and> n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) (Some t') \<rangle>\<rightarrow> (OneNode n)" .
    from electionValue_not_Free_max show "\<And>n n' a'. electionValueState (nodeState n) \<noteq> ElectionValueFree \<Longrightarrow>
               n' \<in> joinVotes (nodeState n) \<Longrightarrow> n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) a' \<rangle>\<rightarrow> (OneNode n) \<Longrightarrow> maxTermOption a' (lastAcceptedTerm (nodeState n)) = lastAcceptedTerm (nodeState n)".
    from electionValue_Forced show "\<And>n. electionValueState (nodeState n) = ElectionValueForced \<Longrightarrow> \<exists>n'\<in>joinVotes (nodeState n). n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) (lastAcceptedTerm (nodeState n)) \<rangle>\<rightarrow> (OneNode n)".

    fix n
    from sent publishVotes
    show "\<And>n'. n' \<in> publishVotes (nodeState' n) \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) \<rangle>\<leadsto>"
      unfolding nodeState'_def
      by (cases "n = n\<^sub>0", simp_all add: nd' nd_def, blast)
  qed
qed

lemma (in zenStep) handlePublishResponse_invariants:
  fixes s i t
  defines "result \<equiv> handlePublishResponse s i t nd"
  assumes nd': "nd' = fst result"
  assumes messages': "messages' = send broadcast result"
  assumes sent: "s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>"
  shows "zenImpl messages' nodeState'"
proof (cases "i = firstUncommittedSlot nd \<and> t = currentTerm nd")
  case False
  hence [simp]: "result = (nd, None)"
    by (auto simp add: result_def handlePublishResponse_def Let_def)

  have [simp]: "messages' = messages"
    by (simp add: messages')

  have [simp]: "nodeState' = nodeState"
    unfolding nodeState'_def
    by (intro ext, simp add: nd' nd_def)

  from zenImpl_axioms show ?thesis by simp

next
  case True
  hence i: "i = firstUncommittedSlot nd"
    and t: "t = currentTerm nd"
    by simp_all

  define newVotes where "newVotes \<equiv> insert s (publishVotes nd)"

  define nd1 where "nd1 \<equiv> nd \<lparr>publishVotes := newVotes\<rparr>"
  define nodeState1 where "nodeState1 \<equiv> \<lambda>n. if n = n\<^sub>0 then nd1 else nodeState n"

  have nodeState1: "nodeState1 = zenStep.nodeState' nodeState n\<^sub>0 nd1"
    by (intro ext, simp add: zenStep.nodeState'_def [OF zenStep_axioms] nodeState1_def)

  note zenStep.addPublishVote_invariants

  have zenImpl1: "zenImpl messages nodeState1"
     unfolding nodeState1
 proof (intro_locales, intro zenImpl.axioms zenStep.addPublishVote_invariants)
    show "nd1 = nd\<lparr>publishVotes := insert s (publishVotes nd)\<rparr>"
      by (simp add: nd1_def newVotes_def)
    show "messages = messages"..
    from sent i t
    show "\<exists>d. \<lparr>sender = s, destination = d, payload = PublishResponse (firstUncommittedSlot nd) (currentTerm nd)\<rparr> \<in> messages"
      unfolding isMessageFrom_def isMessageFromTo_def by simp
    from message show "zenStep messages nodeState messages message" by (unfold_locales, simp_all)
  qed

  have zenStep1: "zenStep messages nodeState1 messages' message"
  proof (intro_locales)
    from zenImpl1 show "zenImpl_axioms messages nodeState1" by (simp add: zenImpl_def)
    from zenStep_axioms show "zenStep_axioms messages messages' message" by (simp add: zenStep_def)
  qed

  have result: "result = commitIfQuorate nd1"
    by (simp add: result_def handlePublishResponse_def i t newVotes_def nd1_def)

  have nodeState': "nodeState' = zenStep.nodeState' nodeState1 n\<^sub>0 nd'"
    unfolding nodeState'_def zenStep.nodeState'_def [OF zenStep1]
    by (intro ext, simp add: nodeState1_def)

  have nd1[simp]: "zenStep.nd nodeState1 n\<^sub>0 = nd1"
    by (simp add: zenStep.nd_def [OF zenStep1], simp add: nodeState1_def)

  show ?thesis
    unfolding nodeState'
    by (intro zenStep.commitIfQuorate_invariants [OF zenStep1], simp_all add: nd' messages' result)
qed

lemma (in zenStep) handleReboot_invariants:
  assumes nd': "nd' = handleReboot nd"
  assumes messages': "messages' = messages"
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
    "\<And>n. lastAcceptedTerm (nodeState' n) = lastAcceptedTerm (nodeState n)"
    "\<And>n. lastAcceptedValue (nodeState' n) = lastAcceptedValue (nodeState n)"
    "\<And>n. currentTerm (nodeState' n) = currentTerm (nodeState n)"
    by (unfold nodeState'_def, auto simp add: nd_def isQuorum_def nd' handleReboot_def Let_def)

  have reset_states_simps[simp]:
    "publishPermitted nd' = False" "joinVotes nd' = {}" "electionWon nd' = False" "electionValueState nd' = ElectionValueFree"
    "publishVotes nd' = {}"
    by (auto simp add: nd' handleReboot_def)

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
  proof -
    from zen_axioms show "zen messages'" by (simp add: messages')
    from nodesIdentified show "\<And>n. currentNode (nodeState n) = n".
    from committedToLocalCheckpoint show "\<And>n. committed\<^sub>< (firstUncommittedSlot (nodeState n))".
    from eraMatchesLocalCheckpoint show "\<And>n. currentEra (nodeState n) = era\<^sub>i (firstUncommittedSlot (nodeState n))".
    from isQuorum_firstUncommittedSlot show "\<And>n. {q. isQuorum (nodeState n) q} = Q (era\<^sub>i (firstUncommittedSlot (nodeState n)))".
    from nothingAcceptedInLaterSlots show "\<And>i n t. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>" .
    from lastAccepted_None show "\<And>n t. lastAcceptedTerm (nodeState n) = None \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>" .
    from lastAccepted_Some_sent show "\<And>n t. lastAcceptedTerm (nodeState n) = Some t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>" .
    from lastAccepted_Some_value show "\<And>n t. lastAcceptedTerm (nodeState n) = Some t \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t (lastAcceptedValue (nodeState n)) \<rangle>\<leadsto>" .
    from lastAccepted_Some_max show "\<And>n t t'. lastAcceptedTerm (nodeState n) = Some t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t' \<rangle>\<leadsto> \<Longrightarrow> t' \<le> t" .
    from JoinRequest_currentTerm show "\<And>n i t a. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)" .
    from JoinRequest_slot_function show "\<And>n i i' t a a'. n \<midarrow>\<langle> JoinRequest i t a \<rangle>\<leadsto> \<Longrightarrow> n \<midarrow>\<langle> JoinRequest i' t a' \<rangle>\<leadsto> \<Longrightarrow> i = i'" .
    from PublishRequest_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)" .

    fix n

    from PublishRequest_currentTerm_applyRequested
    show "\<And>t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> publishPermitted (nodeState' n) \<Longrightarrow> t < currentTerm (nodeState n)"
      by (cases "n = n\<^sub>0", auto simp add: nodeState'_def)

    from joinVotes
    show "\<And>n'. n' \<in> joinVotes (nodeState' n) \<Longrightarrow> promised (firstUncommittedSlot (nodeState n)) n' n (currentTerm (nodeState n))"
      by (cases "n = n\<^sub>0", auto simp add: nodeState'_def promised_def)

    from electionWon_isQuorum
    show "electionWon (nodeState' n) \<Longrightarrow> isQuorum (nodeState n) (joinVotes (nodeState' n))"
      by (cases "n = n\<^sub>0", auto simp add: nodeState'_def)

    from electionWon_era
    show "electionWon (nodeState' n) \<Longrightarrow> era\<^sub>t (currentTerm (nodeState n)) = era\<^sub>i (firstUncommittedSlot (nodeState n))"
      by (cases "n = n\<^sub>0", auto simp add: nodeState'_def)

    from electionValue_Free
    show "\<And>n'. electionValueState (nodeState' n) = ElectionValueFree \<Longrightarrow>
            n' \<in> joinVotes (nodeState' n) \<Longrightarrow> (n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) None \<rangle>\<rightarrow> (OneNode n))
           \<or> (\<exists>i<firstUncommittedSlot (nodeState n). \<exists>a. n' \<midarrow>\<langle> JoinRequest i (currentTerm (nodeState n)) a \<rangle>\<rightarrow> (OneNode n))"
      by (cases "n = n\<^sub>0", auto simp add: nodeState'_def)

    from electionValue_not_Free
    show "electionValueState (nodeState' n) \<noteq> ElectionValueFree \<Longrightarrow> \<exists>n'\<in>joinVotes (nodeState' n).
      \<exists>t t'. lastAcceptedTerm (nodeState n) = Some t \<and> t' \<le> t \<and> n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) (Some t') \<rangle>\<rightarrow> (OneNode n)"
      by (cases "n = n\<^sub>0", auto simp add: nodeState'_def)

    from electionValue_not_Free_max
    show "\<And>n' a'. electionValueState (nodeState' n) \<noteq> ElectionValueFree \<Longrightarrow>
               n' \<in> joinVotes (nodeState' n) \<Longrightarrow> n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) a' \<rangle>\<rightarrow> (OneNode n) \<Longrightarrow> maxTermOption a' (lastAcceptedTerm (nodeState n)) = lastAcceptedTerm (nodeState n)"
      by (cases "n = n\<^sub>0", auto simp add: nodeState'_def)

    from electionValue_Forced
    show "electionValueState (nodeState' n) = ElectionValueForced \<Longrightarrow> \<exists>n'\<in>joinVotes (nodeState' n). n' \<midarrow>\<langle> JoinRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) (lastAcceptedTerm (nodeState n)) \<rangle>\<rightarrow> (OneNode n)"
      by (cases "n = n\<^sub>0", auto simp add: nodeState'_def)

    from publishVotes
    show "\<And>n'. n' \<in> publishVotes (nodeState' n) \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) \<rangle>\<leadsto>"
      by (cases "n = n\<^sub>0", auto simp add: nodeState'_def)
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

  have nodeState': "nodeState' = zenStep.nodeState' nodeState n\<^sub>0 (fst result)"
    by (intro ext, simp add: zenStep.nodeState'_def [OF zenStep] nodeState'_def)

  have nd[simp]: "zenStep.nd nodeState n\<^sub>0 = nd"
    by (simp add: zenStep.nd_def [OF zenStep])

  define broadcast' :: "(NodeData * Message option) \<Rightarrow> (NodeData * RoutedMessage option)" where
    "\<And>p. broadcast' p \<equiv> case p of
            (nd, Some m') \<Rightarrow> (nd, Some \<lparr>sender = currentNode nd,
                                   destination = Broadcast,
                                   payload = m' \<rparr>)
            | (nd, None) \<Rightarrow> (nd, None)"

  define respond' :: "(NodeData * Message option) \<Rightarrow> (NodeData * RoutedMessage option)" where
    "\<And>p. respond' p \<equiv> case p of
            (nd, Some m') \<Rightarrow> (nd, Some \<lparr>sender = currentNode nd,
                                   destination = OneNode (sender m),
                                   payload = m' \<rparr>)
            | (nd, None) \<Rightarrow> (nd, None)"

  have fst_broadcast[simp]: "\<And>p. fst (broadcast' p) = fst p"
    unfolding broadcast'_def by (simp add: case_prod_unfold option.case_eq_if)

  have fst_respond[simp]: "\<And>p. fst (respond' p) = fst p"
    unfolding respond'_def by (simp add: case_prod_unfold option.case_eq_if)

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
      proof (cases "currentTerm nd < t \<and> era\<^sub>t t = currentEra nd \<and> (case lastAcceptedTerm nd of None \<Rightarrow> True | Some t' \<Rightarrow> t' < t)")
        case False
        hence "result = (nd, None)"
          unfolding result_def ProcessMessage_def Let_def dest_True StartJoin
          by (simp add: handleStartJoin_def)
        thus ?thesis by (intro noop)
      next
        case True
        hence new_term: "currentTerm nd < t" and era_eq: "era\<^sub>t t = currentEra nd" by simp_all

        hence result: "result = respond' (handleStartJoin t nd)"
          unfolding result_def ProcessMessage_def Let_def dest_True StartJoin respond'_def by simp

        note zenStep.nodeState'_def zenStep.response_def zenStep.send.simps zenStep.nd_def
        note [simp] = this [OF zenStep]

        note zenStep.handleStartJoin_invariants [OF zenStep, where t = t]

        have "zenImpl messages' (zenStep.nodeState' nodeState n\<^sub>0 (fst (handleStartJoin t nd)))"
        proof (intro zenStep.handleStartJoin_invariants [OF zenStep])
          show "fst (handleStartJoin t nd) = fst (handleStartJoin t (zenStep.nd nodeState n\<^sub>0))" by simp

          from True show "messages' = zenStep.send messages (zenStep.response n\<^sub>0 m) (handleStartJoin t (zenStep.nd nodeState n\<^sub>0))"
            by (auto simp add: messages'_def result respond'_def handleStartJoin_def ensureCurrentTerm_def)
        qed
        moreover have "nodeState' = zenStep.nodeState' nodeState n\<^sub>0 (fst (handleStartJoin t nd))"
          unfolding nodeState'_def result_def ProcessMessage_def dest_True StartJoin
          by (intro ext, cases "handleStartJoin t nd", cases "snd (handleStartJoin t nd)", auto)
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
      proof (cases "i \<le> firstUncommittedSlot nd
             \<and> era\<^sub>t t = currentEra nd
             \<and> currentTerm nd \<le> t
             \<and> (currentTerm nd = t \<longrightarrow> \<not> electionWon nd)
             \<and> (maxTermOption a (lastAcceptedTerm nd) = lastAcceptedTerm nd)")
        case False
        have "result = (nd, None)"
        unfolding result_def ProcessMessage_def dest_True JoinRequest
          by (simp add: handleJoinRequest_def False)
        thus ?thesis by (intro noop)
      next
        case True
        hence True': "i \<le> firstUncommittedSlot nd"
          "era\<^sub>t t = currentEra nd"
          "currentTerm nd \<le> t"
          "currentTerm nd = t \<Longrightarrow> \<not> electionWon nd"
          "maxTermOption a (lastAcceptedTerm nd) = lastAcceptedTerm nd"
          by auto
        hence False_eq: "(i \<le> firstUncommittedSlot nd
             \<and> era\<^sub>t t = currentEra nd
             \<and> currentTerm nd \<le> t
             \<and> (currentTerm nd = t \<longrightarrow> \<not> electionWon nd)
             \<and> (maxTermOption a (lastAcceptedTerm nd) = lastAcceptedTerm nd)) = True"
          by auto

        define nd1 where "nd1 \<equiv> ensureCurrentTerm t nd"
        define nodeState1 where "\<And>n. nodeState1 n \<equiv> if n = n\<^sub>0 then nd1 else nodeState n"

        have nodeState1: "nodeState1 = zenStep.nodeState' nodeState n\<^sub>0 nd1"
          by (intro ext, simp add: zenStep.nodeState'_def [OF zenStep] nodeState1_def)

        have zenImpl1: "zenImpl messages nodeState1"
          unfolding nodeState1
        proof (intro zenStep.ensureCurrentTerm_invariants)
          from `m \<in> messages`
          show "zenStep messages nodeState messages m"
            by (intro_locales, intro zenStep_axioms.intro, simp_all)

          from `currentTerm nd \<le> t` show "currentTerm (zenStep.nd nodeState n\<^sub>0) \<le> t"
            by (simp add: zenStep.nd_def [OF zenStep])

          show "nd1 = ensureCurrentTerm t (zenStep.nd nodeState n\<^sub>0)"
            by (simp add: zenStep.nd_def [OF zenStep] nd1_def)
        qed simp

        from zenImpl1
        have zenStep1: "zenStep messages nodeState1 messages' m" by (intro zenStepI)

        define newVotes where "newVotes \<equiv> insert (sender m) (joinVotes nd1)"
        define nd2 where "nd2 \<equiv> addElectionVote (sender m) i a nd1"
        define nodeState2 where "\<And>n. nodeState2 n \<equiv> if n = n\<^sub>0 then nd2 else nodeState1 n"

        have nodeState2: "nodeState2 = zenStep.nodeState' nodeState1 n\<^sub>0 nd2"
          by (intro ext, simp add: zenStep.nodeState'_def [OF zenStep1] nodeState2_def)

        have nd1[simp]: "zenStep.nd nodeState1 n\<^sub>0 = nd1"
          by (simp add: zenStep.nd_def [OF zenStep1] nodeState1_def)

        have currentNode_nd1[simp]: "currentNode nd1 = n\<^sub>0"
          by (auto simp add: nd1_def ensureCurrentTerm_def)

        have currentTerm_nd1[simp]: "currentTerm nd1 = t"
          by (simp add: nd1_def ensureCurrentTerm_def)

        have currentEra_nd1[simp]: "currentEra nd1 = currentEra nd"
          by (simp add: nd1_def ensureCurrentTerm_def)

        have firstUncommittedSlot_nd1[simp]: "firstUncommittedSlot nd1 = firstUncommittedSlot nd"
          by (simp add: nd1_def ensureCurrentTerm_def)

        from True'
        have electionWon_nd1[simp]: "\<not> electionWon nd1"
          by (simp add: nd1_def ensureCurrentTerm_def)

        have zenImpl2: "zenImpl messages nodeState2"
          unfolding nodeState2
          using `era\<^sub>t t = currentEra nd` `i \<le> firstUncommittedSlot nd`
        proof (intro zenStep.addElectionVote_invariants)
          from `m \<in> messages` zenImpl1
          show "zenStep messages nodeState1 messages m"
            by (intro_locales, simp add: zenImpl_def, intro zenStep_axioms.intro, simp_all)

          show "nd2 = addElectionVote (sender m) i a (zenStep.nd nodeState1 n\<^sub>0)" by (simp add: nd2_def)

          from m
          show "\<lparr>sender = sender m, destination = OneNode n\<^sub>0, payload = JoinRequest i (currentTerm (zenStep.nd nodeState1 n\<^sub>0)) a\<rparr> \<in> messages"
            by (simp add: isMessageFromTo_def)

          from True' show "maxTermOption a (lastAcceptedTerm (zenStep.nd nodeState1 n\<^sub>0)) = lastAcceptedTerm (zenStep.nd nodeState1 n\<^sub>0)"
            by (simp add: nd1_def ensureCurrentTerm_def)

        qed simp_all

        from zenImpl2
        have zenStep2: "zenStep messages nodeState2 messages' m" by (intro zenStepI)

        from True'
        have "handleJoinRequest (sender m) i t a nd = publishValue (lastAcceptedValue nd2) nd2"
          apply (auto simp add: handleJoinRequest_def nd2_def nd1_def)         
          by metis
        hence result: "result = broadcast' (publishValue (lastAcceptedValue nd2) nd2)"
          unfolding result_def ProcessMessage_def dest_True JoinRequest broadcast'_def by simp

        have nodeState': "nodeState' = zenStep.nodeState' nodeState2 n\<^sub>0 (fst result)"
          by (intro ext, simp add: zenStep.nodeState'_def [OF zenStep2] nodeState2_def nodeState1_def nodeState'_def)

        have nd2[simp]: "zenStep.nd nodeState2 n\<^sub>0 = nd2"
          by (simp add: zenStep.nd_def [OF zenStep2] nodeState2_def)

        have currentNode_nd2[simp]: "currentNode nd2 = n\<^sub>0"
          by (auto simp add: nd2_def addElectionVote_def Let_def)

        show ?thesis
          unfolding nodeState'
        proof (intro zenStep.publishValue_invariants [OF zenStep2])
          show "fst result = fst (publishValue (lastAcceptedValue nd2) (zenStep.nd nodeState2 n\<^sub>0))"
            by (cases "electionWon nd2 \<and> publishPermitted nd2", simp_all add: result publishValue_def broadcast'_def)
          show "lastAcceptedValue nd2 = lastAcceptedValue (zenStep.nd nodeState2 n\<^sub>0)" by simp
          show "messages' = zenStep.send messages (zenStep.broadcast n\<^sub>0) (publishValue (lastAcceptedValue nd2) (zenStep.nd nodeState2 n\<^sub>0))"
            by (cases "electionWon nd2 \<and> publishPermitted nd2", simp_all add: messages'_def result broadcast'_def publishValue_def
              zenStep.send.simps [OF zenStep2] zenStep.broadcast_def [OF zenStep2])
        qed
      qed

    next
      case (ClientValue x)

      have result: "result = broadcast' (handleClientValue x nd)"
        unfolding result_def ProcessMessage_def ClientValue dest_True broadcast'_def by simp

      show ?thesis
      proof (cases "electionValueState nd = ElectionValueFree")
        case False
        hence "handleClientValue x nd = (nd, None)"
          by (auto simp add: handleClientValue_def)
        hence "result = (nd, None)"
          by (simp add: result broadcast'_def)
        thus ?thesis by (intro noop)
      next
        case True
        hence handleClientValue_eq[simp]: "handleClientValue x nd = publishValue x nd"
          by (auto simp add: handleClientValue_def)

        have result: "result = broadcast' (publishValue x nd)"
          unfolding result_def ProcessMessage_def ClientValue dest_True broadcast'_def by simp

        show ?thesis
          unfolding nodeState'
        proof (intro zenStep.publishValue_invariants [OF zenStep])
          show "fst result = fst (publishValue x (zenStep.nd nodeState n\<^sub>0))"
            by (simp add: result)
          show "messages' = zenStep.send messages (zenStep.broadcast n\<^sub>0) (publishValue x (zenStep.nd nodeState n\<^sub>0))"
            by (simp_all add: messages'_def result broadcast'_def publishValue_def
                zenStep.send.simps [OF zenStep] zenStep.broadcast_def [OF zenStep])
          from True show "electionValueState (zenStep.nd nodeState n\<^sub>0) = ElectionValueForced \<Longrightarrow> x = lastAcceptedValue (zenStep.nd nodeState n\<^sub>0)"
            by simp
        qed
      qed

    next
      case Reboot
      have result: "result = (handleReboot nd, None)"
        unfolding result_def ProcessMessage_def Reboot dest_True by simp

      show ?thesis
      proof (unfold nodeState', intro zenStep.handleReboot_invariants [OF zenStep])
        show "fst result = handleReboot (zenStep.nd nodeState n\<^sub>0)"
          by (simp add: result)
        show "messages' = messages"
          by (simp add: result messages'_def)
      qed

    next
      case (PublishRequest i t x)

      have result: "result = respond' (handlePublishRequest i t x nd)"
        unfolding result_def ProcessMessage_def PublishRequest dest_True by (simp add: respond'_def)

      show ?thesis
      proof (unfold nodeState', intro zenStep.handlePublishRequest_invariants [OF zenStep])
        show "fst result = fst (handlePublishRequest i t x (zenStep.nd nodeState n\<^sub>0))"
          by (simp add: result)
        show "messages' = zenStep.send messages (zenStep.response n\<^sub>0 m) (handlePublishRequest i t x (zenStep.nd nodeState n\<^sub>0))"
          by (simp_all add: messages'_def result respond'_def handlePublishRequest_def zenStep.send.simps [OF zenStep] zenStep.response_def [OF zenStep])

        from m
        show "\<exists>s d. \<lparr>sender = s, destination = d, payload = PublishRequest i t x\<rparr> \<in> messages"
          by (auto simp add: PublishRequest isMessageFromTo_def)
      qed

    next
      case (PublishResponse i t)

      have result: "result = broadcast' (handlePublishResponse (sender m) i t nd)"
        unfolding result_def ProcessMessage_def PublishResponse dest_True by (simp add: broadcast'_def)

      show ?thesis
      proof (unfold nodeState', intro zenStep.handlePublishResponse_invariants [OF zenStep])
        show "fst result = fst (handlePublishResponse (sender m) i t (zenStep.nd nodeState n\<^sub>0))"
          by (simp add: result)
        show "messages' = zenStep.send messages (zenStep.broadcast n\<^sub>0) (handlePublishResponse (sender m) i t (zenStep.nd nodeState n\<^sub>0))"
          by (simp_all add: messages'_def result broadcast'_def handlePublishResponse_def zenStep.send.simps [OF zenStep] zenStep.broadcast_def [OF zenStep] commitIfQuorate_def)

        from m
        show "\<exists>d. \<lparr>sender = sender m, destination = d, payload = PublishResponse i t\<rparr> \<in> messages"
          by (auto simp add: PublishResponse isMessageFromTo_def)
      qed

    next


      oops
end
