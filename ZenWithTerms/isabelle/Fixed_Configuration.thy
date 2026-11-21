theory Fixed_Configuration
  imports Quorum_Basics "HOL-Library.Sublist"
begin

section \<open>Fixed-configuration cluster coordination\<close>

type_synonym update = "nat \<times> nat \<times> nat"
type_synonym history = "update list"

definition epoch :: "history \<Rightarrow> nat" where
  "epoch h = (if h = [] then 0 else fst (last h))"

definition version :: "history \<Rightarrow> nat" where
  "version h = (if h = [] then 0 else fst (snd (last h)))"

definition fresher_eq :: "history \<Rightarrow> history \<Rightarrow> bool" (infix "\<preceq>" 50) where
  "a \<preceq> b \<longleftrightarrow> epoch a < epoch b \<or> epoch a = epoch b \<and> version a \<le> version b"

text \<open>
  Histories carry ghost ancestry as well as opaque state identities. The empty history
  is the common bootstrap state. Sent joins and durable acceptance receipts are
  retained, so delivery can select an old message, select it again, or ignore it.
  Election and commit steps consume quorum certificates in one step. This abstracts
  the transient vote collections and processes only successful elections and commits.
\<close>

record coordination =
  current :: "node \<Rightarrow> nat"
  accepted :: "node \<Rightarrow> history"
  joins :: "(node \<times> node \<times> nat \<times> history) set"
  leader :: "nat \<Rightarrow> node option"
  electors :: "nat \<Rightarrow> node set"
  started :: "node set"
  active :: "node set"
  tip :: "nat \<Rightarrow> history"
  published :: "history set"
  receipts :: "(node \<times> history) set"
  committed :: "history set"

definition initial :: coordination where
  "initial = \<lparr> current = (\<lambda>_. 0), accepted = (\<lambda>_. []), joins = {}, leader = (\<lambda>_. None),
      electors = (\<lambda>_. {}), started = {}, active = {}, tip = (\<lambda>_. []), published = {},
      receipts = {}, committed = {} \<rparr>"

inductive step :: "node set \<Rightarrow> coordination \<Rightarrow> coordination \<Rightarrow> bool" for V where
  join: "current s n < t \<Longrightarrow>
    step V s (s\<lparr>current := (current s)(n := t),
      joins := insert (n, c, t, accepted s n) (joins s), started := insert n (started s), active := active s - {n}\<rparr>)"
| elect: "c \<in> started s \<Longrightarrow> t = current s c \<Longrightarrow> leader s t = None \<Longrightarrow>
    majority V Q \<Longrightarrow> (\<forall>n\<in>Q. \<exists>h. (n,c,t,h) \<in> joins s \<and> h \<preceq> accepted s c) \<Longrightarrow>
    (\<exists>c' h. (c,c',t,h) \<in> joins s) \<Longrightarrow>
    step V s (s\<lparr>leader := (leader s)(t := Some c), electors := (electors s)(t := Q),
      tip := (tip s)(t := accepted s c), active := insert c (active s)\<rparr>)"
| propose: "c \<in> active s \<Longrightarrow> t = current s c \<Longrightarrow> leader s t = Some c \<Longrightarrow>
    tip s t = accepted s c \<Longrightarrow> version (tip s t) < v \<Longrightarrow>
    h = tip s t @ [(t, v, payload)] \<Longrightarrow>
    step V s (s\<lparr>tip := (tip s)(t := h), published := insert h (published s)\<rparr>)"
| accept: "h \<in> published s \<Longrightarrow> epoch h = current s n \<Longrightarrow>
    (epoch (accepted s n) < epoch h \<or>
      epoch (accepted s n) = epoch h \<and> version (accepted s n) < version h) \<Longrightarrow>
    step V s (s\<lparr>accepted := (accepted s)(n := h), receipts := insert (n,h) (receipts s)\<rparr>)"
| commit: "c \<in> active s \<Longrightarrow> t = current s c \<Longrightarrow> leader s t = Some c \<Longrightarrow>
    tip s t \<in> published s \<Longrightarrow> epoch (tip s t) = t \<Longrightarrow>
    majority V Q \<Longrightarrow> (\<forall>n\<in>Q. (n,tip s t) \<in> receipts s) \<Longrightarrow>
    step V s (s\<lparr>committed := insert (tip s t) (committed s)\<rparr>)"
| restart: "step V s (s\<lparr>started := started s - {n}, active := active s - {n}\<rparr>)"

inductive reachable :: "node set \<Rightarrow> coordination \<Rightarrow> bool" for V where
  initial: "reachable V initial"
| advance: "reachable V s \<Longrightarrow> step V s s' \<Longrightarrow> reachable V s'"

definition possible :: "node set \<Rightarrow> coordination \<Rightarrow> history \<Rightarrow> bool" where
  "possible V s h \<longleftrightarrow> (\<exists>Q. majority V Q \<and>
    (\<forall>n\<in>Q. (n,h) \<in> receipts s \<or> current s n \<le> epoch h))"

definition well_formed :: "node set \<Rightarrow> coordination \<Rightarrow> bool" where
  "well_formed V s \<longleftrightarrow>
    (\<forall>n. accepted s n \<in> insert [] (published s) \<and> epoch (accepted s n) \<le> current s n) \<and>
    (\<forall>n h. (n,h) \<in> receipts s \<longrightarrow> h \<in> published s \<and> h \<preceq> accepted s n) \<and>
    (\<forall>n c t a. (n,c,t,a) \<in> joins s \<longrightarrow> t \<le> current s n \<and> 0 < t \<and>
      (\<forall>h. (n,h) \<in> receipts s \<and> epoch h < t \<longrightarrow> h \<preceq> a)) \<and>
    (\<forall>t c. leader s t = Some c \<longrightarrow> 0 < t \<and> majority V (electors s t) \<and>
      tip s t \<in> insert [] (published s) \<and>
      (\<forall>n\<in>electors s t. \<exists>a. (n,c,t,a) \<in> joins s \<and> a \<preceq> tip s t)) \<and>
    (\<forall>h\<in>published s. (\<exists>c. leader s (epoch h) = Some c) \<and>
       prefix h (tip s (epoch h)) \<and> h \<noteq> [] \<and>
       sorted_wrt (\<lambda>a b. fst (snd a) < fst (snd b)) h) \<and>
    (\<forall>h\<in>committed s. h \<in> published s \<and> (\<exists>Q. majority V Q \<and> (\<forall>n\<in>Q. (n,h) \<in> receipts s))) \<and>
    (\<forall>a\<in>published s. \<forall>b\<in>published s. possible V s a \<and> epoch a < epoch b \<longrightarrow> prefix a b)"

lemma rank_refl[simp]: "a \<preceq> a"
  by (simp add: fresher_eq_def)

lemma rank_trans: "a \<preceq> b \<Longrightarrow> b \<preceq> c \<Longrightarrow> a \<preceq> c"
  unfolding fresher_eq_def by (auto intro: le_trans)

lemma epoch_snoc[simp]: "epoch (h @ [(t,v,x)]) = t"
  by (simp add: epoch_def)

lemma version_snoc[simp]: "version (h @ [(t,v,x)]) = v"
  by (simp add: version_def)

lemma epoch_empty[simp]: "epoch [] = 0"
  by (simp add: epoch_def)

lemma wfD:
  assumes "well_formed V s"
  shows
    "accepted s n \<in> insert [] (published s)"
    "epoch (accepted s n) \<le> current s n"
    "(n,h) \<in> receipts s \<Longrightarrow> h \<in> published s"
    "(n,h) \<in> receipts s \<Longrightarrow> h \<preceq> accepted s n"
    "(n,c,t,a) \<in> joins s \<Longrightarrow> t \<le> current s n"
    "(n,c,t,a) \<in> joins s \<Longrightarrow> 0 < t"
    "(n,c,t,a) \<in> joins s \<Longrightarrow> (n,h) \<in> receipts s \<Longrightarrow> epoch h < t \<Longrightarrow> h \<preceq> a"
    "leader s t = Some c \<Longrightarrow> 0 < t"
    "leader s t = Some c \<Longrightarrow> majority V (electors s t)"
    "leader s t = Some c \<Longrightarrow> tip s t \<in> insert [] (published s)"
    "leader s t = Some c \<Longrightarrow> n \<in> electors s t \<Longrightarrow> \<exists>a. (n,c,t,a) \<in> joins s \<and> a \<preceq> tip s t"
    "h \<in> published s \<Longrightarrow> \<exists>c. leader s (epoch h) = Some c"
    "h \<in> published s \<Longrightarrow> prefix h (tip s (epoch h))"
    "h \<in> published s \<Longrightarrow> h \<noteq> []"
    "h \<in> published s \<Longrightarrow> sorted_wrt (\<lambda>a b. fst (snd a) < fst (snd b)) h"
    "h \<in> committed s \<Longrightarrow> h \<in> published s"
    "h \<in> committed s \<Longrightarrow> \<exists>Q. majority V Q \<and> (\<forall>n\<in>Q. (n,h) \<in> receipts s)"
    "a \<in> published s \<Longrightarrow> b \<in> published s \<Longrightarrow>
      possible V s a \<Longrightarrow> epoch a < epoch b \<Longrightarrow> prefix a b"
  using assms unfolding well_formed_def by auto

lemma initial_wf: "well_formed V initial"
  by (simp add: well_formed_def initial_def)

lemma join_wf:
  assumes wf: "well_formed V s" and newer: "current s n < t"
  shows "well_formed V (s\<lparr>current := (current s)(n := t),
      joins := insert (n,c,t,accepted s n) (joins s), started := insert n (started s), active := active s - {n}\<rparr>)"
proof -
  let ?s' = "s\<lparr>current := (current s)(n := t),
      joins := insert (n,c,t,accepted s n) (joins s), started := insert n (started s), active := active s - {n}\<rparr>"
  have mono: "current s i \<le> current ?s' i" for i using newer by auto
  have bound: "current ?s' i \<le> epoch h \<Longrightarrow> current s i \<le> epoch h" for i h
    by (rule le_trans[OF mono])
  have possibleD: "possible V ?s' h \<Longrightarrow> possible V s h" for h
  proof -
    assume "possible V ?s' h"
    then obtain Q where quorum: "majority V Q"
      and votes: "\<forall>i\<in>Q. (i,h) \<in> receipts s \<or> current ?s' i \<le> epoch h"
      unfolding possible_def by auto
    have eligible: "(i,h) \<in> receipts s \<or> current s i \<le> epoch h" if "i \<in> Q" for i
      using votes[rule_format, OF that] bound[of i h] by blast
    show "possible V s h" unfolding possible_def
      using quorum eligible by blast
  qed
  have accepted_bound: "epoch (accepted s i) \<le> current ?s' i" for i
    by (rule le_trans[OF wfD(2)[OF wf] mono])
  have join_bound: "(i,d,u,a) \<in> joins s \<Longrightarrow> u \<le> current ?s' i" for i d u a
    by (rule le_trans[OF wfD(5)[OF wf, of i d u a] mono])
  have election_votes: "\<exists>a. (i,d,u,a) \<in> joins ?s' \<and> a \<preceq> tip s u"
    if "leader s u = Some d" "i \<in> electors s u" for i d u
    using wfD(11)[OF wf that] by auto
  show ?thesis using wf newer possibleD accepted_bound join_bound election_votes wfD(4)[OF wf]
    unfolding well_formed_def by (auto simp add: fun_upd_same simp del: fun_upd_apply)
qed

lemma elect_wf:
  assumes "well_formed V s" and "t = current s c" and none: "leader s t = None"
    and majority: "majority V Q"
    and votes: "\<forall>n\<in>Q. \<exists>h. (n,c,t,h) \<in> joins s \<and> h \<preceq> accepted s c"
    and own: "\<exists>c' h. (c,c',t,h) \<in> joins s"
  shows "well_formed V (s\<lparr>leader := (leader s)(t := Some c), electors := (electors s)(t := Q),
      tip := (tip s)(t := accepted s c), active := insert c (active s)\<rparr>)"
proof -
  have pos: "0 < t" using own wfD(6)[OF assms(1)] by blast
  have diff: "h \<in> published s \<Longrightarrow> epoch h \<noteq> t" for h
    using none wfD(12)[OF assms(1)] by fastforce
  show ?thesis
    using assms(1) pos majority votes diff
    unfolding well_formed_def by (auto simp: possible_def)
qed

lemma accept_wf:
  assumes wf: "well_formed V s" and pub: "h \<in> published s"
    and cur: "epoch h = current s n"
    and newer: "epoch (accepted s n) < epoch h \<or>
      epoch (accepted s n) = epoch h \<and> version (accepted s n) < version h"
  shows "well_formed V (s\<lparr>accepted := (accepted s)(n := h), receipts := insert (n,h) (receipts s)\<rparr>)"
proof -
  let ?s' = "s\<lparr>accepted := (accepted s)(n := h), receipts := insert (n,h) (receipts s)\<rparr>"
  have rank: "accepted s n \<preceq> h" using newer unfolding fresher_eq_def by auto
  have possibleD: "possible V ?s' p \<Longrightarrow> possible V s p" for p
  proof -
    assume "possible V ?s' p"
    then obtain Q where quorum: "majority V Q"
      and votes: "\<forall>i\<in>Q. (i,p) \<in> receipts ?s' \<or> current s i \<le> epoch p"
      unfolding possible_def by auto
    have "(i,p) \<in> receipts s \<or> current s i \<le> epoch p" if "i \<in> Q" for i
      using votes[rule_format, OF that] cur by auto
    with quorum show "possible V s p" unfolding possible_def by blast
  qed
  have older: "(n,c,t,a) \<in> joins s \<Longrightarrow> \<not> epoch h < t" for c t a
    using cur wfD(5)[OF wf] by fastforce
  have receipt_rank: "(n,p) \<in> receipts s \<Longrightarrow> p \<preceq> h" for p
    by (rule rank_trans[OF wfD(4)[OF wf] rank])
  have commit_receipts: "p \<in> committed s \<Longrightarrow>
      \<exists>Q. majority V Q \<and> (\<forall>i\<in>Q. (i,p) \<in> receipts ?s')" for p
    using wfD(17)[OF wf, of p] by auto
  show ?thesis using wf pub cur possibleD older receipt_rank commit_receipts
    unfolding well_formed_def by auto
qed

lemma commit_wf:
  assumes "well_formed V s" "h \<in> published s" "majority V Q" "\<forall>n\<in>Q. (n,h) \<in> receipts s"
  shows "well_formed V (s\<lparr>committed := insert h (committed s)\<rparr>)"
  using assms unfolding well_formed_def possible_def by auto

lemma prefix_version:
  assumes "prefix a b" "a \<noteq> []" "a \<noteq> b"
    "sorted_wrt (\<lambda>x y. fst (snd x) < fst (snd y)) b"
  shows "version a < version b"
proof -
  obtain tail where tail: "b = a @ tail" "tail \<noteq> []"
    using assms(1,3) by (auto elim: prefixE)
  with assms show ?thesis
    unfolding version_def by (auto simp: sorted_wrt_append last_in_set)
qed

lemma comparable_same_epoch:
  assumes wf: "well_formed V s" and pubs: "a \<in> published s" "b \<in> published s"
    and epoch: "epoch a = epoch b"
  shows "prefix a b \<or> prefix b a"
  using wfD(13)[OF wf pubs(1)] wfD(13)[OF wf pubs(2)] epoch
  by (metis prefix_same_cases)

lemma lower_rank_is_prefix:
  assumes wf: "well_formed V s" and pubs: "a \<in> published s" "b \<in> published s"
    and possible: "possible V s a" and rank: "a \<preceq> b"
  shows "prefix a b"
proof (cases "epoch a < epoch b")
  case True
  with assms show ?thesis by (auto intro: wfD(18))
next
  case False
  with rank have eq: "epoch a = epoch b" and le: "version a \<le> version b"
    unfolding fresher_eq_def by auto
  from comparable_same_epoch[OF wf pubs eq] show ?thesis
  proof
    assume "prefix a b"
    then show ?thesis .
  next
    assume reverse: "prefix b a"
    have "a = b"
    proof (rule ccontr)
      assume "a \<noteq> b"
      then have "b \<noteq> a" by simp
      from prefix_version[OF reverse wfD(14)[OF wf pubs(2)] this wfD(15)[OF wf pubs(1)]]
        le show False by simp
    qed
    then show ?thesis by simp
  qed
qed

lemma possible_vote:
  assumes wf: "well_formed V s" and led: "leader s t = Some c"
    and pos: "possible V s p" and old: "epoch p < t"
  shows "p \<preceq> tip s t"
proof -
  obtain Q where "majority V Q" and witnesses: "\<forall>n\<in>Q. (n,p) \<in> receipts s \<or> current s n \<le> epoch p"
    using pos unfolding possible_def by blast
  then obtain n where n: "n \<in> Q" "n \<in> electors s t"
    using majority_intersects[OF wfD(9)[OF wf led]] by blast
  then obtain a where vote: "(n,c,t,a) \<in> joins s" "a \<preceq> tip s t"
    using wfD(11)[OF wf led] by blast
  have "(n,p) \<in> receipts s"
    using witnesses n(1) wfD(5)[OF wf vote(1)] old by auto
  then show ?thesis using wfD(7)[OF wf vote(1) _ old] vote(2) by (blast intro: rank_trans)
qed

lemma dominated_new_proposal:
  assumes wf: "well_formed V s" and pub: "p \<in> published s"
    and fresh: "h \<notin> published s" and old: "epoch h < epoch p"
  shows "\<not> possible V s h"
proof
  assume "possible V s h"
  then obtain Q where "majority V Q" and witnesses: "\<forall>n\<in>Q. (n,h) \<in> receipts s \<or> current s n \<le> epoch h"
    unfolding possible_def by blast
  obtain c where led: "leader s (epoch p) = Some c" using wfD(12)[OF wf pub] by blast
  obtain n where n: "n \<in> Q" "n \<in> electors s (epoch p)"
    using majority_intersects[OF wfD(9)[OF wf led] \<open>majority V Q\<close>] by blast
  then obtain a where "(n,c,epoch p,a) \<in> joins s" using wfD(11)[OF wf led] by blast
  then have "epoch p \<le> current s n" by (rule wfD(5)[OF wf])
  with old n(1) witnesses have "(n,h) \<in> receipts s" by auto
  with fresh show False by (blast dest: wfD(3)[OF wf])
qed

lemma sorted_snoc:
  assumes "sorted_wrt (\<lambda>x y. fst (snd x) < fst (snd y)) a" "version a < v"
  shows "sorted_wrt (\<lambda>x y. fst (snd x) < fst (snd y)) (a @ [(t,v,value)])"
proof -
  have "fst (snd x) < v" if "x \<in> set a" for x
    using that assms
    by (cases a rule: rev_cases) (auto simp: version_def sorted_wrt_append elim: less_trans)
  with assms(1) show ?thesis by (simp add: sorted_wrt_append)
qed

lemma propose_wf:
  assumes wf: "well_formed V s"
    and cur: "t = current s c" and led: "leader s t = Some c"
    and base: "tip s t = accepted s c" and inc: "version (tip s t) < v"
  shows "well_formed V (s\<lparr>tip := (tip s)(t := tip s t @ [(t,v,value)]),
                          published := insert (tip s t @ [(t,v,value)]) (published s)\<rparr>)"
proof -
  let ?base = "tip s t"
  let ?h = "?base @ [(t,v,value)]"
  let ?s' = "s\<lparr>tip := (tip s)(t := ?h), published := insert ?h (published s)\<rparr>"
  have rank: "?base \<preceq> ?h"
    using wfD(2)[OF wf, of c] cur base inc unfolding fresher_eq_def by auto
  have votes: "n \<in> electors s t \<Longrightarrow> \<exists>a. (n,c,t,a) \<in> joins s \<and> a \<preceq> ?h" for n
    using wfD(11)[OF wf led] rank by (blast intro: rank_trans)
  have "sorted_wrt (\<lambda>x y. fst (snd x) < fst (snd y)) ?base"
    using wfD(10)[OF wf led] wfD(15)[OF wf, of ?base] by auto
  then have sorted: "sorted_wrt (\<lambda>x y. fst (snd x) < fst (snd y)) ?h"
    by (rule sorted_snoc[OF _ inc])
  have fresh: "?h \<notin> published s"
  proof
    assume pub: "?h \<in> published s"
    from wfD(13)[OF wf pub] show False by simp
  qed
  have precedes: "prefix p ?h" if pub: "p \<in> published s" and poss: "possible V s p" and old: "epoch p < t" for p
  proof -
    have pre: "p \<preceq> ?base" by (rule possible_vote[OF wf led poss old])
    have "?base \<in> published s"
      using pre pub wfD(10)[OF wf led] wfD(12)[OF wf pub] wfD(8)[OF wf]
      unfolding fresher_eq_def by fastforce
    then have "prefix p ?base" by (rule lower_rank_is_prefix[OF wf pub _ poss pre])
    then show ?thesis by simp
  qed
  have blocks: "p \<in> published s \<Longrightarrow> t < epoch p \<Longrightarrow> \<not> possible V s ?h" for p
    using dominated_new_proposal[OF wf _ fresh] by simp
  have possible_unchanged: "possible V ?s' p = possible V s p" for p
    by (simp add: possible_def)
  show ?thesis
    using wf led votes sorted precedes blocks
    unfolding well_formed_def by (auto simp: possible_unchanged)
qed

lemma step_preserves_wf:
  assumes wf: "well_formed V s" and transition: "step V s s'"
  shows "well_formed V s'"
  using transition
proof (cases rule: step.cases)
  case join
  with wf show ?thesis by (simp add: join_wf)
next
  case elect
  with wf show ?thesis by (blast intro: elect_wf)
next
  case propose
  with wf show ?thesis by (blast intro: propose_wf)
next
  case accept
  with wf show ?thesis by (blast intro: accept_wf)
next
  case commit
  with wf show ?thesis by (blast intro: commit_wf)
next
  case restart
  with wf show ?thesis by (simp add: well_formed_def possible_def)
qed

lemma reachable_wf:
  assumes "reachable V s"
  shows "well_formed V s"
  using assms by (induction rule: reachable.induct) (auto intro: initial_wf step_preserves_wf)

theorem committed_states_form_chain:
  assumes "reachable V s" "a \<in> committed s" "b \<in> committed s"
  shows "prefix a b \<or> prefix b a"
proof -
  have wf: "well_formed V s" by (rule reachable_wf[OF assms(1)])
  have pubs: "a \<in> published s" "b \<in> published s"
    using wfD(16)[OF wf] assms by auto
  have possible: "possible V s a" "possible V s b"
    using wfD(17)[OF wf] assms unfolding possible_def by blast+
  consider "epoch a < epoch b" | "epoch a = epoch b" | "epoch b < epoch a"
    by linarith
  then show ?thesis
    using comparable_same_epoch[OF wf pubs] wfD(18)[OF wf pubs possible(1)]
      wfD(18)[OF wf pubs(2,1) possible(2)] by cases auto
qed

theorem unique_publication:
  assumes "reachable V s" "a \<in> published s" "b \<in> published s"
    "epoch a = epoch b" "version a = version b"
  shows "a = b"
proof -
  have wf: "well_formed V s" by (rule reachable_wf[OF assms(1)])
  show ?thesis
    using comparable_same_epoch[OF wf assms(2-4)] wfD(14,15)[OF wf assms(2)]
      wfD(14,15)[OF wf assms(3)] assms(5) by (metis less_irrefl prefix_version)
qed

lemma join_has_unique_destination:
  assumes "reachable V s" "(n,c,t,a) \<in> joins s" "(n,d,t,b) \<in> joins s"
  shows "c = d"
  using assms
proof (induction rule: reachable.induct)
  case initial
  then show ?case by (simp add: initial_def)
next
  case (advance s s')
  have bound: "(n,c,t,a) \<in> joins s \<Longrightarrow> t \<le> current s n" for n c t a
    by (rule wfD(5)[OF reachable_wf[OF advance.hyps(1)]])
  from advance.hyps(2) advance.prems advance.IH bound show ?case
    by (cases rule: step.cases) (auto dest: bound)
qed

theorem one_election_candidate_per_term:
  assumes "reachable V s" "majority V Q" "majority V R"
    "\<And>n. n \<in> Q \<Longrightarrow> \<exists>a. (n,c,t,a) \<in> joins s"
    "\<And>n. n \<in> R \<Longrightarrow> \<exists>b. (n,d,t,b) \<in> joins s"
  shows "c = d"
proof -
  obtain n where "n \<in> Q" "n \<in> R"
    using majority_intersects[OF assms(2,3)] by blast
  with assms(4,5) show ?thesis
    by (blast intro: join_has_unique_destination[OF assms(1)])
qed

end
