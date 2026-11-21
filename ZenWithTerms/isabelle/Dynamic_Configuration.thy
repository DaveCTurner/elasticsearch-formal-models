theory Dynamic_Configuration
  imports Quorum_Basics "HOL-Library.Sublist" "HOL-Library.Product_Lexorder"
begin

section \<open>Dynamic quorum certificates and publication ancestry\<close>

type_synonym config = "node set"
record rank =
  rank_term :: nat
  rank_version :: nat

abbreviation rank_zero :: rank where
  "rank_zero \<equiv> \<lparr>rank_term = 0, rank_version = 0\<rparr>"

text \<open>
  Ranks are ordered lexicographically, by term and then by version. A record cannot
  inherit the order of a pair, so the order is defined on every record extension and
  is the lexicographic order on the two fields followed by the extension.
\<close>

instantiation rank_ext :: (linorder) linorder
begin

definition less_eq_rank_ext :: "'a rank_ext \<Rightarrow> 'a rank_ext \<Rightarrow> bool" where
  "a \<le> b \<longleftrightarrow> (rank_term a, rank_version a, rank.more a) \<le> (rank_term b, rank_version b, rank.more b)"

definition less_rank_ext :: "'a rank_ext \<Rightarrow> 'a rank_ext \<Rightarrow> bool" where
  "a < b \<longleftrightarrow> (rank_term a, rank_version a, rank.more a) < (rank_term b, rank_version b, rank.more b)"

instance
proof
  fix a b c :: "'a rank_ext"
  show "a < b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a"
    unfolding less_eq_rank_ext_def less_rank_ext_def by (simp add: less_le_not_le)
  show "a \<le> a" unfolding less_eq_rank_ext_def by simp
  show "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c"
    unfolding less_eq_rank_ext_def by (rule order_trans)
  show "a \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a = b"
  proof -
    assume "a \<le> b" "b \<le> a"
    then have "(rank_term a, rank_version a, rank.more a) = (rank_term b, rank_version b, rank.more b)"
      unfolding less_eq_rank_ext_def by (rule antisym)
    then show "a = b" by (simp add: rank.equality)
  qed
  show "a \<le> b \<or> b \<le> a"
    unfolding less_eq_rank_ext_def by (rule linear)
qed

end

lemma rank_eta[simp]: "\<lparr>rank_term = rank_term (k :: rank), rank_version = rank_version k\<rparr> = k"
  by (cases k) simp

lemma rank_le_iff:
  fixes a b :: rank
  shows "a \<le> b \<longleftrightarrow> rank_term a < rank_term b \<or> rank_term a = rank_term b \<and> rank_version a \<le> rank_version b"
  unfolding less_eq_rank_ext_def by (auto simp: less_eq_prod_def less_prod_def order_le_less)

lemma rank_less_iff:
  fixes a b :: rank
  shows "a < b \<longleftrightarrow> rank_term a < rank_term b \<or> rank_term a = rank_term b \<and> rank_version a < rank_version b"
  unfolding less_rank_ext_def by (auto simp: less_prod_def order_le_less)

record publication =
  pub_term :: nat
  pub_version :: nat
  pub_payload :: nat
  pub_owner :: node
  pub_config :: config
  pub_previous :: config

type_synonym lineage = "publication list"

fun at_tip :: "'a \<Rightarrow> (publication \<Rightarrow> 'a) \<Rightarrow> lineage \<Rightarrow> 'a" where
  "at_tip z f [] = z"
| "at_tip z f (x # xs) = (if xs = [] then f x else at_tip z f xs)"

lemma at_tip_snoc[simp]: "at_tip z f (h @ [x]) = f x"
  by (induction h) auto

abbreviation position :: "lineage \<Rightarrow> rank" where
  "position \<equiv> at_tip rank_zero (\<lambda>x. \<lparr>rank_term = pub_term x, rank_version = pub_version x\<rparr>)"

abbreviation term_of :: "lineage \<Rightarrow> nat" where
  "term_of h \<equiv> rank_term (position h)"

abbreviation config_of :: "config \<Rightarrow> lineage \<Rightarrow> config" where
  "config_of C \<equiv> at_tip C pub_config"

abbreviation carried :: "config \<Rightarrow> lineage \<Rightarrow> config" where
  "carried C \<equiv> at_tip C pub_previous"

abbreviation owner :: "lineage \<Rightarrow> node" where
  "owner \<equiv> at_tip 0 pub_owner"

definition quorum :: "config \<Rightarrow> node set \<Rightarrow> bool" where
  "quorum C Q \<longleftrightarrow> majority C (C \<inter> Q)"

lemma quorum_intersects:
  assumes "quorum C Q" "quorum C R"
  obtains n where "n \<in> Q" "n \<in> R"
  using majority_intersects assms unfolding quorum_def by blast

record election =
  elected_from :: lineage
  elected_committed :: config
  elected_votes :: "node set"

record dynamic_state =
  node_term :: "node \<Rightarrow> nat"
  durable_history :: "node \<Rightarrow> lineage"
  committed_config :: "node \<Rightarrow> config"
  sent_joins :: "(node \<times> node \<times> nat \<times> rank) set"
  joined_since_restart :: "node set"
  certificate :: "(node \<times> nat) \<Rightarrow> election option"
  publication_tip :: "(node \<times> nat) \<Rightarrow> lineage"
  publications :: "lineage set"
  acknowledgements :: "(node \<times> lineage) set"
  quorum_commits :: "lineage set"

definition bootstrapped :: "config \<Rightarrow> dynamic_state" where
  "bootstrapped C = \<lparr>node_term = (\<lambda>_. 0), durable_history = (\<lambda>_. []),
    committed_config = (\<lambda>_. C), sent_joins = {}, joined_since_restart = {},
    certificate = (\<lambda>_. None), publication_tip = (\<lambda>_. []), publications = {},
    acknowledgements = {}, quorum_commits = {}\<rparr>"

definition voted :: "dynamic_state \<Rightarrow> node \<Rightarrow> nat \<Rightarrow> node set \<Rightarrow> bool" where
  "voted s c t Q \<longleftrightarrow> (\<forall>n\<in>Q. \<exists>r. (n,c,t,r) \<in> sent_joins s)"

definition fresh_votes :: "dynamic_state \<Rightarrow> node \<Rightarrow> nat \<Rightarrow> lineage \<Rightarrow> node set \<Rightarrow> bool" where
  "fresh_votes s c t h Q \<longleftrightarrow> (\<forall>n\<in>Q. \<exists>r\<le>position h. (n,c,t,r) \<in> sent_joins s)"

lemma fresh_votes_voted: "fresh_votes s c t h Q \<Longrightarrow> voted s c t Q"
  unfolding voted_def fresh_votes_def by blast

definition active_leader :: "dynamic_state \<Rightarrow> node \<Rightarrow> bool" where
  "active_leader s n \<longleftrightarrow>
    n \<in> joined_since_restart s \<and> certificate s (n,node_term s n) \<noteq> None"

definition joint_receipts :: "config \<Rightarrow> dynamic_state \<Rightarrow> lineage \<Rightarrow> bool" where
  "joint_receipts C s h \<longleftrightarrow>
    (\<exists>Q. quorum (carried C h) Q \<and> quorum (config_of C h) Q \<and>
      (\<forall>n\<in>Q. (n,h) \<in> acknowledgements s))"

text \<open>
  The carried configuration is the committed configuration in the publish request.
  A first quorum commit uses that configuration and the publication's new configuration.
  Once a commit is recorded, subsequent commit notifications can replay it.
  Elections and quorum commits are recorded atomically. The join certificate used for
  a proposal may include further votes since election.
\<close>

inductive transition :: "config \<Rightarrow> dynamic_state \<Rightarrow> dynamic_state \<Rightarrow> bool" for C where
  start_join: "node_term s n < t \<Longrightarrow>
    transition C s (s\<lparr>node_term := (node_term s)(n := t),
      sent_joins := insert (n,c,t,position (durable_history s n)) (sent_joins s),
      joined_since_restart := insert n (joined_since_restart s)\<rparr>)"
| win: "c \<in> joined_since_restart s \<Longrightarrow>
    certificate s (c,node_term s c) = None \<Longrightarrow>
    quorum (committed_config s c) Q \<Longrightarrow> quorum (config_of C (durable_history s c)) Q \<Longrightarrow>
    fresh_votes s c (node_term s c) (durable_history s c) Q \<Longrightarrow>
    transition C s (s\<lparr>certificate := (certificate s)((c,node_term s c) :=
        Some \<lparr>elected_from = durable_history s c, elected_committed = committed_config s c, elected_votes = Q\<rparr>),
      publication_tip := (publication_tip s)((c,node_term s c) := durable_history s c)\<rparr>)"
| publish: "active_leader s c \<Longrightarrow>
    publication_tip s (c,node_term s c) = durable_history s c \<Longrightarrow>
    rank_version (position (durable_history s c)) < v \<Longrightarrow>
    (D \<noteq> config_of C (durable_history s c) \<longrightarrow> committed_config s c = config_of C (durable_history s c)) \<Longrightarrow>
    quorum D Q \<Longrightarrow> fresh_votes s c (node_term s c) (durable_history s c) Q \<Longrightarrow>
    h = durable_history s c @ [\<lparr>pub_term = node_term s c, pub_version = v, pub_payload = payload,
        pub_owner = c, pub_config = D, pub_previous = committed_config s c\<rparr>] \<Longrightarrow>
    transition C s (s\<lparr>publication_tip := (publication_tip s)((c,node_term s c) := h),
      publications := insert h (publications s)\<rparr>)"
| receive: "h \<in> publications s \<Longrightarrow> term_of h = node_term s n \<Longrightarrow>
    position (durable_history s n) < position h \<Longrightarrow>
    transition C s (s\<lparr>durable_history := (durable_history s)(n := h),
      committed_config := (committed_config s)(n := carried C h),
      acknowledgements := insert (n,h) (acknowledgements s)\<rparr>)"
| certify: "active_leader s c \<Longrightarrow> h = publication_tip s (c,node_term s c) \<Longrightarrow>
    h \<in> publications s \<Longrightarrow> term_of h = node_term s c \<Longrightarrow> owner h = c \<Longrightarrow>
    joint_receipts C s h \<Longrightarrow>
    transition C s (s\<lparr>quorum_commits := insert h (quorum_commits s)\<rparr>)"
| apply_commit: "durable_history s n \<in> quorum_commits s \<Longrightarrow>
    term_of (durable_history s n) = node_term s n \<Longrightarrow>
    (active_leader s n \<longrightarrow> durable_history s n = publication_tip s (n,node_term s n)) \<Longrightarrow>
    transition C s (s\<lparr>committed_config := (committed_config s)(n := config_of C (durable_history s n))\<rparr>)"
| reboot: "transition C s (s\<lparr>joined_since_restart := joined_since_restart s - {n}\<rparr>)"

inductive dynamic_reachable :: "config \<Rightarrow> dynamic_state \<Rightarrow> bool" for C where
  boot: "finite C \<Longrightarrow> C \<noteq> {} \<Longrightarrow> dynamic_reachable C (bootstrapped C)"
| advance: "dynamic_reachable C s \<Longrightarrow> transition C s s' \<Longrightarrow> dynamic_reachable C s'"

definition effective_config :: "config \<Rightarrow> lineage set \<Rightarrow> lineage \<Rightarrow> config \<Rightarrow> bool" where
  "effective_config C K h D \<longleftrightarrow> D = carried C h \<or> h \<in> K \<and> D = config_of C h"

lemma effective_config_insert:
  "effective_config C K h D \<Longrightarrow> effective_config C (insert x K) h D"
  by (simp only: effective_config_def insert_iff) blast

definition valid_edge :: "config \<Rightarrow> lineage set \<Rightarrow> lineage \<Rightarrow> publication \<Rightarrow> bool" where
  "valid_edge C K h x \<longleftrightarrow> term_of h \<le> pub_term x \<and> 0 < pub_term x \<and>
    rank_version (position h) < pub_version x \<and>
    effective_config C K h (pub_previous x) \<and>
    (pub_config x \<noteq> config_of C h \<longrightarrow> pub_previous x = config_of C h)"

lemma valid_edge_insert:
  "valid_edge C K h x \<Longrightarrow> valid_edge C (insert p K) h x"
  unfolding valid_edge_def by (blast intro: effective_config_insert)

definition prefix_closed :: "lineage set \<Rightarrow> bool" where
  "prefix_closed P \<longleftrightarrow> (\<forall>h x. h @ [x] \<in> P \<longrightarrow> h \<in> insert [] P)"

definition journal_ok :: "config \<Rightarrow> dynamic_state \<Rightarrow> bool" where
  "journal_ok C s \<longleftrightarrow>
    (\<forall>n. durable_history s n \<in> insert [] (publications s) \<and>
      term_of (durable_history s n) \<le> node_term s n \<and>
      effective_config C (quorum_commits s) (durable_history s n) (committed_config s n)) \<and>
    (\<forall>n h. (n,h) \<in> acknowledgements s \<longrightarrow> position h \<le> position (durable_history s n)) \<and>
    (\<forall>n c t r. (n,c,t,r) \<in> sent_joins s \<longrightarrow> t \<le> node_term s n \<and>
      (\<forall>h. (n,h) \<in> acknowledgements s \<and> term_of h < t \<longrightarrow> position h \<le> r)) \<and>
    (\<forall>n c d t r u. (n,c,t,r) \<in> sent_joins s \<and> (n,d,t,u) \<in> sent_joins s \<longrightarrow> c = d) \<and>
    (\<forall>n\<in>joined_since_restart s. 0 < node_term s n)"

definition publications_ok :: "config \<Rightarrow> dynamic_state \<Rightarrow> bool" where
  "publications_ok C s \<longleftrightarrow>
    finite (publications s) \<and> [] \<notin> publications s \<and> prefix_closed (publications s) \<and>
    (\<forall>h x. h @ [x] \<in> publications s \<longrightarrow> valid_edge C (quorum_commits s) h x) \<and>
    (\<forall>h\<in>quorum_commits s. h \<in> publications s \<and> joint_receipts C s h)"

definition leadership_ok :: "config \<Rightarrow> dynamic_state \<Rightarrow> bool" where
  "leadership_ok C s \<longleftrightarrow>
    (\<forall>c t e. certificate s (c,t) = Some e \<longrightarrow>
      elected_from e \<in> insert [] (publications s) \<and> term_of (elected_from e) < t \<and>
      effective_config C (quorum_commits s) (elected_from e) (elected_committed e) \<and>
      quorum (elected_committed e) (elected_votes e) \<and>
      quorum (config_of C (elected_from e)) (elected_votes e) \<and>
      fresh_votes s c t (elected_from e) (elected_votes e) \<and>
      prefix (elected_from e) (publication_tip s (c,t))) \<and>
    (\<forall>h\<in>publications s.
      (\<exists>e. certificate s (owner h,term_of h) = Some e \<and> prefix (elected_from e) h) \<and>
      prefix h (publication_tip s (owner h,term_of h)) \<and>
      (\<exists>Q. quorum (config_of C h) Q \<and> voted s (owner h) (term_of h) Q))"

lemma journalD:
  assumes "journal_ok C s"
  shows
    "durable_history s n \<in> insert [] (publications s)"
    "term_of (durable_history s n) \<le> node_term s n"
    "effective_config C (quorum_commits s) (durable_history s n) (committed_config s n)"
    "(n,h) \<in> acknowledgements s \<Longrightarrow> position h \<le> position (durable_history s n)"
    "(n,c,t,r) \<in> sent_joins s \<Longrightarrow> t \<le> node_term s n"
    "(n,c,t,r) \<in> sent_joins s \<Longrightarrow> (n,h) \<in> acknowledgements s \<Longrightarrow>
      term_of h < t \<Longrightarrow> position h \<le> r"
    "(n,c,t,r) \<in> sent_joins s \<Longrightarrow> (n,d,t,u) \<in> sent_joins s \<Longrightarrow> c = d"
    "n \<in> joined_since_restart s \<Longrightarrow> 0 < node_term s n"
  using assms unfolding journal_ok_def
  apply (auto simp del: split_paired_All split_paired_Ex)
  by blast

lemma publicationsD:
  assumes "publications_ok C s"
  shows
    "finite (publications s)"
    "[] \<notin> publications s"
    "prefix_closed (publications s)"
    "h @ [x] \<in> publications s \<Longrightarrow> valid_edge C (quorum_commits s) h x"
    "h \<in> quorum_commits s \<Longrightarrow> h \<in> publications s"
    "h \<in> quorum_commits s \<Longrightarrow> joint_receipts C s h"
  using assms unfolding publications_ok_def by auto

lemma leadershipD:
  assumes "leadership_ok C s"
  shows
    "certificate s (c,t) = Some e \<Longrightarrow> elected_from e \<in> insert [] (publications s)"
    "certificate s (c,t) = Some e \<Longrightarrow> term_of (elected_from e) < t"
    "certificate s (c,t) = Some e \<Longrightarrow>
      effective_config C (quorum_commits s) (elected_from e) (elected_committed e)"
    "certificate s (c,t) = Some e \<Longrightarrow> quorum (elected_committed e) (elected_votes e)"
    "certificate s (c,t) = Some e \<Longrightarrow> quorum (config_of C (elected_from e)) (elected_votes e)"
    "certificate s (c,t) = Some e \<Longrightarrow> fresh_votes s c t (elected_from e) (elected_votes e)"
    "certificate s (c,t) = Some e \<Longrightarrow> prefix (elected_from e) (publication_tip s (c,t))"
    "h \<in> publications s \<Longrightarrow> \<exists>e. certificate s (owner h,term_of h) = Some e \<and> prefix (elected_from e) h"
    "h \<in> publications s \<Longrightarrow> prefix h (publication_tip s (owner h,term_of h))"
    "h \<in> publications s \<Longrightarrow> \<exists>Q. quorum (config_of C h) Q \<and> voted s (owner h) (term_of h) Q"
  using assms unfolding leadership_ok_def by auto

lemma same_config_vote:
  assumes ok: "journal_ok C s" and q: "quorum D Q" "quorum D R"
    and votes: "voted s c t Q" "voted s d t R"
  shows "c = d"
proof -
  obtain n where "n \<in> Q" "n \<in> R" using quorum_intersects[OF q] by blast
  with votes obtain r u where "(n,c,t,r) \<in> sent_joins s" "(n,d,t,u) \<in> sent_joins s"
    unfolding voted_def by blast
  then show ?thesis by (rule journalD(7)[OF ok])
qed

lemma new_election_base:
  assumes journal: "journal_ok C s" and leaders: "leadership_ok C s"
    and none: "certificate s (c,node_term s c) = None"
    and t: "0 < node_term s c"
    and q: "quorum (config_of C (durable_history s c)) Q"
    and fresh: "fresh_votes s c (node_term s c) (durable_history s c) Q"
  shows "term_of (durable_history s c) < node_term s c"
proof (rule ccontr)
  let ?h = "durable_history s c"
  let ?t = "node_term s c"
  assume "\<not> term_of ?h < ?t"
  then have eq: "term_of ?h = ?t" using journalD(2)[OF journal, of c] by simp
  have pub: "?h \<in> publications s" using journalD(1)[OF journal, of c] t eq by auto
  obtain R where "quorum (config_of C ?h) R" "voted s (owner ?h) ?t R"
    using leadershipD(10)[OF leaders pub] eq by auto
  then have "c = owner ?h" by (rule same_config_vote[OF journal q _ fresh_votes_voted[OF fresh]])
  with leadershipD(8)[OF leaders pub] eq none show False by auto
qed

lemma journal_start_join:
  assumes ok: "journal_ok C s" and newer: "node_term s n < t"
  shows "journal_ok C (s\<lparr>node_term := (node_term s)(n := t),
      sent_joins := insert (n,c,t,position (durable_history s n)) (sent_joins s),
      joined_since_restart := insert n (joined_since_restart s)\<rparr>)"
proof -
  have mono: "node_term s i \<le> ((node_term s)(n := t)) i" for i using newer by auto
  have accepted_bound: "term_of (durable_history s i) \<le> ((node_term s)(n := t)) i" for i
    by (rule order_trans[OF journalD(2)[OF ok] mono])
  have join_bound: "(i,d,u,r) \<in> sent_joins s \<Longrightarrow> u \<le> ((node_term s)(n := t)) i" for i d u r
    by (rule order_trans[OF journalD(5)[OF ok, of i d u r] mono])
  have no_prior_vote: "(n,d,t,r) \<notin> sent_joins s" for d r
    using newer journalD(5)[OF ok, of n d t r] by auto
  have positive: "0 < ((node_term s)(n := t)) i" if "i \<in> joined_since_restart s" for i
    using journalD(8)[OF ok that] mono[of i] by linarith
  show ?thesis
    using ok newer accepted_bound join_bound no_prior_vote positive journalD(4,7)[OF ok]
    unfolding journal_ok_def
    by (auto simp add: fun_upd_same simp del: fun_upd_apply)
qed

lemma journal_receive:
  assumes ok: "journal_ok C s" and pub: "h \<in> publications s"
    and cur: "term_of h = node_term s n" and rank: "position (durable_history s n) < position h"
  shows "journal_ok C (s\<lparr>durable_history := (durable_history s)(n := h),
      committed_config := (committed_config s)(n := carried C h),
      acknowledgements := insert (n,h) (acknowledgements s)\<rparr>)"
proof -
  have receipt: "position p \<le> position h" if "(n,p) \<in> acknowledgements s" for p
    using rank journalD(4)[OF ok that] by order
  have "\<not> term_of h < t" if "(n,c,t,r) \<in> sent_joins s" for c t r
    using cur journalD(5)[OF ok that] by simp
  then show ?thesis using ok pub cur receipt unfolding journal_ok_def effective_config_def by auto
qed

lemma journal_certify:
  assumes "journal_ok C s"
  shows "journal_ok C (s\<lparr>quorum_commits := insert h (quorum_commits s)\<rparr>)"
  using assms unfolding journal_ok_def effective_config_def by auto

lemma journal_apply:
  assumes "journal_ok C s" "durable_history s n \<in> quorum_commits s"
  shows "journal_ok C (s\<lparr>committed_config := (committed_config s)(n := config_of C (durable_history s n))\<rparr>)"
  using assms unfolding journal_ok_def effective_config_def by auto

lemma publications_publish:
  assumes ok: "publications_ok C s" and j: "journal_ok C s"
    and active: "active_leader s c" and inc: "rank_version (position (durable_history s c)) < v"
    and guard: "D \<noteq> config_of C (durable_history s c) \<longrightarrow>
      committed_config s c = config_of C (durable_history s c)"
    and new: "h = durable_history s c @ [\<lparr>pub_term = node_term s c, pub_version = v, pub_payload = payload,
        pub_owner = c, pub_config = D, pub_previous = committed_config s c\<rparr>]"
  shows "publications_ok C (s\<lparr>publication_tip := tips, publications := insert h (publications s)\<rparr>)"
proof -
  let ?x = "\<lparr>pub_term = node_term s c, pub_version = v, pub_payload = payload,
        pub_owner = c, pub_config = D, pub_previous = committed_config s c\<rparr>"
  have "c \<in> joined_since_restart s" using active unfolding active_leader_def by simp
  have "valid_edge C (quorum_commits s) (durable_history s c) ?x"
    using journalD(2,3)[OF j, of c] journalD(8)[OF j \<open>c \<in> joined_since_restart s\<close>] inc guard
    unfolding valid_edge_def by simp
  from this journalD(1)[OF j, of c] ok show ?thesis
    unfolding publications_ok_def prefix_closed_def joint_receipts_def new by auto
qed

lemma publications_receive:
  assumes ok: "publications_ok C s"
  shows "publications_ok C (s\<lparr>durable_history := (durable_history s)(n := h),
      committed_config := (committed_config s)(n := carried C h),
      acknowledgements := insert (n,h) (acknowledgements s)\<rparr>)"
proof -
  let ?s' = "s\<lparr>durable_history := (durable_history s)(n := h),
      committed_config := (committed_config s)(n := carried C h),
      acknowledgements := insert (n,h) (acknowledgements s)\<rparr>"
  have "joint_receipts C ?s' p" if "p \<in> quorum_commits s" for p
    using publicationsD(6)[OF ok that] unfolding joint_receipts_def by auto
  then show ?thesis using ok unfolding publications_ok_def by auto
qed

lemma publications_certify:
  assumes "publications_ok C s" "h \<in> publications s" "joint_receipts C s h"
  shows "publications_ok C (s\<lparr>quorum_commits := insert h (quorum_commits s)\<rparr>)"
  using assms unfolding publications_ok_def joint_receipts_def by (auto intro: valid_edge_insert)

lemma leadership_start_join:
  assumes ok: "leadership_ok C s"
  shows "leadership_ok C (s\<lparr>node_term := (node_term s)(n := t),
      sent_joins := insert (n,c,t,position (durable_history s n)) (sent_joins s),
      joined_since_restart := insert n (joined_since_restart s)\<rparr>)"
proof -
  let ?s' = "s\<lparr>node_term := (node_term s)(n := t),
      sent_joins := insert (n,c,t,position (durable_history s n)) (sent_joins s),
      joined_since_restart := insert n (joined_since_restart s)\<rparr>"
  have fresh: "fresh_votes s d u h Q \<Longrightarrow> fresh_votes ?s' d u h Q" for d u h Q
    unfolding fresh_votes_def by force
  have votes: "\<exists>Q. quorum (config_of C h) Q \<and> voted ?s' (owner h) (term_of h) Q"
    if "h \<in> publications s" for h
    using leadershipD(10)[OF ok that] unfolding voted_def by force
  show ?thesis using ok fresh votes unfolding leadership_ok_def by auto
qed

lemma leadership_win:
  assumes journal: "journal_ok C s" and ok: "leadership_ok C s"
    and started: "c \<in> joined_since_restart s" and none: "certificate s (c,node_term s c) = None"
    and quorum: "quorum (committed_config s c) Q" "quorum (config_of C (durable_history s c)) Q"
    and vote: "fresh_votes s c (node_term s c) (durable_history s c) Q"
  shows "leadership_ok C (s\<lparr>certificate := (certificate s)((c,node_term s c) :=
        Some \<lparr>elected_from = durable_history s c, elected_committed = committed_config s c, elected_votes = Q\<rparr>),
      publication_tip := (publication_tip s)((c,node_term s c) := durable_history s c)\<rparr>)"
proof -
  have base: "term_of (durable_history s c) < node_term s c"
    by (rule new_election_base[OF journal ok none journalD(8)[OF journal started] quorum(2) vote])
  have other: "h \<in> publications s \<Longrightarrow> (owner h,term_of h) \<noteq> (c,node_term s c)" for h
    using leadershipD(8)[OF ok, of h] none by auto
  show ?thesis
    using ok none base quorum vote other journalD(1,3)[OF journal, of c]
    unfolding leadership_ok_def fresh_votes_def voted_def by auto
qed

lemma leadership_publish:
  assumes ok: "leadership_ok C s" and active: "active_leader s c"
    and tip: "publication_tip s (c,node_term s c) = durable_history s c"
    and quorum: "quorum D Q" and vote: "fresh_votes s c (node_term s c) (durable_history s c) Q"
    and new: "h = durable_history s c @ [\<lparr>pub_term = node_term s c, pub_version = v, pub_payload = payload,
        pub_owner = c, pub_config = D, pub_previous = committed_config s c\<rparr>]"
  shows "leadership_ok C (s\<lparr>publication_tip := (publication_tip s)((c,node_term s c) := h),
      publications := insert h (publications s)\<rparr>)"
proof -
  have meta: "owner h = c" "term_of h = node_term s c" "config_of C h = D" using new by auto
  have extends: "prefix p (publication_tip s (c,node_term s c)) \<Longrightarrow> prefix p h" for p
    using tip new by simp
  obtain e where e: "certificate s (c,node_term s c) = Some e"
    using active unfolding active_leader_def by auto
  have base: "prefix (elected_from e) h"
    by (rule extends[OF leadershipD(7)[OF ok e]])
  have new_votes: "\<exists>R. quorum (config_of C h) R \<and> voted s (owner h) (term_of h) R"
    by (rule exI[of _ Q]) (simp add: meta quorum fresh_votes_voted[OF vote])
  show ?thesis using ok e base new_votes meta extends
    unfolding leadership_ok_def fresh_votes_def voted_def by auto
qed

lemma leadership_certify:
  assumes "leadership_ok C s"
  shows "leadership_ok C (s\<lparr>quorum_commits := insert h (quorum_commits s)\<rparr>)"
  using assms unfolding leadership_ok_def fresh_votes_def voted_def by (auto intro: effective_config_insert)

lemma dynamic_invariants:
  assumes "dynamic_reachable C s"
  shows "journal_ok C s \<and> publications_ok C s \<and> leadership_ok C s"
  using assms
proof (induction rule: dynamic_reachable.induct)
  case boot
  show ?case by (simp add: bootstrapped_def journal_ok_def effective_config_def
      publications_ok_def prefix_closed_def leadership_ok_def)
next
  case (advance s s')
  then have j: "journal_ok C s" and p: "publications_ok C s" and l: "leadership_ok C s" by auto
  from advance.hyps(2) show ?case
  proof (cases rule: transition.cases)
    case start_join
    with j p l show ?thesis
      by (simp add: journal_start_join leadership_start_join publications_ok_def joint_receipts_def)
  next
    case win
    with j p l show ?thesis
      by (simp add: leadership_win journal_ok_def publications_ok_def joint_receipts_def)
  next
    case publish
    then show ?thesis
    proof (intro conjI)
      show "journal_ok C s'" using publish j unfolding journal_ok_def by auto
      show "publications_ok C s'" using publish p j by (blast intro: publications_publish)
      show "leadership_ok C s'" using publish l by (blast intro: leadership_publish)
    qed
  next
    case receive
    with j p l show ?thesis by (simp add: journal_receive publications_receive leadership_ok_def
        fresh_votes_def voted_def)
  next
    case certify
    with j p l show ?thesis by (simp add: journal_certify publications_certify leadership_certify)
  next
    case apply_commit
    with j p l show ?thesis by (simp add: journal_apply publications_ok_def joint_receipts_def
        leadership_ok_def fresh_votes_def voted_def)
  next
    case reboot
    with j p l show ?thesis by (auto simp: journal_ok_def publications_ok_def joint_receipts_def
        leadership_ok_def fresh_votes_def voted_def)
  qed
qed

section \<open>Quorums between committed configurations\<close>

lemma lineage_prefix:
  assumes ok: "publications_ok C s" and ran: "h \<in> insert [] (publications s)"
    and pref: "prefix p h"
  shows "p \<in> insert [] (publications s) \<and> (p = h \<or> position p < position h)"
  using ran pref
proof (induction h rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x h)
  then have pub: "h @ [x] \<in> publications s" by simp
  then have parent: "h \<in> insert [] (publications s)"
    using publicationsD(3)[OF ok] unfolding prefix_closed_def by blast
  have inc: "position h < position (h @ [x])"
    using publicationsD(4)[OF ok pub] by (auto simp: valid_edge_def rank_less_iff)
  show ?case
  proof (cases "p = h @ [x]")
    case True
    with pub show ?thesis by simp
  next
    case False
    then have "prefix p h" using snoc.prems by simp
    from snoc.IH[OF parent this] inc show ?thesis by (auto intro: less_trans)
  qed
qed

lemma position_term_mono: "position p \<le> position h \<Longrightarrow> term_of p \<le> term_of h"
  by (auto simp: rank_le_iff)

text \<open>
  Starting at a checkpoint, either the old or the new configuration remains the
  checkpoint's configuration until an intervening publication is committed.
  A change to both would require applying such a commit before proposing again.
\<close>

lemma checkpoint_config:
  assumes ok: "publications_ok C s" and mem: "h \<in> insert [] (publications s)"
    and p: "prefix p h"
    and gap: "\<forall>k\<in>quorum_commits s. \<not> (position p < position k \<and> position k < position h)"
  shows "config_of C p = carried C h \<or> config_of C p = config_of C h"
  using mem p gap
proof (induction h rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x h)
  show ?case
  proof (cases "p = h @ [x]")
    case True
    then show ?thesis by simp
  next
    case False
    have pub: "h @ [x] \<in> publications s" using snoc.prems(1) by simp
    have parent: "h \<in> insert [] (publications s)"
      using lineage_prefix[OF ok snoc.prems(1), of h] by simp
    have pref: "prefix p h" using snoc.prems(2) False by simp
    have inc: "position h < position (h @ [x])"
      using lineage_prefix[OF ok snoc.prems(1), of h] by simp
    have no_commit: "h \<in> quorum_commits s \<Longrightarrow> p = h"
      using lineage_prefix[OF ok parent pref] snoc.prems(3) inc by blast
    have earlier_gap: "\<forall>k\<in>quorum_commits s. \<not> (position p < position k \<and> position k < position h)"
      using snoc.prems(3) inc by (meson less_trans)
    have ih: "config_of C p = carried C h \<or> config_of C p = config_of C h"
      by (rule snoc.IH[OF parent pref earlier_gap])
    have edge: "valid_edge C (quorum_commits s) h x" by (rule publicationsD(4)[OF ok pub])
    from ih edge no_commit show ?thesis
      unfolding valid_edge_def effective_config_def by auto
  qed
qed

lemma checkpoint_election_quorum:
  assumes ok: "publications_ok C s" "leadership_ok C s"
    and cert: "certificate s (c,t) = Some e"
    and pref: "prefix p (elected_from e)"
    and gap: "\<forall>h\<in>quorum_commits s. \<not> (position p < position h \<and> position h < position (elected_from e))"
    and applied: "elected_from e \<in> quorum_commits s \<Longrightarrow> p = elected_from e"
  shows "quorum (config_of C p) (elected_votes e)"
  using checkpoint_config[OF ok(1) leadershipD(1)[OF ok(2) cert] pref gap]
    leadershipD(3,4,5)[OF ok(2) cert] applied
  unfolding effective_config_def by auto

lemma checkpoint_commit_quorum:
  assumes ok: "publications_ok C s" and committed: "h \<in> quorum_commits s"
    and pref: "prefix p h"
    and gap: "\<forall>k\<in>quorum_commits s. \<not> (position p < position k \<and> position k < position h)"
  obtains Q where "quorum (config_of C p) Q" "\<forall>n\<in>Q. (n,h) \<in> acknowledgements s"
proof -
  have "h \<in> insert [] (publications s)" using publicationsD(5)[OF ok committed] by simp
  from checkpoint_config[OF ok this pref gap] have cfg: "config_of C p = carried C h \<or> config_of C p = config_of C h" .
  obtain Q where "quorum (carried C h) Q" "quorum (config_of C h) Q"
    and receipts: "\<forall>n\<in>Q. (n,h) \<in> acknowledgements s"
    using publicationsD(6)[OF ok committed] unfolding joint_receipts_def by blast
  with cfg have "quorum (config_of C p) Q" by auto
  from this receipts show thesis by (rule that)
qed

lemma rank_maximum:
  fixes f :: "'a \<Rightarrow> 'b::linorder"
  assumes "finite A" "A \<noteq> {}"
  obtains x where "x \<in> A" "\<And>y. y \<in> A \<Longrightarrow> f y \<le> f x"
proof -
  have fin: "finite (image f A)" using assms by simp
  have "Max (image f A) \<in> image f A" using Max_in[OF fin] assms by simp
  then obtain x where x: "x \<in> A" and eq: "Max (image f A) = f x" by blast
  show thesis
  proof (rule that[OF x])
    fix y
    assume "y \<in> A"
    then have "f y \<le> Max (image f A)" by (intro Max_ge[OF fin]) simp
    then show "f y \<le> f x" by (simp only: eq)
  qed
qed

lemma rank_minimum:
  fixes f :: "'a \<Rightarrow> 'b::linorder"
  assumes "finite A" "A \<noteq> {}"
  obtains x where "x \<in> A" "\<And>y. y \<in> A \<Longrightarrow> f x \<le> f y"
proof -
  have fin: "finite (image f A)" using assms by simp
  have "Min (image f A) \<in> image f A" using Min_in[OF fin] assms by simp
  then obtain x where x: "x \<in> A" and eq: "Min (image f A) = f x" by blast
  show thesis
  proof (rule that[OF x])
    fix y
    assume "y \<in> A"
    then have "Min (image f A) \<le> f y" by (intro Min_le[OF fin]) simp
    then show "f x \<le> f y" by (simp only: eq)
  qed
qed

definition unique_leader :: "dynamic_state \<Rightarrow> nat \<Rightarrow> bool" where
  "unique_leader s t \<longleftrightarrow>
    (\<forall>c d e f. certificate s (c,t) = Some e \<longrightarrow> certificate s (d,t) = Some f \<longrightarrow> c = d)"

definition safe_term :: "dynamic_state \<Rightarrow> nat \<Rightarrow> bool" where
  "safe_term s t \<longleftrightarrow> unique_leader s t \<and>
    (\<forall>a\<in>quorum_commits s. \<forall>b\<in>publications s. term_of a < t \<and> term_of b = t \<longrightarrow> prefix a b)"

lemma same_term_prefix:
  assumes ok: "leadership_ok C s" and unique: "unique_leader s (term_of a)"
    and pub: "a \<in> publications s" "b \<in> publications s" and same: "term_of a = term_of b"
  shows "prefix a b \<or> prefix b a"
proof -
  have "owner a = owner b"
    using leadershipD(8)[OF ok pub(1)] leadershipD(8)[OF ok pub(2)] unique same
    unfolding unique_leader_def by fastforce
  with leadershipD(9)[OF ok pub(1)] leadershipD(9)[OF ok pub(2)] same
  show ?thesis by (metis prefix_same_cases)
qed

lemma earlier_prefix:
  assumes pub_ok: "publications_ok C s" and leaders: "leadership_ok C s"
    and lower: "\<And>u. u < t \<Longrightarrow> safe_term s u"
    and a: "a \<in> insert [] (quorum_commits s)" and b: "b \<in> insert [] (publications s)"
    and bt: "term_of b < t" and rank: "position a \<le> position b"
  shows "prefix a b"
proof (cases "a = []")
  case True
  then show ?thesis by simp
next
  case False
  then have commit: "a \<in> quorum_commits s" using a by simp
  have a_pub: "a \<in> publications s" by (rule publicationsD(5)[OF pub_ok commit])
  have b_pub: "b \<in> publications s"
  proof (rule ccontr)
    assume "b \<notin> publications s"
    with b have "b = []" by simp
    moreover have "position [] < position a"
      using lineage_prefix[OF pub_ok, of a "[]"] a_pub False by simp
    ultimately show False using rank by simp
  qed
  have safe: "safe_term s (term_of b)" by (rule lower[OF bt])
  show ?thesis
  proof (cases "term_of a = term_of b")
    case True
    have "unique_leader s (term_of a)" using safe True unfolding safe_term_def by simp
    from same_term_prefix[OF leaders this a_pub b_pub True]
    show ?thesis using lineage_prefix[OF pub_ok, of a b] a_pub rank by auto
  next
    case False
    then have "term_of a < term_of b" using position_term_mono[OF rank] by simp
    with safe commit b_pub show ?thesis unfolding safe_term_def by blast
  qed
qed

lemma older_commit_bound:
  assumes j: "journal_ok C s" and p: "publications_ok C s" and l: "leadership_ok C s"
    and lower: "\<And>u. u < t \<Longrightarrow> safe_term s u"
    and cert: "certificate s (c,t) = Some e"
    and committed: "a \<in> quorum_commits s" and older: "term_of a < t"
  shows "position a \<le> position (elected_from e)"
proof (rule ccontr)
  let ?b = "elected_from e"
  let ?K = "quorum_commits s"
  let ?small = "insert [] {h \<in> ?K. position h \<le> position ?b}"
  let ?large = "{h \<in> ?K. term_of h < t \<and> position ?b < position h}"
  assume not_le: "\<not> position a \<le> position ?b"
  have fin: "finite ?K" using publicationsD(1,5)[OF p] by (meson finite_subset subsetI)
  obtain k where kin: "k \<in> ?small" and kmax: "\<And>h. h \<in> ?small \<Longrightarrow> position h \<le> position k"
    by (rule rank_maximum[of ?small position]) (use fin in auto)
  obtain x where xin: "x \<in> ?large" and xmin: "\<And>h. h \<in> ?large \<Longrightarrow> position x \<le> position h"
    by (rule rank_minimum[of ?large position]) (use fin committed older not_le in auto)
  from kin have kcomm: "k \<in> insert [] ?K" and kb: "position k \<le> position ?b"
    by (auto simp: rank_le_iff split: list.splits)
  from xin have xc: "x \<in> ?K" and xt: "term_of x < t" and bx: "position ?b < position x" by auto
  have kp: "prefix k ?b"
    by (rule earlier_prefix[OF p l lower kcomm leadershipD(1,2)[OF l cert] kb])
  have x_pub: "x \<in> insert [] (publications s)" using publicationsD(5)[OF p xc] by simp
  have kx: "prefix k x"
    by (rule earlier_prefix[OF p l lower kcomm x_pub xt less_imp_le[OF le_less_trans[OF kb bx]]])
  have b_gap: "h \<in> ?K \<Longrightarrow> position k < position h \<Longrightarrow>
    position h \<le> position ?b \<Longrightarrow> False" for h
    using kmax[of h] by auto
  have x_gap: "h \<in> ?K \<Longrightarrow> position k < position h \<Longrightarrow>
    position h < position x \<Longrightarrow> False" for h
  proof -
    assume hc: "h \<in> ?K" and kh: "position k < position h" and hx: "position h < position x"
    have "position ?b < position h" by (rule not_le_imp_less) (rule notI, erule b_gap[OF hc kh])
    moreover have "term_of h < t" using position_term_mono[OF less_imp_le[OF hx]] xt by simp
    ultimately have "h \<in> ?large" using hc by simp
    from xmin[OF this] hx show False by simp
  qed
  have applied: "k = ?b" if "?b \<in> ?K"
  proof (rule ccontr)
    assume "k \<noteq> ?b"
    from lineage_prefix[OF p leadershipD(1)[OF l cert] kp] this
    have "position k < position ?b" by blast
    from b_gap[OF that this order_refl] show False .
  qed
  have bg: "\<forall>h\<in>?K. \<not> (position k < position h \<and> position h < position ?b)"
    using b_gap by (meson less_imp_le)
  have xg: "\<forall>h\<in>?K. \<not> (position k < position h \<and> position h < position x)"
    using x_gap by blast
  have eq: "quorum (config_of C k) (elected_votes e)"
    by (rule checkpoint_election_quorum[OF p l cert kp bg applied])
  obtain Q where q: "quorum (config_of C k) Q" and receipts: "\<forall>n\<in>Q. (n,x) \<in> acknowledgements s"
    by (rule checkpoint_commit_quorum[OF p xc kx xg])
  obtain n where n: "n \<in> elected_votes e" "n \<in> Q" using quorum_intersects[OF eq q] by blast
  obtain r where r: "r \<le> position ?b" "(n,c,t,r) \<in> sent_joins s"
    using leadershipD(6)[OF l cert] n(1) unfolding fresh_votes_def by blast
  have "(n,x) \<in> acknowledgements s" using receipts n(2) by blast
  from journalD(6)[OF j r(2) this xt] r(1) bx show False by order
qed

theorem every_term_safe:
  assumes j: "journal_ok C s" and p: "publications_ok C s" and l: "leadership_ok C s"
  shows "safe_term s t"
proof (induction t rule: less_induct)
  case (less t)
  have older: "position a \<le> position (elected_from e)"
    if "certificate s (c,t) = Some e" "a \<in> quorum_commits s" "term_of a < t" for a c e
    by (rule older_commit_bound[OF j p l less.IH that])
  have unique: "unique_leader s t"
  proof (unfold unique_leader_def, intro allI impI)
    fix c d e f
    assume cert: "certificate s (c,t) = Some e" "certificate s (d,t) = Some f"
    let ?K = "quorum_commits s"
    let ?older = "insert [] {h \<in> ?K. term_of h < t}"
    have fin: "finite ?K" using publicationsD(1,5)[OF p] by (meson finite_subset subsetI)
    obtain k where k: "k \<in> ?older" and max: "\<And>h. h \<in> ?older \<Longrightarrow> position h \<le> position k"
      by (rule rank_maximum[of ?older position]) (use fin in auto)
    have kcomm: "k \<in> insert [] ?K" using k by auto
    have votes: "quorum (config_of C k) (elected_votes g)" if certg: "certificate s (n,t) = Some g" for n g
    proof -
      let ?b = "elected_from g"
      have old: "term_of ?b < t" by (rule leadershipD(2)[OF l certg])
      have kb: "position k \<le> position ?b" using k older[OF certg, of k]
        by (auto simp: rank_le_iff split: list.splits)
      have mem: "?b \<in> insert [] (publications s)" by (rule leadershipD(1)[OF l certg])
      have pref: "prefix k ?b" by (rule earlier_prefix[OF p l less.IH kcomm mem old kb])
      have cutoff: "h \<in> ?K \<Longrightarrow> position h \<le> position ?b \<Longrightarrow> position h \<le> position k" for h
        using old max[of h] position_term_mono[of h ?b] by auto
      have gap: "\<forall>h\<in>?K. \<not> (position k < position h \<and> position h < position ?b)"
      proof (intro ballI notI, elim conjE)
        fix h
        assume hc: "h \<in> ?K" and kh: "position k < position h" and hb: "position h < position ?b"
        from cutoff[OF hc less_imp_le[OF hb]] kh show False by order
      qed
      have applied: "?b \<in> ?K \<Longrightarrow> k = ?b"
        using cutoff[of ?b] lineage_prefix[OF p mem pref] by auto
      show ?thesis by (rule checkpoint_election_quorum[OF p l certg pref gap applied])
    qed
    show "c = d" by (rule same_config_vote[OF j votes[OF cert(1)] votes[OF cert(2)]
          fresh_votes_voted[OF leadershipD(6)[OF l cert(1)]]
          fresh_votes_voted[OF leadershipD(6)[OF l cert(2)]]])
  qed
  have "prefix a b" if ac: "a \<in> quorum_commits s" and bp: "b \<in> publications s"
    and at: "term_of a < t" and bt: "term_of b = t" for a b
  proof -
    obtain e where cert: "certificate s (owner b,t) = Some e" and base: "prefix (elected_from e) b"
      using leadershipD(8)[OF l bp] bt by blast
    have "a \<in> insert [] (quorum_commits s)" using ac by simp
    from earlier_prefix[OF p l less.IH this leadershipD(1,2)[OF l cert] older[OF cert ac at]] base
    show ?thesis by (rule prefix_order.trans)
  qed
  with unique show ?case unfolding safe_term_def by blast
qed

section \<open>Safety for reachable executions\<close>

lemma reachable_term_safe:
  assumes "dynamic_reachable C s"
  shows "safe_term s t"
  using dynamic_invariants[OF assms] by (blast intro: every_term_safe)

theorem dynamic_one_election_candidate_per_term:
  assumes "dynamic_reachable C s"
    "certificate s (c,t) = Some e" "certificate s (d,t) = Some f"
  shows "c = d"
  using reachable_term_safe[OF assms(1), of t] assms(2,3)
  unfolding safe_term_def unique_leader_def by blast

theorem dynamic_unique_publication:
  assumes reach: "dynamic_reachable C s" and pub: "a \<in> publications s" "b \<in> publications s"
    and rank: "position a = position b"
  shows "a = b"
proof -
  from dynamic_invariants[OF reach] have p: "publications_ok C s" and l: "leadership_ok C s" by auto
  have unique: "unique_leader s (term_of a)" using reachable_term_safe[OF reach, of "term_of a"]
    unfolding safe_term_def by simp
  from same_term_prefix[OF l unique pub] rank have "prefix a b \<or> prefix b a" by simp
  with lineage_prefix[OF p, of a b] lineage_prefix[OF p, of b a] pub rank show ?thesis by auto
qed

theorem dynamic_committed_states_form_chain:
  assumes reach: "dynamic_reachable C s" and commits: "a \<in> quorum_commits s" "b \<in> quorum_commits s"
  shows "prefix a b \<or> prefix b a"
proof -
  from dynamic_invariants[OF reach] have p: "publications_ok C s" and l: "leadership_ok C s" by auto
  have pub: "a \<in> publications s" "b \<in> publications s"
    using publicationsD(5)[OF p commits(1)] publicationsD(5)[OF p commits(2)] by auto
  consider (earlier) "term_of a < term_of b" | (same) "term_of a = term_of b" | (later) "term_of b < term_of a" by linarith
  then show ?thesis
  proof cases
    case earlier
    then show ?thesis using reachable_term_safe[OF reach, of "term_of b"] commits(1) pub(2)
      unfolding safe_term_def by blast
  next
    case same
    have "unique_leader s (term_of a)" using reachable_term_safe[OF reach, of "term_of a"]
      unfolding safe_term_def by simp
    then show ?thesis by (rule same_term_prefix[OF l _ pub same])
  next
    case later
    then show ?thesis using reachable_term_safe[OF reach, of "term_of a"] commits(2) pub(1)
      unfolding safe_term_def by blast
  qed
qed

section \<open>The quorum for a first commit\<close>

abbreviation current_tip :: "dynamic_state \<Rightarrow> node \<Rightarrow> lineage" where
  "current_tip s n \<equiv> publication_tip s (n,node_term s n)"

definition local_tips_ok :: "config \<Rightarrow> dynamic_state \<Rightarrow> bool" where
  "local_tips_ok C s \<longleftrightarrow>
    (\<forall>n t. certificate s (n,t) \<noteq> None \<longrightarrow> t \<le> node_term s n) \<and>
    (\<forall>n. active_leader s n \<and> term_of (current_tip s n) = node_term s n \<longrightarrow>
      current_tip s n \<in> publications s \<and>
      (durable_history s n = current_tip s n \<or> durable_history s n = butlast (current_tip s n)) \<and>
      effective_config C (quorum_commits s) (current_tip s n) (committed_config s n))"

lemma local_tips_start_join:
  assumes ok: "local_tips_ok C s" and inc: "node_term s n < t"
  shows "local_tips_ok C (s\<lparr>node_term := (node_term s)(n := t),
      sent_joins := insert (n,c,t,position (durable_history s n)) (sent_joins s),
      joined_since_restart := insert n (joined_since_restart s)\<rparr>)"
proof -
  have old_term: "u \<le> node_term s i" if "certificate s (i,u) \<noteq> None" for i u
    using ok that unfolding local_tips_ok_def by blast
  have none: "certificate s (n,t) = None"
  proof (rule ccontr)
    assume "certificate s (n,t) \<noteq> None"
    from old_term[OF this] inc show False by simp
  qed
  have bound: "u \<le> t" if "certificate s (n,u) \<noteq> None" for u
    using old_term[OF that] inc by linarith
  show ?thesis using ok none bound unfolding local_tips_ok_def active_leader_def by auto
qed

lemma local_tips_win:
  assumes "local_tips_ok C s" "term_of (durable_history s c) < node_term s c"
  shows "local_tips_ok C (s\<lparr>certificate := (certificate s)((c,node_term s c) := Some e),
    publication_tip := (publication_tip s)((c,node_term s c) := durable_history s c)\<rparr>)"
  using assms unfolding local_tips_ok_def active_leader_def by auto

lemma local_tips_publish:
  assumes ok: "local_tips_ok C s"
    and new: "h = durable_history s c @ [\<lparr>pub_term = node_term s c, pub_version = v, pub_payload = payload,
        pub_owner = c, pub_config = D, pub_previous = committed_config s c\<rparr>]"
  shows "local_tips_ok C (s\<lparr>publication_tip := (publication_tip s)((c,node_term s c) := h),
    publications := insert h (publications s)\<rparr>)"
proof -
  have good: "effective_config C (quorum_commits s) h (committed_config s c)"
    by (simp add: new effective_config_def)
  have parent: "butlast h = durable_history s c" by (simp add: new)
  show ?thesis using ok good parent
    unfolding local_tips_ok_def active_leader_def by auto
qed

lemma receive_at_current_tip:
  assumes reach: "dynamic_reachable C s" and local: "local_tips_ok C s"
    and active: "active_leader s n" and current: "term_of (current_tip s n) = node_term s n"
    and pub: "h \<in> publications s" and same: "term_of h = node_term s n"
    and inc: "position (durable_history s n) < position h"
  shows "h = current_tip s n"
proof -
  let ?t = "node_term s n"
  let ?tip = "current_tip s n"
  let ?a = "durable_history s n"
  from dynamic_invariants[OF reach]
  have j: "journal_ok C s" and p: "publications_ok C s" and l: "leadership_ok C s" by auto
  obtain e f where certs: "certificate s (n,?t) = Some e" "certificate s (owner h,?t) = Some f"
    using active leadershipD(8)[OF l pub] same unfolding active_leader_def by auto
  have n: "n = owner h" by (rule dynamic_one_election_candidate_per_term[OF reach certs])
  have pref: "prefix h ?tip" using leadershipD(9)[OF l pub] n same by simp
  have accepted: "?a = ?tip \<or> ?a = butlast ?tip"
    using local active current unfolding local_tips_ok_def by blast
  show ?thesis
  proof (rule ccontr)
    assume ne: "h \<noteq> ?tip"
    have "prefix h (butlast ?tip)"
      using pref ne by (cases ?tip rule: rev_cases) auto
    with pref accepted have "prefix h ?a" by auto
    from lineage_prefix[OF p journalD(1)[OF j] this] inc show False by auto
  qed
qed

lemma local_tips_receive:
  assumes reach: "dynamic_reachable C s" and ok: "local_tips_ok C s"
    and pub: "h \<in> publications s" and t: "term_of h = node_term s n"
    and rank: "position (durable_history s n) < position h"
  shows "local_tips_ok C (s\<lparr>durable_history := (durable_history s)(n := h),
      committed_config := (committed_config s)(n := carried C h),
      acknowledgements := insert (n,h) (acknowledgements s)\<rparr>)"
proof -
  have eq: "active_leader s n \<Longrightarrow> term_of (current_tip s n) = node_term s n \<Longrightarrow> h = current_tip s n"
    by (rule receive_at_current_tip[OF reach ok _ _ pub t rank])
  have cfg: "effective_config C (quorum_commits s) h (carried C h)" by (simp add: effective_config_def)
  show ?thesis using ok eq pub cfg
    unfolding local_tips_ok_def active_leader_def by auto
qed

lemma reachable_local_tips:
  assumes "dynamic_reachable C s"
  shows "local_tips_ok C s"
  using assms
proof (induction rule: dynamic_reachable.induct)
  case boot
  show ?case by (simp add: local_tips_ok_def active_leader_def bootstrapped_def)
next
  case (advance s s')
  from dynamic_invariants[OF advance.hyps(1)] have j: "journal_ok C s" and l: "leadership_ok C s" by auto
  from advance.hyps(2) show ?case
  proof (cases rule: transition.cases)
    case start_join
    with advance.IH show ?thesis by (simp add: local_tips_start_join)
  next
    case win
    with j l advance.IH show ?thesis
      by (blast intro: local_tips_win new_election_base dest: journalD(8))
  next
    case publish
    with advance.IH show ?thesis by (blast intro: local_tips_publish)
  next
    case receive
    with advance.IH advance.hyps(1) show ?thesis by (simp add: local_tips_receive)
  next
    case certify
    with advance.IH show ?thesis
      by (auto simp: local_tips_ok_def active_leader_def intro: effective_config_insert)
  next
    case apply_commit
    with advance.IH show ?thesis
      by (auto simp: local_tips_ok_def active_leader_def effective_config_def)
  next
    case reboot
    with advance.IH show ?thesis by (auto simp: local_tips_ok_def active_leader_def)
  qed
qed

theorem first_commit_quorums_agree:
  assumes reach: "dynamic_reachable C s" and active: "active_leader s c"
    and h: "h = current_tip s c" "term_of h = node_term s c" "h \<notin> quorum_commits s"
  shows "joint_receipts C s h \<longleftrightarrow>
    (\<exists>Q. quorum (committed_config s c) Q \<and> quorum (config_of C h) Q \<and>
      (\<forall>n\<in>Q. (n,h) \<in> acknowledgements s))"
proof -
  have "effective_config C (quorum_commits s) h (committed_config s c)"
    using reachable_local_tips[OF reach] active h unfolding local_tips_ok_def by blast
  then have "committed_config s c = carried C h" using h(3) unfolding effective_config_def by simp
  then show ?thesis unfolding joint_receipts_def by simp
qed

end
