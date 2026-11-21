theory Zen_With_Terms_Refinement
  imports Zen_With_Terms_Translation
begin

section \<open>Relating messages and local state to the dynamic model\<close>

definition normalized :: "rank \<Rightarrow> rank" where
  "normalized k = (if rank_term k = 0 then rank_zero else k)"

lemma normalized_mono:
  "k \<le> r \<Longrightarrow> normalized k \<le> normalized r"
  by (cases k; cases r) (auto simp: normalized_def rank_le_iff)

lemma quorum_nonempty: "quorum C Q \<Longrightarrow> C \<noteq> {}"
  unfolding quorum_def majority_def by auto

lemma quorum_grow:
  assumes q: "quorum C Q" and sub: "Q \<subseteq> R"
  shows "quorum C R"
proof -
  have fin: "finite C" using q unfolding quorum_def majority_def by simp
  have "card (C \<inter> Q) \<le> card (C \<inter> R)"
    by (rule card_mono) (use fin sub in auto)
  with q fin show ?thesis unfolding quorum_def majority_def by auto
qed

lemma election_quorum_insert: "election_quorum x Q \<Longrightarrow> election_quorum x (insert n Q)"
  unfolding election_quorum_def by (auto intro: quorum_grow)

definition known_tip :: "config \<Rightarrow> dynamic_state \<Rightarrow> node \<Rightarrow> 'v local_node \<Rightarrow> bool" where
  "known_tip C a n x \<longleftrightarrow>
    (term_of (current_tip a n) < current_term x \<and> current_tip a n = durable_history a n \<and>
      published_version x = rank_version (accepted_key x)) \<or>
    (current_tip a n \<in> publications a \<and> position (current_tip a n) = published_key x \<and> owner (current_tip a n) = n \<and>
      published_config x = config_of C (current_tip a n) \<and>
      quorum (carried C (current_tip a n)) (join_votes x) \<and> quorum (config_of C (current_tip a n)) (join_votes x) \<and>
      (published_version x = rank_version (accepted_key x) \<longrightarrow> current_tip a n = durable_history a n))"

definition node_link :: "config \<Rightarrow> dynamic_state \<Rightarrow> node \<Rightarrow> 'v local_node \<Rightarrow> bool" where
  "node_link C a n x \<longleftrightarrow>
    current_term x = node_term a n \<and> started_join x = (n \<in> joined_since_restart a) \<and>
    election_won x = active_leader a n \<and>
    normalized (accepted_key x) = position (durable_history a n) \<and>
    (if accepted_config x = {} then durable_history a n = [] \<and> local_committed x = {}
     else accepted_config x = config_of C (durable_history a n)) \<and>
    committed_config a n = (if local_committed x = {} then C else local_committed x) \<and>
    fresh_votes a n (node_term a n) (durable_history a n) (join_votes x) \<and>
    (election_won x \<longrightarrow> election_quorum x (join_votes x) \<and> known_tip C a n x)"

lemma node_linkD:
  assumes "node_link C a n x"
  shows "current_term x = node_term a n"
    "started_join x = (n \<in> joined_since_restart a)"
    "election_won x = active_leader a n"
    "normalized (accepted_key x) = position (durable_history a n)"
    "accepted_config x = {} \<Longrightarrow> durable_history a n = [] \<and> local_committed x = {}"
    "accepted_config x \<noteq> {} \<Longrightarrow> accepted_config x = config_of C (durable_history a n)"
    "committed_config a n = (if local_committed x = {} then C else local_committed x)"
    "fresh_votes a n (node_term a n) (durable_history a n) (join_votes x)"
    "election_won x \<Longrightarrow> election_quorum x (join_votes x)"
    "election_won x \<Longrightarrow> known_tip C a n x"
  using assms unfolding node_link_def by (auto split: if_splits)

lemma node_link_publish_votes[simp]:
  "node_link C a n (x\<lparr>publish_votes := Q\<rparr>) \<longleftrightarrow> node_link C a n x"
  by (simp add: node_link_def known_tip_def election_quorum_def)

lemma node_link_quorum_commits[simp]:
  "node_link C (a\<lparr>quorum_commits := K\<rparr>) n x \<longleftrightarrow> node_link C a n x"
  by (simp add: node_link_def known_tip_def fresh_votes_def active_leader_def)

lemma key_term[simp]: "rank_term (normalized k) = rank_term k"
  by (auto simp: normalized_def rank_le_iff)

lemma publication_positive:
  assumes "publications_ok C a" "h \<in> publications a"
  shows "0 < term_of h"
  using publicationsD(2,4)[OF assms(1)] assms(2)
  by (cases h rule: rev_cases) (auto simp: valid_edge_def)

lemma durable_key:
  assumes "node_link C a n x" "durable_history a n \<noteq> []"
    "dynamic_reachable C a"
  shows "accepted_key x = position (durable_history a n)"
proof -
  have ok: "publications_ok C a" and j: "journal_ok C a" using dynamic_invariants[OF assms(3)] by auto
  have h: "durable_history a n \<in> publications a" using journalD(1)[OF j, of n] assms(2) by simp
  have positive: "0 < term_of (durable_history a n)" by (rule publication_positive[OF ok h])
  with node_linkD(4)[OF assms(1)] show ?thesis by (auto simp: normalized_def split: if_splits)
qed

lemma linked_key_equal:
  assumes "node_link C a n x" "active_leader a n" "published_version x = rank_version (accepted_key x)"
  shows "current_tip a n = durable_history a n"
  using node_linkD(3,10)[OF assms(1)] assms(2,3) unfolding known_tip_def by auto

lemma linked_boot_versions:
  assumes "node_link C a n x" "rank_version (accepted_key x) < v"
  shows "rank_version (position (durable_history a n)) < v"
proof -
  have "rank_version (normalized (accepted_key x)) \<le> rank_version (accepted_key x)" by (simp add: normalized_def)
  then show ?thesis using node_linkD(4)[OF assms(1)] assms(2) by (metis le_less_trans)
qed

fun wire_link :: "dynamic_state \<Rightarrow> 'v message \<Rightarrow> bool" where
  "wire_link a (Join_Msg n c t r) = ((n,c,t,normalized r) \<in> sent_joins a)"
| "wire_link a (Publish_Msg n p payload_value) =
    (pub_config p \<noteq> {} \<and> pub_previous p \<noteq> {} \<and> (\<exists>b. b @ [p] \<in> publications a))"
| "wire_link a (Response_Msg n c k) =
    (\<exists>h\<in>publications a. (n,h) \<in> acknowledgements a \<and> owner h = c \<and> position h = k)"
| "wire_link a (Commit_Msg c n k) =
    (\<exists>h\<in>quorum_commits a. owner h = c \<and> position h = k)"

definition wire_unique :: "'v message set \<Rightarrow> bool" where
  "wire_unique M \<longleftrightarrow>
    (\<forall>n m p q v w. Publish_Msg n p v \<in> M \<longrightarrow> Publish_Msg m q w \<in> M \<longrightarrow>
      request_key p = request_key q \<longrightarrow> p = q \<and> v = w)"

definition ancestry_link :: "'v tla_state \<Rightarrow> dynamic_state \<Rightarrow> bool" where
  "ancestry_link s a \<longleftrightarrow>
    (\<forall>h\<in>publications a. \<forall>p\<in>publications a.
      prefix p h \<and> p \<noteq> h \<longrightarrow> (position p,position h) \<in> descendant s)"

lemma ancestry_edge:
  assumes "ancestry_link s a" "p \<in> publications a" "h \<in> publications a" "prefix p h" "p \<noteq> h"
  shows "(position p,position h) \<in> descendant s"
  using assms unfolding ancestry_link_def by auto

definition linked :: "config \<Rightarrow> 'v tla_state \<Rightarrow> dynamic_state \<Rightarrow> bool" where
  "linked C s a \<longleftrightarrow>
    (\<forall>n. node_link C a n (nodes_at s n)) \<and>
    (\<forall>n p. p \<in> publish_votes (nodes_at s n) \<longrightarrow>
      Response_Msg p n (published_key (nodes_at s n)) \<in> messages s) \<and>
    (\<forall>m\<in>messages s. wire_link a m) \<and> wire_unique (messages s) \<and> ancestry_link s a"

lemma linkedD:
  assumes "linked C s a"
  shows "node_link C a n (nodes_at s n)"
    "p \<in> publish_votes (nodes_at s n) \<Longrightarrow>
      Response_Msg p n (published_key (nodes_at s n)) \<in> messages s"
    "m \<in> messages s \<Longrightarrow> wire_link a m"
    "wire_unique (messages s)"
    "ancestry_link s a"
  using assms unfolding linked_def by auto

definition grows :: "dynamic_state \<Rightarrow> dynamic_state \<Rightarrow> bool" where
  "grows a b \<longleftrightarrow>
    sent_joins a \<subseteq> sent_joins b \<and> publications a \<subseteq> publications b \<and>
    acknowledgements a \<subseteq> acknowledgements b \<and> quorum_commits a \<subseteq> quorum_commits b"

lemma wire_frame:
  "grows a b \<Longrightarrow> wire_link a m \<Longrightarrow> wire_link b m"
  by (cases m) (auto simp: grows_def)

lemma fresh_frame:
  assumes "grows a b" "fresh_votes a n t h Q" "position h \<le> position k" "Q' \<subseteq> Q"
  shows "fresh_votes b n t k Q'"
proof (unfold fresh_votes_def, intro ballI)
  fix q
  assume "q \<in> Q'"
  then have "q \<in> Q" using assms(4) by blast
  then obtain r where "r \<le> position h" "(q,n,t,r) \<in> sent_joins a"
    using assms(2) unfolding fresh_votes_def by blast
  then have "r \<le> position k" using assms(3) by order
  moreover have "(q,n,t,r) \<in> sent_joins b"
    using \<open>(q,n,t,r) \<in> sent_joins a\<close> assms(1) unfolding grows_def by blast
  ultimately show "\<exists>r\<le>position k. (q,n,t,r) \<in> sent_joins b" by blast
qed

definition node_frame :: "dynamic_state \<Rightarrow> dynamic_state \<Rightarrow> node \<Rightarrow> bool" where
  "node_frame a b n \<longleftrightarrow>
    node_term a n = node_term b n \<and> durable_history a n = durable_history b n \<and>
    committed_config a n = committed_config b n \<and>
    (n \<in> joined_since_restart a) = (n \<in> joined_since_restart b) \<and>
    active_leader a n = active_leader b n \<and> current_tip a n = current_tip b n"

lemma node_link_frame:
  assumes node: "node_link C a n x" and g: "grows a b" and f: "node_frame a b n"
  shows "node_link C b n x"
proof -
  have "fresh_votes b n (node_term b n) (durable_history b n) (join_votes x)"
    using fresh_frame[OF g node_linkD(8)[OF node], of "durable_history a n" "join_votes x"] f
    unfolding node_frame_def by simp
  with node g f show ?thesis unfolding node_link_def known_tip_def node_frame_def grows_def
    by (auto simp: Let_def split: if_splits)
qed

lemma link_update:
  assumes old: "linked C s a" and g: "grows a b"
    and node: "node_link C b n x"
    and frame: "\<And>i. i \<noteq> n \<Longrightarrow> node_frame a b i"
    and replies: "\<forall>p\<in>publish_votes x. Response_Msg p n (published_key x) \<in> M"
    and messages: "messages s \<subseteq> M"
    and news: "\<And>m. m \<in> M \<Longrightarrow> m \<notin> messages s \<Longrightarrow> wire_link b m"
    and unique: "wire_unique M" and ancestry: "ancestry_link ((put_node s n x)\<lparr>messages := M, descendant := G\<rparr>) b"
  shows "linked C ((put_node s n x)\<lparr>messages := M, descendant := G\<rparr>) b"
proof -
  have "node_link C b i (((nodes_at s)(n := x)) i)" for i
    using node node_link_frame[OF linkedD(1)[OF old, of i] g] frame[of i] by auto
  moreover have "wire_link b m" if "m \<in> M" for m
    using that news[of m] wire_frame[OF g linkedD(3)[OF old, of m]] by blast
  ultimately show ?thesis using replies messages linkedD(2)[OF old] unique ancestry
    unfolding linked_def put_node_def by auto
qed

lemma ancestry_unchanged:
  assumes "linked C s a" "publications b = publications a" "descendant s \<subseteq> descendant s'"
  shows "ancestry_link s' b"
  using linkedD(5)[OF assms(1)] assms(2,3) unfolding ancestry_link_def by blast

lemma linked_initial:
  "linked C (tla_initial initial_value versions) (bootstrapped C)"
  unfolding linked_def node_link_def wire_unique_def ancestry_link_def fresh_votes_def active_leader_def
  by (simp add: tla_initial_def bootstrapped_def normalized_def)

lemma transition_grows:
  "transition C a b \<Longrightarrow> grows a b"
  by (erule transition.cases) (auto simp: grows_def)

lemma grows_refl[simp]: "grows a a"
  by (simp add: grows_def)

lemma node_frame_refl[simp]: "node_frame a a n"
  by (simp add: node_frame_def)

lemma link_node_update:
  assumes old: "linked C s a" and g: "grows a b"
    and node: "node_link C b n x"
    and frame: "\<And>i. i \<noteq> n \<Longrightarrow> node_frame a b i"
    and replies: "\<forall>p\<in>publish_votes x. Response_Msg p n (published_key x) \<in> messages s"
    and pubs: "publications b = publications a"
  shows "linked C (put_node s n x) b"
proof -
  have "ancestry_link ((put_node s n x)\<lparr>messages := messages s, descendant := descendant s\<rparr>) b"
    by (rule ancestry_unchanged[OF old pubs]) (simp add: put_node_def)
  from link_update[OF old g node frame replies _ _ linkedD(4)[OF old] this] show ?thesis
    by (simp add: put_node_def)
qed

lemma wire_unique_control:
  assumes "wire_unique M" "\<And>d p v. Publish_Msg d p v \<notin> K"
  shows "wire_unique (M \<union> K)"
  using assms unfolding wire_unique_def by blast

lemma fresh_vote_insert:
  assumes fresh: "fresh_votes a c t h Q" and msg: "(n,c,t,r) \<in> sent_joins a" "r \<le> position h"
  shows "fresh_votes a c t h (insert n Q)"
proof (unfold fresh_votes_def, intro ballI)
  fix i
  assume "i \<in> insert n Q"
  then show "\<exists>r\<le>position h. (i,c,t,r) \<in> sent_joins a"
    using fresh msg unfolding fresh_votes_def by blast
qed

lemma certificate_future:
  assumes reaches: "dynamic_reachable C a" and newer: "node_term a n < t"
  shows "certificate a (n,t) = None"
proof (rule ccontr)
  assume "certificate a (n,t) \<noteq> None"
  then have "t \<le> node_term a n" using reachable_local_tips[OF reaches]
    unfolding local_tips_ok_def by blast
  with newer show False by simp
qed

lemma known_tip_insert_join:
  assumes "known_tip C a n x"
  shows "known_tip C a n (x\<lparr>join_votes := insert i (join_votes x)\<rparr>)"
  using assms unfolding known_tip_def by (auto simp: Let_def intro: quorum_grow)

lemma ancestry_extend:
  assumes old: "ancestry_link s a" and ok: "publications_ok C a"
    and parent: "p \<in> insert [] (publications a)" and key: "p \<noteq> [] \<Longrightarrow> k = position p"
    and new: "h = p @ [x]" "h \<notin> publications a"
    and pubs: "publications b = insert h (publications a)"
    and graph: "descendant s' = extend_descendant (descendant s) k (position h)"
  shows "ancestry_link s' b"
  unfolding ancestry_link_def
proof (intro ballI impI)
  fix e d
  assume e: "e \<in> publications b" and d: "d \<in> publications b" and pref: "prefix d e \<and> d \<noteq> e"
  have "e \<in> publications a \<or> e = h" using e pubs by auto
  then show "(position d,position e) \<in> descendant s'"
  proof
    assume ep: "e \<in> publications a"
    have dp: "d \<in> publications a"
      using lineage_prefix[OF ok, of e d] ep pref d pubs new by auto
    from old ep dp pref show ?thesis unfolding ancestry_link_def graph extend_descendant_def by blast
  next
    assume eh: "e = h"
    then have dp: "d \<in> publications a" using d pref pubs by simp
    have pre: "prefix d p" using pref eh new(1) by auto
    then have nonempty: "p \<noteq> []" using dp publicationsD(2)[OF ok] by auto
    have pp: "p \<in> publications a" using parent nonempty by simp
    show ?thesis
    proof (cases "d = p")
      case True
      with key[OF nonempty] eh show ?thesis unfolding graph extend_descendant_def by simp
    next
      case False
      have edge: "(position d,position p) \<in> descendant s" by (rule ancestry_edge[OF old dp pp pre False])
      have "(position d,position h) \<in> {(a,position h) | a. (a,k) \<in> descendant s}"
        by (rule CollectI, rule exI[of _ "position d"]) (simp add: edge key[OF nonempty])
      with eh show ?thesis unfolding graph extend_descendant_def by blast
    qed
  qed
qed

lemma no_wire_collision:
  assumes unique: "wire_unique M" and fresh: "\<And>d p v. Publish_Msg d p v \<in> M \<Longrightarrow> request_key p \<noteq> request_key q"
  shows "wire_unique (M \<union> {Publish_Msg d q w | d. d \<in> N})"
  unfolding wire_unique_def
proof (intro allI impI)
  fix d e p r v x
  let ?M = "M \<union> {Publish_Msg d q w | d. d \<in> N}"
  assume p: "Publish_Msg d p v \<in> ?M" and r: "Publish_Msg e r x \<in> ?M" and key: "request_key p = request_key r"
  from p have p': "Publish_Msg d p v \<in> M \<or> p = q \<and> v = w" by auto
  from r have r': "Publish_Msg e r x \<in> M \<or> r = q \<and> x = w" by auto
  from p' r' key unique fresh[of d p v] fresh[of e r x]
  show "p = r \<and> v = x" unfolding wire_unique_def by auto
qed

locale simulation =
  fixes C :: config and s :: "'v tla_state" and a :: dynamic_state
  assumes boot: "C \<noteq> {}" and reach: "dynamic_reachable C a" and link: "linked C s a"
begin

lemmas node = linkedD(1)[OF link]
lemmas wire = linkedD(3)[OF link]
lemmas sent_response = linkedD(2)[OF link]

lemma simulate_bootstrap:
  assumes "enabled N V s (Bootstrap n)"
  shows "linked C (execute N C initial_value s (Bootstrap n)) a"
proof -
  let ?x = "nodes_at s n"
  let ?x' = "?x\<lparr>accepted_config := C, local_committed := C, accepted_value := initial_value\<rparr>"
  from assms have cfg: "accepted_config ?x = {}" and votes: "publish_votes ?x = {}" and off: "\<not> election_won ?x"
    by (simp_all add: Let_def)
  have empty: "durable_history a n = []" "local_committed ?x = {}"
    using node_linkD(5)[OF node[of n] cfg] by auto
  have "node_link C a n ?x'" using node[of n] boot cfg off empty
    unfolding node_link_def by simp
  from link_node_update[OF link grows_refl this] votes show ?thesis by simp
qed

lemma simulate_restart:
  "\<exists>b. transition C a b \<and> linked C (execute N C initial_value s (Restart n)) b"
proof -
  let ?b = "a\<lparr>joined_since_restart := joined_since_restart a - {n}\<rparr>"
  have step: "transition C a ?b" by (rule transition.reboot)
  have n: "node_link C ?b n (reset_transient (nodes_at s n))" using node[of n]
    unfolding node_link_def reset_transient_def active_leader_def fresh_votes_def by simp
  have frame: "i \<noteq> n \<Longrightarrow> node_frame a ?b i" for i
    unfolding node_frame_def active_leader_def by auto
  have "linked C (execute N C initial_value s (Restart n)) ?b"
    unfolding execute.simps
    by (rule link_node_update[OF link transition_grows[OF step] n frame])
       (simp_all add: reset_transient_def)
  with step show ?thesis by (intro exI[of _ ?b]) simp
qed

lemma simulate_start_join:
  assumes enable: "enabled N V s (Start_Join n c t)"
  shows "\<exists>b. transition C a b \<and> linked C (execute N C initial_value s (Start_Join n c t)) b"
proof -
  let ?b = "a\<lparr>node_term := (node_term a)(n := t),
      sent_joins := insert (n,c,t,position (durable_history a n)) (sent_joins a),
      joined_since_restart := insert n (joined_since_restart a)\<rparr>"
  let ?x = "nodes_at s n"
  let ?y = "(reset_transient ?x)\<lparr>current_term := t, started_join := True\<rparr>"
  let ?msg = "Join_Msg n c t (accepted_key ?x)"
  let ?M = "insert ?msg (messages s)"
  have inc: "node_term a n < t" using enable node_linkD(1)[OF node[of n]] by simp
  have step: "transition C a ?b" by (rule transition.start_join[OF inc])
  have nl: "node_link C ?b n ?y" using node[of n] certificate_future[OF reach inc]
    unfolding node_link_def reset_transient_def active_leader_def fresh_votes_def by simp
  have frame: "i \<noteq> n \<Longrightarrow> node_frame a ?b i" for i
    unfolding node_frame_def active_leader_def by auto
  have add: "wire_link ?b ?msg" using node_linkD(4)[OF node[of n]] by simp
  have unique: "wire_unique ?M"
    using wire_unique_control[OF linkedD(4)[OF link], of "{?msg}"] by simp
  have anc: "ancestry_link ((put_node s n ?y)\<lparr>messages := ?M, descendant := descendant s\<rparr>) ?b"
    by (rule ancestry_unchanged[OF link]) (simp_all add: put_node_def)
  from link_update[OF link transition_grows[OF step] nl frame _ _ _ unique anc] add
  have "linked C (execute N C initial_value s (Start_Join n c t)) ?b"
    by (auto simp: reset_transient_def put_node_def Let_def)
  with step show ?thesis by (intro exI[of _ ?b]) simp
qed

lemma simulate_handle_join:
  assumes enable: "enabled N V s (Handle_Join n c t r)"
  shows "\<exists>b. (b = a \<or> transition C a b) \<and>
    linked C (execute N C initial_value s (Handle_Join n c t r)) b"
proof -
  let ?x = "nodes_at s c"
  let ?Q = "insert n (join_votes ?x)"
  let ?won = "election_quorum ?x ?Q"
  have c: "node_link C a c ?x" by (rule node)
  from enable have sent: "Join_Msg n c t r \<in> messages s" and term_match: "t = node_term a c"
    and fresh: "r \<le> accepted_key ?x" and started: "c \<in> joined_since_restart a"
    and acfg: "accepted_config ?x \<noteq> {}"
    using node_linkD(1,2)[OF c] by (auto simp: Let_def)
  have r: "normalized r \<le> position (durable_history a c)"
    using normalized_mono[OF fresh] node_linkD(4)[OF c] by simp
  have msg: "(n,c,node_term a c,normalized r) \<in> sent_joins a" using wire[OF sent] term_match by simp
  have votes: "fresh_votes a c (node_term a c) (durable_history a c) ?Q"
    by (rule fresh_vote_insert[OF node_linkD(8)[OF c] msg r])
  have retained: "election_won ?x \<Longrightarrow> ?won"
    by (rule election_quorum_insert[OF node_linkD(9)[OF c]])
  show ?thesis
  proof (cases "\<not> election_won ?x \<and> ?won")
    case False
    then have won: "?won = election_won ?x" using retained by blast
    let ?y = "?x\<lparr>join_votes := ?Q\<rparr>"
    have nl: "node_link C a c ?y"
      using c votes won known_tip_insert_join[OF node_linkD(10)[OF c], of n]
      unfolding node_link_def election_quorum_def by simp
    have "linked C (put_node s c ?y) a"
      by (rule link_node_update[OF link grows_refl nl]) (simp_all add: sent_response)
    with False won show ?thesis by (intro exI[of _ a]) (simp add: Let_def)
  next
    case True
    then have off: "\<not> election_won ?x" and won: "?won" by auto
    let ?b = "a\<lparr>certificate := (certificate a)((c,node_term a c) :=
        Some \<lparr>elected_from = durable_history a c, elected_committed = committed_config a c, elected_votes = ?Q\<rparr>),
      publication_tip := (publication_tip a)((c,node_term a c) := durable_history a c)\<rparr>"
    let ?y = "?x\<lparr>join_votes := ?Q, election_won := True, published_version := rank_version (accepted_key ?x)\<rparr>"
    have none: "certificate a (c,node_term a c) = None"
      using node_linkD(3)[OF c] started off unfolding active_leader_def by auto
    have q: "quorum (committed_config a c) ?Q" "quorum (config_of C (durable_history a c)) ?Q"
      using won node_linkD(6)[OF c acfg] node_linkD(7)[OF c]
      unfolding election_quorum_def by (auto dest: quorum_nonempty)
    have step: "transition C a ?b" by (rule transition.win[OF started none q votes])
    have base: "term_of (durable_history a c) < node_term a c"
    proof -
      have j: "journal_ok C a" and l: "leadership_ok C a" using dynamic_invariants[OF reach] by auto
      show ?thesis by (rule new_election_base[OF j l none journalD(8)[OF j started] q(2) votes])
    qed
    have nl: "node_link C ?b c ?y" using c votes won base started node_linkD(1)[OF c]
      unfolding node_link_def known_tip_def fresh_votes_def active_leader_def election_quorum_def
      by simp
    have frame: "i \<noteq> c \<Longrightarrow> node_frame a ?b i" for i
      unfolding node_frame_def active_leader_def by auto
    have replies: "publish_votes ?x = {}"
    proof (rule ccontr)
      assume "publish_votes ?x \<noteq> {}"
      then obtain p where "p \<in> publish_votes ?x" by blast
      from wire[OF sent_response[OF this]] obtain h where
        h: "h \<in> publications a" "owner h = c" "position h = published_key ?x" by auto
      have l: "leadership_ok C a" using dynamic_invariants[OF reach] by auto
      from leadershipD(8)[OF l h(1)] h(2,3) none node_linkD(1)[OF c]
      show False by auto
    qed
    have "linked C (put_node s c ?y) ?b"
      by (rule link_node_update[OF link transition_grows[OF step] nl frame]) (simp_all add: replies)
    with step True show ?thesis by (intro exI[of _ ?b]) (simp add: Let_def)
  qed
qed

lemma current_publication_prefix:
  assumes active: "active_leader a n" and pub: "h \<in> publications a"
    and t: "term_of h = node_term a n"
  shows "owner h = n" "prefix h (current_tip a n)"
proof -
  have l: "leadership_ok C a" using dynamic_invariants[OF reach] by auto
  obtain e f where votes: "certificate a (owner h,node_term a n) = Some e" "certificate a (n,node_term a n) = Some f"
    using leadershipD(8)[OF l pub] active t unfolding active_leader_def by auto
  show "owner h = n" by (rule dynamic_one_election_candidate_per_term[OF reach votes])
  with leadershipD(9)[OF l pub] t show "prefix h (current_tip a n)" by simp
qed

lemma older_tip_impossible:
  assumes active: "active_leader a n" and pub: "h \<in> publications a" and t: "term_of h = node_term a n"
    and old: "term_of (current_tip a n) < node_term a n" and base: "current_tip a n = durable_history a n"
  shows False
proof -
  have j: "journal_ok C a" and p: "publications_ok C a" using dynamic_invariants[OF reach] by auto
  have mem: "current_tip a n \<in> insert [] (publications a)" using base journalD(1)[OF j, of n] by simp
  have "position h \<le> position (current_tip a n)"
    using lineage_prefix[OF p mem current_publication_prefix(2)[OF active pub t]] by auto
  from position_term_mono[OF this] old t show False by simp
qed

lemma simulate_client_value:
  assumes enabled: "enabled N V s (Client_Value n t v payload_value D)"
  shows "\<exists>b. transition C a b \<and> linked C (execute N C initial_value s (Client_Value n t v payload_value D)) b"
proof -
  let ?x = "nodes_at s n"
  let ?hist = "durable_history a n"
  let ?p = "request n t v D (local_committed ?x)"
  let ?h = "?hist @ [?p]"
  let ?b = "a\<lparr>publication_tip := (publication_tip a)((n,node_term a n) := ?h),
    publications := insert ?h (publications a)\<rparr>"
  let ?x' = "?x\<lparr>published_version := v, published_config := D, publish_votes := {}\<rparr>"
  let ?M = "messages s \<union> {Publish_Msg d ?p payload_value | d. d \<in> N}"
  let ?G = "extend_descendant (descendant s) (accepted_key ?x) \<lparr>rank_term = t, rank_version = v\<rparr>"
  have nl: "node_link C a n ?x" by (rule node)
  from enabled have won: "election_won ?x" and ver: "published_version ?x = rank_version (accepted_key ?x)"
    and t: "t = node_term a n" and inc: "published_version ?x < v" and proposed: "quorum D (join_votes ?x)"
    and guard: "D \<noteq> accepted_config ?x \<Longrightarrow> local_committed ?x = accepted_config ?x"
    using node_linkD(1)[OF nl] by (simp_all add: Let_def)
  have active: "active_leader a n" using won node_linkD(3)[OF nl] by simp
  have tip: "current_tip a n = ?hist" by (rule linked_key_equal[OF nl active ver])
  have E: "quorum (local_committed ?x) (join_votes ?x)" and A: "quorum (accepted_config ?x) (join_votes ?x)"
    using node_linkD(9)[OF nl won] unfolding election_quorum_def by auto
  have ac: "accepted_config ?x = config_of C ?hist" by (rule node_linkD(6)[OF nl quorum_nonempty[OF A]])
  have cc: "committed_config a n = local_committed ?x" using node_linkD(7)[OF nl] quorum_nonempty[OF E] by simp
  have inc': "rank_version (position ?hist) < v" by (rule linked_boot_versions[OF nl]) (simp add: ver[symmetric] inc)
  have step: "transition C a ?b"
    by (rule transition.publish[OF active tip inc' _ proposed node_linkD(8)[OF nl]])
       (use guard ac cc t in \<open>auto simp: request_def\<close>)
  have after: "dynamic_reachable C ?b" by (rule dynamic_reachable.advance[OF reach step])
  have p: "publications_ok C a" and j: "journal_ok C a" and l: "leadership_ok C a"
    using dynamic_invariants[OF reach] by auto
  have hk: "position ?h = \<lparr>rank_term = t, rank_version = v\<rparr>" and own: "owner ?h = n" by (simp_all add: request_def)
  have new: "?h \<notin> publications a"
  proof
    assume "?h \<in> publications a"
    from leadershipD(9)[OF l this] hk own t tip show False by simp
  qed
  have no_collision: "request_key q \<noteq> request_key ?p"
    if prior: "Publish_Msg d q w \<in> messages s" for d q w
  proof
    assume keys: "request_key q = request_key ?p"
    obtain b where old_pub: "b @ [q] \<in> publications a" using wire[OF prior] by auto
    have "b @ [q] = ?h"
      by (rule dynamic_unique_publication[OF after]) (simp_all add: old_pub keys)
    with old_pub new show False by simp
  qed
  have new_tip: "known_tip C ?b n ?x'"
    using won t node_linkD(1)[OF nl] E proposed inc ver
    unfolding known_tip_def by (simp add: request_def)
  have new_link: "node_link C ?b n ?x'"
    using nl new_tip active unfolding node_link_def active_leader_def fresh_votes_def election_quorum_def by simp
  have frame: "i \<noteq> n \<Longrightarrow> node_frame a ?b i" for i
    unfolding node_frame_def active_leader_def by auto
  have wires: "wire_link ?b m" if "m \<in> ?M" "m \<notin> messages s" for m
    using that quorum_nonempty[OF E] quorum_nonempty[OF proposed]
    by (auto simp: request_def)
  have graph: "ancestry_link ((put_node s n ?x')\<lparr>messages := ?M, descendant := ?G\<rparr>) ?b"
    by (rule ancestry_extend[OF linkedD(5)[OF link] p journalD(1)[OF j] durable_key[OF nl _ reach] refl new])
       (simp_all add: request_def)
  from link_update[OF link transition_grows[OF step] new_link frame _ _ wires
      no_wire_collision[OF linkedD(4)[OF link] no_collision] graph] step
  show ?thesis by (intro exI[of _ ?b]) (simp add: Let_def)
qed

lemma simulate_handle_publish:
  assumes enabled: "enabled N V s (Handle_Publish n p payload_value)"
  shows "\<exists>b. transition C a b \<and> linked C (execute N C initial_value s (Handle_Publish n p payload_value)) b"
proof -
  let ?x = "nodes_at s n"
  have nl: "node_link C a n ?x" by (rule node)
  from enabled have sent: "Publish_Msg n p payload_value \<in> messages s" and term_match: "pub_term p = node_term a n"
    and ver: "pub_term p = rank_term (accepted_key ?x) \<Longrightarrow> rank_version (accepted_key ?x) < pub_version p"
    using node_linkD(1)[OF nl] by (simp_all add: Let_def)
  obtain base where pub: "base @ [p] \<in> publications a" and cfg: "pub_config p \<noteq> {}" "pub_previous p \<noteq> {}"
    using wire[OF sent] by auto
  let ?h = "base @ [p]"
  let ?b = "a\<lparr>durable_history := (durable_history a)(n := ?h),
    committed_config := (committed_config a)(n := carried C ?h),
    acknowledgements := insert (n,?h) (acknowledgements a)\<rparr>"
  let ?x' = "?x\<lparr>accepted_key := request_key p, accepted_value := payload_value,
    accepted_config := pub_config p, local_committed := pub_previous p\<rparr>"
  let ?msg = "Response_Msg n (pub_owner p) (request_key p)"
  let ?M = "insert ?msg (messages s)"
  have j: "journal_ok C a" and p_ok: "publications_ok C a" using dynamic_invariants[OF reach] by auto
  have pos: "0 < pub_term p" using publication_positive[OF p_ok pub] by simp
  have bound: "rank_term (accepted_key ?x) \<le> pub_term p"
    using journalD(2)[OF j, of n] node_linkD(4)[OF nl] term_match
    by (metis key_term)
  obtain u v where key: "accepted_key ?x = \<lparr>rank_term = u, rank_version = v\<rparr>" by (cases "accepted_key ?x") auto
  have increase: "v < pub_version p" if "u = pub_term p"
    using that key ver by auto
  have "normalized (accepted_key ?x) < request_key p"
  proof (cases "u = 0")
    case True
    then show ?thesis using key pos by (simp add: normalized_def rank_less_iff)
  next
    case False
    from bound key have "u \<le> pub_term p" by simp
    then have "u < pub_term p \<or> u = pub_term p" by (simp add: le_less)
    then show ?thesis using key False increase by (auto simp: normalized_def rank_le_iff rank_less_iff)
  qed
  then have inc: "position (durable_history a n) < position ?h"
    using node_linkD(4)[OF nl] by simp
  have step: "transition C a ?b" by (rule transition.receive[OF pub _ inc]) (simp add: term_match)
  have grow: "grows a ?b" by (rule transition_grows[OF step])
  have nterm: "term_of ?h = node_term a n" using term_match by simp
  have voted: "fresh_votes ?b n (node_term ?b n) (durable_history ?b n) (join_votes ?x')"
    using fresh_frame[OF grow node_linkD(8)[OF nl] less_imp_le[OF inc], of "join_votes ?x"] by simp
  have active: "active_leader a n" if "election_won ?x" using that node_linkD(3)[OF nl] by simp
  have at_tip: "current_tip a n = ?h" if won: "election_won ?x"
  proof -
    have "term_of (current_tip a n) = node_term a n"
      using node_linkD(10)[OF nl won] node_linkD(1)[OF nl] older_tip_impossible[OF active[OF won] pub nterm]
      unfolding known_tip_def by auto
    then show ?thesis using receive_at_current_tip[OF reach reachable_local_tips[OF reach]
        active[OF won] _ pub nterm inc] by simp
  qed
  have leader: "election_quorum ?x' (join_votes ?x') \<and> known_tip C ?b n ?x'" if won: "election_won ?x"
  proof -
    have old_tip: "known_tip C a n ?x" by (rule node_linkD(10)[OF nl won])
    with at_tip[OF won] term_match node_linkD(1)[OF nl] pub
    show ?thesis unfolding known_tip_def election_quorum_def by auto
  qed
  have new_link: "node_link C ?b n ?x'" using nl pos cfg voted leader
    unfolding node_link_def active_leader_def by (simp add: normalized_def)
  have frame: "i \<noteq> n \<Longrightarrow> node_frame a ?b i" for i
    unfolding node_frame_def active_leader_def by auto
  have fresh: "wire_link ?b ?msg" using pub by (auto intro!: bexI[of _ ?h])
  have unique: "wire_unique ?M" using wire_unique_control[OF linkedD(4)[OF link], of "{?msg}"] by simp
  have graph: "ancestry_link ((put_node s n ?x')\<lparr>messages := ?M, descendant := descendant s\<rparr>) ?b"
    by (rule ancestry_unchanged[OF link]) (simp_all add: put_node_def)
  have updated: "linked C ((put_node s n ?x')\<lparr>messages := ?M, descendant := descendant s\<rparr>) ?b"
    by (rule link_update[OF link grow new_link frame _ _ _ unique graph]) (use sent_response fresh in auto)
  from step updated show ?thesis by (intro exI[of _ ?b]) (simp add: put_node_def)
qed

lemma simulate_handle_response:
  assumes enabled: "enabled N V s (Handle_Response n c k)"
  shows "\<exists>b. (b = a \<or> transition C a b) \<and>
    linked C (execute N C initial_value s (Handle_Response n c k)) b"
proof -
  let ?x = "nodes_at s c"
  let ?h = "current_tip a c"
  let ?Q = "insert n (publish_votes ?x)"
  let ?y = "?x\<lparr>publish_votes := ?Q\<rparr>"
  have nl: "node_link C a c ?x" by (rule node)
  from enabled have sent: "Response_Msg n c k \<in> messages s"
    and won: "election_won ?x" and k: "k = published_key ?x" by (auto simp: Let_def)
  have active: "active_leader a c" using won node_linkD(3)[OF nl] by simp
  have term_match: "rank_term k = node_term a c" using k node_linkD(1)[OF nl] by simp
  have replies: "\<forall>p\<in>?Q. Response_Msg p c k \<in> messages s"
    using sent k sent_response[of _ c] by auto
  obtain h where mem: "h \<in> publications a" and hkey: "position h = k"
    using wire[OF sent] by auto
  have ht: "term_of h = node_term a c" by (simp add: hkey term_match)
  have tip: "?h \<in> publications a" "position ?h = k" "owner ?h = c"
    "published_config ?x = config_of C ?h"
    using node_linkD(10)[OF nl won] k node_linkD(1)[OF nl] older_tip_impossible[OF active mem ht]
    unfolding known_tip_def by auto
  have cur: "term_of ?h = node_term a c" using tip(2) term_match by simp
  have acks: "\<forall>p\<in>?Q. (p,?h) \<in> acknowledgements a"
  proof (intro ballI)
    fix p
    assume "p \<in> ?Q"
    from replies[rule_format, OF this] have "Response_Msg p c k \<in> messages s" .
    from wire[OF this] obtain u where u: "u \<in> publications a" "(p,u) \<in> acknowledgements a" "position u = k" by auto
    have "u = ?h" by (rule dynamic_unique_publication[OF reach u(1) tip(1)]) (simp add: u(3) tip(2))
    with u(2) show "(p,?h) \<in> acknowledgements a" by simp
  qed
  have local_replies: "\<forall>p\<in>publish_votes ?y. Response_Msg p c (published_key ?y) \<in> messages s"
    using replies k by simp
  show ?thesis
  proof (cases "response_quorum ?x ?Q")
    case False
    have "node_link C a c ?y" using nl by simp
    from link_node_update[OF link grows_refl this _ local_replies] False
    show ?thesis by (intro exI[of _ a]) (simp add: Let_def put_node_def)
  next
    case True
    let ?b = "a\<lparr>quorum_commits := insert ?h (quorum_commits a)\<rparr>"
    let ?M = "messages s \<union> {Commit_Msg c d k | d. d \<in> N}"
    have joint: "joint_receipts C a ?h"
    proof (cases "?h \<in> quorum_commits a")
      case True
      have "publications_ok C a" using dynamic_invariants[OF reach] by auto
      from publicationsD(6)[OF this True] show ?thesis .
    next
      case False
      have "committed_config a c = local_committed ?x"
        using node_linkD(7)[OF nl] True unfolding response_quorum_def by (auto dest: quorum_nonempty)
      with True tip(4) acks have "\<exists>Q. quorum (committed_config a c) Q \<and> quorum (config_of C ?h) Q \<and>
        (\<forall>p\<in>Q. (p,?h) \<in> acknowledgements a)"
        unfolding response_quorum_def by (intro exI[of _ ?Q]) auto
      with first_commit_quorums_agree[OF reach active refl cur False] show ?thesis by simp
    qed
    have step: "transition C a ?b" by (rule transition.certify[OF active refl tip(1) cur tip(3) joint])
    have nl': "node_link C ?b c ?y" using nl by simp
    have frame: "i \<noteq> c \<Longrightarrow> node_frame a ?b i" for i
      unfolding node_frame_def active_leader_def by simp
    have new: "wire_link ?b m" if "m \<in> ?M" "m \<notin> messages s" for m
      using that tip by (auto intro!: bexI[of _ ?h])
    have unique: "wire_unique ?M" by (rule wire_unique_control[OF linkedD(4)[OF link]]) auto
    have graph: "ancestry_link ((put_node s c ?y)\<lparr>messages := ?M, descendant := descendant s\<rparr>) ?b"
      by (rule ancestry_unchanged[OF link]) (simp_all add: put_node_def)
    have "linked C ((put_node s c ?y)\<lparr>messages := ?M, descendant := descendant s\<rparr>) ?b"
      by (rule link_update[OF link transition_grows[OF step] nl' frame _ _ new unique graph])
         (use local_replies in auto)
    with step True show ?thesis by (intro exI[of _ ?b]) (simp add: Let_def put_node_def)
  qed
qed

lemma simulate_handle_commit:
  assumes enabled: "enabled N V s (Handle_Commit c n k)"
  shows "\<exists>b. transition C a b \<and> linked C (execute N C initial_value s (Handle_Commit c n k)) b"
proof -
  let ?x = "nodes_at s n"
  let ?h = "durable_history a n"
  let ?b = "a\<lparr>committed_config := (committed_config a)(n := config_of C ?h)\<rparr>"
  let ?y = "?x\<lparr>local_committed := accepted_config ?x\<rparr>"
  have nl: "node_link C a n ?x" by (rule node)
  from enabled have sent: "Commit_Msg c n k \<in> messages s" and t: "rank_term k = node_term a n"
    and k: "k = accepted_key ?x" and guard: "election_won ?x \<Longrightarrow> rank_version k = published_version ?x"
    using node_linkD(1)[OF nl] by (auto simp: Let_def)
  obtain h where committed: "h \<in> quorum_commits a" and hk: "position h = k"
    using wire[OF sent] by auto
  have p: "publications_ok C a" and j: "journal_ok C a" using dynamic_invariants[OF reach] by auto
  have pub: "h \<in> publications a" by (rule publicationsD(5)[OF p committed])
  have pos: "0 < rank_term k" using publication_positive[OF p pub] hk by simp
  have match: "position ?h = k"
    using node_linkD(4)[OF nl] k pos unfolding normalized_def by simp
  have mem: "?h \<in> publications a" using journalD(1)[OF j, of n] match pos by auto
  have same: "?h = h" by (rule dynamic_unique_publication[OF reach mem pub]) (simp add: hk match)
  have ack: "?h \<in> quorum_commits a" using same committed by simp
  have cur: "term_of ?h = node_term a n" using match t by simp
  have own: "active_leader a n \<longrightarrow> ?h = current_tip a n"
    using guard k node_linkD(3)[OF nl] linked_key_equal[OF nl] by auto
  have step: "transition C a ?b" by (rule transition.apply_commit[OF ack cur own])
  have nonempty: "accepted_config ?x \<noteq> {}"
    using node_linkD(5)[OF nl] mem publicationsD(2)[OF p] by auto
  have cfg: "accepted_config ?x = config_of C ?h" by (rule node_linkD(6)[OF nl nonempty])
  have nl': "node_link C ?b n ?y" using nl nonempty cfg
    unfolding node_link_def known_tip_def election_quorum_def fresh_votes_def active_leader_def by auto
  have frame: "i \<noteq> n \<Longrightarrow> node_frame a ?b i" for i
    unfolding node_frame_def active_leader_def by simp
  have "linked C (put_node s n ?y) ?b"
    by (rule link_node_update[OF link transition_grows[OF step] nl' frame])
       (auto intro: sent_response)
  with step show ?thesis by (intro exI[of _ ?b]) (simp add: Let_def)
qed

theorem simulate_action:
  assumes "enabled N V s action"
  shows "\<exists>b. (b = a \<or> transition C a b) \<and> linked C (execute N C initial_value s action) b"
  using assms
proof (cases action)
  case (Bootstrap n)
  then show ?thesis using simulate_bootstrap[of N V n initial_value] assms by blast
next
  case (Start_Join n c t)
  then have "enabled N V s (Start_Join n c t)" using assms by simp
  from simulate_start_join[OF this, of initial_value] Start_Join show ?thesis by blast
next
  case (Handle_Join n c t r)
  then show ?thesis using simulate_handle_join[of N V n c t r initial_value] assms by simp
next
  case (Client_Value n t v payload_value D)
  then show ?thesis using simulate_client_value[of N V n t v payload_value D initial_value] assms by blast
next
  case (Handle_Publish n p payload_value)
  then show ?thesis using simulate_handle_publish[of N V n p payload_value initial_value] assms by blast
next
  case (Handle_Response n c k)
  then show ?thesis using simulate_handle_response[of N V n c k initial_value] assms by simp
next
  case (Handle_Commit c n k)
  then show ?thesis using simulate_handle_commit[of N V c n k initial_value] assms by blast
next
  case (Restart n)
  then show ?thesis using simulate_restart[of N initial_value n] by blast
qed

end

theorem tla_dynamic_refinement:
  assumes "tla_reachable N V C initial_value versions s"
  shows "\<exists>a. dynamic_reachable C a \<and> linked C s a"
  using assms
proof (induction rule: tla_reachable.induct)
  case init
  have fin: "finite C" using init.hyps by (meson finite_subset)
  show ?case by (intro exI[of _ "bootstrapped C"] conjI)
      (rule dynamic_reachable.boot[OF fin init.hyps(3)], rule linked_initial)
next
  case (advance s action)
  then obtain a where a: "dynamic_reachable C a" "linked C s a" by blast
  have nonempty: "C \<noteq> {}" using a(1) by (induction rule: dynamic_reachable.induct) auto
  interpret simulation C s a by (unfold_locales; fact)
  obtain b where step: "b = a \<or> transition C a b" and link: "linked C (execute N C initial_value s action) b"
    using simulate_action[OF advance.hyps(2), of initial_value] by blast
  have "dynamic_reachable C b" using a(1) step by (auto intro: dynamic_reachable.advance)
  with link show ?case by blast
qed

section \<open>Transfer to TLA+ messages and descendant edges\<close>

definition tla_next :: "node set \<Rightarrow> 'v set \<Rightarrow> config \<Rightarrow> 'v \<Rightarrow> 'v tla_state \<Rightarrow> 'v tla_state \<Rightarrow> bool" where
  "tla_next N V C initial_value s s' \<longleftrightarrow>
    (\<exists>action. enabled N V s action \<and> s' = execute N C initial_value s action)"

lemma followed_by_simulation:
  assumes run: "rtranclp (tla_next N V C initial_value) s s'"
    and reach: "dynamic_reachable C a" and link: "linked C s a"
  shows "\<exists>b. rtranclp (transition C) a b \<and> dynamic_reachable C b \<and> linked C s' b"
  using run
proof (induction rule: rtranclp_induct)
  case base
  show ?case using reach link by blast
next
  case (step u v)
  then obtain b where trail: "rtranclp (transition C) a b" and b: "dynamic_reachable C b" "linked C u b" by blast
  have nonempty: "C \<noteq> {}" using b(1) by (induction rule: dynamic_reachable.induct) auto
  interpret simulation C u b by (unfold_locales; fact)
  obtain action where enabled: "enabled N V u action" and v: "v = execute N C initial_value u action"
    using step.hyps(2) unfolding tla_next_def by blast
  obtain c where move: "c = b \<or> transition C b c" and c: "linked C v c"
    using simulate_action[OF enabled, of initial_value] v by blast
  have "rtranclp (transition C) a c" using trail move by (auto intro: rtranclp.rtrancl_into_rtrancl)
  moreover have "dynamic_reachable C c" using b(1) move by (auto intro: dynamic_reachable.advance)
  ultimately show ?case using c by blast
qed

lemma certificate_persists:
  assumes "rtranclp (transition C) a b" "certificate a k = Some e"
  shows "certificate b k = Some e"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step u v)
  from step.hyps(2) show ?case using step.IH[OF step.prems]
    by (cases rule: transition.cases) auto
qed

theorem tla_one_election_candidate_per_term:
  assumes reach: "tla_reachable N V C initial_value versions s"
    and run: "rtranclp (tla_next N V C initial_value) s s'"
    and won: "election_won (nodes_at s c)" "election_won (nodes_at s' d)"
    and same: "current_term (nodes_at s c) = current_term (nodes_at s' d)"
  shows "c = d"
proof -
  obtain a where a: "dynamic_reachable C a" "linked C s a"
    using tla_dynamic_refinement[OF reach] by blast
  obtain b where trail: "rtranclp (transition C) a b" and b: "dynamic_reachable C b" "linked C s' b"
    using followed_by_simulation[OF run a] by blast
  let ?t = "current_term (nodes_at s c)"
  have u: "node_link C a c (nodes_at s c)" and v: "node_link C b d (nodes_at s' d)"
    by (rule linkedD(1)[OF a(2)], rule linkedD(1)[OF b(2)])
  obtain e f where e: "certificate a (c,?t) = Some e" and f: "certificate b (d,?t) = Some f"
    using node_linkD(1,3)[OF u] node_linkD(1,3)[OF v] won same unfolding active_leader_def by auto
  show ?thesis by (rule dynamic_one_election_candidate_per_term[OF b(1) certificate_persists[OF trail e] f])
qed

theorem tla_one_publisher_per_term:
  assumes reach: "tla_reachable N V C initial_value versions s"
    and m: "Publish_Msg d p v \<in> messages s" "Publish_Msg e q w \<in> messages s"
    and t: "pub_term p = pub_term q"
  shows "pub_owner p = pub_owner q"
proof -
  obtain a where a: "dynamic_reachable C a" "linked C s a"
    using tla_dynamic_refinement[OF reach] by blast
  obtain h k where pubs: "h @ [p] \<in> publications a" "k @ [q] \<in> publications a"
    using linkedD(3)[OF a(2) m(1)] linkedD(3)[OF a(2) m(2)] by auto
  have l: "leadership_ok C a" using dynamic_invariants[OF a(1)] by auto
  obtain ep eq where "certificate a (pub_owner p,pub_term p) = Some ep"
    "certificate a (pub_owner q,pub_term p) = Some eq"
    using leadershipD(8)[OF l pubs(1)] leadershipD(8)[OF l pubs(2)] t by auto
  then show ?thesis by (rule dynamic_one_election_candidate_per_term[OF a(1)])
qed

theorem tla_log_matching:
  assumes "tla_reachable N V C initial_value versions s"
    "Publish_Msg d p v \<in> messages s" "Publish_Msg e q w \<in> messages s"
    "request_key p = request_key q"
  shows "p = q \<and> v = w"
proof -
  obtain a where "linked C s a" using tla_dynamic_refinement[OF assms(1)] by blast
  from linkedD(4)[OF this] assms(2-4) show ?thesis unfolding wire_unique_def by blast
qed

definition commit_for :: "'v tla_state \<Rightarrow> publication \<Rightarrow> bool" where
  "commit_for s p \<longleftrightarrow> (\<exists>c d. Commit_Msg c d (request_key p) \<in> messages s)"

lemma committed_request_link:
  assumes a: "dynamic_reachable C a" "linked C s a"
    and pub: "Publish_Msg d p v \<in> messages s" and commit: "commit_for s p"
  obtains h where "h \<in> quorum_commits a" "h \<in> publications a" "position h = request_key p"
proof -
  obtain h where hp: "h @ [p] \<in> publications a" using linkedD(3)[OF a(2) pub] by auto
  obtain c d where "Commit_Msg c d (request_key p) \<in> messages s" using commit unfolding commit_for_def by blast
  from linkedD(3)[OF a(2) this] obtain k where kc: "k \<in> quorum_commits a" and kp: "position k = request_key p" by auto
  have pub_ok: "publications_ok C a" using dynamic_invariants[OF a(1)] by auto
  have kpub: "k \<in> publications a" by (rule publicationsD(5)[OF pub_ok kc])
  have "k = h @ [p]" by (rule dynamic_unique_publication[OF a(1) kpub hp]) (simp add: kp)
  with kc have "h @ [p] \<in> quorum_commits a" by simp
  from this hp show thesis by (rule that) simp
qed

theorem tla_committed_values_form_chain:
  assumes reach: "tla_reachable N V C initial_value versions s"
    and m: "Publish_Msg d p v \<in> messages s" "Publish_Msg e q w \<in> messages s"
    and commits: "commit_for s p" "commit_for s q"
    and distinct: "request_key p \<noteq> request_key q"
  shows "(request_key p,request_key q) \<in> descendant s \<or> (request_key q,request_key p) \<in> descendant s"
proof -
  obtain a where a: "dynamic_reachable C a" "linked C s a"
    using tla_dynamic_refinement[OF reach] by blast
  obtain h where h: "h \<in> quorum_commits a" "h \<in> publications a" "position h = request_key p"
    by (rule committed_request_link[OF a m(1) commits(1)])
  obtain k where k: "k \<in> quorum_commits a" "k \<in> publications a" "position k = request_key q"
    by (rule committed_request_link[OF a m(2) commits(2)])
  have prefixes: "prefix h k \<or> prefix k h" by (rule dynamic_committed_states_form_chain[OF a(1) h(1) k(1)])
  have different: "h \<noteq> k" "k \<noteq> h" using distinct h(3) k(3) by auto
  from prefixes show ?thesis
  proof
    assume "prefix h k"
    from ancestry_edge[OF linkedD(5)[OF a(2)] h(2) k(2) this different(1)] h(3) k(3)
    show ?thesis by simp
  next
    assume "prefix k h"
    from ancestry_edge[OF linkedD(5)[OF a(2)] k(2) h(2) this different(2)] h(3) k(3)
    show ?thesis by simp
  qed
qed

end
