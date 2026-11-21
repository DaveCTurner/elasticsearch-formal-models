theory Stateless_Persistence
  imports Master_Service_Executors
begin

section \<open>Lease, published histories, and completed blob images\<close>

type_synonym incarnation_id = "node \<times> nat"

datatype stored_search = Probe nat | Found lineage | No_Stored_State

record stateless_state =
  reserved_term :: nat
  confirmed_floor :: nat
  granted_to :: "nat \<Rightarrow> incarnation_id option"
  confirmed_terms :: "nat set"
  issued :: "lineage set"
  latest_issued :: "nat \<Rightarrow> lineage option"
  completed_images :: "lineage set"
  visible_image :: "nat \<Rightarrow> lineage option"
  searches :: "nat \<Rightarrow> stored_search option"
  approvals :: "lineage set"
  frontier :: lineage
  notifications :: "lineage set"

definition stateless_initial where
  "stateless_initial = \<lparr>reserved_term = 0, confirmed_floor = 0, granted_to = (\<lambda>_. None),
    confirmed_terms = {}, issued = {}, latest_issued = (\<lambda>_. None), completed_images = {},
    visible_image = (\<lambda>_. None), searches = (\<lambda>_. None), approvals = {}, frontier = [], notifications = {}\<rparr>"

definition holds_grant where
  "holds_grant s who t \<longleftrightarrow> t \<in> confirmed_terms s \<and> granted_to s t = Some who"

definition newer_image where
  "newer_image warm remote = (if position warm < position remote then remote else warm)"

inductive election_base for s t warm where
  empty:
    "searches s t = Some No_Stored_State \<Longrightarrow> election_base s t warm warm"
| retained_local:
    "searches s t = Some (Found seen) \<Longrightarrow> position seen \<le> position warm \<Longrightarrow> election_base s t warm warm"
| downloaded:
    "searches s t = Some (Found seen) \<Longrightarrow> remote \<in> completed_images s \<Longrightarrow>
     term_of remote = term_of seen \<Longrightarrow>
     position seen \<le> position remote \<or> term_of seen \<noteq> term_of (frontier s) \<or>
       position (frontier s) \<le> position remote \<Longrightarrow>
     election_base s t warm (newer_image warm remote)"

definition stateless_update where
  "stateless_update who t payload F base =
    base @ [\<lparr>pub_term = t, pub_version = Suc (rank_version (position base)), pub_payload = payload,
      pub_owner = fst who, pub_config = {fst who}, pub_previous = F\<rparr>]"

inductive publish_parent for s t where
  first:
    "latest_issued s t = None \<Longrightarrow> warm \<in> insert [] (issued s) \<Longrightarrow> term_of warm < t \<Longrightarrow>
     election_base s t warm base \<Longrightarrow> publish_parent s t base"
| subsequent:
    "latest_issued s t = Some base \<Longrightarrow> base \<in> approvals s \<Longrightarrow> publish_parent s t base"

text \<open>
  reserve is the successful register CAS effect. A CAS whose caller receives
  an exception may still reserve a term. Only a success callback confirms
  a term and allows use of its grant. A lease read in progress need not be
  linearizable with a concurrent CAS. The approval rule uses the largest
  completed successful grant at read invocation as a lower bound. It can
  therefore approve an old upload during an overlapping CAS, but the upload
  already exists when the read begins.

  Blob visibility is separate from lease ownership. Old leaders may finish
  an upload after a higher term is confirmed. A directory exposes a completed
  image only after its segments manifest is visible. A header probe counts
  down from the election term, skipping absent directories. A successful
  download may return a different image in the probed directory. At the
  frontier term, the image must still cover the approved history. Below
  the frontier, partial cleanup may expose an older manifest or leave no
  manifest at all. The local copy is eligible even after volatile restart,
  which supplies the empty history.
\<close>

inductive stateless_step where
  reserve:
    "expected = reserved_term s \<Longrightarrow> t = max proposed (Suc expected) \<Longrightarrow>
     stateless_step s (s\<lparr>reserved_term := t, granted_to := (granted_to s)(t := Some who)\<rparr>)"
| confirm:
    "granted_to s t = Some who \<Longrightarrow>
     stateless_step s (s\<lparr>confirmed_floor := max t (confirmed_floor s), confirmed_terms := insert t (confirmed_terms s)\<rparr>)"
| start_search:
    "holds_grant s who t \<Longrightarrow>
     stateless_step s (s\<lparr>searches := (searches s)(t := Some (Probe (t - 1)))\<rparr>)"
| absent:
    "searches s t = Some (Probe i) \<Longrightarrow> visible_image s i = None \<or> i < term_of (frontier s) \<Longrightarrow>
     stateless_step s (s\<lparr>searches := (searches s)(t := Some (if 1 < i then Probe (i - 1) else No_Stored_State))\<rparr>)"
| header:
    "searches s t = Some (Probe i) \<Longrightarrow>
     visible_image s i = Some h \<or> (h \<in> completed_images s \<and> term_of h = i \<and>
       (i = term_of (frontier s) \<longrightarrow> position (frontier s) \<le> position h)) \<Longrightarrow>
     stateless_step s (s\<lparr>searches := (searches s)(t := Some (Found h))\<rparr>)"
| publish:
    "holds_grant s who t \<Longrightarrow> publish_parent s t base \<Longrightarrow>
     h = stateless_update who t payload F base \<Longrightarrow>
     stateless_step s (s\<lparr>issued := insert h (issued s), latest_issued := (latest_issued s)(t := Some h)\<rparr>)"
| upload:
    "latest_issued s t = Some h \<Longrightarrow>
     (\<And>old. visible_image s t = Some old \<Longrightarrow> position old \<le> position h) \<Longrightarrow>
     stateless_step s (s\<lparr>completed_images := insert h (completed_images s), visible_image := (visible_image s)(t := Some h)\<rparr>)"
| approve:
    "latest_issued s t = Some h \<Longrightarrow> visible_image s t = Some h \<Longrightarrow>
     confirmed_floor s \<le> t \<Longrightarrow>
     stateless_step s (s\<lparr>approvals := insert h (approvals s), frontier := h\<rparr>)"
| notify_commit:
    "h \<in> approvals s \<Longrightarrow>
     stateless_step s (s\<lparr>notifications := insert h (notifications s)\<rparr>)"
| cleanup:
    "h \<in> notifications s \<Longrightarrow> removed \<subseteq> {i. i < term_of h} \<Longrightarrow>
     stateless_step s (s\<lparr>visible_image := (\<lambda>i. if i \<in> removed then None else visible_image s i)\<rparr>)"

inductive stateless_reachable where
  init: "stateless_reachable stateless_initial"
| step: "stateless_reachable s \<Longrightarrow> stateless_step s s' \<Longrightarrow> stateless_reachable s'"

section \<open>State invariants\<close>

definition lease_ok where
  "lease_ok s \<longleftrightarrow>
    (\<forall>t who. granted_to s t = Some who \<longrightarrow> 0 < t \<and> t \<le> reserved_term s) \<and>
    (\<forall>t\<in>confirmed_terms s. 0 < t \<and> t \<le> confirmed_floor s \<and> granted_to s t \<noteq> None)"

definition issued_ok where
  "issued_ok s \<longleftrightarrow>
    (\<forall>t h. latest_issued s t = Some h \<longrightarrow> h \<in> issued s \<and> term_of h = t) \<and>
    (\<forall>h\<in>issued s. h \<noteq> [] \<and> 0 < term_of h \<and>
      (\<exists>who. holds_grant s who (term_of h) \<and> owner h = fst who) \<and>
      (\<exists>p. latest_issued s (term_of h) = Some p \<and> prefix h p \<and> position h \<le> position p)) \<and>
    (\<forall>h\<in>issued s. \<forall>p\<in>issued s. position h = position p \<longrightarrow> h = p)"

definition store_ok where
  "store_ok s \<longleftrightarrow> completed_images s \<subseteq> issued s \<and>
    (\<forall>i h. visible_image s i = Some h \<longrightarrow> h \<in> completed_images s \<and> term_of h = i)"

definition frontier_ok where
  "frontier_ok s \<longleftrightarrow> (frontier s = [] \<or> frontier s \<in> approvals s) \<and>
    notifications s \<subseteq> approvals s \<and>
    (\<forall>h\<in>approvals s. h \<in> issued s \<and> prefix h (frontier s) \<and> position h \<le> position (frontier s)) \<and>
    (\<forall>p\<in>issued s. position (frontier s) \<le> position p \<longrightarrow> prefix (frontier s) p)"

definition retained_frontier where
  "retained_frontier s \<longleftrightarrow> (frontier s \<noteq> [] \<longrightarrow>
    (\<exists>d. visible_image s (term_of (frontier s)) = Some d \<and> position (frontier s) \<le> position d))"

fun search_bound where
  "search_bound h (Probe i) = (term_of h \<le> i)"
| "search_bound h (Found b) = (position h \<le> position b)"
| "search_bound h No_Stored_State = False"

fun search_origin where
  "search_origin images t (Probe i) = (i < t)"
| "search_origin images t (Found b) = (b \<in> images \<and> term_of b < t)"
| "search_origin images t No_Stored_State = True"

lemma search_origin_grows:
  "search_origin imgs t q \<Longrightarrow> search_origin (insert h imgs) t q"
  by (cases q) simp_all

definition searches_ok where
  "searches_ok s \<longleftrightarrow> (\<forall>t q. searches s t = Some q \<longrightarrow>
    t \<in> confirmed_terms s \<and> search_origin (completed_images s) t q \<and>
      (frontier s \<noteq> [] \<and> term_of (frontier s) < t \<longrightarrow> search_bound (frontier s) q))"

lemmas stateless_inv_defs = lease_ok_def issued_ok_def store_ok_def frontier_ok_def retained_frontier_def searches_ok_def

lemma position_term_mono: "position a \<le> position b \<Longrightarrow> term_of a \<le> term_of b"
  by (cases "position a"; cases "position b") (auto simp: rank_le_iff)

lemma earlier_term_position: "term_of a < term_of b \<Longrightarrow> position a < position b"
  by (cases "position a"; cases "position b") (simp add: rank_less_iff)

lemma zero_key_le: "rank_zero \<le> (p :: rank)"
  by (cases p) (auto simp: rank_le_iff)

lemma new_tip_fields:
  "term_of (stateless_update who t v F b) = t"
  "owner (stateless_update who t v F b) = fst who"
  "stateless_update who t v F b \<noteq> []"
  "prefix b (stateless_update who t v F b)"
  "term_of b \<le> t \<Longrightarrow> position b < position (stateless_update who t v F b)"
  by (auto simp: stateless_update_def rank_less_iff)

lemma issued_latest:
  assumes "issued_ok s" "h \<in> issued s"
  obtains b where "latest_issued s (term_of h) = Some b" "prefix h b" "position h \<le> position b"
  using assms unfolding issued_ok_def by (meson)

lemma issued_term_bound:
  assumes "lease_ok s" "issued_ok s" "h \<in> issued s"
  shows "term_of h \<le> confirmed_floor s"
proof -
  have "term_of h \<in> confirmed_terms s"
    using assms(2,3) by (auto simp: issued_ok_def holds_grant_def)
  with assms(1) show ?thesis unfolding lease_ok_def by auto
qed

lemma frontier_issued:
  "frontier_ok s \<Longrightarrow> frontier s \<noteq> [] \<Longrightarrow> frontier s \<in> issued s"
  unfolding frontier_ok_def by blast

lemma issued_positive:
  "issued_ok s \<Longrightarrow> h \<in> issued s \<Longrightarrow> 0 < term_of h"
  unfolding issued_ok_def by fast

lemma issued_binding:
  assumes "issued_ok s" "p \<in> issued s"
  obtains who where "holds_grant s who (term_of p)" "owner p = fst who"
  using assms unfolding issued_ok_def by (meson)

lemma issued_key_eq:
  "issued_ok s \<Longrightarrow> h \<in> issued s \<Longrightarrow> p \<in> issued s \<Longrightarrow>
    position h = position p \<Longrightarrow> h = p"
  unfolding issued_ok_def by fast

lemma search_observation:
  assumes "searches_ok s" "searches s t = Some q"
  shows "t \<in> confirmed_terms s" "search_origin (completed_images s) t q"
    "frontier s \<noteq> [] \<Longrightarrow> term_of (frontier s) < t \<Longrightarrow> search_bound (frontier s) q"
  using assms unfolding searches_ok_def by auto

lemma election_base_facts:
  assumes base: "election_base s t warm b" and searches: "searches_ok s" and store: "store_ok s"
    and warm: "warm \<in> insert [] (issued s)" "term_of warm < t"
  shows "b \<in> insert [] (issued s)" "term_of b < t"
    "frontier s \<noteq> [] \<Longrightarrow> term_of (frontier s) < t \<Longrightarrow> position (frontier s) \<le> position b"
proof -
  have result: "b \<in> insert [] (issued s) \<and> term_of b < t \<and>
    (frontier s \<noteq> [] \<and> term_of (frontier s) < t \<longrightarrow> position (frontier s) \<le> position b)"
    using base
  proof cases
    case empty
    have impossible: "False" if "frontier s \<noteq> []" "term_of (frontier s) < t"
      using search_observation(3)[OF searches empty(2) that] by simp
    show ?thesis using empty(1) warm impossible by auto
  next
    case (retained_local seen)
    have bound: "position (frontier s) \<le> position seen" if "frontier s \<noteq> []" "term_of (frontier s) < t"
      using search_observation(3)[OF searches retained_local(2) that] by simp
    show ?thesis using retained_local(1,3) warm bound by (auto intro: order_trans)
  next
    case (downloaded seen remote)
    have origin: "term_of seen < t" using search_observation(2)[OF searches downloaded(2)] by simp
    have remote: "remote \<in> issued s" using store downloaded(3) unfolding store_ok_def by blast
    have bound: "position (frontier s) \<le> position b" if "frontier s \<noteq> []" "term_of (frontier s) < t"
    proof -
      have low: "position (frontier s) \<le> position seen"
        using search_observation(3)[OF searches downloaded(2) that] by simp
      have "position (frontier s) \<le> position remote"
      proof (cases "term_of seen = term_of (frontier s)")
        case True
        with downloaded(5) low show ?thesis by (meson order_trans)
      next
        case False
        with position_term_mono[OF low] downloaded(4)
        have "term_of (frontier s) < term_of remote" by auto
        then show ?thesis by (rule less_imp_le[OF earlier_term_position])
      qed
      then show ?thesis using downloaded(1)
        by (auto simp: newer_image_def not_less split: if_splits intro: order_trans)
    qed
    show ?thesis using downloaded(1,4) remote warm origin bound
      by (auto simp: newer_image_def split: if_splits)
  qed
  from result show "b \<in> insert [] (issued s)" "term_of b < t"
    "frontier s \<noteq> [] \<Longrightarrow> term_of (frontier s) < t \<Longrightarrow> position (frontier s) \<le> position b"
    by blast+
qed

lemma parent_facts:
  assumes parent: "publish_parent s t b" and issued: "issued_ok s" and ff: "frontier_ok s"
    and searches: "searches_ok s" and store: "store_ok s"
  shows "b \<in> insert [] (issued s)" "term_of b \<le> t"
    "term_of (frontier s) \<le> t \<Longrightarrow> prefix (frontier s) b"
proof -
  have result: "b \<in> insert [] (issued s) \<and> term_of b \<le> t \<and>
    (term_of (frontier s) \<le> t \<longrightarrow> prefix (frontier s) b)" using parent
  proof cases
    case (first warm)
    have lookup: "latest_issued s t = None" and rd: "election_base s t warm b"
      and warm: "warm \<in> insert [] (issued s)" "term_of warm < t" using first by auto
    have prefix: "prefix (frontier s) b" if "term_of (frontier s) \<le> t"
    proof (cases "frontier s = []")
      case True
      then show ?thesis by simp
    next
      case False
      have f: "frontier s \<in> issued s" by (rule frontier_issued[OF ff False])
      obtain q where "latest_issued s (term_of (frontier s)) = Some q" by (rule issued_latest[OF issued f])
      with lookup have "term_of (frontier s) \<noteq> t" by auto
      with that have lt: "term_of (frontier s) < t" by simp
      have le: "position (frontier s) \<le> position b"
        by (rule election_base_facts(3)[OF rd searches store warm False lt])
      have "b \<noteq> []" using issued_positive[OF issued f] position_term_mono[OF le] by auto
      with election_base_facts(1)[OF rd searches store warm] have "b \<in> issued s" by auto
      from ff this le show ?thesis unfolding frontier_ok_def by blast
    qed
    from election_base_facts(1,2)[OF rd searches store warm] prefix show ?thesis by (auto intro: less_imp_le)
  next
    case subsequent
    then have latest: "latest_issued s t = Some b" by auto
    with issued have facts: "b \<in> issued s" "term_of b = t" unfolding issued_ok_def by auto
    have prefix: "prefix (frontier s) b" if "term_of (frontier s) \<le> t"
    proof (cases "frontier s = []")
      case True
      then show ?thesis by simp
    next
      case False
      have f: "frontier s \<in> issued s" by (rule frontier_issued[OF ff False])
      show ?thesis
      proof (cases "term_of (frontier s) = t")
        case True
        obtain p where "latest_issued s (term_of (frontier s)) = Some p" "prefix (frontier s) p"
          by (rule issued_latest[OF issued f])
        with True latest show ?thesis by simp
      next
        case False
        with that facts have "term_of (frontier s) < term_of b" by simp
        from less_imp_le[OF earlier_term_position[OF this]] ff facts(1)
        show ?thesis unfolding frontier_ok_def by blast
      qed
    qed
    from facts prefix show ?thesis by auto
  qed
  from result show "b \<in> insert [] (issued s)" "term_of b \<le> t"
    "term_of (frontier s) \<le> t \<Longrightarrow> prefix (frontier s) b" by auto
qed

lemma issue_preserves_tables:
  fixes v :: nat and F :: config
  assumes ii: "issued_ok s" and grant: "holds_grant s who t"
    and pp: "publish_parent s t b" and lo: "term_of b \<le> t" and positive: "0 < t"
  defines "h \<equiv> stateless_update who t v F b"
  shows "issued_ok (s\<lparr>issued := insert h (issued s), latest_issued := (latest_issued s)(t := Some h)\<rparr>)"
proof -
  have follows: "position p < position h \<and> prefix p h"
    if mem: "p \<in> issued s" and tag: "term_of p = t" for p
  proof -
    obtain q where q: "latest_issued s (term_of p) = Some q" "prefix p q" "position p \<le> position q"
      by (rule issued_latest[OF ii mem])
    from pp q(1) tag have eq: "b = q" by (cases rule: publish_parent.cases) auto
    have "position b < position h" unfolding h_def by (rule new_tip_fields(5)[OF lo])
    with q(3) eq have "position p < position h" by (auto intro: le_less_trans)
    moreover have "prefix p h"
      by (rule prefix_order.trans[OF q(2)]) (simp add: eq[symmetric] h_def new_tip_fields(4))
    ultimately show ?thesis by simp
  qed
  let ?s' = "s\<lparr>issued := insert h (issued s), latest_issued := (latest_issued s)(t := Some h)\<rparr>"
  have tag: "term_of h = t" "owner h = fst who" "h \<noteq> []" unfolding h_def by (simp_all add: stateless_update_def)
  have oldtip: "p \<in> issued s \<and> term_of p = i" if "latest_issued s i = Some p" for i p
    using that ii unfolding issued_ok_def by fast
  have tips: "p \<in> issued ?s' \<and> term_of p = i" if "latest_issued ?s' i = Some p" for i p
  proof (cases "i = t")
    case True
    with that tag(1) show ?thesis by simp
  next
    case False
    then have "latest_issued s i = Some p" using that by simp
    from oldtip[OF this] show ?thesis by simp
  qed
  have histories: "p \<noteq> [] \<and> 0 < term_of p \<and>
    (\<exists>a. holds_grant ?s' a (term_of p) \<and> owner p = fst a) \<and>
    (\<exists>q. latest_issued ?s' (term_of p) = Some q \<and> prefix p q \<and> position p \<le> position q)"
    if mem: "p \<in> issued ?s'" for p
  proof (cases "p = h")
    case True
    with grant tag positive show ?thesis by (simp add: holds_grant_def)
  next
    case False
    with mem have old: "p \<in> issued s" by simp
    have nonempty: "p \<noteq> []" using ii old unfolding issued_ok_def by fast
    obtain a where a: "holds_grant s a (term_of p)" "owner p = fst a" by (rule issued_binding[OF ii old])
    obtain q where q: "latest_issued s (term_of p) = Some q" "prefix p q" "position p \<le> position q"
      by (rule issued_latest[OF ii old])
    have " (\<exists>q. latest_issued ?s' (term_of p) = Some q \<and> prefix p q \<and> position p \<le> position q)"
    proof (cases "term_of p = t")
      case True
      from follows[OF old this] True show ?thesis
        by (intro exI[of _ h]) (simp add: less_imp_le)
    next
      case False
      from q False show ?thesis by (intro exI[of _ q]) simp
    qed
    with a nonempty issued_positive[OF ii old] show ?thesis by (auto simp: holds_grant_def)
  qed
  have only_h: "y = h" if "y \<in> issued ?s'" "position y = position h" for y
  proof (rule ccontr)
    assume "y \<noteq> h"
    with that(1) have old: "y \<in> issued s" by simp
    from tag(1) that(2) have term_eq: "term_of y = t" by simp
    from follows[OF old term_eq] that(2) show False by simp
  qed
  have unique: "p = q" if "p \<in> issued ?s'" "q \<in> issued ?s'" "position p = position q" for p q
  proof (cases "p = h")
    case p_new: True
    then have "position q = position h" using that(3) by simp
    then have "q = h" by (rule only_h[OF that(2)])
    with p_new show ?thesis by simp
  next
    case p_other: False
    with that(1) have p_old: "p \<in> issued s" by simp
    show ?thesis
    proof (cases "q = h")
      case q_new: True
      then have "position p = position h" using that(3) by simp
      then have "p = h" by (rule only_h[OF that(1)])
      with p_other show ?thesis by simp
    next
      case q_other: False
      with that(2) have q_old: "q \<in> issued s" by simp
      show ?thesis by (rule issued_key_eq[OF ii p_old q_old that(3)])
    qed
  qed
  from tips histories unique show ?thesis unfolding issued_ok_def by blast
qed

lemma approval_reaches_top:
  assumes ii: "issued_ok s" "lease_ok s" and tip: "latest_issued s t = Some h" and floor: "confirmed_floor s \<le> t"
  shows "h \<in> issued s" "term_of h = t" "p \<in> issued s \<Longrightarrow> position p \<le> position h"
proof -
  have h: "h \<in> issued s" "term_of h = t" using ii(1) tip unfolding issued_ok_def by blast+
  then show "h \<in> issued s" "term_of h = t" by auto
  assume p: "p \<in> issued s"
  have low: "term_of p \<le> t" by (rule order_trans[OF issued_term_bound[OF ii(2,1) p] floor])
  show "position p \<le> position h"
  proof (cases "term_of p = t")
    case True
    obtain q where "latest_issued s (term_of p) = Some q" "position p \<le> position q"
      by (rule issued_latest[OF ii(1) p])
    with True tip show ?thesis by simp
  next
    case False
    with low h(2) have "term_of p < term_of h" by simp
    then show ?thesis by (rule less_imp_le[OF earlier_term_position])
  qed
qed

definition stateless_ok where
  "stateless_ok s \<longleftrightarrow> lease_ok s \<and> issued_ok s \<and> store_ok s \<and> frontier_ok s \<and>
    retained_frontier s \<and> searches_ok s"

lemma stateless_step_preserves:
  assumes step: "stateless_step s s'" and ok: "stateless_ok s"
  shows "stateless_ok s'"
proof -
  have lo: "lease_ok s" and ii: "issued_ok s" and so: "store_ok s" and fo: "frontier_ok s"
    and rf: "retained_frontier s" and qo: "searches_ok s" using ok unfolding stateless_ok_def by auto
  show ?thesis using step
  proof cases
    case (reserve expected t proposed who)
    have inc: "reserved_term s < t" using reserve(2,3) by simp
    have fresh: "granted_to s t = None"
    proof (cases "granted_to s t")
      case None
      then show ?thesis .
    next
      case (Some actor)
      with lo have "t \<le> reserved_term s" unfolding lease_ok_def by fast
      with inc show ?thesis by simp
    qed
    have unconfirmed: "t \<notin> confirmed_terms s" using lo fresh unfolding lease_ok_def by fast
    have grant_eq: "holds_grant s' a i \<longleftrightarrow> holds_grant s a i" for a i
      using unconfirmed by (simp add: reserve(1) holds_grant_def)
    have issued_eq: "issued s' = issued s" "latest_issued s' = latest_issued s" by (simp_all add: reserve(1))
    have issued': "issued_ok s'" using ii by (simp only: issued_ok_def issued_eq grant_eq)
    have grant_limit: "0 < i \<and> i \<le> t" if "granted_to s' i = Some a" for i a
    proof (cases "i = t")
      case True
      then show ?thesis using inc by simp
    next
      case False
      with that have "granted_to s i = Some a" by (simp add: reserve(1))
      with lo have "0 < i \<and> i \<le> reserved_term s" unfolding lease_ok_def by fast
      with inc show ?thesis by auto
    qed
    have old_confirmed: "0 < i \<and> i \<le> confirmed_floor s' \<and> granted_to s' i \<noteq> None"
      if "i \<in> confirmed_terms s'" for i
    proof -
      have c: "i \<in> confirmed_terms s" using that by (simp add: reserve(1))
      with lo have "0 < i \<and> i \<le> confirmed_floor s \<and> granted_to s i \<noteq> None"
        unfolding lease_ok_def by fast
      then show ?thesis using c unconfirmed by (simp add: reserve(1))
    qed
    have limits: "0 < i \<and> i \<le> reserved_term s'" if "granted_to s' i = Some a" for i a
      using grant_limit[OF that] by (simp add: reserve(1))
    have "lease_ok s'" unfolding lease_ok_def using limits old_confirmed by blast
    with issued' so fo rf qo show ?thesis
      by (simp add: reserve(1) stateless_ok_def store_ok_def frontier_ok_def retained_frontier_def searches_ok_def)
  next
    case confirm
    then show ?thesis using ok by (auto simp: stateless_ok_def stateless_inv_defs holds_grant_def)
  next
    case (start_search who t)
    then show ?thesis using ok by (auto simp: stateless_ok_def stateless_inv_defs holds_grant_def)
  next
    case (absent t i)
    have low: "term_of (frontier s) < i" if "frontier s \<noteq> []" "term_of (frontier s) < t"
    proof -
      have "term_of (frontier s) \<le> i" using absent(2) qo that unfolding searches_ok_def by force
      moreover have "term_of (frontier s) \<noteq> i"
        using rf that(1) absent(3) unfolding retained_frontier_def by auto
      ultimately show ?thesis by simp
    qed
    have positive: "0 < term_of (frontier s)" if "frontier s \<noteq> []"
      by (rule issued_positive[OF ii frontier_issued[OF fo that]])
    let ?q = "if 1 < i then Probe (i - 1) else No_Stored_State"
    have seen: "t \<in> confirmed_terms s" "i < t" using search_observation(1,2)[OF qo absent(2)] by simp_all
    have origin: "search_origin (completed_images s) t ?q" using seen(2) by (auto split: if_splits; presburger)
    have bound: "search_bound (frontier s) ?q" if "frontier s \<noteq> []" "term_of (frontier s) < t"
      using low[OF that] positive[OF that(1)] by (auto split: if_splits; presburger)
    have "searches_ok s'" using qo seen(1) origin bound
      by (auto simp: absent(1) searches_ok_def)
    with lo ii so fo rf show ?thesis
      by (simp add: absent(1) stateless_ok_def lease_ok_def issued_ok_def holds_grant_def
        store_ok_def frontier_ok_def retained_frontier_def)
  next
    case (header t i h)
    have tag: "term_of h = i" "h \<in> completed_images s" using header(3) so unfolding store_ok_def by auto
    have low: "position (frontier s) \<le> position h" if "frontier s \<noteq> []" "term_of (frontier s) < t"
    proof -
      have "term_of (frontier s) \<le> i" using header(2) qo that unfolding searches_ok_def by force
      then show ?thesis using rf that(1) tag(1) header(3)
        by (cases "term_of (frontier s) = i")
          (auto simp: retained_frontier_def intro: less_imp_le[OF earlier_term_position])
    qed
    have seen: "t \<in> confirmed_terms s" "i < t" using search_observation(1,2)[OF qo header(2)] by simp_all
    have "searches_ok s'" using qo seen tag low
      by (auto simp: header(1) searches_ok_def)
    with lo ii so fo rf show ?thesis
      by (simp add: header(1) stateless_ok_def lease_ok_def issued_ok_def holds_grant_def
        store_ok_def frontier_ok_def retained_frontier_def)
  next
    case (publish who t base h payload F)
    have facts: "base \<in> insert [] (issued s)" "term_of base \<le> t"
      using parent_facts[OF publish(3) ii fo qo so] by auto
    have "0 < t" using lo publish(2) by (auto simp: lease_ok_def holds_grant_def)
    have table: "issued_ok s'" unfolding publish(1)
      using issue_preserves_tables[OF ii publish(2,3) facts(2) \<open>0 < t\<close>, of payload F] publish(4) by simp
    have tag: "term_of h = t" using publish(4) by (simp add: stateless_update_def)
    have pref: "prefix (frontier s) h" if "position (frontier s) \<le> position h"
    proof -
      from position_term_mono[OF that] tag
      have "term_of (frontier s) \<le> t" by simp
      from parent_facts(3)[OF publish(3) ii fo qo so this] publish(4)
      show ?thesis using new_tip_fields(4)[of base who t payload F] by (auto simp: prefix_def)
    qed
    from table ok publish(1) pref show ?thesis
      by (auto simp: stateless_ok_def lease_ok_def frontier_ok_def store_ok_def retained_frontier_def searches_ok_def)
  next
    case (upload t h)
    have i: "h \<in> issued s" "term_of h = t" using ii upload(2) unfolding issued_ok_def by auto
    let ?s' = "s\<lparr>completed_images := insert h (completed_images s),
      visible_image := (visible_image s)(t := Some h)\<rparr>"
    have lease: "lease_ok ?s'" using lo unfolding lease_ok_def by simp
    have issued: "issued_ok ?s'" using ii unfolding issued_ok_def holds_grant_def by simp
    have store: "store_ok ?s'" using so i unfolding store_ok_def by auto
    have front: "frontier_ok ?s'" using fo unfolding frontier_ok_def by simp
    have retained: "retained_frontier ?s'"
    proof (cases "frontier s = []")
      case True
      then show ?thesis unfolding retained_frontier_def by simp
    next
      case nonempty: False
      from rf nonempty obtain d where d: "visible_image s (term_of (frontier s)) = Some d"
        "position (frontier s) \<le> position d" unfolding retained_frontier_def by blast
      show ?thesis
      proof (cases "term_of (frontier s) = t")
        case same_term: True
        with d(1) have "position d \<le> position h" using upload(3) by simp
        with d(2) have "position (frontier s) \<le> position h" by (rule order_trans)
        with same_term show ?thesis unfolding retained_frontier_def by simp
      next
        case other_term: False
        with d show ?thesis unfolding retained_frontier_def by auto
      qed
    qed
    have searches: "searches_ok ?s'"
      using qo unfolding searches_ok_def by (auto intro: search_origin_grows)
    show ?thesis unfolding upload(1) stateless_ok_def
      using lease issued store front retained searches by blast
  next
    case (approve t h)
    from approval_reaches_top[OF ii lo approve(2,4)]
    have member: "h \<in> issued s" and term_eq: "term_of h = t"
      and top: "p \<in> issued s \<Longrightarrow> position p \<le> position h" for p by auto
    have monotone: "position (frontier s) \<le> position h"
      using top frontier_issued[OF fo] by (cases "frontier s = []") (auto simp: zero_key_le)
    have base: "prefix (frontier s) h" using fo member monotone unfolding frontier_ok_def by blast
    have newest: "p = h" if p: "p \<in> issued s" and low: "position h \<le> position p" for p
    proof -
      have "position p = position h" by (rule order_antisym[OF top[OF p] low])
      then show ?thesis by (rule issued_key_eq[OF ii p member])
    qed
    have qbound: "u \<le> t" if "searches s u = Some q" for u q
    proof -
      have "u \<in> confirmed_terms s" by (rule search_observation(1)[OF qo that])
      with lo have "u \<le> confirmed_floor s" by (simp add: lease_ok_def)
      then show ?thesis by (rule order_trans[OF _ approve(4)])
    qed
    have prior: "p \<in> issued s \<and> prefix p h \<and> position p \<le> position h" if "p \<in> approvals s" for p
    proof -
      from fo that have mem: "p \<in> issued s" and pref: "prefix p (frontier s)" unfolding frontier_ok_def by auto
      from mem prefix_order.trans[OF pref base] top[OF mem] show ?thesis by simp
    qed
    have new_front: "frontier_ok s'"
      using fo member
      by (auto simp: approve(1) frontier_ok_def dest: prior newest)
    have retained: "retained_frontier s'" using approve(3) term_eq
      by (auto simp: approve(1) retained_frontier_def)
    have new_queries: "searches_ok s'"
      unfolding searches_ok_def
    proof (intro allI impI)
      fix u q
      assume "searches s' u = Some q"
      then have lookup: "searches s u = Some q" by (simp add: approve(1))
      from search_observation(1,2)[OF qo lookup] qbound[OF lookup] term_eq
      show "u \<in> confirmed_terms s' \<and> search_origin (completed_images s') u q \<and>
        (frontier s' \<noteq> [] \<and> term_of (frontier s') < u \<longrightarrow> search_bound (frontier s') q)"
        by (simp add: approve(1))
    qed
    show ?thesis using new_front retained new_queries lo ii so
      by (simp add: approve(1) stateless_ok_def lease_ok_def issued_ok_def holds_grant_def store_ok_def)
  next
    case notify_commit
    then show ?thesis using ok by (auto simp: stateless_ok_def stateless_inv_defs holds_grant_def)
  next
    case (cleanup h removed)
    have "position h \<le> position (frontier s)"
      using cleanup(2) fo unfolding frontier_ok_def by blast
    then have "term_of h \<le> term_of (frontier s)" by (rule position_term_mono)
    with cleanup ok show ?thesis
      by (auto simp: stateless_ok_def stateless_inv_defs holds_grant_def subset_eq)
  qed
qed

theorem stateless_invariants:
  assumes "stateless_reachable s"
  shows "stateless_ok s"
  using assms
proof induction
  case init
  then show ?case by (simp add: stateless_initial_def stateless_ok_def stateless_inv_defs)
next
  case step
  show ?case by (rule stateless_step_preserves[OF step.hyps(2) step.IH])
qed

section \<open>Safety transfer to an append-only committed history\<close>

definition stateless_log_step :: "lineage \<Rightarrow> lineage \<Rightarrow> bool" where
  "stateless_log_step h k \<longleftrightarrow> prefix h k \<and> position h \<le> position k"

lemma stateless_refines_log_step:
  assumes "stateless_reachable s" "stateless_step s s'"
  shows "stateless_log_step (frontier s) (frontier s')"
  using assms(2)
proof cases
  case (approve t h)
  have ok: "stateless_ok s" by (rule stateless_invariants[OF assms(1)])
  have ii: "issued_ok s" and lo: "lease_ok s" and fo: "frontier_ok s" using ok by (auto simp: stateless_ok_def)
  have "h \<in> issued s" and top: "p \<in> issued s \<Longrightarrow> position p \<le> position h" for p
    using approval_reaches_top[OF ii lo approve(2,4)] by auto
  moreover have "position (frontier s) \<le> position h"
    using top frontier_issued[OF fo] by (cases "frontier s = []") (auto simp: zero_key_le)
  ultimately show ?thesis using fo approve(1)
    by (auto simp: stateless_log_step_def frontier_ok_def)
qed (auto simp: stateless_log_step_def)

theorem stateless_refines_committed_log:
  assumes "stateless_reachable s"
  shows "rtranclp stateless_log_step [] (frontier s)"
  using assms
proof induction
  case init
  show ?case by (simp add: stateless_initial_def)
next
  case step
  from step.IH stateless_refines_log_step[OF step.hyps]
  show ?case by (rule rtranclp.rtrancl_into_rtrancl)
qed

theorem stateless_commits_form_chain:
  assumes run: "stateless_reachable s" and n: "h \<in> notifications s" "p \<in> notifications s"
  shows "prefix h p \<or> prefix p h"
proof -
  have "frontier_ok s" using stateless_invariants[OF run] unfolding stateless_ok_def by blast
  then have "prefix h (frontier s)" "prefix p (frontier s)"
    using n unfolding frontier_ok_def by blast+
  then show ?thesis by (meson prefix_same_cases)
qed

theorem stateless_unique_publication:
  assumes "stateless_reachable s" "h \<in> issued s" "p \<in> issued s" "position h = position p"
  shows "h = p"
proof -
  have "issued_ok s" using stateless_invariants[OF assms(1)] unfolding stateless_ok_def by blast
  from issued_key_eq[OF this assms(2-4)] show ?thesis .
qed

theorem stateless_one_grantee_per_term:
  "holds_grant s who t \<Longrightarrow> holds_grant s other t \<Longrightarrow> who = other"
  by (simp add: holds_grant_def)

lemma confirmed_grant_persists:
  assumes run: "stateless_reachable s" and step: "stateless_step s s'" and grant: "holds_grant s who t"
  shows "holds_grant s' who t"
  using step
proof cases
  case reserve
  have "t \<le> reserved_term s"
    using stateless_invariants[OF run] grant by (auto simp: stateless_ok_def lease_ok_def holds_grant_def)
  with reserve grant show ?thesis by (auto simp: holds_grant_def)
qed (use grant in \<open>auto simp: holds_grant_def\<close>)

theorem stateless_one_grantee_across_execution:
  assumes run: "stateless_reachable s" and path: "rtranclp stateless_step s s'"
    and one: "holds_grant s who t" and two: "holds_grant s' other t"
  shows "who = other"
proof -
  have "stateless_reachable s' \<and> holds_grant s' who t" using path
  proof induction
    case base
    show ?case using run one by simp
  next
    case (step x y)
    then have reach: "stateless_reachable x" and grant: "holds_grant x who t" by auto
    from stateless_reachable.step[OF reach step.hyps(2)] confirmed_grant_persists[OF reach step.hyps(2) grant]
    show ?case by simp
  qed
  then show ?thesis using two stateless_one_grantee_per_term by blast
qed

theorem chosen_parent_extends_prior_commits:
  assumes run: "stateless_reachable s" and parent: "publish_parent s t b"
    and earlier: "term_of (frontier s) \<le> t" and notified: "h \<in> notifications s"
  shows "prefix h b"
proof -
  have "stateless_ok s" by (rule stateless_invariants[OF run])
  then have ii: "issued_ok s" and ff: "frontier_ok s" and qs: "searches_ok s" and ss: "store_ok s"
    unfolding stateless_ok_def by auto
  from ff notified have "prefix h (frontier s)" unfolding frontier_ok_def by blast
  then show ?thesis by (rule prefix_order.trans) (rule parent_facts(3)[OF parent ii ff qs ss earlier])
qed

lemma restart_loads_remote_when_present:
  assumes run: "stateless_reachable s" and scan: "searches s t = Some (Found seen)"
    and download: "remote \<in> completed_images s" "term_of remote = term_of seen" "position seen \<le> position remote"
  shows "election_base s t [] remote"
proof -
  have mem: "remote \<in> issued s" using stateless_invariants[OF run] download(1)
    unfolding stateless_ok_def store_ok_def by blast
  have ii: "issued_ok s" using stateless_invariants[OF run] unfolding stateless_ok_def by blast
  have "term_of [] < term_of remote" using issued_positive[OF ii mem] by simp
  then have "position [] < position remote" by (rule earlier_term_position)
  then show ?thesis using election_base.downloaded[OF scan download(1,2), where warm="[]"] download(3)
    by (simp add: newer_image_def)
qed

section \<open>Alternate input to the election-completion task\<close>

lemma first_election_snapshot_preserves_committed:
  assumes run: "stateless_reachable s" and unopened: "latest_issued s t = None"
    and current: "current_term (java_nodes j n) = t" and older: "rank_term (accepted_key (java_nodes j n)) < t"
    and configured: "accepted_config (java_nodes j n) \<noteq> {}"
    and checked: "java_checks j a"
    and delivery: "\<And>p u. a = Java_Publish n p u \<Longrightarrow>
      \<exists>h\<in>issued s. position h = request_key p"
  shows "local_committed (java_nodes (java_execute N E j a) n) = local_committed (java_nodes j n)"
proof (cases "receiver a = n")
  case False
  then show ?thesis using java_execute_other_node[of n a N E j] by simp
next
  case True
  show ?thesis
  proof (cases a)
    case (Java_Publish i p u)
    with True have n: "i = n" by simp
    from delivery Java_Publish n obtain h where h: "h \<in> issued s" "position h = request_key p" by auto
    have "term_of h = t" using h(2) checked Java_Publish n current by (simp add: Let_def)
    moreover have ii: "issued_ok s" using stateless_invariants[OF run] unfolding stateless_ok_def by blast
    ultimately show ?thesis using issued_latest[OF ii h(1)] unopened by simp
  qed (use True checked configured current older in
    \<open>auto simp: java_put_def Let_def java_reset_def\<close>)
qed

definition adapt_stored_base where
  "adapt_stored_base n snapshot stored =
    stored\<lparr>executor_master := None, executor_accepted := {n}, executor_committed := executor_committed snapshot\<rparr>"

definition stateless_executor_result where
  "stateless_executor_result n t metadata_changed snapshot alternate =
    (let b = select_join_base snapshot (map_option (adapt_stored_base n snapshot) alternate)
     in patch_executor_versions True metadata_changed
       (b\<lparr>executor_term := t, executor_master := Some n, executor_accepted := {n}\<rparr>))"

lemma stateless_executor_uses_selected_base:
  shows "executor_parent (stateless_executor_result n t md snapshot alternate) =
    executor_parent (select_join_base snapshot alternate)"
    "executor_version (stateless_executor_result n t md snapshot alternate) =
      Suc (executor_version (select_join_base snapshot alternate))"
    "executor_committed (stateless_executor_result n t md snapshot alternate) = executor_committed snapshot"
    "executor_accepted (stateless_executor_result n t md snapshot alternate) = {n}"
proof -
  have "executor_parent (stateless_executor_result n t md snapshot alternate) =
    executor_parent (select_join_base snapshot alternate) \<and>
    executor_version (stateless_executor_result n t md snapshot alternate) =
      Suc (executor_version (select_join_base snapshot alternate)) \<and>
    executor_committed (stateless_executor_result n t md snapshot alternate) = executor_committed snapshot \<and>
    executor_accepted (stateless_executor_result n t md snapshot alternate) = {n}"
    by (cases alternate) (simp_all add: stateless_executor_result_def select_join_base_def
      adapt_stored_base_def patch_executor_versions_def executor_key_def Let_def split: if_splits)
  then show
    "executor_parent (stateless_executor_result n t md snapshot alternate) = executor_parent (select_join_base snapshot alternate)"
    "executor_version (stateless_executor_result n t md snapshot alternate) = Suc (executor_version (select_join_base snapshot alternate))"
    "executor_committed (stateless_executor_result n t md snapshot alternate) = executor_committed snapshot"
    "executor_accepted (stateless_executor_result n t md snapshot alternate) = {n}" by simp_all
qed

theorem downloaded_executor_refines_election_base:
  assumes scan: "searches s t = Some (Found seen)"
    and remote: "downloaded \<in> completed_images s" "term_of downloaded = term_of seen" "position seen \<le> position downloaded"
    and keys: "executor_key snapshot = position warm" "executor_key stored = position downloaded"
  defines "b \<equiv> newer_image warm downloaded"
  shows "election_base s t warm b"
    "executor_parent (stateless_executor_result n t md snapshot (Some stored)) =
       executor_parent (if position warm < position downloaded then stored else snapshot)"
    "executor_key (stateless_executor_result n t md snapshot (Some stored)) =
       position (stateless_update (n,incarnation) t payload (executor_committed snapshot) b)"
proof -
  show "election_base s t warm b" unfolding b_def
    by (rule election_base.downloaded[OF scan remote(1,2)]) (simp add: remote(3))
  let ?out = "stateless_executor_result n t md snapshot (Some stored)"
  have term_eq: "executor_term ?out = t"
    by (simp add: stateless_executor_result_def patch_executor_versions_def Let_def)
  have chosen: "select_join_base snapshot (Some stored) =
    (if position warm < position downloaded then stored else snapshot)"
    using keys by (simp add: select_join_base_def)
  have versions: "executor_version snapshot = rank_version (position warm)"
    "executor_version stored = rank_version (position downloaded)"
    using arg_cong[OF keys(1), of rank_version] arg_cong[OF keys(2), of rank_version]
    by (simp_all add: executor_key_def)
  from stateless_executor_uses_selected_base(1)[of n t md snapshot "Some stored"] chosen
  show "executor_parent ?out = executor_parent (if position warm < position downloaded then stored else snapshot)"
    by simp
  from stateless_executor_uses_selected_base(2)[of n t md snapshot "Some stored"]
    term_eq chosen versions
  show "executor_key ?out = position (stateless_update (n,incarnation) t payload (executor_committed snapshot) b)"
    by (auto simp: b_def newer_image_def executor_key_def stateless_update_def split: if_splits)
qed

end
