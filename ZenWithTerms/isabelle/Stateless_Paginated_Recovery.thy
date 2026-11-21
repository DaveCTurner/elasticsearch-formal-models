theory Stateless_Paginated_Recovery
  imports Stateless_Manifest_Retention
begin

section \<open>Cursor listings with a changing directory\<close>

inductive cursor_listing ::
  "(state_manifest \<Rightarrow> 'k::linorder) \<Rightarrow> 'k option \<Rightarrow> state_manifest set list \<Rightarrow> state_manifest set \<Rightarrow> bool"
where
  final_page:
    "cursor_listing key cursor [view] {m \<in> view. case cursor of None \<Rightarrow> True | Some lo \<Rightarrow> lo < key m}"
| next_page:
    "(case cursor of None \<Rightarrow> True | Some lo \<Rightarrow> lo < hi) \<Longrightarrow>
     (\<exists>m\<in>view. key m = hi) \<Longrightarrow>
     cursor_listing key (Some hi) views tail \<Longrightarrow>
     cursor_listing key cursor (view # views)
       ({m \<in> view. (case cursor of None \<Rightarrow> True | Some lo \<Rightarrow> lo < key m) \<and> key m \<le> hi} \<union> tail)"
| empty_continuation:
    "cursor_listing key (Some lo) views listed \<Longrightarrow>
     cursor_listing key (Some lo) (view # views) listed"

lemma cursor_lists_persistent_key:
  assumes "cursor_listing key cursor views listed"
    "\<forall>view\<in>set views. anchor \<in> view"
    "case cursor of None \<Rightarrow> True | Some lo \<Rightarrow> lo < key anchor"
  shows "anchor \<in> listed"
  using assms
proof induction
  case final_page
  then show ?case by simp
next
  case (next_page cursor hi view key views tail)
  show ?case
  proof (cases "key anchor \<le> hi")
    case True
    then show ?thesis using next_page.prems by simp
  next
    case False
    then have bound: "case Some hi of None \<Rightarrow> True | Some lo \<Rightarrow> lo < key anchor" by simp
    have all: "\<forall>v\<in>set views. anchor \<in> v" using next_page.prems(1) by simp
    have "anchor \<in> tail" by (rule next_page.IH[OF all bound])
    then show ?thesis by simp
  qed
next
  case empty_continuation
  then show ?case by simp
qed

lemma cursor_lists_only_observed_keys:
  "cursor_listing key cursor views listed \<Longrightarrow> listed \<subseteq> \<Union>(set views)"
  by (induction rule: cursor_listing.induct) auto

lemma cursor_nonempty:
  assumes "cursor_listing key None (view # views) listed" "view \<noteq> {}"
  shows "listed \<noteq> {}"
  using assms by (cases rule: cursor_listing.cases) auto

lemma confirmed_floor_grows:
  "stateless_step s s' \<Longrightarrow> confirmed_floor s \<le> confirmed_floor s'"
  by (cases rule: stateless_step.cases) auto

lemma later_grant_fences_lower_term:
  assumes "stateless_reachable s" "holds_grant s who election" "term < election"
    "rtranclp stateless_step s s'"
  shows "term < confirmed_floor s'"
proof -
  from stateless_invariants[OF assms(1)] assms(2)
  have floor: "election \<le> confirmed_floor s"
    by (auto simp: stateless_ok_def lease_ok_def holds_grant_def)
  from assms(4) have "confirmed_floor s \<le> confirmed_floor s'"
    by induction (auto intro: order_trans confirmed_floor_grows)
  from assms(3) order_trans[OF floor this] show ?thesis by (rule less_le_trans)
qed

lemma issuance_cannot_disappear:
  "stateless_step s s' \<Longrightarrow> latest_issued s' t = None \<Longrightarrow> latest_issued s t = None"
  by (cases rule: stateless_step.cases) (auto split: if_splits)

lemma frontier_fixed_before_first_publication:
  assumes run: "stateless_reachable s" and grant: "holds_grant s who t"
    and path: "rtranclp stateless_step s s'"
    and first: "latest_issued s' t = None" and fence: "confirmed_floor s' \<le> t"
  shows "frontier s' = frontier s"
proof -
  from stateless_invariants[OF run] grant have lower: "t \<le> confirmed_floor s"
    by (auto simp: stateless_ok_def lease_ok_def holds_grant_def)
  show ?thesis using path first fence
  proof induction
    case base
    then show ?case by simp
  next
    case (step a b)
    from step.hyps(1) run lower have a: "stateless_reachable a" "t \<le> confirmed_floor a"
      by (induction rule: rtranclp_induct) (auto intro: stateless_reachable.step confirmed_floor_grows order_trans)
    have upper: "confirmed_floor a \<le> t"
      by (rule order_trans[OF confirmed_floor_grows[OF step.hyps(2)] step.prems(2)])
    have unissued: "latest_issued a t = None" by (rule issuance_cannot_disappear[OF step.hyps(2) step.prems(1)])
    have "frontier b = frontier a" using step.hyps(2)
    proof cases
      case (approve i h)
      from stateless_invariants[OF a(1)] have ii: "issued_ok a" and lo: "lease_ok a"
        unfolding stateless_ok_def by auto
      from ii approve(2) have member: "h \<in> issued a" and tag: "term_of h = i"
        unfolding issued_ok_def by auto
      from issued_term_bound[OF lo ii member] tag upper a(2) approve(4)
      have "i = t" by simp
      from this approve(2) unissued show ?thesis by simp
    qed auto
    then show ?case using step.IH[OF unissued upper] by simp
  qed
qed

section \<open>Manifest renames after the last commit fence\<close>

text \<open>
  Start at the manifest of the last approved publication in the term.
  The next publication can finish uploading after the fence, but cannot
  obtain another approval. The first publication can also be rewritten
  with its committed metadata, before the next publication. Later
  publications already carry that metadata.

  BlobStoreSyncDirectory takes its deletion snapshot inside rename.
  Lucene marks the preceding manifest obsolete at the checkpoint after
  rename. This leaves the two most recent manifests outside the deletion
  snapshot, even when deletion tasks execute out of order. Whole-directory
  cleanup of an earlier term is modeled separately.
\<close>

type_synonym term_manifest_state = "state_manifest list \<times> state_manifest set"

definition extends_manifest where
  "extends_manifest anchor m \<longleftrightarrow>
    term_of (manifest_history m) = term_of (manifest_history anchor) \<and>
    position (manifest_history anchor) \<le> position (manifest_history m)"

inductive fenced_manifest_step :: "bool \<Rightarrow> state_manifest \<Rightarrow> term_manifest_state \<Rightarrow> term_manifest_state \<Rightarrow> bool"
  for is_first anchor where
  mark:
    "is_first \<Longrightarrow> manifest_history m = manifest_history anchor \<Longrightarrow>
     fenced_manifest_step is_first anchor ([], live) ([m], insert m live)"
| successor:
    "length renames \<le> 1 \<Longrightarrow>
     (\<And>p. p \<in> set renames \<Longrightarrow> is_first \<and> manifest_history p = manifest_history anchor) \<Longrightarrow>
     extends_manifest anchor m \<Longrightarrow> position (manifest_history anchor) < position (manifest_history m) \<Longrightarrow>
     fenced_manifest_step is_first anchor (renames, live) (m # renames, insert m live)"
| prune:
    "kept \<subseteq> live \<Longrightarrow> set (take 2 (renames @ [anchor])) \<subseteq> kept \<Longrightarrow>
     fenced_manifest_step is_first anchor (renames, live) (renames, kept)"

definition manifest_suffix_ok where
  "manifest_suffix_ok is_first anchor st \<longleftrightarrow>
    set (take 2 (fst st @ [anchor])) \<subseteq> snd st \<and>
    (if is_first then (\<forall>m\<in>snd st. extends_manifest anchor m) else length (fst st) \<le> 1)"

lemma remote_retry_refines_prune:
  assumes io: "rtranclp manifest_io_step manifest_io_initial store"
    and generations: "rename_log store = map manifest_generation (renames @ [anchor]) @ earlier"
    and batch: "removed \<subseteq> queued_generations store"
    and ok: "manifest_suffix_ok is_first anchor (renames, live)"
  shows "fenced_manifest_step is_first anchor (renames, live)
    (renames, {m \<in> live. manifest_generation m \<notin> removed})"
proof (rule fenced_manifest_step.prune)
  show "{m \<in> live. manifest_generation m \<notin> removed} \<subseteq> live" by simp
  show "set (take 2 (renames @ [anchor])) \<subseteq> {m \<in> live. manifest_generation m \<notin> removed}"
  proof
    fix m
    assume member: "m \<in> set (take 2 (renames @ [anchor]))"
    have image: "manifest_generation m \<in> set (take 2 (map manifest_generation (renames @ [anchor])))"
      unfolding take_map set_map by (rule imageI[OF member])
    have "set (take 2 xs) \<subseteq> set (take 2 (xs @ earlier))" for xs
      by (simp only: take_append set_append) blast
    with image have "manifest_generation m \<in> protected_generations store"
      unfolding protected_generations_def generations by blast
    moreover have "m \<in> live" using ok member unfolding manifest_suffix_ok_def by auto
    ultimately show "m \<in> {m \<in> live. manifest_generation m \<notin> removed}"
      using any_pending_retry_preserves_protected[OF io batch] by blast
  qed
qed

lemma fenced_manifest_step_preserves:
  assumes "fenced_manifest_step is_first anchor s s'" "manifest_suffix_ok is_first anchor s"
  shows "manifest_suffix_ok is_first anchor s'"
  using assms(1)
proof cases
  case (mark m live)
  have present: "anchor \<in> live" and good: "\<forall>p\<in>live. extends_manifest anchor p"
    using assms(2) mark(1,3) by (simp_all add: manifest_suffix_ok_def)
  have "extends_manifest anchor m" using mark(4) by (simp add: extends_manifest_def)
  with present good mark(2,3) show ?thesis by (simp add: manifest_suffix_ok_def insert_subset)
next
  case (successor renames m live)
  have old: "manifest_suffix_ok is_first anchor (renames, live)" using assms(2) successor(1) by simp
  show ?thesis
  proof (cases renames)
    case Nil
    from old Nil have present: "anchor \<in> live"
      and good: "is_first \<Longrightarrow> \<forall>p\<in>live. extends_manifest anchor p"
      by (simp_all add: manifest_suffix_ok_def split: if_splits)
    from present good successor(2,5) Nil show ?thesis
      by (cases is_first) (simp_all add: manifest_suffix_ok_def insert_subset)
  next
    case (Cons previous rest)
    have len: "rest = []" using Cons successor(3) by simp
    have head: "previous \<in> set renames" using Cons by simp
    from successor(4)[OF head] have first: is_first by simp
    have present: "previous \<in> live" and good: "\<forall>p\<in>live. extends_manifest anchor p"
      using Cons len first old by (simp_all add: manifest_suffix_ok_def)
    from present good successor(2,5) Cons len first show ?thesis
      by (simp add: manifest_suffix_ok_def insert_subset)
  qed
next
  case prune
  with assms(2) show ?thesis unfolding manifest_suffix_ok_def by (simp split: if_splits) blast
qed

lemma fenced_manifest_views:
  assumes "anchor \<in> original"
    and first: "is_first \<Longrightarrow> \<forall>m\<in>original. extends_manifest anchor m"
    and trace: "rtranclp (fenced_manifest_step is_first anchor) ([], original) (renames, live)"
  shows "live \<noteq> {}"
    "is_first \<Longrightarrow> \<forall>m\<in>live. extends_manifest anchor m"
    "\<not> is_first \<Longrightarrow> anchor \<in> live"
proof -
  have ok: "manifest_suffix_ok is_first anchor (renames, live)"
    using trace
  proof (induction rule: rtranclp_induct)
    case base
    then show ?case using assms(1) first by (simp add: manifest_suffix_ok_def)
  next
    case (step a b)
    from fenced_manifest_step_preserves[OF step.hyps(2) step.IH] show ?case .
  qed
  then show "live \<noteq> {}" "is_first \<Longrightarrow> \<forall>m\<in>live. extends_manifest anchor m"
    "\<not> is_first \<Longrightarrow> anchor \<in> live"
    by (cases renames; auto simp: manifest_suffix_ok_def)+
qed

theorem live_term_paginated_listing:
  assumes present: "anchor \<in> original"
    and first: "is_first \<Longrightarrow> \<forall>m\<in>original. extends_manifest anchor m"
    and order: "\<And>m. m \<in> listed \<Longrightarrow> manifest_generation m \<le> manifest_generation selected
        \<Longrightarrow> extends_manifest m selected"
    and from_writer: "\<And>view. view \<in> set (view0 # views) \<Longrightarrow>
      \<exists>renames. rtranclp (fenced_manifest_step is_first anchor) ([], original) (renames, view)"
    and pages: "cursor_listing key None (view0 # views) listed"
  shows "listed \<noteq> {}" "newest_manifest listed (Some selected) \<Longrightarrow> extends_manifest anchor selected"
proof -
  have live: "live \<noteq> {}" and good: "is_first \<Longrightarrow> \<forall>m\<in>live. extends_manifest anchor m"
    and retained: "\<not> is_first \<Longrightarrow> anchor \<in> live" if "live \<in> set (view0 # views)" for live
  proof -
    from from_writer[OF that] obtain renames where
      "rtranclp (fenced_manifest_step is_first anchor) ([], original) (renames, live)" by blast
    note views = fenced_manifest_views[OF present first this]
    from views show "live \<noteq> {}" "is_first \<Longrightarrow> \<forall>m\<in>live. extends_manifest anchor m"
      "\<not> is_first \<Longrightarrow> anchor \<in> live" by blast+
  qed
  have "view0 \<noteq> {}" by (rule live) simp
  then show "listed \<noteq> {}" by (rule cursor_nonempty[OF pages])
  assume pick: "newest_manifest listed (Some selected)"
  have selected: "selected \<in> listed" using pick unfolding newest_manifest_def by simp
  show "extends_manifest anchor selected"
  proof (cases is_first)
    case True
    from cursor_lists_only_observed_keys[OF pages] selected obtain v where
      v: "v \<in> set (view0 # views)" "selected \<in> v" by blast
    from good[OF v(1) True] v(2) show ?thesis by blast
  next
    case False
    have all: "\<forall>v\<in>set (view0 # views). anchor \<in> v" using retained False by blast
    have member: "anchor \<in> listed" using cursor_lists_persistent_key[OF pages all] by simp
    from member pick have g: "manifest_generation anchor \<le> manifest_generation selected"
      unfolding newest_manifest_def by (cases "anchor = selected") auto
    show ?thesis by (rule order[OF member g])
  qed
qed

lemma paginated_header_refines_scan:
  assumes probe: "searches s election = Some (Probe t)"
    and selected: "h \<in> completed_images s" "term_of h = t"
    and floor: "t = term_of (frontier s) \<Longrightarrow> position (frontier s) \<le> position h"
  shows "stateless_step s (s\<lparr>searches := (searches s)(election := Some (Found h))\<rparr>)"
  by (rule stateless_step.header[OF probe]) (use selected floor in auto)

theorem paginated_download_preserves_commits:
  assumes run: "stateless_reachable s"
    and search: "searches s election = Some (Found seen)"
    and remote: "downloaded \<in> completed_images s" "term_of downloaded = term_of seen"
    and floor: "term_of seen = term_of (frontier s) \<Longrightarrow> position (frontier s) \<le> position downloaded"
    and warm: "warm \<in> insert [] (issued s)" "term_of warm < election"
    and first: "latest_issued s election = None"
    and eligible: "confirmed_floor s \<le> election"
    and prior: "h \<in> notifications s"
  shows "prefix h (newer_image warm downloaded)"
proof -
  have base: "election_base s election warm (newer_image warm downloaded)"
    by (rule election_base.downloaded[OF search remote]) (use floor in auto)
  have parent: "publish_parent s election (newer_image warm downloaded)"
    by (rule publish_parent.first[OF first warm base])
  have "term_of (frontier s) \<le> confirmed_floor s"
  proof (cases "frontier s = []")
    case False
    from stateless_invariants[OF run] have lo: "lease_ok s" and ii: "issued_ok s" and fo: "frontier_ok s"
      unfolding stateless_ok_def by auto
    show ?thesis by (rule issued_term_bound[OF lo ii frontier_issued[OF fo False]])
  qed simp
  from chosen_parent_extends_prior_commits[OF run parent order_trans[OF this eligible] prior] show ?thesis .
qed

end
