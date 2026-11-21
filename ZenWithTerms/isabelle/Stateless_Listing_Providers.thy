theory Stateless_Listing_Providers
  imports Stateless_Paginated_Recovery
begin

section \<open>Name-based continuation\<close>

definition after_name where
  "after_name key cursor m \<longleftrightarrow> (case cursor of None \<Rightarrow> True | Some lo \<Rightarrow> lo < key m)"

text \<open>
  A GCS page gives an ordered prefix of the matching objects after
  the previous token. The token identifies the last returned name and
  generation. For this listing there is one live object per name and
  manifest names are immutable, so the token projects to its name.
  The remainder of a page's view is irrelevant to the next request:
  that request reads a new view. An empty continued response cannot
  advance the last-returned name.
\<close>

inductive gcs_listing for key :: "state_manifest \<Rightarrow> 'k::linorder" where
  last:
    "set rows = {m \<in> view. after_name key cursor m} \<Longrightarrow>
     gcs_listing key cursor [view] [rows]"
| more:
    "rows \<noteq> [] \<Longrightarrow>
     set (rows @ remainder) = {m \<in> view. after_name key cursor m} \<Longrightarrow>
     sorted_wrt (\<lambda>a b. key a < key b) (rows @ remainder) \<Longrightarrow>
     gcs_listing key (Some (key (last rows))) views pages \<Longrightarrow>
     gcs_listing key cursor (view # views) (rows # pages)"
| empty_continuation:
    "gcs_listing key (Some lo) views pages \<Longrightarrow>
     gcs_listing key (Some lo) (view # views) ([] # pages)"

lemma ordered_prefix_is_cursor_range:
  fixes key :: "state_manifest \<Rightarrow> 'k::linorder"
  assumes nonempty: "rows \<noteq> []"
    and keys: "set (rows @ rest) = {m \<in> view. after_name key cursor m}"
    and ordered: "sorted_wrt (\<lambda>a b. key a < key b) (rows @ rest)"
  defines "hi \<equiv> key (last rows)"
  shows "after_name key cursor (last rows)"
    "last rows \<in> view"
    "set rows = {m \<in> view. after_name key cursor m \<and> key m \<le> hi}"
proof -
  from nonempty have member: "last rows \<in> set rows" by (rule last_in_set)
  with keys show "after_name key cursor (last rows)" "last rows \<in> view" by auto
  have before: "key m \<le> hi" if "m \<in> set rows" for m
  proof -
    from nonempty obtain front final where rows: "rows = front @ [final]"
      by (cases rows rule: rev_cases) auto
    from ordered that show ?thesis by (auto simp: hi_def rows sorted_wrt_append)
  qed
  have later: "hi < key m" if "m \<in> set rest" for m
    using ordered member that by (auto simp: hi_def sorted_wrt_append)
  from keys show "set rows = {m \<in> view. after_name key cursor m \<and> key m \<le> hi}"
    using before later by fastforce
qed

theorem gcs_listing_refines_cursor:
  assumes "gcs_listing key cursor views pages"
  shows "cursor_listing key cursor views (\<Union>(set (map set pages)))"
  using assms
proof induction
  case (last rows view cursor)
  then show ?case using cursor_listing.final_page[of key cursor view]
    by (simp add: after_name_def)
next
  case (more rows remainder view cursor views pages)
  let ?hi = "key (last rows)"
  from ordered_prefix_is_cursor_range[OF more.hyps(1-3)]
  have above: "case cursor of None \<Rightarrow> True | Some lo \<Rightarrow> lo < ?hi"
    and ends: "last rows \<in> view"
    and range: "set rows = {m \<in> view. (case cursor of None \<Rightarrow> True | Some lo \<Rightarrow> lo < key m) \<and> key m \<le> ?hi}"
    by (simp_all add: after_name_def)
  have marker: "\<exists>m\<in>view. key m = ?hi" using ends by blast
  from cursor_listing.next_page[OF above marker more.IH] range show ?case by simp
next
  case empty_continuation
  from cursor_listing.empty_continuation[OF empty_continuation.IH] show ?case by simp
qed

corollary gcs_listing_keeps_persistent_manifest:
  assumes "gcs_listing key None views pages" "\<forall>view\<in>set views. anchor \<in> view"
  shows "anchor \<in> \<Union>(set (map set pages))"
  by (rule cursor_lists_persistent_key[OF gcs_listing_refines_cursor[OF assms(1)] assms(2)]) simp

section \<open>What an opaque marker leaves unspecified\<close>

text \<open>
  This is a countermodel to deriving key coverage from sorted, fresh
  pages and opaque continuation. It is not a model of either provider's
  private implementation. The token carries a next-item hint and an
  offset. When that item is still present it is returned first. When
  the item has disappeared, resumption uses the offset in the current
  view. The last returned key still bounds all subsequent results.
\<close>

definition opaque_suffix where
  "opaque_suffix key last_key hint offset view =
    filter (\<lambda>m. last_key < key m)
      (if hint \<in> set view then dropWhile (\<lambda>m. m \<noteq> hint) view else drop offset view)"

lemma opaque_suffix_preserves_page_guarantees:
  fixes key :: "'a \<Rightarrow> 'k::linorder" and last_key :: 'k and hint :: 'a and offset :: nat
  assumes "sorted_wrt (\<lambda>a b. key a < key b) view"
  defines "rows \<equiv> opaque_suffix key last_key hint offset view"
  shows "set rows \<subseteq> set view"
    "sorted_wrt (\<lambda>a b. key a < key b) rows"
    "\<forall>m\<in>set rows. last_key < key m"
  using assms(1)
  by (auto simp: rows_def opaque_suffix_def sorted_wrt_filter sorted_wrt_dropWhile sorted_wrt_drop
      dest: set_dropWhileD in_set_dropD split: if_splits)

lemma opaque_suffix_on_unchanged_view:
  fixes key :: "'a \<Rightarrow> 'k::linorder"
  assumes "sorted_wrt (\<lambda>a b. key a < key b) (rows @ hint # tail)" "rows \<noteq> []"
  shows "opaque_suffix key (key (last rows)) hint (length rows) (rows @ hint # tail) = hint # tail"
proof -
  have "hint \<notin> set rows" using assms(1) by (auto simp: sorted_wrt_append)
  moreover have "\<forall>m\<in>set (hint # tail). key (last rows) < key m"
    using assms last_in_set by (auto simp: sorted_wrt_append)
  ultimately show ?thesis
    by (simp add: opaque_suffix_def dropWhile_append filter_id_conv)
qed

lemma opaque_fallback_can_skip_first_for_any_page_size:
  assumes "0 < offset" "hint \<notin> set (anchor # tail)" "anchor \<notin> set tail"
  shows "anchor \<notin> set (opaque_suffix key last_key hint offset (anchor # tail))"
  using assms by (cases offset) (auto simp: opaque_suffix_def dest: in_set_dropD)

theorem opaque_marker_contract_does_not_imply_cursor:
  fixes a b anchor z :: state_manifest
    and key :: "state_manifest \<Rightarrow> 'k::linorder"
  assumes keys: "key a < key b" "key b < key anchor" "key anchor < key z"
  defines "views \<equiv> [{a,b,anchor,z}, {anchor,z}]"
  shows "opaque_suffix key (key a) b 1 [anchor,z] = [z]"
    "\<forall>view\<in>set views. anchor \<in> view"
    "\<not> cursor_listing key None views {a,z}"
proof -
  have distinct: "a \<noteq> b" "b \<noteq> anchor" "b \<noteq> z" "a \<noteq> anchor" "anchor \<noteq> z"
    using keys by (meson less_trans less_irrefl)+
  have "key a < key z" using keys by (meson less_trans)
  with distinct show "opaque_suffix key (key a) b 1 [anchor,z] = [z]"
    by (simp add: opaque_suffix_def)
  have retained: "\<forall>view\<in>set views. anchor \<in> view" by (simp add: views_def)
  then show "\<forall>view\<in>set views. anchor \<in> view" .
  show "\<not> cursor_listing key None views {a,z}"
  proof
    assume "cursor_listing key None views {a,z}"
    from cursor_lists_persistent_key[OF this retained] distinct show False by simp
  qed
qed

end
