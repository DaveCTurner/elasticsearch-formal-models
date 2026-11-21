theory Stateless_Single_Page_Recovery
  imports Stateless_Paginated_Recovery
begin

section \<open>Checking the first S3 or Azure listing response\<close>

datatype recovery_list_reply =
    S3_First "bool option" bool "state_manifest set"
  | Azure_First bool "state_manifest set"
  | Listing_Failure

text \<open>
  The Boolean flag in S3_First records whether a continuation token was
  present. Azure_First records whether the SDK returned a nonempty
  continuation marker. A missing first response or an I/O failure
  is Listing_Failure. None is an error, while Some {} is a genuine
  empty directory. No further pages contribute to either result.
\<close>

fun checked_first_listing where
  "checked_first_listing (S3_First truncated token rows) =
     (if truncated = Some False \<and> \<not> token then Some rows else None)"
| "checked_first_listing (Azure_First marker rows) = (if marker then None else Some rows)"
| "checked_first_listing Listing_Failure = None"

fun first_listing_contract where
  "first_listing_contract view (S3_First truncated token rows) =
     (truncated = Some False \<longrightarrow> rows = view)"
| "first_listing_contract view (Azure_First marker rows) = (\<not> marker \<longrightarrow> rows = view)"
| "first_listing_contract view Listing_Failure = True"

lemma checked_listing_is_complete:
  assumes "first_listing_contract view reply" "checked_first_listing reply = Some rows"
  shows "rows = view"
  using assms by (cases reply) (auto split: if_splits)

lemma incomplete_listing_fails_closed [simp]:
  "checked_first_listing (S3_First (Some True) token rows) = None"
  "checked_first_listing (S3_First None token rows) = None"
  "checked_first_listing (S3_First truncated True rows) = None"
  "checked_first_listing (Azure_First True rows) = None"
  "checked_first_listing Listing_Failure = None"
  by simp_all

lemma checked_listing_refines_single_view:
  assumes "first_listing_contract view reply" "checked_first_listing reply = Some rows"
  shows "cursor_listing key None [view] rows"
  using checked_listing_is_complete[OF assms] cursor_listing.final_page[of key None view]
  by simp

lemma checked_header_refines_scan:
  assumes reply: "first_listing_contract view reply" "checked_first_listing reply = Some rows"
    and probe: "searches s election = Some (Probe t)"
    and rep: "newest_manifest view selected" "directory_rep s t selected"
  shows "newest_manifest rows selected"
    "case selected of
      None \<Rightarrow> stateless_step s (s\<lparr>searches := (searches s)
        (election := Some (if 1 < t then Probe (t - 1) else No_Stored_State))\<rparr>)
    | Some m \<Rightarrow> stateless_step s (s\<lparr>searches := (searches s)
        (election := Some (Found (manifest_history m)))\<rparr>)"
  using checked_listing_is_complete[OF reply] rep(1) manifest_probe_refines_scan[OF probe rep(2)]
  by simp_all

section \<open>Independent complete responses for the header and the download\<close>

text \<open>
  The storage snapshot can change between requests. The existing rename
  and deletion argument supplies a lower bound in the frontier term
  for each accepted response separately. A successful first response
  at that term cannot be empty. A failed response may abort the attempt.
\<close>

theorem checked_live_term_listing:
  assumes reply: "first_listing_contract view reply" "checked_first_listing reply = Some rows"
    and present: "anchor \<in> original"
    and first: "is_first \<Longrightarrow> \<forall>m\<in>original. extends_manifest anchor m"
    and trace: "rtranclp (fenced_manifest_step is_first anchor) ([], original) (renames, view)"
    and order: "\<And>m. m \<in> rows \<Longrightarrow> manifest_generation m \<le> manifest_generation selected
        \<Longrightarrow> extends_manifest m selected"
  shows "rows \<noteq> {}" "newest_manifest rows (Some selected) \<Longrightarrow> extends_manifest anchor selected"
proof -
  have snapshots: "\<And>v. v \<in> set [view] \<Longrightarrow>
      \<exists>log. rtranclp (fenced_manifest_step is_first anchor) ([], original) (log, v)"
    using trace by auto
  note pages = checked_listing_refines_single_view[OF reply, where key=manifest_generation]
  from live_term_paginated_listing[OF present first order snapshots pages]
  show "rows \<noteq> {}" "newest_manifest rows (Some selected) \<Longrightarrow> extends_manifest anchor selected"
    by blast+
qed

theorem checked_download_preserves_commits:
  assumes run: "stateless_reachable s"
    and search: "searches s election = Some (Found seen)"
    and remote: "manifest_history selected \<in> completed_images s"
      "term_of (manifest_history selected) = term_of seen"
    and reply: "first_listing_contract view reply" "checked_first_listing reply = Some rows"
    and pick: "newest_manifest rows (Some selected)"
    and present: "anchor \<in> original"
    and anchor: "term_of seen = term_of (frontier s) \<Longrightarrow> manifest_history anchor = frontier s"
    and first: "is_first \<Longrightarrow> \<forall>m\<in>original. extends_manifest anchor m"
    and trace: "rtranclp (fenced_manifest_step is_first anchor) ([], original) (renames, view)"
    and order: "\<And>m. m \<in> rows \<Longrightarrow> manifest_generation m \<le> manifest_generation selected
        \<Longrightarrow> extends_manifest m selected"
    and warm: "warm \<in> insert [] (issued s)" "term_of warm < election"
    and open_term: "latest_issued s election = None"
    and eligible: "confirmed_floor s \<le> election"
    and prior: "h \<in> notifications s"
  shows "prefix h (newer_image warm (manifest_history selected))"
proof -
  have bound: "position (frontier s) \<le> position (manifest_history selected)"
    if "term_of seen = term_of (frontier s)"
    using checked_live_term_listing(2)[OF reply present first trace order pick] anchor[OF that]
    unfolding extends_manifest_def by simp
  show ?thesis by (rule paginated_download_preserves_commits[OF run search remote bound warm open_term eligible prior])
qed

end
