theory Stateless_Storage
  imports Stateless_Persistence
begin

section \<open>The lease object and successful reads\<close>

record lease_fields =
  lease_term :: nat
  left_generation :: nat
  deletion_generation :: nat

definition empty_lease where
  "empty_lease = \<lparr>lease_term = 0, left_generation = 0, deletion_generation = 0\<rparr>"

text \<open>
  These constructors represent empty bytes and the format-1 encoding (format
  tag followed by three fixed-width big-endian longs). The correspondence
  uses nonnegative longs and excludes arithmetic overflow.
\<close>

datatype lease_bytes = Empty_Register | Format_One nat nat nat

definition encode_lease where
  "encode_lease w = (if w = empty_lease then Empty_Register
    else Format_One (lease_term w) (left_generation w) (deletion_generation w))"

fun decode_lease where
  "decode_lease Empty_Register = empty_lease"
| "decode_lease (Format_One t l d) =
    \<lparr>lease_term = t, left_generation = l, deletion_generation = d\<rparr>"

lemma lease_roundtrip [simp]: "decode_lease (encode_lease w) = w"
  by (cases w) (simp add: encode_lease_def)

lemma lease_bytes_match [simp]: "encode_lease w = encode_lease v \<longleftrightarrow> w = v"
proof
  assume eq: "encode_lease w = encode_lease v"
  from arg_cong[OF eq, of decode_lease] show "w = v" by simp
next
  assume "w = v"
  then show "encode_lease w = encode_lease v" by (rule arg_cong)
qed

datatype lease_write = Claim_Term incarnation_id nat | Set_Generations nat nat

fun lease_update where
  "lease_update (Claim_Term who proposed) w =
    w\<lparr>lease_term := max proposed (Suc (lease_term w)), left_generation := 0\<rparr>"
| "lease_update (Set_Generations l d) w = w\<lparr>left_generation := l, deletion_generation := d\<rparr>"

datatype register_backend = S3_Conditional | GCS_Generation | Azure_Lease

text \<open>
  For a successful replacement, S3 pins the bytes with the matching ETag,
  GCS pins them with a matching live generation, and Azure pins them by
  reading and writing under the same valid exclusive lease. For creation
  all three require the object still to be absent. The token properties
  are the repository service boundary. Only a matching witness from a
  successful replacement can produce the Boolean success callback.
\<close>

datatype register_guard = Create_If_Absent | Match_Object | Hold_Exclusive_Lease

fun replacement_guard where
  "replacement_guard backend False = Create_If_Absent"
| "replacement_guard Azure_Lease True = Hold_Exclusive_Lease"
| "replacement_guard S3_Conditional True = Match_Object"
| "replacement_guard GCS_Generation True = Match_Object"

definition valid_guard where
  "valid_guard guard before live \<longleftrightarrow> (case guard of
    Create_If_Absent \<Rightarrow> before = None \<and> live = None
  | Match_Object \<Rightarrow> before \<noteq> None \<and> before = live
  | Hold_Exclusive_Lease \<Rightarrow> before \<noteq> None \<and> before = live)"

definition lease_effect where
  "lease_effect backend before live expected op result \<longleftrightarrow>
    valid_guard (replacement_guard backend (before \<noteq> None)) before live \<and>
    case_option Empty_Register id before = encode_lease expected \<and>
    result = Some (encode_lease (lease_update op expected))"

lemma effective_lease_write:
  assumes "lease_effect backend before live expected op result"
  shows "decode_lease (case_option Empty_Register id live) = expected"
    "decode_lease (case_option Empty_Register id result) = lease_update op expected"
    "lease_term expected \<le> lease_term (lease_update op expected)"
proof -
  have same: "before = live"
    using assms by (cases backend; cases "before = None"; simp add: lease_effect_def valid_guard_def)
  then show "decode_lease (case_option Empty_Register id live) = expected"
    using assms unfolding lease_effect_def by simp
  show "decode_lease (case_option Empty_Register id result) = lease_update op expected"
    using assms unfolding lease_effect_def by simp
  show "lease_term expected \<le> lease_term (lease_update op expected)"
    by (cases op) simp_all
qed

definition lease_value where
  "lease_value b = decode_lease (case_option Empty_Register id b)"

lemma lease_claim_refines_reserve:
  assumes effect: "lease_effect backend before live expected (Claim_Term who proposed) result"
    and rep: "lease_term (lease_value live) = reserved_term s"
  defines "t \<equiv> lease_term (lease_value result)"
  shows "stateless_step s (s\<lparr>reserved_term := t, granted_to := (granted_to s)(t := Some who)\<rparr>)"
    "reserved_term s < t"
proof -
  from effective_lease_write[OF effect] rep have "lease_term expected = reserved_term s"
    "t = max proposed (Suc (reserved_term s))" by (simp_all add: lease_value_def t_def)
  then show "stateless_step s (s\<lparr>reserved_term := t, granted_to := (granted_to s)(t := Some who)\<rparr>)"
    by (intro stateless_step.reserve) auto
  from \<open>t = max proposed (Suc (reserved_term s))\<close> show "reserved_term s < t" by simp
qed

lemma generation_update_stutters:
  assumes "lease_effect backend before live expected (Set_Generations l d) result"
  shows "lease_term (lease_value result) = lease_term (lease_value live)"
  using effective_lease_write[OF assms] by (simp add: lease_value_def)

text \<open>
  The register revision list indexes effects, including an effect whose caller
  received an exception. A successful read is at or after every register
  effect whose write already returned success at invocation. Bind a grant
  confirmation to its particular successful CAS, even if later effects
  have already run. A fence read may overlap any unacknowledged effect.
\<close>

definition lease_journal where
  "lease_journal revisions \<longleftrightarrow> revisions \<noteq> [] \<and> hd revisions = None \<and>
    (\<forall>i j. i \<le> j \<and> j < length revisions \<longrightarrow>
      lease_term (lease_value (revisions ! i)) \<le> lease_term (lease_value (revisions ! j)))"

lemma journal_init [simp]: "lease_journal [None]"
  by (auto simp: lease_journal_def lease_value_def)

lemma journal_append:
  assumes "lease_journal revisions" "lease_effect backend before (last revisions) expected op result"
  shows "lease_journal (revisions @ [result])"
proof -
  have nonempty: "revisions \<noteq> []" and head: "hd revisions = None"
    using assms(1) unfolding lease_journal_def by auto
  have mono: "i \<le> j \<Longrightarrow> j < length revisions \<Longrightarrow>
    lease_term (lease_value (revisions ! i)) \<le> lease_term (lease_value (revisions ! j))" for i j
    using assms(1) unfolding lease_journal_def by blast
  have "lease_term (lease_value (last revisions)) \<le> lease_term (lease_value result)"
    using effective_lease_write[OF assms(2)] by (simp add: lease_value_def)
  moreover have "lease_term (lease_value (revisions ! i)) \<le> lease_term (lease_value (last revisions))"
    if "i < length revisions" for i
    using mono[of i "length revisions - 1"] that nonempty by (simp add: last_conv_nth)
  ultimately show ?thesis using nonempty head mono
    by (auto simp: lease_journal_def nth_append hd_append split: if_splits intro: order_trans)
qed

inductive production_lease_revisions where
  initial: "production_lease_revisions [None]"
| replace:
    "production_lease_revisions revisions \<Longrightarrow>
     lease_effect backend before (last revisions) expected op result \<Longrightarrow>
     production_lease_revisions (revisions @ [result])"

lemma production_lease_journal:
  "production_lease_revisions revisions \<Longrightarrow> lease_journal revisions"
  by (induction rule: production_lease_revisions.induct) (auto intro: journal_append)

definition callback_floor where
  "callback_floor revisions returned = Max (insert 0 ((\<lambda>i. lease_term (lease_value (revisions ! i))) ` returned))"

lemma callback_floor_insert:
  assumes "finite returned"
  shows "callback_floor revisions (insert k returned) =
    max (lease_term (lease_value (revisions ! k))) (callback_floor revisions returned)"
proof -
  let ?f = "\<lambda>i. lease_term (lease_value (revisions ! i))"
  have finite: "finite (insert 0 (?f ` returned))" using assms by simp
  have "callback_floor revisions (insert k returned) = Max (insert (?f k) (insert 0 (?f ` returned)))"
    by (simp only: callback_floor_def image_insert insert_commute[of 0 "?f k" "?f ` returned"])
  also have "\<dots> = max (?f k) (callback_floor revisions returned)"
    unfolding callback_floor_def by (rule Max_insert[OF finite]) simp
  finally show ?thesis .
qed

lemma callback_floor_append:
  assumes "\<forall>k\<in>returned. k < length revisions"
  shows "callback_floor (revisions @ [result]) returned = callback_floor revisions returned"
proof -
  have "(\<lambda>i. lease_term (lease_value ((revisions @ [result]) ! i))) ` returned =
    (\<lambda>i. lease_term (lease_value (revisions ! i))) ` returned"
    using assms by (intro image_cong) (auto simp: nth_append)
  then show ?thesis by (simp add: callback_floor_def)
qed

lemma election_callback_refines_confirm:
  assumes "granted_to s t = Some who" "t = lease_term (lease_value (revisions ! k))"
    "finite returned" "confirmed_floor s = callback_floor revisions returned"
  defines "s' \<equiv> s\<lparr>confirmed_floor := callback_floor revisions (insert k returned),
      confirmed_terms := insert t (confirmed_terms s)\<rparr>"
  shows "stateless_step s s'"
proof -
  have "callback_floor revisions (insert k returned) = max t (confirmed_floor s)"
    using callback_floor_insert[OF assms(3), of revisions k] assms(2,4) by simp
  from this stateless_step.confirm[OF assms(1)] show ?thesis by (simp add: s'_def)
qed

lemma read_after_success_floor:
  assumes revisions: "lease_journal revisions" and read: "r < length revisions"
    and timing: "\<forall>k\<in>returned. k \<le> r" and returned: "finite returned"
  shows "callback_floor revisions returned \<le> lease_term (lease_value (revisions ! r))"
  unfolding callback_floor_def
  using assms by (subst Max_le_iff) (auto simp: lease_journal_def)

lemma successful_before_commit_refines:
  assumes "production_lease_revisions revisions" "r < length revisions" "\<forall>k\<in>returned. k \<le> r" "finite returned"
    "confirmed_floor s = callback_floor revisions returned"
    "lease_term (lease_value (revisions ! r)) = t"
    "latest_issued s t = Some h" "visible_image s t = Some h"
  shows "stateless_step s (s\<lparr>approvals := insert h (approvals s), frontier := h\<rparr>)"
  using read_after_success_floor[OF production_lease_journal[OF assms(1)] assms(2-4)] assms(5,6)
  by (intro stateless_step.approve[OF assms(7,8)]) simp

section \<open>Per-term Lucene manifests\<close>

type_synonym file_name = string
type_synonym file_bytes = "nat list"

datatype coordination_object = Lease_Object | Heartbeat_Object file_name | Term_Object nat file_name

definition term_objects where
  "term_objects i = range (Term_Object i)"

lemma term_prefix_isolated:
  "Lease_Object \<notin> term_objects i"
  "Heartbeat_Object name \<notin> term_objects i"
  "i \<noteq> j \<Longrightarrow> term_objects i \<inter> term_objects j = {}"
  by (auto simp: term_objects_def)

record state_manifest =
  manifest_generation :: nat
  manifest_history :: lineage
  manifest_files :: "file_name \<Rightarrow> file_bytes option"

definition files_match where
  "files_match files m \<longleftrightarrow> (\<forall>name bytes. manifest_files m name = Some bytes \<longrightarrow> files name = Some bytes)"

definition file_sync where
  "file_sync uploads files = (\<lambda>name. case uploads name of None \<Rightarrow> files name | Some bytes \<Rightarrow> Some bytes)"

definition same_reused_files where
  "same_reused_files previous new uploads \<longleftrightarrow>
    (\<forall>name bytes. manifest_files new name = Some bytes \<longrightarrow>
      uploads name = Some bytes \<or> (uploads name = None \<and> manifest_files previous name = Some bytes))"

lemma sync_completes_manifest:
  assumes "files_match files previous" "same_reused_files previous new uploads"
  shows "files_match (file_sync uploads files) new"
  unfolding files_match_def
proof (intro allI impI)
  fix name bytes
  assume "manifest_files new name = Some bytes"
  with assms(2) have "uploads name = Some bytes \<or>
    (uploads name = None \<and> manifest_files previous name = Some bytes)"
    unfolding same_reused_files_def by blast
  with assms(1) show "file_sync uploads files name = Some bytes"
    unfolding files_match_def file_sync_def by fastforce
qed

lemma colliding_file_upload_invalidates_manifest:
  assumes "manifest_files m name = Some bytes" "uploads name = Some other" "other \<noteq> bytes"
  shows "\<not> files_match (file_sync uploads files) m"
proof
  assume "files_match (file_sync uploads files) m"
  with assms(1) have "file_sync uploads files name = Some bytes" unfolding files_match_def by blast
  with assms(2,3) show False by (simp add: file_sync_def)
qed

lemma prune_preserves_latest_manifest:
  assumes "files_match files m" "removed \<inter> dom (manifest_files m) = {}"
  shows "files_match (\<lambda>name. if name \<in> removed then None else files name) m"
  using assms by (auto simp: files_match_def dom_def)

text \<open>
  A visible manifest is a successfully finalized segments object. The
  listing abstraction chooses the greatest generation in the live term
  directory. Term-directory cleanup can remove individual objects from an
  obsolete directory, so it can expose a smaller generation there.

  A paginated traversal of a changing prefix need not act as a single
  listing. Here the numbers are ranks in key order, independent of
  manifest generation order. The replacement sorts before the page cursor.
\<close>

lemma paginated_listing_can_miss_replacement:
  "{k\<in>{2, 3::nat}. k \<le> 2} \<union> {k\<in>{1, 2::nat}. 2 < k} = {2}"
  by auto

definition newest_manifest where
  "newest_manifest listed result \<longleftrightarrow>
    (case result of None \<Rightarrow> listed = {}
     | Some m \<Rightarrow> m \<in> listed \<and>
       (\<forall>p\<in>listed. p \<noteq> m \<longrightarrow> manifest_generation p < manifest_generation m))"

lemma newest_manifest_unique:
  assumes m: "newest_manifest listed (Some m)" and p: "newest_manifest listed (Some p)"
  shows "m = p"
proof (rule ccontr)
  assume "m \<noteq> p"
  have mem: "m \<in> listed" "p \<in> listed" using m p by (simp_all add: newest_manifest_def)
  from p mem(1) \<open>m \<noteq> p\<close> have "manifest_generation m < manifest_generation p"
    unfolding newest_manifest_def by simp
  moreover from m mem(2) \<open>m \<noteq> p\<close> have "manifest_generation p < manifest_generation m"
    unfolding newest_manifest_def by auto
  ultimately show False by (rule less_asym')
qed

inductive live_manifest_step where
  install:
    "newest_manifest before previous \<Longrightarrow> files_match files new \<Longrightarrow>
     (\<And>old. previous = Some old \<Longrightarrow>
       manifest_generation old < manifest_generation new \<and>
       position (manifest_history old) \<le> position (manifest_history new)) \<Longrightarrow>
     retained \<subseteq> before \<Longrightarrow>
     live_manifest_step before (insert new retained)"
| prune:
    "newest_manifest before (Some latest) \<Longrightarrow> latest \<in> retained \<Longrightarrow>
     retained \<subseteq> before \<Longrightarrow> live_manifest_step before retained"

lemma live_manifest_preserves_header:
  assumes path: "rtranclp live_manifest_step before after"
    and head: "newest_manifest before (Some seen)"
  shows "\<exists>m. newest_manifest after (Some m) \<and>
    position (manifest_history seen) \<le> position (manifest_history m)"
  using path
proof induction
  case base
  then show ?case using head by blast
next
  case (step middle after)
  obtain m where latest: "newest_manifest middle (Some m)"
    and key: "position (manifest_history seen) \<le> position (manifest_history m)"
    using step.IH by blast
  show ?case using step.hyps(2)
  proof cases
    case (install previous files new retained)
    obtain p where p: "previous = Some p"
      using latest install(2) by (cases previous) (auto simp: newest_manifest_def)
    have eq: "m = p" by (rule newest_manifest_unique[OF latest]) (use install(2) p in simp)
    have gen: "manifest_generation m < manifest_generation new"
      and advance: "position (manifest_history m) \<le> position (manifest_history new)"
      using install(4)[OF p] eq by simp_all
    have "manifest_generation q < manifest_generation new" if "q \<in> retained" for q
    proof -
      have "q \<in> middle" by (rule subsetD[OF install(5) that])
      with latest have "manifest_generation q \<le> manifest_generation m"
        unfolding newest_manifest_def by (cases "q = m") auto
      from this gen show ?thesis by (rule le_less_trans)
    qed
    then have "newest_manifest after (Some new)" by (auto simp: install(1) newest_manifest_def)
    moreover have "position (manifest_history seen) \<le> position (manifest_history new)"
      by (rule order_trans[OF key advance])
    ultimately show ?thesis by blast
  next
    case (prune latest')
    have "m = latest'" by (rule newest_manifest_unique[OF latest prune(1)])
    then have "newest_manifest after (Some m)"
      using latest prune(2,3) by (auto simp: newest_manifest_def)
    with key show ?thesis by blast
  qed
qed

lemma later_manifest_dominates_header:
  assumes "newest_manifest before (Some seen)" "newest_manifest after (Some m)"
    "rtranclp live_manifest_step before after"
  shows "position (manifest_history seen) \<le> position (manifest_history m)"
  using live_manifest_preserves_header[OF assms(3,1)] newest_manifest_unique[OF assms(2)] by blast

definition directory_rep where
  "directory_rep s t selected \<longleftrightarrow>
    (\<forall>m. selected = Some m \<longrightarrow>
      manifest_history m \<in> completed_images s \<and> term_of (manifest_history m) = t) \<and>
    (term_of (frontier s) \<le> t \<longrightarrow>
       map_option manifest_history selected = visible_image s t)"

lemma issued_image_key:
  assumes run: "stateless_reachable s" and new: "latest_issued s t = Some h"
    and old: "p \<in> completed_images s" "term_of p = t"
  shows "position p \<le> position h"
proof -
  have ii: "issued_ok s" and ss: "store_ok s"
    using stateless_invariants[OF run] unfolding stateless_ok_def by auto
  from ss old(1) have pub: "p \<in> issued s" unfolding store_ok_def by blast
  obtain q where q: "latest_issued s (term_of p) = Some q" "prefix p q" "position p \<le> position q"
    by (rule issued_latest[OF ii pub])
  from q new old(2) show ?thesis by auto
qed

lemma serialized_writer_advances_manifest:
  assumes run: "stateless_reachable s" and own: "latest_issued s t = Some (manifest_history new)"
    and rep: "directory_rep s t selected"
    and listing: "newest_manifest before selected" and synced: "files_match files new"
    and generation: "\<And>old. selected = Some old \<Longrightarrow> manifest_generation old < manifest_generation new"
    and retains: "retained \<subseteq> before"
  shows "live_manifest_step before (insert new retained)"
proof (rule live_manifest_step.install[OF listing synced _ retains])
  fix old
  assume old: "selected = Some old"
  from rep old have "manifest_history old \<in> completed_images s" "term_of (manifest_history old) = t"
    by (simp_all add: directory_rep_def)
  from generation[OF old] issued_image_key[OF run own this]
  show "manifest_generation old < manifest_generation new \<and>
    position (manifest_history old) \<le> position (manifest_history new)" by simp
qed

lemma manifest_install_refines_upload:
  assumes reach: "stateless_reachable s" and own: "latest_issued s t = Some (manifest_history m)"
    and synced: "files_match files m"
  defines "s' \<equiv> s\<lparr>completed_images := insert (manifest_history m) (completed_images s),
        visible_image := (visible_image s)(t := Some (manifest_history m))\<rparr>"
  shows "stateless_step s s'" "directory_rep s' t (Some m)"
proof -
  have ii: "issued_ok s" and so: "store_ok s"
    using stateless_invariants[OF reach] unfolding stateless_ok_def by auto
  have tag: "term_of (manifest_history m) = t" using ii own unfolding issued_ok_def by blast
  have advance: "position old \<le> position (manifest_history m)" if vis: "visible_image s t = Some old" for old
  proof -
    from so vis have "old \<in> completed_images s" "term_of old = t" unfolding store_ok_def by auto
    from issued_image_key[OF reach own this] show ?thesis .
  qed
  show "stateless_step s s'" unfolding s'_def by (rule stateless_step.upload[OF own advance])
  show "directory_rep s' t (Some m)" using tag by (simp add: s'_def directory_rep_def)
qed

lemma manifest_probe_refines_scan:
  assumes probe: "searches s election = Some (Probe t)"
    and rep: "directory_rep s t selected"
  shows "case selected of
      None \<Rightarrow> stateless_step s (s\<lparr>searches := (searches s)
        (election := Some (if 1 < t then Probe (t - 1) else No_Stored_State))\<rparr>)
    | Some m \<Rightarrow> stateless_step s (s\<lparr>searches := (searches s)
        (election := Some (Found (manifest_history m)))\<rparr>)"
proof (cases selected)
  case None
  have "visible_image s t = None \<or> t < term_of (frontier s)"
    using rep None by (cases "t < term_of (frontier s)") (auto simp: directory_rep_def)
  from stateless_step.absent[OF probe this] show ?thesis by (simp add: None)
next
  case (Some m)
  have "visible_image s t = Some (manifest_history m) \<or>
      (manifest_history m \<in> completed_images s \<and> term_of (manifest_history m) = t \<and>
        (t = term_of (frontier s) \<longrightarrow> position (frontier s) \<le> position (manifest_history m)))"
    using rep Some by (cases "t < term_of (frontier s)") (auto simp: directory_rep_def)
  from stateless_step.header[OF probe this] show ?thesis by (simp add: Some)
qed

lemma manifest_download_refines_base:
  assumes scan: "searches s election = Some (Found (manifest_history seen))"
    and rep: "directory_rep s (term_of (manifest_history seen)) (Some m)"
    and read: "files_match downloaded_files m"
    and progress: "term_of (frontier s) \<le> term_of (manifest_history seen) \<Longrightarrow>
      rtranclp live_manifest_step listed_at_header listed_at_download"
    and header: "newest_manifest listed_at_header (Some seen)"
    and download: "newest_manifest listed_at_download (Some m)"
  shows "election_base s election warm (newer_image warm (manifest_history m))"
proof -
  have member: "manifest_history m \<in> completed_images s"
    and tag: "term_of (manifest_history m) = term_of (manifest_history seen)"
    using rep by (simp_all add: directory_rep_def)
  have "position (manifest_history seen) \<le> position (manifest_history m) \<or>
        term_of (manifest_history seen) < term_of (frontier s)"
  proof (cases "term_of (manifest_history seen) < term_of (frontier s)")
    case True
    then show ?thesis by simp
  next
    case False
    then have "term_of (frontier s) \<le> term_of (manifest_history seen)" by simp
    from later_manifest_dominates_header[OF header download progress[OF this]] show ?thesis by simp
  qed
  then have "position (manifest_history seen) \<le> position (manifest_history m) \<or>
    term_of (manifest_history seen) \<noteq> term_of (frontier s) \<or>
    position (frontier s) \<le> position (manifest_history m)" by auto
  from election_base.downloaded[OF scan member tag this]
  show "election_base s election warm (newer_image warm (manifest_history m))" .
qed

theorem obsolete_manifest_fences_first_publication:
  assumes run: "stateless_reachable s" and scan: "searches s election = Some (Found seen)"
    and obsolete: "term_of seen < term_of (frontier s)" and first: "latest_issued s election = None"
  shows "election < confirmed_floor s"
proof -
  have "frontier s \<noteq> []" using obsolete by auto
  have ok: "stateless_ok s" by (rule stateless_invariants[OF run])
  then have ii: "issued_ok s" and so: "searches_ok s" and lo: "lease_ok s" and fo: "frontier_ok s"
    unfolding stateless_ok_def by auto
  note tip = frontier_issued[OF fo \<open>frontier s \<noteq> []\<close>]
  have "election \<le> term_of (frontier s)"
  proof (rule leI, rule notI)
    assume "term_of (frontier s) < election"
    from search_observation(3)[OF so scan \<open>frontier s \<noteq> []\<close> this]
    have "position (frontier s) \<le> position seen" by simp
    from position_term_mono[OF this] obsolete show False by simp
  qed
  moreover have "election \<noteq> term_of (frontier s)"
  proof
    assume same: "election = term_of (frontier s)"
    obtain b where "latest_issued s (term_of (frontier s)) = Some b"
      using issued_latest[OF ii tip] by blast
    with same first show False by simp
  qed
  ultimately show ?thesis using issued_term_bound[OF lo ii tip] by (meson le_neq_implies_less less_le_trans)
qed

theorem storage_recovery_extends_prior_commits:
  assumes run: "stateless_reachable s"
    and first: "latest_issued s election = None"
    and warm_state: "warm \<in> insert [] (issued s)" "term_of warm < election"
    and scan: "searches s election = Some (Found (manifest_history seen))"
    and rep: "directory_rep s (term_of (manifest_history seen)) (Some m)"
    and read: "files_match downloaded_files m"
    and progress: "term_of (frontier s) \<le> term_of (manifest_history seen) \<Longrightarrow>
      rtranclp live_manifest_step listed_at_header listed_at_download"
    and header: "newest_manifest listed_at_header (Some seen)"
    and download: "newest_manifest listed_at_download (Some m)"
    and fence: "confirmed_floor s \<le> election"
    and prior: "h \<in> notifications s"
  shows "prefix h (newer_image warm (manifest_history m))"
proof -
  have parent: "publish_parent s election (newer_image warm (manifest_history m))"
    by (rule publish_parent.first[OF first warm_state manifest_download_refines_base[OF scan rep read progress header download]])
  have "term_of (frontier s) \<le> confirmed_floor s"
  proof (cases "frontier s = []")
    case False
    from stateless_invariants[OF run] have lo: "lease_ok s" and ii: "issued_ok s" and fo: "frontier_ok s"
      unfolding stateless_ok_def by auto
    show ?thesis by (rule issued_term_bound[OF lo ii frontier_issued[OF fo False]])
  qed simp
  then have "term_of (frontier s) \<le> election" by (rule order_trans[OF _ fence])
  from chosen_parent_extends_prior_commits[OF run parent this prior] show ?thesis .
qed

lemma term_cleanup_refines:
  assumes applied: "h \<in> notifications s" and earlier: "\<And>i. i \<in> removed \<Longrightarrow> i < term_of h"
  defines "s' \<equiv> s\<lparr>visible_image := (\<lambda>i. if i \<in> removed then None else visible_image s i)\<rparr>"
  shows "stateless_step s s'"
    "stateless_reachable s \<Longrightarrow> term_of (frontier s) \<notin> removed"
proof -
  show "stateless_step s s'" unfolding s'_def
    by (rule stateless_step.cleanup[OF applied]) (use earlier in auto)
  assume "stateless_reachable s"
  then have "frontier_ok s" using stateless_invariants unfolding stateless_ok_def by blast
  with applied have "position h \<le> position (frontier s)" unfolding frontier_ok_def by blast
  from position_term_mono[OF this] earlier show "term_of (frontier s) \<notin> removed" by force
qed

end
