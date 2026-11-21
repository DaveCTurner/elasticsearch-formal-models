theory Stateless_Failover_Authority
  imports Stateless_Storage
begin

section \<open>A separate group for stateless failover evidence\<close>

text \<open>
  StatelessElectionStrategy uses a local self-vote and the shared lease
  register. The evidence group below has its own deployment roster. Its
  membership comes from an authenticated deployment snapshot that remains
  readable while cluster-state publication is stalled. A change of membership
  requires a fresh roster epoch. The deployment must bind transport identities
  to that roster and distribute the current snapshot, including the cluster
  identity. The lease bytes contain no cluster identifier. This theory does not
  implement roster distribution or derive its availability. If the roster of
  three contains both the candidate and the incumbent, at most one eligible
  reporter remains and authorization is impossible. A deployment can keep
  candidate and incumbent nodes outside its observer roster, but still needs a
  stably eligible, healthy majority of the configured roster.

  AtomicRegisterPreVoteCollector opens the existing attempt path on a
  successful heartbeat read that is absent or old. A recent heartbeat
  suppresses that path, and a read error produces no attempt. The proposed
  evidence path is additive. Neither the ordinary path nor initial startup
  is made contingent on a separate quorum. Candidate eligibility, becoming a
  candidate, and the one-shot start callback remain part of the handoff to
  Coordinator. The register and the exact-term commit fence are unchanged.
\<close>

record stateless_failover_view =
  sf_cluster :: nat
  sf_roster_epoch :: nat
  sf_roster :: "node set"
  sf_incumbent :: incarnation_id
  sf_candidate :: incarnation_id
  sf_lease_term :: nat
  sf_round :: nat
  sf_commit :: rank
  sf_deadline :: nat

record stateless_progress_sample =
  sf_sample_time :: nat
  sf_sample_rank :: rank
  sf_sample_pending :: bool
  sf_sample_term :: nat

record stateless_failover_report =
  sf_report_view :: stateless_failover_view
  sf_before :: stateless_progress_sample
  sf_after :: stateless_progress_sample
  sf_received :: nat

text \<open>
  The authenticated inbox records the transport identity, rather than an
  asserted identity in a payload. The two sample times are from one observer's
  monotonic clock. The deadline and receive time use the candidate's clock;
  the response echoes the entire challenged view including the candidate's
  incarnation and round. The candidate never reuses a round identifier in one
  incarnation. The observer takes both samples after seeing that challenge.
  The candidate never compares its clock to the observer's clock.

  The observed rank is a fenced-commit watermark for the incumbent. Neither
  the term and generations in a lease nor a term and timestamp in a stored
  heartbeat provide that watermark or identify the incumbent incarnation.
  The report path requires an independently serviceable source of current
  pending work, a binding between incumbent identity and lease term, and
  fenced progress. Such a source must cover successful fences even if an
  applier or publication callback stalls. Reading a manifest alone supplies
  no such guarantee, since the write can precede fence approval.
\<close>

definition stateless_report_valid where
  "stateless_report_valid threshold now view r \<longleftrightarrow>
    sf_report_view r = view \<and> sf_received r \<le> now \<and> now < sf_deadline view \<and>
    0 < threshold \<and> sf_sample_time (sf_before r) + threshold \<le> sf_sample_time (sf_after r) \<and>
    sf_sample_pending (sf_before r) \<and> sf_sample_pending (sf_after r) \<and>
    sf_sample_rank (sf_before r) = sf_commit view \<and> sf_sample_rank (sf_after r) = sf_commit view \<and>
    sf_sample_term (sf_before r) = sf_lease_term view \<and> sf_sample_term (sf_after r) = sf_lease_term view"

definition stateless_evidence_voters where
  "stateless_evidence_voters threshold now view inbox =
    {n. \<exists>r. (n,r) \<in> inbox \<and> stateless_report_valid threshold now view r}"

definition stateless_failover_authority where
  "stateless_failover_authority threshold healthy now view inbox Q \<longleftrightarrow>
    0 < sf_lease_term view \<and>
    fst (sf_candidate view) \<in> healthy \<and> fst (sf_candidate view) \<noteq> fst (sf_incumbent view) \<and>
    majority (sf_roster view) Q \<and>
    Q \<subseteq> healthy - {fst (sf_incumbent view), fst (sf_candidate view)} \<and>
    Q \<subseteq> stateless_evidence_voters threshold now view inbox"

definition stateless_attempt_permitted where
  "stateless_attempt_permitted ordinary threshold healthy now view inbox \<longleftrightarrow>
    ordinary \<or> (\<exists>Q. stateless_failover_authority threshold healthy now view inbox Q)"

lemma ordinary_stateless_attempt_retained:
  "ordinary \<Longrightarrow> stateless_attempt_permitted ordinary threshold healthy now view inbox"
  by (simp add: stateless_attempt_permitted_def)

lemma independently_serviced_reports_open_attempt:
  assumes "0 < sf_lease_term view" "fst (sf_candidate view) \<in> healthy"
    "fst (sf_candidate view) \<noteq> fst (sf_incumbent view)"
    "majority (sf_roster view) Q" "Q \<subseteq> healthy - {fst (sf_incumbent view), fst (sf_candidate view)}"
    "\<And>n. n \<in> Q \<Longrightarrow> \<exists>r. (n,r) \<in> inbox \<and> stateless_report_valid threshold now view r"
  shows "stateless_attempt_permitted ordinary threshold healthy now view inbox"
  using assms by (auto simp: stateless_attempt_permitted_def stateless_failover_authority_def stateless_evidence_voters_def)

lemma stateless_authorities_intersect:
  assumes "stateless_failover_authority threshold healthy t view inbox Q"
    "stateless_failover_authority threshold' healthy' t' view' inbox' R"
    "sf_roster view' = sf_roster view"
  shows "\<exists>n\<in>Q. n \<in> R"
  using assms by (auto simp: stateless_failover_authority_def intro: majority_intersects)

lemma stateless_authority_has_live_report:
  assumes "stateless_failover_authority threshold healthy now view inbox Q"
  obtains n r where "n \<in> Q" "(n,r) \<in> inbox" "stateless_report_valid threshold now view r"
proof -
  have quorum: "majority (sf_roster view) Q" and valid: "Q \<subseteq> stateless_evidence_voters threshold now view inbox"
    using assms by (simp_all add: stateless_failover_authority_def)
  obtain n where "n \<in> Q" using majority_intersects[OF quorum quorum] by blast
  then show thesis using valid that unfolding stateless_evidence_voters_def by blast
qed

theorem expired_stateless_evidence_cannot_open:
  assumes "sf_deadline view \<le> now"
  shows "\<not> stateless_failover_authority threshold healthy now view inbox Q"
  using assms stateless_authority_has_live_report unfolding stateless_report_valid_def by force

theorem stale_stateless_evidence_cannot_open:
  assumes changed: "old \<noteq> view"
    and inbox: "\<And>n r. (n,r) \<in> inbox \<Longrightarrow> sf_report_view r = old"
  shows "\<not> stateless_failover_authority threshold healthy now view inbox Q"
proof
  assume "stateless_failover_authority threshold healthy now view inbox Q"
  then obtain n r where "(n,r) \<in> inbox" "stateless_report_valid threshold now view r"
    by (rule stateless_authority_has_live_report)
  with inbox changed show False by (simp add: stateless_report_valid_def)
qed

corollary stateless_evidence_invalidated_by_change:
  assumes "sf_cluster old \<noteq> sf_cluster view \<or> sf_roster_epoch old \<noteq> sf_roster_epoch view \<or>
    sf_roster old \<noteq> sf_roster view \<or> sf_incumbent old \<noteq> sf_incumbent view \<or>
    sf_candidate old \<noteq> sf_candidate view \<or> sf_lease_term old \<noteq> sf_lease_term view \<or>
    sf_round old \<noteq> sf_round view \<or> sf_commit old \<noteq> sf_commit view"
    "\<And>n r. (n,r) \<in> inbox \<Longrightarrow> sf_report_view r = old"
  shows "\<not> stateless_failover_authority threshold healthy now view inbox Q"
  by (rule stale_stateless_evidence_cannot_open[OF _ assms(2)]) (use assms(1) in blast)

lemma duplicate_stateless_reports_cannot_increase_quorum:
  assumes "(n,r) \<in> inbox"
  shows "stateless_failover_authority threshold healthy now view (insert (n,r) inbox) Q =
    stateless_failover_authority threshold healthy now view inbox Q"
  by (simp only: insert_absorb[OF assms])

lemma invalid_stateless_report_does_not_count:
  assumes "\<not> stateless_report_valid threshold now view r"
  shows "stateless_evidence_voters threshold now view (insert (n,r) inbox) =
    stateless_evidence_voters threshold now view inbox"
  using assms by (auto simp: stateless_evidence_voters_def)

lemma independent_observer_capacity:
  assumes "stateless_failover_authority threshold healthy now view inbox Q"
  shows "card (sf_roster view) <
    2 * card (sf_roster view \<inter> (healthy - {fst (sf_incumbent view), fst (sf_candidate view)}))"
proof -
  let ?eligible = "sf_roster view \<inter> (healthy - {fst (sf_incumbent view), fst (sf_candidate view)})"
  from assms have "card (sf_roster view) < 2 * card Q" "finite (sf_roster view)" "Q \<subseteq> ?eligible"
    by (auto simp: stateless_failover_authority_def majority_def)
  then have "card Q \<le> card ?eligible" by (intro card_mono) simp_all
  with \<open>card (sf_roster view) < 2 * card Q\<close> show ?thesis by linarith
qed

lemma three_observers_including_both_parties_insufficient:
  assumes size: "card (sf_roster view) = 3"
    and members: "fst (sf_incumbent view) \<in> sf_roster view" "fst (sf_candidate view) \<in> sf_roster view"
  shows "\<not> stateless_failover_authority threshold healthy now view inbox Q"
proof
  assume auth: "stateless_failover_authority threshold healthy now view inbox Q"
  let ?parties = "{fst (sf_incumbent view), fst (sf_candidate view)}"
  from auth have fin: "finite (sf_roster view)" and distinct: "fst (sf_candidate view) \<noteq> fst (sf_incumbent view)"
    by (simp_all add: stateless_failover_authority_def majority_def)
  have "card (sf_roster view - ?parties) = 1"
    using size distinct by (simp add: card_Diff_subset[of ?parties "sf_roster view"] members)
  moreover have "card (sf_roster view \<inter> (healthy - ?parties)) \<le> card (sf_roster view - ?parties)"
    by (rule card_mono) (use fin in auto)
  ultimately show False using independent_observer_capacity[OF auth] size by linarith
qed

section \<open>Required fenced-progress observation\<close>

definition fenced_progress_observation where
  "fenced_progress_observation watermark fences \<longleftrightarrow>
    mono (watermark :: nat \<Rightarrow> rank) \<and> (\<forall>i\<in>fences. watermark i < watermark (Suc i))"

lemma no_fenced_progress_between_equal_samples:
  assumes observed: "fenced_progress_observation watermark fences"
    and endpoints: "watermark i = watermark j"
  shows "fences \<inter> {i..<j} = {}"
proof (rule equals0I)
  fix k
  assume "k \<in> fences \<inter> {i..<j}"
  with observed have mono: "mono watermark" and step: "watermark k < watermark (Suc k)"
    and bounds: "i \<le> k" "Suc k \<le> j" by (auto simp: fenced_progress_observation_def)
  from monoD[OF mono bounds(1)] step monoD[OF mono bounds(2)] endpoints show False by order
qed

theorem live_report_with_fenced_observation_certifies_interval:
  assumes valid: "stateless_report_valid threshold now view r"
    and source: "fenced_progress_observation watermark fences"
    and fidelity:
      "watermark (sf_sample_time (sf_before r)) = sf_sample_rank (sf_before r)"
      "watermark (sf_sample_time (sf_after r)) = sf_sample_rank (sf_after r)"
  shows "fences \<inter> {sf_sample_time (sf_before r)..<sf_sample_time (sf_after r)} = {}"
  by (rule no_fenced_progress_between_equal_samples[OF source])
    (use valid fidelity in \<open>simp add: stateless_report_valid_def\<close>)

lemma application_lag_cannot_diagnose_fenced_stall:
  defines "no_fence \<equiv> (\<lambda>i::nat. rank_zero::rank)"
    and "progress \<equiv> (\<lambda>i::nat. if i = 0 then rank_zero else \<lparr>rank_term = 1, rank_version = 1\<rparr>::rank)"
    and "applied \<equiv> (\<lambda>i::nat. rank_zero::rank)"
  shows "fenced_progress_observation no_fence {}"
    "fenced_progress_observation progress {0}"
    "\<forall>i. applied i \<le> no_fence i \<and> applied i \<le> progress i"
    "applied 0 = applied 1 \<and> progress 0 < progress 1"
  by (auto simp: fenced_progress_observation_def mono_def no_fence_def progress_def applied_def rank_le_iff rank_less_iff)

end
