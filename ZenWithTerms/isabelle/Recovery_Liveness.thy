theory Recovery_Liveness
  imports Bounded_Service Dynamic_Configuration
begin

section \<open>Detector observations and Coordinator effects\<close>

datatype publication_phase = No_Publication | Before_Quorum | After_Quorum
datatype detector_signal =
    Leader_Failure
  | Follower_Failure node
  | Follower_Lag node
  | Publication_Deadline rank

record detector_view =
  callback_executor_available :: bool
  coordinator_mutex_free :: bool
  reporting_leader :: bool
  prevote_incumbent :: "node option"
  local_term :: nat
  local_phase :: publication_phase
  local_slot :: "rank option"
  local_targets_terminal :: bool
  local_self_reply :: bool
  local_applied :: bool
  queued_removals :: "node set"

definition can_dispatch where
  "can_dispatch s \<longleftrightarrow> callback_executor_available s \<and> coordinator_mutex_free s"

definition local_completion_enabled where
  "local_completion_enabled s \<longleftrightarrow> can_dispatch s \<and> local_phase s = After_Quorum
    \<and> local_targets_terminal s \<and> local_self_reply s \<and> local_applied s"

definition enqueue_removal where
  "enqueue_removal n s =
    (if can_dispatch s \<and> reporting_leader s then s\<lparr>queued_removals := insert n (queued_removals s)\<rparr> else s)"

fun dispatch_signal where
  "dispatch_signal Leader_Failure s =
    (if can_dispatch s then s\<lparr>reporting_leader := False, prevote_incumbent := None\<rparr> else s)"
| "dispatch_signal (Follower_Failure n) s = enqueue_removal n s"
| "dispatch_signal (Follower_Lag n) s = enqueue_removal n s"
| "dispatch_signal (Publication_Deadline k) s =
    (if can_dispatch s \<and> local_slot s = Some k then
      case local_phase s of
        No_Publication \<Rightarrow> s
      | Before_Quorum \<Rightarrow> s\<lparr>local_slot := None, local_phase := No_Publication,
          prevote_incumbent := (if reporting_leader s \<and> rank_term k = local_term s then None else prevote_incumbent s),
          reporting_leader := reporting_leader s \<and> rank_term k \<noteq> local_term s\<rparr>
      | After_Quorum \<Rightarrow> s\<lparr>local_targets_terminal := True\<rparr>
     else s)"

definition complete_local_publication where
  "complete_local_publication s =
    (if local_completion_enabled s then s\<lparr>local_phase := No_Publication, local_slot := None\<rparr> else s)"

text \<open>
  This projection starts with an emitted, correctly scoped detector callback.
  LeaderChecker's delivered callback permits candidate activity; other changes
  made by becomeCandidate are outside its detector projection. FollowersChecker
  and LagDetector call removeNode, which can enqueue a NodeLeft task. Committing
  that task still requires ordinary publication. The publication deadline is
  modeled only when a timer exists. Executor service means the relevant callback
  path can run to completion after acquiring the mutex. The deadline must still
  identify the active publication.

  Before quorum, cancellation fails the targets and clears the slot through
  the failed local response. After quorum, it can end the wait for targets.
  Successful slot release requires the self response and local application.
  A callback for another slot leaves the current slot untouched.
\<close>

lemma blocked_callback_stutters:
  "\<not> can_dispatch s \<Longrightarrow> dispatch_signal e s = s"
  by (cases e) (simp_all add: enqueue_removal_def)

lemma leader_report_removes_prevote_observation:
  assumes "can_dispatch s"
  shows "prevote_incumbent (dispatch_signal Leader_Failure s) = None"
    "\<not> reporting_leader (dispatch_signal Leader_Failure s)"
  using assms by simp_all

lemma follower_report_only_queues:
  assumes "can_dispatch s" "reporting_leader s"
  shows "dispatch_signal (Follower_Failure n) s = s\<lparr>queued_removals := insert n (queued_removals s)\<rparr>"
    "dispatch_signal (Follower_Lag n) s = s\<lparr>queued_removals := insert n (queued_removals s)\<rparr>"
  using assms by (simp_all add: enqueue_removal_def)

lemma current_precommit_deadline_releases_and_steps_down:
  assumes "can_dispatch s" "local_slot s = Some k" "local_phase s = Before_Quorum" "rank_term k = local_term s"
  shows "local_slot (dispatch_signal (Publication_Deadline k) s) = None"
    "\<not> reporting_leader (dispatch_signal (Publication_Deadline k) s)"
  using assms by simp_all

lemma deadline_for_old_slot_stutters:
  "local_slot s \<noteq> Some k \<Longrightarrow> dispatch_signal (Publication_Deadline k) s = s"
  by simp

lemma postquorum_deadline_still_needs_local_completion:
  assumes "can_dispatch s" "local_slot s = Some k" "local_phase s = After_Quorum"
  defines "s' \<equiv> dispatch_signal (Publication_Deadline k) s"
  shows "local_slot s' = Some k"
    "local_completion_enabled s' \<longleftrightarrow> local_self_reply s \<and> local_applied s"
proof -
  have update: "s' = s\<lparr>local_targets_terminal := True\<rparr>"
    unfolding s'_def using assms(1-3) by simp
  show "local_slot s' = Some k" using assms(2) unfolding update by simp
  show "local_completion_enabled s' \<longleftrightarrow> local_self_reply s \<and> local_applied s"
    using assms(1,3) unfolding update local_completion_enabled_def can_dispatch_def by simp
qed

lemma successful_slot_release_needs_application:
  "\<not> local_self_reply s \<or> \<not> local_applied s \<Longrightarrow> complete_local_publication s = s"
  by (auto simp: complete_local_publication_def local_completion_enabled_def)

section \<open>A stalled incumbent can keep answering checks\<close>

definition leader_check_replies where
  "leader_check_replies s health known = (reporting_leader s \<and> health \<and> known)"

definition ordinary_prevote where
  "ordinary_prevote candidate remembered = (remembered = None \<or> remembered = Some candidate)"

definition frozen_incumbent where
  "frozen_incumbent incumbent k = \<lparr>callback_executor_available = True, coordinator_mutex_free = False,
    reporting_leader = True, prevote_incumbent = Some incumbent, local_term = rank_term k, local_phase = Before_Quorum, local_slot = Some k,
    local_targets_terminal = False, local_self_reply = False, local_applied = False, queued_removals = {}\<rparr>"

fun stalled_trace where
  "stalled_trace incumbent k 0 = frozen_incumbent incumbent k"
| "stalled_trace incumbent k (Suc n) = dispatch_signal (Publication_Deadline k) (stalled_trace incumbent k n)"

theorem stalled_write_trace_keeps_leader_checks_alive:
  assumes "candidate \<noteq> incumbent"
  shows "stalled_trace incumbent k n = frozen_incumbent incumbent k"
    "leader_check_replies (stalled_trace incumbent k n) True True"
    "local_phase (stalled_trace incumbent k n) = Before_Quorum"
    "local_slot (stalled_trace incumbent k n) = Some k"
    "\<not> ordinary_prevote candidate (Some incumbent)"
proof -
  show eq: "stalled_trace incumbent k n = frozen_incumbent incumbent k"
    by (induction n) (simp_all add: can_dispatch_def frozen_incumbent_def)
  show "leader_check_replies (stalled_trace incumbent k n) True True"
    "local_phase (stalled_trace incumbent k n) = Before_Quorum"
    "local_slot (stalled_trace incumbent k n) = Some k"
    "\<not> ordinary_prevote candidate (Some incumbent)"
    using eq assms by (simp_all add: frozen_incumbent_def leader_check_replies_def ordinary_prevote_def)
qed

text \<open>
  This is a persistent blocked state of the callback projection. Repeated
  deadline service in the trace denotes repeated observation of the same
  pending callback, without mutex entry. A single pending deadline suffices.
  Coordinator.handlePublishRequest holds its mutex across the durable setter.
  The deadline and the state-changing response path need that mutex.
  LeaderChecker.handleLeaderCheck runs on the direct handler and can use the
  last completed filesystem health result. Given no disconnect or health
  failure, a healthy alternative quorum may still remember the incumbent.
  The witness does not depend on a particular cluster size.
\<close>

section \<open>Policy evidence for an attempt\<close>

record replacement_round =
  replaced_leader :: node
  replacement_candidate :: node
  incumbent_term :: nat
  request_generation :: nat
  committed_voters :: config
  accepted_voters :: config

record replacement_report =
  reporting_voter :: node
  reported_round :: replacement_round
  expires :: nat

definition report_valid where
  "report_valid r generation now p \<longleftrightarrow>
    request_generation r = generation \<and> reported_round p = r \<and> now < expires p"

definition alternative_authority where
  "alternative_authority r generation now reports healthy Q \<longleftrightarrow>
    replacement_candidate r \<noteq> replaced_leader r \<and> replacement_candidate r \<in> healthy
    \<and> replaced_leader r \<notin> Q \<and> Q \<subseteq> healthy
    \<and> quorum (committed_voters r) Q \<and> quorum (accepted_voters r) Q
    \<and> (\<forall>n\<in>Q. \<exists>p\<in>reports. reporting_voter p = n \<and> report_valid r generation now p)"

datatype attempt_policy = Current_Checks | Quorum_Backed

fun can_open_attempt where
  "can_open_attempt Current_Checks r generation now reports healthy Q remembered =
    (replacement_candidate r \<in> healthy \<and> Q \<subseteq> healthy
       \<and> quorum (committed_voters r) Q \<and> quorum (accepted_voters r) Q
       \<and> (\<forall>n\<in>Q. ordinary_prevote (replacement_candidate r) (remembered n)))"
| "can_open_attempt Quorum_Backed r generation now reports healthy Q remembered =
    alternative_authority r generation now reports healthy Q"

text \<open>
  An alternative report is an authenticated affirmative observation of
  unavailability on the incumbent's progress path, addressed to a named
  replacement round. The report identifies the incumbent, term, candidate,
  generation and both voting configurations. A caller supplies the live
  round and its clock. Generations prevent using evidence from a previous
  attempt with the same leader and term. Neither the report collection nor its
  application should wait for the incumbent to take its Coordinator mutex.

  The proposed policy uses the certificate to let the replacement enter
  candidate mode and request pre-votes despite the incumbent still being
  remembered at the voters. Ordinary election eligibility, freshness, votes,
  and publication remain separate. This is a proposed policy interface.
  Production does not implement this override.
\<close>

lemma authority_requires_live_reports:
  assumes "alternative_authority r generation now reports healthy Q" "n \<in> Q"
  obtains p where "p \<in> reports" "reporting_voter p = n"
    "reported_round p = r" "request_generation r = generation" "now < expires p"
  using assms unfolding alternative_authority_def report_valid_def by blast

lemma quorum_backed_permits_attempt_despite_incumbent:
  assumes auth: "alternative_authority r generation now reports healthy Q"
  shows "can_open_attempt Quorum_Backed r generation now reports healthy Q (\<lambda>_. Some (replaced_leader r))"
  using auth by simp

lemma current_checks_need_prevote_permission:
  assumes "replacement_candidate r \<noteq> replaced_leader r"
    "n \<in> Q" "remembered n = Some (replaced_leader r)"
  shows "\<not> can_open_attempt Current_Checks r generation now reports healthy Q remembered"
  using assms by (auto simp: ordinary_prevote_def)

theorem stalled_write_blocks_current_replacement:
  assumes distinct: "replacement_candidate r \<noteq> replaced_leader r"
  shows "leader_check_replies (stalled_trace (replaced_leader r) k n) True True"
    "\<not> can_open_attempt Current_Checks r generation now reports healthy Q (\<lambda>_. Some (replaced_leader r))"
proof -
  show "leader_check_replies (stalled_trace (replaced_leader r) k n) True True"
    by (rule stalled_write_trace_keeps_leader_checks_alive(2)[OF distinct])
  show "\<not> can_open_attempt Current_Checks r generation now reports healthy Q (\<lambda>_. Some (replaced_leader r))"
  proof
    assume current: "can_open_attempt Current_Checks r generation now reports healthy Q (\<lambda>_. Some (replaced_leader r))"
    then have quorum: "quorum (committed_voters r) Q" by simp
    then obtain n where "n \<in> Q" using quorum_intersects[OF quorum quorum] by blast
    with current distinct show False by (auto simp: ordinary_prevote_def)
  qed
qed

lemma delivered_leader_failures_open_attempt:
  assumes healthy: "replacement_candidate r \<in> healthy" "Q \<subseteq> healthy"
    and quorum: "quorum (committed_voters r) Q" "quorum (accepted_voters r) Q"
    and dispatched: "\<And>n. n \<in> Q \<Longrightarrow> can_dispatch (views n)"
  shows "can_open_attempt Current_Checks r generation now reports healthy Q
    (\<lambda>n. prevote_incumbent (dispatch_signal Leader_Failure (views n)))"
  using healthy quorum dispatched by (auto simp: ordinary_prevote_def)

definition approval_reports where
  "approval_reports r expiry voters =
    (\<lambda>n. \<lparr>reporting_voter = n, reported_round = r, expires = expiry n\<rparr>) ` voters"

lemma alternative_reports_service:
  assumes service: "bounded_service Q (\<lambda>_. {}) select delay horizon" "delay \<le> horizon"
    and healthy: "replacement_candidate r \<in> healthy" "Q \<subseteq> healthy"
    and replacement: "replacement_candidate r \<noteq> replaced_leader r" "replaced_leader r \<notin> Q"
    and quorum: "quorum (committed_voters r) Q" "quorum (accepted_voters r) Q"
    and valid: "request_generation r = generation" "\<And>n. n \<in> Q \<Longrightarrow> start + delay \<le> now \<and> now < expiry n"
  shows "alternative_authority r generation now
    (approval_reports r expiry (completed_work Q (\<lambda>_. {}) select delay)) healthy Q"
proof -
  have "0 + delay \<le> horizon" using service(2) by simp
  from bounded_service_finishes_group[OF service(1) this, where batch=Q]
  have all: "Q \<subseteq> completed_work Q (\<lambda>_. {}) select delay" by simp
  have "\<exists>p\<in>approval_reports r expiry (completed_work Q (\<lambda>_. {}) select delay).
    reporting_voter p = n \<and> report_valid r generation now p" if "n \<in> Q" for n
    using that all valid
    by (intro bexI[of _ "\<lparr>reporting_voter = n, reported_round = r, expires = expiry n\<rparr>"])
      (auto simp: approval_reports_def report_valid_def)
  with healthy replacement quorum show ?thesis unfolding alternative_authority_def by blast
qed

section \<open>Service of recovery and retries\<close>

datatype recovery_job = Run_Discovery | Deliver_Pre_Vote node | Begin_Replacement

definition recovery_jobs where
  "recovery_jobs Q = insert Run_Discovery (insert Begin_Replacement (Deliver_Pre_Vote ` Q))"

fun recovery_dependencies where
  "recovery_dependencies Q Run_Discovery = {}"
| "recovery_dependencies Q (Deliver_Pre_Vote n) = {Run_Discovery}"
| "recovery_dependencies Q Begin_Replacement = insert Run_Discovery (Deliver_Pre_Vote ` Q)"

abbreviation recovery_done where
  "recovery_done Q select i \<equiv> completed_work (recovery_jobs Q) (recovery_dependencies Q) select i"

theorem serviced_recovery_starts_attempt:
  assumes service: "bounded_service (recovery_jobs Q) (recovery_dependencies Q) select delay horizon"
    and time: "3 * delay \<le> horizon"
  shows "Begin_Replacement \<in> recovery_done Q select (3 * delay)"
proof -
  have bounds: "0 + delay \<le> horizon" "delay + delay \<le> horizon"
    "(delay + delay) + delay \<le> horizon" using time by linarith+
  have discovery: "Run_Discovery \<in> recovery_done Q select (0 + delay)"
    using bounded_service_finishes_group[OF service bounds(1), where batch="{Run_Discovery}"]
    by (simp add: recovery_jobs_def)
  have voted: "Deliver_Pre_Vote ` Q \<subseteq> recovery_done Q select (delay + delay)"
    by (rule bounded_service_finishes_group[OF service bounds(2)])
      (use discovery in \<open>auto simp: recovery_jobs_def\<close>)
  have grows: "recovery_done Q select (0 + delay) \<subseteq> recovery_done Q select (delay + delay)"
    by (rule completed_work_mono) simp
  have seen: "Run_Discovery \<in> recovery_done Q select (delay + delay)"
    by (rule subsetD[OF grows discovery])
  have "Begin_Replacement \<in> recovery_done Q select ((delay + delay) + delay)"
    using bounded_service_finishes_group[OF service bounds(3), where batch="{Begin_Replacement}"]
      voted seen by (simp add: recovery_jobs_def)
  then show ?thesis by (simp add: numeral_eq_Suc algebra_simps)
qed

record recovery_episode =
  episode_policy :: attempt_policy
  episode_round :: replacement_round
  episode_generation :: nat
  episode_reports :: "replacement_report set"
  episode_healthy :: "node set"
  episode_quorum :: "node set"
  episode_eligible :: bool
  episode_fresh_enough :: "node set"
  episode_remembered :: "node \<Rightarrow> node option"
  episode_schedule :: "nat \<Rightarrow> recovery_job option"
  episode_delay :: nat

definition episode_permission where
  "episode_permission start e \<longleftrightarrow>
    episode_eligible e \<and> episode_quorum e \<subseteq> episode_fresh_enough e \<and>
    can_open_attempt (episode_policy e) (episode_round e) (episode_generation e)
      (start + 3 * episode_delay e) (episode_reports e) (episode_healthy e) (episode_quorum e) (episode_remembered e)"

definition episode_service where
  "episode_service e \<longleftrightarrow>
    bounded_service (recovery_jobs (episode_quorum e)) (recovery_dependencies (episode_quorum e))
      (episode_schedule e) (episode_delay e) (3 * episode_delay e)"

definition opens_attempt_at where
  "opens_attempt_at start e k \<longleftrightarrow>
    episode_permission start e \<and>
    (\<exists>j. k = start + Suc j \<and> Suc j \<le> 3 * episode_delay e
      \<and> Begin_Replacement \<notin> recovery_done (episode_quorum e) (episode_schedule e) j
      \<and> Begin_Replacement \<in> recovery_done (episode_quorum e) (episode_schedule e) (Suc j))"

lemma serviced_episode_opens_attempt:
  assumes permission: "episode_permission start e" and service: "episode_service e"
  shows "\<exists>k>start. k \<le> start + 3 * episode_delay e \<and> opens_attempt_at start e k"
proof -
  let ?done = "\<lambda>j. Begin_Replacement \<in> recovery_done (episode_quorum e) (episode_schedule e) j"
  have bounded: "bounded_service (recovery_jobs (episode_quorum e)) (recovery_dependencies (episode_quorum e))
      (episode_schedule e) (episode_delay e) (3 * episode_delay e)"
    using service unfolding episode_service_def .
  have at_deadline: "?done (3 * episode_delay e)"
    by (rule serviced_recovery_starts_attempt[OF bounded]) simp
  let ?m = "Least ?done"
  have exists: "\<exists>j. ?done j" using at_deadline by blast
  have first: "?done ?m" by (rule LeastI_ex[OF exists])
  have within: "?m \<le> 3 * episode_delay e" by (rule Least_le) (rule at_deadline)
  obtain j where tick: "?m = Suc j" using first by (cases ?m) auto
  have earlier: "\<not> ?done j"
  proof
    assume "?done j"
    then have "?m \<le> j" by (rule Least_le)
    with tick show False by simp
  qed
  have step: "Suc j \<le> 3 * episode_delay e" using within tick by simp
  have opened: "opens_attempt_at start e (start + Suc j)"
    unfolding opens_attempt_at_def using permission step earlier first tick
    by (intro conjI exI[of _ j]) simp_all
  show ?thesis by (intro exI[of _ "start + Suc j"]) (use step opened in simp)
qed

text \<open>
  One serviced episode starts after the controls which allow discovery have
  been processed. Its pre-vote and attempt jobs stand for successful handling
  along the healthy path, subject to a fixed round, eligible candidate and
  fresh votes throughout this episode. The window horizon must fit within
  the lifetime of the evidence and any conflicting action must be absent.
  Bounds are on service of enabled work, including callback dispatch.

  Retry availability is a separate premise: if the cluster remains stalled,
  a later episode can get the policy permission and service again. For the
  current policy, this depends on removing blocking incumbent observations.
  For the proposed policy it depends on timely independent evidence.
\<close>

theorem persistent_stall_has_recurring_attempts:
  fixes commits :: "nat set" and episodes :: "nat \<Rightarrow> recovery_episode"
  assumes retry: "\<And>i. (\<And>j. i \<le> j \<Longrightarrow> j \<notin> commits) \<Longrightarrow>
      \<exists>start\<ge>i. episode_permission start (episodes start) \<and> episode_service (episodes start)"
  shows "\<exists>j\<ge>i. j \<in> commits \<or> (\<exists>start\<ge>i. opens_attempt_at start (episodes start) j)"
proof (cases "\<exists>j\<ge>i. j \<in> commits")
  case True
  then show ?thesis by blast
next
  case False
  have no_commit: "i \<le> j \<Longrightarrow> j \<notin> commits" for j using False by blast
  from retry[OF no_commit] obtain start where
    start: "i \<le> start" and permit: "episode_permission start (episodes start)"
    and service: "episode_service (episodes start)" by blast
  from serviced_episode_opens_attempt[OF permit service] obtain k where
    finish: "start < k" "opens_attempt_at start (episodes start) k" by blast
  have "i \<le> k" by (rule order_trans[OF start less_imp_le[OF finish(1)]])
  with start finish(2) show ?thesis by blast
qed

corollary retry_opportunities_are_unbounded:
  fixes commits :: "nat set" and episodes :: "nat \<Rightarrow> recovery_episode"
  assumes retry: "\<And>i. (\<And>j. i \<le> j \<Longrightarrow> j \<notin> commits) \<Longrightarrow>
       \<exists>start\<ge>i. episode_permission start (episodes start) \<and> episode_service (episodes start)"
    and stalled: "\<And>j. i \<le> j \<Longrightarrow> j \<notin> commits"
    and after: "i \<le> j"
  shows "\<exists>k>j. \<exists>start>j. opens_attempt_at start (episodes start) k"
proof -
  have no_commit: "k \<notin> commits" if "Suc j \<le> k" for k
    by (rule stalled) (use that after in linarith)
  from persistent_stall_has_recurring_attempts[where i="Suc j" and commits=commits and episodes=episodes, OF retry] no_commit
  show ?thesis by (auto simp: Suc_le_eq)
qed

end
