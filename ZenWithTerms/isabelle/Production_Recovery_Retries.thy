theory Production_Recovery_Retries
  imports Recovery_Liveness
begin

section \<open>From detector callbacks to an open pre-vote path\<close>

definition views_after_leader_failures where
  "views_after_leader_failures failed views =
    (\<lambda>n. if n \<in> failed then dispatch_signal Leader_Failure (views n) else views n)"

definition candidates_after_leader_failures where
  "candidates_after_leader_failures failed views prior = prior \<union> {n\<in>failed. can_dispatch (views n)}"

lemma serviced_leader_failure_opens_discovery:
  assumes "can_dispatch (views c)" "c \<in> failed"
  shows "\<not> reporting_leader (views_after_leader_failures failed views c)"
    "prevote_incumbent (views_after_leader_failures failed views c) = None"
    "c \<in> candidates_after_leader_failures failed views prior"
  using assms by (simp_all add: views_after_leader_failures_def candidates_after_leader_failures_def)

lemma partial_leader_failures_open_prevote_quorum:
  assumes healthy: "replacement_candidate r \<in> healthy" "Q \<subseteq> healthy"
    and quorum: "quorum (committed_voters r) Q" "quorum (accepted_voters r) Q"
    and delivered: "\<And>n. n \<in> Q \<inter> failed \<Longrightarrow> can_dispatch (views n)"
    and other: "\<And>n. n \<in> Q - failed \<Longrightarrow>
      ordinary_prevote (replacement_candidate r) (prevote_incumbent (views n))"
  shows "can_open_attempt Current_Checks r generation now reports healthy Q
    (prevote_incumbent \<circ> views_after_leader_failures failed views)"
proof -
  have "ordinary_prevote (replacement_candidate r) (prevote_incumbent (views_after_leader_failures failed views n))"
    if "n \<in> Q" for n
  proof (cases "n \<in> failed")
    case True
    with delivered that show ?thesis by (simp add: views_after_leader_failures_def ordinary_prevote_def)
  next
    case False
    with other[of n] that show ?thesis by (simp add: views_after_leader_failures_def)
  qed
  with healthy quorum show ?thesis by auto
qed

lemma serviced_leader_failure_batch:
  assumes service: "bounded_service failed (\<lambda>_. {}) select delay horizon" "delay \<le> horizon"
  shows "completed_work failed (\<lambda>_. {}) select delay = failed"
proof (rule equalityI)
  show "completed_work failed (\<lambda>_. {}) select delay \<subseteq> failed"
    using ordered_completed_work[of failed "\<lambda>_. {}" select delay] unfolding ordered_work_def by blast
  have "0 + delay \<le> horizon" using service(2) by simp
  from bounded_service_finishes_group[OF service(1) this, where batch=failed]
  show "failed \<subseteq> completed_work failed (\<lambda>_. {}) select delay" by simp
qed

text \<open>
  The detector callbacks in the batch are already emitted and refer to
  the incumbent being replaced. A completed job means that the follower
  executor dispatched its callback and the Coordinator acquired its
  mutex and finished becomeCandidate. The Java method activates peer
  discovery for a new candidate and refreshes the pre-vote collector
  with no leader. The projection of the callback records the latter
  effect. It uses the former effect when arming the first timer.

  A failure at one node is sufficient for that node's mode transition.
  Other voters may already permit the candidate, or need their own
  callbacks. Follower and lag reports only enqueue work and are not
  substitutes for the leader failure callbacks here. The code path
  that generates leader failure notifications still depends on its
  health checks and transport. In particular, the stalled-write
  counterexample need not emit any such notification.
\<close>

section \<open>An open scheduler re-arms before its pre-vote round\<close>

definition arming_condition where
  "arming_condition r candidates eligible known \<longleftrightarrow>
    replacement_candidate r \<in> candidates \<and> replacement_candidate r \<in> eligible
    \<and> quorum (committed_voters r) (insert (replacement_candidate r) known)
    \<and> quorum (accepted_voters r) (insert (replacement_candidate r) known)"

lemma candidate_with_visible_quorum_can_arm:
  assumes failure: "replacement_candidate r \<in> failed" "can_dispatch (views (replacement_candidate r))"
    and eligible: "replacement_candidate r \<in> eligible"
    and quorum: "quorum (committed_voters r) (insert (replacement_candidate r) known)"
      "quorum (accepted_voters r) (insert (replacement_candidate r) known)"
  shows "arming_condition r (candidates_after_leader_failures failed views prior) eligible known"
  using failure eligible quorum
  unfolding arming_condition_def candidates_after_leader_failures_def by blast

record retry_wakeup =
  retry_due :: nat
  retry_handled :: nat

definition rearmed_wakeup where
  "rearmed_wakeup duration jitter before after \<longleftrightarrow>
    retry_due before \<le> retry_handled before \<and> 0 < jitter
    \<and> retry_due after = retry_handled before + duration + jitter
    \<and> retry_due after \<le> retry_handled after"

fun election_wakeup_times where
  "election_wakeup_times first duration jitter dispatch_lag 0 = first"
| "election_wakeup_times first duration jitter dispatch_lag (Suc i) =
    election_wakeup_times first duration jitter dispatch_lag i + duration + jitter i + dispatch_lag i"

lemma election_wakeup_rearms:
  fixes first duration :: nat and jitter dispatch_lag :: "nat \<Rightarrow> nat"
  assumes positive: "0 < jitter i"
  defines "clock \<equiv> election_wakeup_times first duration jitter dispatch_lag"
  shows "rearmed_wakeup duration (jitter i)
    \<lparr>retry_due = clock i, retry_handled = clock i\<rparr>
    \<lparr>retry_due = clock i + duration + jitter i, retry_handled = clock (Suc i)\<rparr>"
  unfolding rearmed_wakeup_def clock_def using positive by simp

lemma election_wakeup_times_unbounded:
  assumes jitter: "\<And>i. 0 < jitter i"
  shows "i \<le> election_wakeup_times first duration jitter dispatch_lag i"
proof (induction i)
  case 0
  show ?case by simp
next
  case (Suc i)
  from Suc.IH jitter[of i] show ?case by simp
qed

text \<open>
  CoordinatorPeerFinder's serviced peer update arms an election scheduler
  for a master-eligible candidate with a discovered election quorum.
  The scheduler's open wakeup re-arms a successor using its duration
  and a fresh positive bounded jitter before invoking the runnable.
  No acknowledgement from this round is required by that scheduling
  call. Cluster shutdown, loss of the discovered quorum, a new leader,
  or a cancelled scheduler can prevent later wakes. The following timing
  recurrence is for an open scheduler and successful dispatch. The first
  time includes service of the initial peer update and first timer. Each
  additional dispatch lag is finite. The separate timing analysis can
  constrain these lags and the legal jitter ranges further.
\<close>

section \<open>Policy evidence and bounded service at successive wakeups\<close>

definition retry_episode where
  "retry_episode policy r healthy Q eligible candidate_key voter_keys remembered reports select delay =
    \<lparr>episode_policy = policy, episode_round = r, episode_generation = request_generation r,
      episode_reports = reports, episode_healthy = healthy, episode_quorum = Q,
      episode_eligible = eligible, episode_fresh_enough = {n. voter_keys n \<le> (candidate_key :: rank)}, episode_remembered = remembered,
      episode_schedule = select, episode_delay = delay\<rparr>"

lemma permitted_wakeup_starts_attempt:
  assumes permit: "can_open_attempt policy r (request_generation r) (start + 3 * delay)
      reports healthy Q remembered"
    and service: "bounded_service (recovery_jobs Q) (recovery_dependencies Q) select delay (3 * delay)"
    and eligible: "eligible"
    and fresh: "\<And>n. n \<in> Q \<Longrightarrow> voter_keys n \<le> candidate_key"
  shows "\<exists>k>start. k \<le> start + 3 * delay \<and>
     opens_attempt_at start (retry_episode policy r healthy Q eligible candidate_key voter_keys remembered reports select delay) k"
proof -
  let ?e = "retry_episode policy r healthy Q eligible candidate_key voter_keys remembered reports select delay"
  have p: "episode_permission start ?e" using permit eligible fresh by (auto simp: retry_episode_def episode_permission_def)
  have s: "episode_service ?e" using service by (simp add: retry_episode_def episode_service_def)
  from serviced_episode_opens_attempt[OF p s] show ?thesis by (simp add: retry_episode_def)
qed

theorem current_checker_wakeups_retry:
  fixes r :: replacement_round and Q :: "node set"
    and first duration :: nat and jitter dispatch_lag :: "nat \<Rightarrow> nat"
    and failed :: "node set" and views :: "node \<Rightarrow> detector_view"
    and detector_select :: "nat \<Rightarrow> node option" and detector_delay :: nat
    and handled :: "node set"
  defines "clock \<equiv> election_wakeup_times first duration jitter dispatch_lag"
    and "handled \<equiv> completed_work failed (\<lambda>_. {}) detector_select detector_delay"
    and "remembered \<equiv> prevote_incumbent \<circ> views_after_leader_failures handled views"
  assumes health: "replacement_candidate r \<in> healthy" "Q \<subseteq> healthy"
    and quorum: "quorum (committed_voters r) Q" "quorum (accepted_voters r) Q"
    and detector_service: "bounded_service failed (\<lambda>_. {}) detector_select detector_delay detector_horizon"
      "detector_delay \<le> detector_horizon"
    and entry: "replacement_candidate r \<in> failed" "can_dispatch (views (replacement_candidate r))"
      "replacement_candidate r \<in> eligible_nodes"
    and visible: "quorum (committed_voters r) (insert (replacement_candidate r) known)"
      "quorum (accepted_voters r) (insert (replacement_candidate r) known)"
    and reported: "\<And>n. n \<in> Q \<inter> failed \<Longrightarrow> can_dispatch (views n)"
    and already: "\<And>n. n \<in> Q - failed \<Longrightarrow>
      ordinary_prevote (replacement_candidate r) (prevote_incumbent (views n))"
    and jitter: "\<And>i. 0 < jitter i"
    and service: "\<And>i. bounded_service (recovery_jobs Q) (recovery_dependencies Q) (select i) delay (3 * delay)"
    and eligible: "\<And>i. eligible i"
    and fresh: "\<And>i n. n \<in> Q \<Longrightarrow> voter_keys i n \<le> candidate_key i"
    and fits: "\<And>i. 3 * delay < duration + jitter i"
  shows "arming_condition r (candidates_after_leader_failures handled views prior) eligible_nodes known"
    "\<exists>k>after. \<exists>i. k < clock (Suc i) \<and>
     opens_attempt_at (clock i) (retry_episode Current_Checks r healthy Q
       (eligible i) (candidate_key i) (voter_keys i) remembered {} (select i) delay) k"
proof -
  have handled: "handled = failed" unfolding handled_def by (rule serviced_leader_failure_batch[OF detector_service])
  show "arming_condition r (candidates_after_leader_failures handled views prior) eligible_nodes known"
    unfolding handled by (rule candidate_with_visible_quorum_can_arm) (rule entry, rule entry, rule entry, rule visible, rule visible)
  have permit: "can_open_attempt Current_Checks r (request_generation r) (clock after + 3 * delay)
    {} healthy Q remembered"
    unfolding remembered_def handled by (rule partial_leader_failures_open_prevote_quorum[OF health quorum reported already])
  let ?e = "retry_episode Current_Checks r healthy Q
       (eligible after) (candidate_key after) (voter_keys after) remembered {} (select after) delay"
  have "\<exists>k>clock after. k \<le> clock after + 3 * delay \<and> opens_attempt_at (clock after) ?e k"
    by (rule permitted_wakeup_starts_attempt[OF permit service[of after] eligible[of after]]) (rule fresh)
  then obtain k where begun: "clock after < k" "k \<le> clock after + 3 * delay"
    "opens_attempt_at (clock after) (retry_episode Current_Checks r healthy Q
       (eligible after) (candidate_key after) (voter_keys after) remembered {} (select after) delay) k"
    by blast
  have "after \<le> clock after" unfolding clock_def by (rule election_wakeup_times_unbounded[OF jitter])
  with begun(1) have later: "after < k" by linarith
  have "k < clock (Suc after)" using begun(2) fits[of after] unfolding clock_def by simp
  with begun(3) later show "\<exists>k>after. \<exists>i. k < clock (Suc i) \<and>
     opens_attempt_at (clock i) (retry_episode Current_Checks r healthy Q
       (eligible i) (candidate_key i) (voter_keys i) remembered {} (select i) delay) k" by blast
qed

definition served_reports where
  "served_reports Q r expiry report_select report_delay =
    approval_reports r expiry (completed_work Q (\<lambda>_. {}) report_select report_delay)"

record progress_observation =
  observed_master :: node
  observed_term :: nat
  observed_committed :: rank
  observed_pending_work :: bool
  observed_at :: nat

definition observes_stalled_publication where
  "observes_stalled_publication r threshold before after \<longleftrightarrow>
    0 < threshold \<and> observed_at before + threshold \<le> observed_at after
    \<and> observed_master before = replaced_leader r \<and> observed_master after = replaced_leader r
    \<and> observed_term before = incumbent_term r \<and> observed_term after = incumbent_term r
    \<and> observed_pending_work before \<and> observed_pending_work after
    \<and> observed_committed before = observed_committed after"

definition independent_report_jobs where
  "independent_report_jobs r threshold report_start voters before after local_service =
    {n\<in>voters. observes_stalled_publication r threshold (before n) (after n)
      \<and> observed_at (after n) \<le> report_start \<and> can_dispatch (local_service n)}"

lemma independently_serviced_observations_cover_voters:
  assumes observed: "\<And>n. n \<in> Q \<Longrightarrow>
      observes_stalled_publication r threshold (before n) (after n)"
    and clock: "\<And>n. n \<in> Q \<Longrightarrow> observed_at (after n) \<le> report_start"
    and local: "\<And>n. n \<in> Q \<Longrightarrow> can_dispatch (local_service n)"
  shows "independent_report_jobs r threshold report_start Q before after local_service = Q"
  using assms unfolding independent_report_jobs_def by blast

lemma independent_reports_open_attempt:
  assumes service: "bounded_service Q (\<lambda>_. {}) report_select report_delay horizon" "report_delay \<le> horizon"
    and health: "replacement_candidate r \<in> healthy" "Q \<subseteq> healthy"
    and alternate: "replacement_candidate r \<noteq> replaced_leader r" "replaced_leader r \<notin> Q"
    and quorum: "quorum (committed_voters r) Q" "quorum (accepted_voters r) Q"
    and live: "\<And>n. n \<in> Q \<Longrightarrow> report_start + report_delay \<le> deadline \<and> deadline < expiry n"
  shows "can_open_attempt Quorum_Backed r (request_generation r) deadline
    (served_reports Q r expiry report_select report_delay) healthy Q remembered"
proof -
  have valid: "request_generation r = request_generation r" by simp
  note auth = alternative_reports_service[OF service health alternate quorum valid live]
  show ?thesis using auth unfolding served_reports_def by simp
qed

text \<open>
  A proposed report job is successful only when the named healthy voter
  independently observes insufficient incumbent progress and signs an
  affirmative report for the round. Its service relies on the voter and
  replacement, with no work on the incumbent's Coordinator executor or
  mutex. The theorem uses this service and each report's expiry to
  construct the authority from scratch on each retry. It assumes an
  independently dispatched mode change and collector override using this
  authority. The model leaves the failure observations and this proposed
  override outside today's Java implementation. Healthy checks from the
  incumbent can continue during these rounds.

  One possible local observation rule samples a committed watermark and
  pending work at two times. A voter can report a stall when the samples
  name the same incumbent and term, show the same watermark and pending
  work, and are separated by a minimum observation interval. Samples
  come from information available to the voter. A healthy direct leader
  check can coexist with those observations. This rule produces grounds
  for an affirmative report; an unseen commit can still make that
  observation stale. The certificate permits only a pre-vote attempt.

  At each wakeup, the service premise covers discovery, the selected
  voters' admissible fresh pre-vote responses, and dispatch of startElection.
  It requires the candidate to remain eligible and healthy, suitable peers
  to remain visible, and no change in round state that prevents these
  operations. The window ends before this scheduler's next wakeup can
  close the pre-vote round. Rival timers and other invalidations are
  subject to the separate quiet-window analysis. Either policy yields
  arbitrarily late attempts when these conditions persist while stalled.
\<close>

theorem quorum_backed_wakeups_retry:
  fixes round :: "nat \<Rightarrow> replacement_round" and Q :: "node set"
    and first duration :: nat and jitter dispatch_lag :: "nat \<Rightarrow> nat"
    and expiry :: "nat \<Rightarrow> node \<Rightarrow> nat"
    and report_select :: "nat \<Rightarrow> nat \<Rightarrow> node option"
    and report_delay :: nat
  defines "clock \<equiv> election_wakeup_times first duration jitter dispatch_lag"
    and "reports \<equiv> (\<lambda>i. served_reports Q (round i) (expiry i) (report_select i) report_delay)"
  assumes leader_health: "\<And>i. replacement_candidate (round i) \<in> healthy"
    and voter_health: "Q \<subseteq> healthy"
    and alternate: "\<And>i. replacement_candidate (round i) \<noteq> replaced_leader (round i)"
      "\<And>i. replaced_leader (round i) \<notin> Q"
    and quorum: "\<And>i. quorum (committed_voters (round i)) Q"
      "\<And>i. quorum (accepted_voters (round i)) Q"
    and jitter: "\<And>i. 0 < jitter i"
    and observed: "\<And>i n. n \<in> Q \<Longrightarrow>
       observes_stalled_publication (round i) observation_interval (earlier i n) (latest i n)"
    and observation_time: "\<And>i n. n \<in> Q \<Longrightarrow> observed_at (latest i n) \<le> clock i"
    and reporter_dispatch: "\<And>i n. n \<in> Q \<Longrightarrow> can_dispatch (reporter i n)"
    and observation: "\<And>i. bounded_service
       (independent_report_jobs (round i) observation_interval (clock i) Q (earlier i) (latest i) (reporter i))
        (\<lambda>_. {}) (report_select i) report_delay report_delay"
    and service: "\<And>i. bounded_service (recovery_jobs Q) (recovery_dependencies Q) (select i) delay (3 * delay)"
    and eligible: "\<And>i. eligible i"
    and fresh: "\<And>i n. n \<in> Q \<Longrightarrow> voter_keys i n \<le> candidate_key i"
    and through: "\<And>i n. n \<in> Q \<Longrightarrow> clock i + report_delay + 3 * delay < expiry i n"
    and fits: "\<And>i. report_delay + 3 * delay < duration + jitter i"
  shows "\<exists>k>after. \<exists>i. k < clock (Suc i) \<and>
     opens_attempt_at (clock i + report_delay)
       (retry_episode Quorum_Backed (round i) healthy Q (eligible i) (candidate_key i) (voter_keys i)
          (\<lambda>_. Some (replaced_leader (round i))) (reports i) (select i) delay) k"
proof -
  let ?i = after
  let ?start = "clock ?i + report_delay"
  let ?remembered = "\<lambda>_. Some (replaced_leader (round ?i))"
  have valid: "clock ?i + report_delay \<le> ?start + 3 * delay \<and> ?start + 3 * delay < expiry ?i n" if "n \<in> Q" for n
    using through[of n ?i, OF that] by simp
  have offered: "independent_report_jobs (round ?i) observation_interval (clock ?i) Q
       (earlier ?i) (latest ?i) (reporter ?i) = Q"
    by (rule independently_serviced_observations_cover_voters[OF observed[of _ ?i] observation_time[of _ ?i] reporter_dispatch[of _ ?i]])
  have report_service: "bounded_service Q (\<lambda>_. {}) (report_select ?i) report_delay report_delay"
    using observation[of ?i] unfolding offered .
  have permit: "can_open_attempt Quorum_Backed (round ?i) (request_generation (round ?i)) (?start + 3 * delay)
    (reports ?i) healthy Q ?remembered"
    unfolding reports_def
    by (rule independent_reports_open_attempt[OF report_service le_refl leader_health[of ?i] voter_health
       alternate[of ?i] quorum[of ?i] valid])
  let ?e = "retry_episode Quorum_Backed (round ?i) healthy Q
      (eligible ?i) (candidate_key ?i) (voter_keys ?i) ?remembered (reports ?i) (select ?i) delay"
  have "\<exists>k>?start. k \<le> ?start + 3 * delay \<and> opens_attempt_at ?start ?e k"
    by (rule permitted_wakeup_starts_attempt[OF permit service[of ?i] eligible[of ?i]]) (rule fresh)
  then obtain k where begun: "?start < k" "k \<le> ?start + 3 * delay"
    "opens_attempt_at ?start (retry_episode Quorum_Backed (round ?i) healthy Q
      (eligible ?i) (candidate_key ?i) (voter_keys ?i) ?remembered (reports ?i) (select ?i) delay) k"
    by blast
  have "?i \<le> clock ?i" unfolding clock_def by (rule election_wakeup_times_unbounded[OF jitter])
  with begun(1) have later: "after < k" by linarith
  have "k < clock (Suc ?i)" using begun(2) fits[of ?i] unfolding clock_def by simp
  with begun(3) later show ?thesis by blast
qed

end
