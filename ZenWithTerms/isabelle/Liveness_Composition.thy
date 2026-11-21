theory Liveness_Composition
  imports Production_Timer_Cut_Recurrence Scheduler_Liveness Bootstrap_Liveness
    Worker_Listener_Handoff Dynamic_Window_Liveness
    Stateless_Window_Liveness Production_Recovery_Retries
    Master_Service_Queue_Liveness
    Stateless_Failover_Recovery Stateless_Recovery_Handoff
begin

section \<open>From a stalled incumbent to a locally completed publication\<close>

text \<open>
  This theory composes the per-stage liveness results on the default
  strategy and a fixed voting configuration. A stall is a time at which
  no update has committed. The premises are the serviced reset episode
  after each stall, the recovery episode that permits an attempt, and the
  service schedule that the attempt starts. The conclusion places a
  completed first publication, with the publisher's local installation and
  slot release, within a bound that is explicit in those premises.
\<close>


section \<open>A timer window after any stall\<close>

text \<open>
  The step shared by every strategy. From a stall, the serviced reset episode
  gives a post-failure cut and so a timer window whose attempt time is after
  the stall and within an explicit bound of it.
\<close>

lemma stalled_timer_window:
  fixes stalled :: "nat \<Rightarrow> bool" and next_reset :: "nat \<Rightarrow> timer_reset_episode"
    and extra :: nat and bounds :: timer_queue_bounds and loss restore tail retry_bound t0 :: nat
    and contenders :: "node set" and c :: node
    and first_limit next_limit duration window_length :: nat
  assumes candidate: "c \<in> contenders"
    and triggers: "\<And>t. stalled t \<Longrightarrow> t \<le> reset_failed (next_reset t)
      \<and> reset_failed (next_reset t) \<le> t + retry_bound
      \<and> reset_episode_service contenders bounds loss restore tail
        (reset_failed (next_reset t) + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length)
        (next_reset t)"
    and margin: "reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length < first_limit"
    and own_timer: "window_length < duration + next_limit"
    and limits: "0 < first_limit" "first_limit \<le> (2::nat)^63" "0 < next_limit" "next_limit \<le> (2::nat)^63"
    and dispatch: "extra \<le> timer_queue_delay bounds"
    and stalled_at: "stalled t0"
  obtains draws where
    "draws c = earliest_safe_draw (reset_armed (next_reset t0) c)
      (reset_drained bounds loss tail (next_reset t0))"
    "timer_window contenders c (reset_armed (next_reset t0)) draws (\<lambda>_. extra) duration next_limit
      (reset_pending contenders (next_reset t0)) (reset_drained bounds loss tail (next_reset t0)) window_length"
    "t0 < reset_armed (next_reset t0) c + draws c + extra"
    "reset_armed (next_reset t0) c + draws c + extra
      \<le> t0 + retry_bound + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds"
proof -
  define e where "e = next_reset t0"
  note rc = recurring_serviced_timer_cuts[where stalled = stalled and next_reset = next_reset and t = t0,
    OF candidate triggers margin own_timer stalled_at]
  let ?base = "reset_armed e" and ?drained = "reset_drained bounds loss tail e"
    and ?pending = "reset_pending contenders e"
  have cut: "postfailure_cut contenders c ?base ?drained (\<lambda>_. first_limit) next_limit duration ?pending
      (timer_queue_delay bounds) window_length"
    using rc(3) by (simp add: e_def)
  have due: "t0 < reset_armed e c + earliest_safe_draw (reset_armed e c) ?drained"
    "reset_armed e c + earliest_safe_draw (reset_armed e c) ?drained
      \<le> t0 + retry_bound + reset_cut_slack bounds loss restore tail"
    using rc(1,2) by (simp_all add: e_def)
  have limit_range: "\<And>n. n \<in> contenders \<Longrightarrow>
      0 < (\<lambda>_. first_limit) n \<and> (\<lambda>_. first_limit) n \<le> (2::nat)^63"
    using limits by simp
  have window: "timer_window contenders c ?base (phase_draws c ?base ?drained (\<lambda>_. first_limit))
      (\<lambda>_. extra) duration next_limit ?pending ?drained window_length"
    using postfailure_cut_suffices(3)[where limit = "\<lambda>_. first_limit" and extra = "\<lambda>_. extra"
      and next_limit = next_limit, OF cut _ limits(3,4)] limit_range dispatch by blast
  show thesis
    by (rule that[of "phase_draws c ?base ?drained (\<lambda>_. first_limit)"])
      (use window due dispatch in \<open>simp_all add: phase_draws_def e_def\<close>)
qed

context fixed_publication_window
begin

theorem stalled_default_leader_completes:
  fixes stalled :: "nat \<Rightarrow> bool" and next_reset :: "nat \<Rightarrow> timer_reset_episode"
    and episode :: "nat \<Rightarrow> recovery_episode" and extra :: nat
    and bounds :: timer_queue_bounds and loss restore tail retry_bound :: nat
  assumes candidate: "c \<in> contenders"
    and triggers: "\<And>t0. stalled t0 \<Longrightarrow> t0 \<le> reset_failed (next_reset t0)
      \<and> reset_failed (next_reset t0) \<le> t0 + retry_bound
      \<and> reset_episode_service contenders bounds loss restore tail
        (reset_failed (next_reset t0) + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length)
        (next_reset t0)"
    and margin: "reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length < first_limit"
    and own_timer: "window_length < duration + next_limit"
    and limits: "0 < first_limit" "first_limit \<le> (2::nat)^63" "0 < next_limit" "next_limit \<le> (2::nat)^63"
    and dispatch: "extra \<le> timer_queue_delay bounds"
    and stalled_at: "stalled t0"
  defines "start \<equiv> reset_armed (next_reset t0) c
      + earliest_safe_draw (reset_armed (next_reset t0) c) (reset_drained bounds loss tail (next_reset t0)) + extra"
  assumes permission: "episode_permission start (episode t0)" "episode_service (episode t0)"
    and chosen: "replacement_candidate (episode_round (episode t0)) = c" "episode_quorum (episode t0) = E"
      "committed_voters (episode_round (episode t0)) = V" "accepted_voters (episode_round (episode t0)) = V"
    and fresh: "fresh"
    and budget: "3 * episode_delay (episode t0) + 12 * delay \<le> window_length"
    and service: "\<And>k. opens_attempt_at start (episode t0) k \<Longrightarrow>
      bounded_service jobs deps (schedule k) delay (12 * delay)"
  obtains k where "t0 < start" "start \<le> t0 + retry_bound + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds"
    "opens_attempt_at start (episode t0) k" "k + 12 * delay \<le> start + window_length"
    "h \<in> committed (core (finished (schedule k) (12 * delay)))"
    "installed (window_applier (finished (schedule k) (12 * delay))) = Some key"
    "window_slot (finished (schedule k) (12 * delay)) = None"
proof -
  define e where "e = next_reset t0"
  note rc = recurring_serviced_timer_cuts[where stalled = stalled and next_reset = next_reset and t = t0,
    OF candidate triggers margin own_timer stalled_at]
  let ?base = "reset_armed e" and ?drained = "reset_drained bounds loss tail e"
    and ?pending = "reset_pending contenders e"
  have cut: "postfailure_cut contenders c ?base ?drained (\<lambda>_. first_limit) next_limit duration ?pending
      (timer_queue_delay bounds) window_length"
    using rc(3) by (simp add: e_def)
  have due: "t0 < reset_armed e c + earliest_safe_draw (reset_armed e c) ?drained"
    "reset_armed e c + earliest_safe_draw (reset_armed e c) ?drained
      \<le> t0 + retry_bound + reset_cut_slack bounds loss restore tail"
    using rc(1,2) by (simp_all add: e_def)
  have limit_range: "\<And>n. n \<in> contenders \<Longrightarrow>
      0 < (\<lambda>_. first_limit) n \<and> (\<lambda>_. first_limit) n \<le> (2::nat)^63"
    using limits by simp
  have window: "timer_window contenders c ?base (phase_draws c ?base ?drained (\<lambda>_. first_limit))
      (\<lambda>_. extra) duration next_limit ?pending ?drained window_length"
    using postfailure_cut_suffices(3)[where limit = "\<lambda>_. first_limit" and extra = "\<lambda>_. extra"
      and next_limit = next_limit, OF cut _ limits(3,4)] limit_range dispatch by blast
  have start_eq: "start = ?base c + phase_draws c ?base ?drained (\<lambda>_. first_limit) c + extra"
    by (simp add: start_def phase_draws_def e_def)
  obtain k where k: "replacement_candidate (episode_round (episode t0)) = c" "episode_quorum (episode t0) = E"
    "opens_attempt_at start (episode t0) k"
    "k + 12 * delay \<le> start + window_length"
    "h \<in> committed (core (finished (schedule k) (12 * delay)))"
    "installed (window_applier (finished (schedule k) (12 * delay))) = Some key"
    "window_slot (finished (schedule k) (12 * delay)) = None"
    by (rule recovered_timer_window_completes[OF window start_eq permission chosen(1,2,3,4) fresh budget service]) blast
  show thesis
    by (rule that[OF _ _ k(3,4,5,6,7)]) (use due dispatch in \<open>simp_all add: start_def e_def\<close>)
qed


text \<open>
  The worker and listener handoff is a separate tick-indexed projection.
  Its input index is aligned with the publication window's service ticks
  by the premise that the slot release is seen as the clear event within
  a stated lag. That alignment is a source-mapping premise.
\<close>

theorem stalled_default_task_published:
  fixes stalled :: "nat \<Rightarrow> bool" and next_reset :: "nat \<Rightarrow> timer_reset_episode"
    and episode :: "nat \<Rightarrow> recovery_episode" and extra :: nat
    and bounds :: timer_queue_bounds and loss restore tail retry_bound :: nat
    and init :: worker_handoff_phase and input :: "nat \<Rightarrow> worker_handoff_event"
    and handoff_bound release_lag :: nat
  assumes candidate: "c \<in> contenders"
    and triggers: "\<And>t0. stalled t0 \<Longrightarrow> t0 \<le> reset_failed (next_reset t0)
      \<and> reset_failed (next_reset t0) \<le> t0 + retry_bound
      \<and> reset_episode_service contenders bounds loss restore tail
        (reset_failed (next_reset t0) + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length)
        (next_reset t0)"
    and margin: "reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length < first_limit"
    and own_timer: "window_length < duration + next_limit"
    and limits: "0 < first_limit" "first_limit \<le> (2::nat)^63" "0 < next_limit" "next_limit \<le> (2::nat)^63"
    and dispatch: "extra \<le> timer_queue_delay bounds"
    and stalled_at: "stalled t0"
  defines "start \<equiv> reset_armed (next_reset t0) c
      + earliest_safe_draw (reset_armed (next_reset t0) c) (reset_drained bounds loss tail (next_reset t0)) + extra"
  assumes permission: "episode_permission start (episode t0)" "episode_service (episode t0)"
    and chosen: "replacement_candidate (episode_round (episode t0)) = c" "episode_quorum (episode t0) = E"
      "committed_voters (episode_round (episode t0)) = V" "accepted_voters (episode_round (episode t0)) = V"
    and fresh: "fresh"
    and budget: "3 * episode_delay (episode t0) + 12 * delay \<le> window_length"
    and service: "\<And>k. opens_attempt_at start (episode t0) k \<Longrightarrow>
      bounded_service jobs deps (schedule k) delay (12 * delay)"
    and worker: "worker_handoff_bounded_service init input handoff_bound"
    and aligned: "\<And>k. opens_attempt_at start (episode t0) k \<Longrightarrow>
      window_slot (finished (schedule k) (12 * delay)) = None \<Longrightarrow>
      \<exists>i. i \<le> k + 12 * delay + release_lag \<and>
        worker_handoff_trace init input i = Handoff_Cleared Handoff_Published"
  obtains k i decision where "t0 < start"
    "opens_attempt_at start (episode t0) k"
    "h \<in> committed (core (finished (schedule k) (12 * delay)))"
    "installed (window_applier (finished (schedule k) (12 * delay))) = Some key"
    "window_slot (finished (schedule k) (12 * delay)) = None"
    "i \<le> k + 12 * delay + release_lag"
    "worker_handoff_trace init input (i + 6 * handoff_bound) = Handoff_Next_Round (Handoff_Deliver Task_Published) decision"
    "handoff_master_task (worker_handoff_trace init input (i + 6 * handoff_bound)) = Task_Delivered Task_Published"
proof -
  note permission' = permission[unfolded start_def]
  note service' = service[unfolded start_def]
  obtain k where k: "t0 < start" "opens_attempt_at start (episode t0) k"
    "h \<in> committed (core (finished (schedule k) (12 * delay)))"
    "installed (window_applier (finished (schedule k) (12 * delay))) = Some key"
    "window_slot (finished (schedule k) (12 * delay)) = None"
    by (rule stalled_default_leader_completes[where stalled = stalled and next_reset = next_reset and episode = episode
          and extra = extra and bounds = bounds and loss = loss and restore = restore and tail = tail
          and retry_bound = retry_bound, OF candidate triggers margin own_timer limits(1,2,3,4) dispatch
          stalled_at permission' chosen fresh budget service'])
       (simp_all add: start_def)
  from aligned[OF k(2) k(5)] obtain i where i: "i \<le> k + 12 * delay + release_lag"
    and cleared: "worker_handoff_trace init input i = Handoff_Cleared Handoff_Published" by blast
  from cleared_publication_to_next_queue_round[OF worker cleared] obtain decision where
    nxt: "worker_handoff_trace init input (i + 6 * handoff_bound) =
      Handoff_Next_Round (publication_handoff_verdict Handoff_Published) decision"
    "handoff_master_task (worker_handoff_trace init input (i + 6 * handoff_bound)) =
      (case publication_handoff_verdict Handoff_Published of
        Handoff_Deliver result \<Rightarrow> Task_Delivered result | Handoff_Omit why \<Rightarrow> Task_Dropped)" by blast
  show thesis by (rule that[OF k(1,2,3,4,5) i]) (use nxt in simp_all)
qed


text \<open>
  The completed first publication is also needed as a named property, so
  that a statement outside the locale can refer to it.
\<close>

definition first_publication_completed where
  "first_publication_completed select delay \<longleftrightarrow>
    h \<in> committed (core (finished select (12 * delay))) \<and>
    installed (window_applier (finished select (12 * delay))) = Some key \<and>
    window_slot (finished select (12 * delay)) = None"

lemma serviced_window_completes_first_publication:
  assumes "fresh" "bounded_service jobs deps select delay (12 * delay)"
  shows "first_publication_completed select delay"
  unfolding first_publication_completed_def
  using fixed_first_publication_local_completion[OF assms(1) assms(2) order_refl]
  by blast

end

section \<open>From configured startup to a locally completed first publication\<close>

text \<open>
  The startup window brings the candidate to pre-vote with a fully resolved
  roster. The election and first publication then run in the next window of
  the same fixed schedule, with their own service bound. The roster and
  quorum premises are the ones of the startup-to-election handoff.
\<close>

theorem configured_startup_first_commit:
  assumes stable: "stable_requirements R matches bind"
    and roster: "V = bind ` R"
    and captures: "\<And>n. n \<in> insert c H \<Longrightarrow> configured_bootstrap R (view n) matches n (C n)"
    and resolved: "\<And>n. n \<in> insert c H \<Longrightarrow> V \<subseteq> view n"
    and eligible: "eligible"
    and healthy: "candidate"
    and live: "initial_quorum (C c) H"
    and new_version: "0 < v" and new_term: "0 < t"
    and startup_service: "bounded_service (bootstrap_jobs retrying) (bootstrap_prerequisites retrying)
      startup_sel startup_delay startup_horizon"
    and startup_time: "(if retrying then 4 else 5) * startup_delay \<le> startup_horizon"
    and window_service: "bounded_service (window_jobs True H H (insert c H) c False)
      (window_dependencies True H H (insert c H) c False) window_sel window_delay (12 * window_delay)"
  shows "\<forall>n\<in>insert c H. C n = Discovered_ID ` V"
    "rtranclp (startup_step (configured_bootstrap R (view c) matches c) H c eligible candidate)
      (Await_View (if retrying then Some (C c) else None)) (Startup_PreVote (C c))"
    "fixed_publication_window.first_publication_completed H H (insert c H) c t v u initial True False
      window_sel window_delay"
proof -
  have cap: "configured_bootstrap R (view c) matches c (C c)" using captures by simp
  have equal: "C n = Discovered_ID ` V" if "n \<in> insert c H" for n
    using fully_resolved_capture[OF stable captures[OF that]] resolved[OF that] roster by simp
  then show "\<forall>n\<in>insert c H. C n = Discovered_ID ` V" by blast
  have member: "n \<in> V" if "n \<in> insert c H" for n
    using configured_known_quorum(1)[OF captures[OF that]] equal[OF that] by (simp add: image_iff)
  then have in_V: "H \<subseteq> V" "c \<in> V" by auto
  have q: "majority V H"
    using configured_quorum_projects[OF stable cap live] in_V(1) roster by (simp add: Int_absorb1)
  then have hfin: "finite H" unfolding majority_def by (auto intro: finite_subset)
  show "rtranclp (startup_step (configured_bootstrap R (view c) matches c) H c eligible candidate)
      (Await_View (if retrying then Some (C c) else None)) (Startup_PreVote (C c))"
    by (rule configured_startup_opens_prevote(2)[OF cap eligible healthy live startup_service startup_time])
  have initial_reach: "reachable V initial" by (rule reachable.initial)
  interpret window: fixed_publication_window V H H "insert c H" c t v u initial True False
    using initial_reach q in_V hfin new_version new_term
    by unfold_locales (auto simp: initial_def version_def fresher_eq_def epoch_def)
  show "window.first_publication_completed window_sel window_delay"
    by (rule window.serviced_window_completes_first_publication[OF TrueI window_service])
qed

section \<open>Which task outcomes the caller sees after a slot clear\<close>

text \<open>
  After a publication slot is cleared, the worker's next queue round starts
  within six service bounds and the task has one of three classified
  outcomes. It is published. It has a delivered retryable rejection, and a
  retry is then a separate attempt that only the caller can make. Or the
  result is dropped by one of the two lifecycle paths that release the
  worker without delivering a result. Those paths are excluded, not
  covered, by any guarantee of delivery.
\<close>

theorem cleared_task_outcome_classified:
  assumes service: "worker_handoff_bounded_service init input B"
    and cleared: "worker_handoff_trace init input i = Handoff_Cleared out"
  obtains decision where
    "worker_handoff_trace init input (i + 6 * B) = Handoff_Next_Round (publication_handoff_verdict out) decision"
    "(\<exists>r. handoff_master_task (worker_handoff_trace init input (i + 6 * B)) = Task_Delivered r \<and>
        (r = Task_Published \<or>
          (master_task_retryable r \<and> (\<forall>attempt. master_caller_retry attempt r True True = Some (Suc attempt))))) \<or>
      (handoff_master_task (worker_handoff_trace init input (i + 6 * B)) = Task_Dropped \<and>
        out \<in> {Handoff_Shutdown_Rejection, Handoff_Unexpected_Failure})"
proof -
  from cleared_publication_to_next_queue_round[OF service cleared] obtain decision where
    trace: "worker_handoff_trace init input (i + 6 * B) =
      Handoff_Next_Round (publication_handoff_verdict out) decision"
    and task: "handoff_master_task (worker_handoff_trace init input (i + 6 * B)) =
      (case publication_handoff_verdict out of
        Handoff_Deliver result \<Rightarrow> Task_Delivered result | Handoff_Omit why \<Rightarrow> Task_Dropped)" by blast
  show thesis
  proof (rule that[OF trace])
    show "(\<exists>r. handoff_master_task (worker_handoff_trace init input (i + 6 * B)) = Task_Delivered r \<and>
        (r = Task_Published \<or>
          (master_task_retryable r \<and> (\<forall>attempt. master_caller_retry attempt r True True = Some (Suc attempt))))) \<or>
      (handoff_master_task (worker_handoff_trace init input (i + 6 * B)) = Task_Dropped \<and>
        out \<in> {Handoff_Shutdown_Rejection, Handoff_Unexpected_Failure})"
      using task by (cases out) (auto simp: master_caller_retry_def)
  qed
qed

section \<open>The same chain for dynamic reconfiguration\<close>

context dynamic_publication_window
begin

theorem stalled_dynamic_leader_completes:
  fixes stalled :: "nat \<Rightarrow> bool" and next_reset :: "nat \<Rightarrow> timer_reset_episode"
    and episode :: "nat \<Rightarrow> recovery_episode" and extra :: nat
    and bounds :: timer_queue_bounds and loss restore tail retry_bound t0 :: nat
  assumes candidate: "c \<in> contenders"
    and triggers: "\<And>t. stalled t \<Longrightarrow> t \<le> reset_failed (next_reset t)
      \<and> reset_failed (next_reset t) \<le> t + retry_bound
      \<and> reset_episode_service contenders bounds loss restore tail
        (reset_failed (next_reset t) + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length)
        (next_reset t)"
    and margin: "reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length < first_limit"
    and own_timer: "window_length < duration + next_limit"
    and limits: "0 < first_limit" "first_limit \<le> (2::nat)^63" "0 < next_limit" "next_limit \<le> (2::nat)^63"
    and dispatch: "extra \<le> timer_queue_delay bounds"
    and stalled_at: "stalled t0"
  defines "start \<equiv> reset_armed (next_reset t0) c
      + earliest_safe_draw (reset_armed (next_reset t0) c) (reset_drained bounds loss tail (next_reset t0)) + extra"
  assumes permission: "episode_permission start (episode t0)" "episode_service (episode t0)"
    and chosen: "replacement_candidate (episode_round (episode t0)) = c" "episode_quorum (episode t0) = E"
      "committed_voters (episode_round (episode t0)) = committed_config s c"
      "accepted_voters (episode_round (episode t0)) = config_of C base"
    and budget: "3 * episode_delay (episode t0) + 12 * delay \<le> window_length"
    and service: "\<And>k. opens_attempt_at start (episode t0) k \<Longrightarrow>
      bounded_service jobs deps (schedule k) delay (12 * delay)"
  obtains k where "t0 < start" "start \<le> t0 + retry_bound + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds"
    "opens_attempt_at start (episode t0) k" "k + 12 * delay \<le> start + window_length"
    "hist \<in> quorum_commits (dynamic_snapshot (finished (schedule k) (12 * delay))) - quorum_commits s"
    "committed_config (dynamic_snapshot (finished (schedule k) (12 * delay))) c = D"
    "dynamic_window_slot (finished (schedule k) (12 * delay)) = None"
    "\<exists>a. application_reachable c (dynamic_window_traffic (finished (schedule k) (12 * delay)))
      (node_term s c) (position base) a \<and> installed a = Some \<lparr>rank_term = t, rank_version = v\<rparr>"
proof -
  obtain draws where draws: "draws c = earliest_safe_draw (reset_armed (next_reset t0) c)
      (reset_drained bounds loss tail (next_reset t0))"
    and window: "timer_window contenders c (reset_armed (next_reset t0)) draws (\<lambda>_. extra) duration next_limit
      (reset_pending contenders (next_reset t0)) (reset_drained bounds loss tail (next_reset t0)) window_length"
    and after: "t0 < reset_armed (next_reset t0) c + draws c + extra"
    and before: "reset_armed (next_reset t0) c + draws c + extra
      \<le> t0 + retry_bound + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds"
    by (rule stalled_timer_window[where stalled = stalled and next_reset = next_reset and extra = extra
          and bounds = bounds and loss = loss and restore = restore and tail = tail and retry_bound = retry_bound, OF candidate triggers margin own_timer limits dispatch stalled_at])
  have start_eq: "start = reset_armed (next_reset t0) c + draws c + extra"
    by (simp add: start_def draws)
  obtain k where k: "opens_attempt_at start (episode t0) k"
    "k + 12 * delay \<le> start + window_length"
    "hist \<in> quorum_commits (dynamic_snapshot (finished (schedule k) (12 * delay))) - quorum_commits s"
    "committed_config (dynamic_snapshot (finished (schedule k) (12 * delay))) c = D"
    "dynamic_window_slot (finished (schedule k) (12 * delay)) = None"
    "\<exists>a. application_reachable c (dynamic_window_traffic (finished (schedule k) (12 * delay)))
      (node_term s c) (position base) a \<and> installed a = Some \<lparr>rank_term = t, rank_version = v\<rparr>"
    by (rule recovered_dynamic_window_completes[OF window start_eq[unfolded]  permission chosen budget service]) blast
  show thesis by (rule that[OF _ _ k]) (use after before start_eq in simp_all)
qed

end

section \<open>The same chain for stateless coordination\<close>

text \<open>
  The stateless attempt starts at the candidate's wakeup, when it is ready
  to claim the lease. There is no separate recovery episode in the stateless
  window theorem. The conclusion reaches the fenced commit notification, local
  installation and the node acknowledgement of the new publication.
\<close>

context stateless_publication_window
begin

theorem stalled_stateless_leader_completes:
  fixes stalled :: "nat \<Rightarrow> bool" and next_reset :: "nat \<Rightarrow> timer_reset_episode"
    and extra :: nat and bounds :: timer_queue_bounds and loss restore tail retry_bound t0 :: nat
  assumes candidate: "c \<in> contenders"
    and triggers: "\<And>t. stalled t \<Longrightarrow> t \<le> reset_failed (next_reset t)
      \<and> reset_failed (next_reset t) \<le> t + retry_bound
      \<and> reset_episode_service contenders bounds loss restore tail
        (reset_failed (next_reset t) + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length)
        (next_reset t)"
    and margin: "reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length < first_limit"
    and own_timer: "window_length < duration + next_limit"
    and limits: "0 < first_limit" "first_limit \<le> (2::nat)^63" "0 < next_limit" "next_limit \<le> (2::nat)^63"
    and dispatch: "extra \<le> timer_queue_delay bounds"
    and stalled_at: "stalled t0"
  defines "start \<equiv> reset_armed (next_reset t0) c
      + earliest_safe_draw (reset_armed (next_reset t0) c) (reset_drained bounds loss tail (next_reset t0)) + extra"
  assumes service: "bounded_service {..<4 + scans + 14} (\<lambda>i. {..<i}) select B window_length"
    and time: "(18 + max 1 (t - 1)) * B \<le> window_length"
  obtains run where "t0 < start"
    "start \<le> t0 + retry_bound + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds"
    "run 0 = x" "\<And>i. run i = run (Suc i) \<or> stateless_exec_step (run i) (run (Suc i))"
    "stateless_execution_reachable (run ((4 + scans + 14) * B))"
    "h \<in> notifications (shared_state (run ((4 + scans + 14) * B)))"
    "installed (processes (run ((4 + scans + 14) * B)) c) = Some (position h)"
    "(incarnation (processes (run ((4 + scans + 14) * B)) c), q, position h)
      \<in> node_acknowledgements (processes (run ((4 + scans + 14) * B)) c)"
proof -
  obtain draws where draws: "draws c = earliest_safe_draw (reset_armed (next_reset t0) c)
      (reset_drained bounds loss tail (next_reset t0))"
    and window: "timer_window contenders c (reset_armed (next_reset t0)) draws (\<lambda>_. extra) duration next_limit
      (reset_pending contenders (next_reset t0)) (reset_drained bounds loss tail (next_reset t0)) window_length"
    and after: "t0 < reset_armed (next_reset t0) c + draws c + extra"
    and before: "reset_armed (next_reset t0) c + draws c + extra
      \<le> t0 + retry_bound + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds"
    by (rule stalled_timer_window[where stalled = stalled and next_reset = next_reset and extra = extra
          and bounds = bounds and loss = loss and restore = restore and tail = tail and retry_bound = retry_bound,
          OF candidate triggers margin own_timer limits dispatch stalled_at])
  have start_eq: "start = reset_armed (next_reset t0) c + draws c + extra"
    by (simp add: start_def draws)
  obtain run where run: "run 0 = x" "\<And>i. run i = run (Suc i) \<or> stateless_exec_step (run i) (run (Suc i))"
    "stateless_execution_reachable (run ((4 + scans + 14) * B))"
    "h \<in> notifications (shared_state (run ((4 + scans + 14) * B)))"
    "installed (processes (run ((4 + scans + 14) * B)) c) = Some (position h)"
    "(incarnation (processes (run ((4 + scans + 14) * B)) c), q, position h)
      \<in> node_acknowledgements (processes (run ((4 + scans + 14) * B)) c)"
    by (rule stateless_timer_window_completes[OF window start_eq[unfolded] service time]) blast
  show thesis by (rule that[OF _ _ run]) (use after before start_eq in simp_all)
qed

end

section \<open>The chain for either failover policy\<close>

text \<open>
  The recovery episode is the policy interface. Its permission is the
  policy's own condition on the replacement round, reports, healthy set,
  recovery quorum and remembered incumbent. The window theorem needs only
  that the episode permits an attempt and is serviced. The two policies
  differ in how that permission arises, so each gets an instance below.
\<close>

context fixed_publication_window
begin

theorem stalled_policy_leader_completes:
  fixes stalled :: "nat \<Rightarrow> bool" and next_reset :: "nat \<Rightarrow> timer_reset_episode" and extra :: nat
    and bounds :: timer_queue_bounds and loss restore tail retry_bound t0 :: nat
    and policy :: attempt_policy and r :: replacement_round and healthy RQ :: "node set"
    and eligible_now :: bool and candidate_key :: rank and voter_keys :: "node \<Rightarrow> rank"
    and remembered :: "node \<Rightarrow> node option" and reports :: "replacement_report set"
    and rselect :: "nat \<Rightarrow> recovery_job option" and rdelay :: nat
  assumes candidate: "c \<in> contenders"
    and triggers: "\<And>t. stalled t \<Longrightarrow> t \<le> reset_failed (next_reset t)
      \<and> reset_failed (next_reset t) \<le> t + retry_bound
      \<and> reset_episode_service contenders bounds loss restore tail
        (reset_failed (next_reset t) + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length)
        (next_reset t)"
    and margin: "reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length < first_limit"
    and own_timer: "window_length < duration + next_limit"
    and limits: "0 < first_limit" "first_limit \<le> (2::nat)^63" "0 < next_limit" "next_limit \<le> (2::nat)^63"
    and dispatch: "extra \<le> timer_queue_delay bounds"
    and stalled_at: "stalled t0"
  defines "start \<equiv> reset_armed (next_reset t0) c
      + earliest_safe_draw (reset_armed (next_reset t0) c) (reset_drained bounds loss tail (next_reset t0)) + extra"
  assumes permit: "can_open_attempt policy r (request_generation r) (start + 3 * rdelay) reports healthy RQ remembered"
    and recovery_service: "bounded_service (recovery_jobs RQ) (recovery_dependencies RQ) rselect rdelay (3 * rdelay)"
    and eligible: eligible_now
    and fresh_votes: "\<And>n. n \<in> RQ \<Longrightarrow> voter_keys n \<le> candidate_key"
    and chosen: "replacement_candidate r = c" "RQ = E" "committed_voters r = V" "accepted_voters r = V"
    and fresh: "fresh"
    and budget: "3 * rdelay + 12 * delay \<le> window_length"
    and service: "\<And>k. opens_attempt_at start
        (retry_episode policy r healthy RQ eligible_now candidate_key voter_keys remembered reports rselect rdelay) k \<Longrightarrow>
      bounded_service jobs deps (schedule k) delay (12 * delay)"
  obtains k where "t0 < start"
    "start \<le> t0 + retry_bound + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds"
    "opens_attempt_at start
      (retry_episode policy r healthy RQ eligible_now candidate_key voter_keys remembered reports rselect rdelay) k"
    "k + 12 * delay \<le> start + window_length"
    "h \<in> committed (core (finished (schedule k) (12 * delay)))"
    "installed (window_applier (finished (schedule k) (12 * delay))) = Some key"
    "window_slot (finished (schedule k) (12 * delay)) = None"
proof -
  let ?e = "retry_episode policy r healthy RQ eligible_now candidate_key voter_keys remembered reports rselect rdelay"
  have perm: "episode_permission start ?e"
    using permit eligible fresh_votes
    by (auto simp: retry_episode_def episode_permission_def)
  have serv: "episode_service ?e"
    using recovery_service by (simp add: retry_episode_def episode_service_def)
  have chosen': "replacement_candidate (episode_round ?e) = c" "episode_quorum ?e = E"
    "committed_voters (episode_round ?e) = V" "accepted_voters (episode_round ?e) = V"
    using chosen by (simp_all add: retry_episode_def)
  have budget': "3 * episode_delay ?e + 12 * delay \<le> window_length"
    using budget by (simp add: retry_episode_def)
  note perm' = perm[unfolded start_def]
  note service' = service[unfolded start_def]
  obtain k where k: "t0 < start"
    "start \<le> t0 + retry_bound + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds"
    "opens_attempt_at start ?e k" "k + 12 * delay \<le> start + window_length"
    "h \<in> committed (core (finished (schedule k) (12 * delay)))"
    "installed (window_applier (finished (schedule k) (12 * delay))) = Some key"
    "window_slot (finished (schedule k) (12 * delay)) = None"
    by (rule stalled_default_leader_completes[where stalled = stalled and next_reset = next_reset
          and episode = "\<lambda>_. ?e" and extra = extra and bounds = bounds and loss = loss and restore = restore
          and tail = tail and retry_bound = retry_bound, OF candidate triggers margin own_timer limits dispatch
          stalled_at perm' serv chosen' fresh budget' service'])
       (simp_all add: start_def)
  show thesis by (rule that[OF k])
qed

theorem stalled_quorum_backed_leader_completes:
  fixes stalled :: "nat \<Rightarrow> bool" and next_reset :: "nat \<Rightarrow> timer_reset_episode" and extra :: nat
    and bounds :: timer_queue_bounds and loss restore tail retry_bound t0 :: nat
    and r :: replacement_round and healthy RQ :: "node set"
    and eligible_now :: bool and candidate_key :: rank and voter_keys :: "node \<Rightarrow> rank"
    and rselect :: "nat \<Rightarrow> recovery_job option" and rdelay :: nat
    and expiry :: "node \<Rightarrow> nat" and report_select :: "nat \<Rightarrow> node option"
    and report_delay report_horizon report_start :: nat and remembered :: "node \<Rightarrow> node option"
  assumes candidate: "c \<in> contenders"
    and triggers: "\<And>t. stalled t \<Longrightarrow> t \<le> reset_failed (next_reset t)
      \<and> reset_failed (next_reset t) \<le> t + retry_bound
      \<and> reset_episode_service contenders bounds loss restore tail
        (reset_failed (next_reset t) + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length)
        (next_reset t)"
    and margin: "reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length < first_limit"
    and own_timer: "window_length < duration + next_limit"
    and limits: "0 < first_limit" "first_limit \<le> (2::nat)^63" "0 < next_limit" "next_limit \<le> (2::nat)^63"
    and dispatch: "extra \<le> timer_queue_delay bounds"
    and stalled_at: "stalled t0"
  defines "start \<equiv> reset_armed (next_reset t0) c
      + earliest_safe_draw (reset_armed (next_reset t0) c) (reset_drained bounds loss tail (next_reset t0)) + extra"
  assumes report_service: "bounded_service RQ (\<lambda>_. {}) report_select report_delay report_horizon"
      "report_delay \<le> report_horizon"
    and health: "replacement_candidate r \<in> healthy" "RQ \<subseteq> healthy"
    and alternate: "replacement_candidate r \<noteq> replaced_leader r" "replaced_leader r \<notin> RQ"
    and quorums: "quorum (committed_voters r) RQ" "quorum (accepted_voters r) RQ"
    and live: "\<And>n. n \<in> RQ \<Longrightarrow> report_start + report_delay \<le> start + 3 * rdelay
      \<and> start + 3 * rdelay < expiry n"
    and recovery_service: "bounded_service (recovery_jobs RQ) (recovery_dependencies RQ) rselect rdelay (3 * rdelay)"
    and eligible: eligible_now
    and fresh_votes: "\<And>n. n \<in> RQ \<Longrightarrow> voter_keys n \<le> candidate_key"
    and chosen: "replacement_candidate r = c" "RQ = E" "committed_voters r = V" "accepted_voters r = V"
    and fresh: "fresh"
    and budget: "3 * rdelay + 12 * delay \<le> window_length"
    and service: "\<And>k. opens_attempt_at start
        (retry_episode Quorum_Backed r healthy RQ eligible_now candidate_key voter_keys remembered
          (served_reports RQ r expiry report_select report_delay) rselect rdelay) k \<Longrightarrow>
      bounded_service jobs deps (schedule k) delay (12 * delay)"
  obtains k where "t0 < start"
    "start \<le> t0 + retry_bound + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds"
    "opens_attempt_at start (retry_episode Quorum_Backed r healthy RQ eligible_now candidate_key voter_keys remembered
      (served_reports RQ r expiry report_select report_delay) rselect rdelay) k"
    "k + 12 * delay \<le> start + window_length"
    "h \<in> committed (core (finished (schedule k) (12 * delay)))"
    "installed (window_applier (finished (schedule k) (12 * delay))) = Some key"
    "window_slot (finished (schedule k) (12 * delay)) = None"
proof -
  have permit: "can_open_attempt Quorum_Backed r (request_generation r) (start + 3 * rdelay)
      (served_reports RQ r expiry report_select report_delay) healthy RQ remembered"
    by (rule independent_reports_open_attempt[OF report_service health alternate quorums live])
  note permit' = permit[unfolded start_def] and service' = service[unfolded start_def]
  obtain k where "t0 < start"
    "start \<le> t0 + retry_bound + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds"
    "opens_attempt_at start (retry_episode Quorum_Backed r healthy RQ eligible_now candidate_key voter_keys
      remembered (served_reports RQ r expiry report_select report_delay) rselect rdelay) k"
    "k + 12 * delay \<le> start + window_length"
    "h \<in> committed (core (finished (schedule k) (12 * delay)))"
    "installed (window_applier (finished (schedule k) (12 * delay))) = Some key"
    "window_slot (finished (schedule k) (12 * delay)) = None"
    by (rule stalled_policy_leader_completes[where stalled = stalled and next_reset = next_reset and extra = extra
          and bounds = bounds and loss = loss and restore = restore and tail = tail and retry_bound = retry_bound
          and policy = Quorum_Backed and r = r and healthy = healthy and RQ = RQ and eligible_now = eligible_now
          and candidate_key = candidate_key and voter_keys = voter_keys and remembered = remembered and reports = "served_reports RQ r expiry report_select report_delay"
          and rselect = rselect and rdelay = rdelay,
          OF candidate triggers margin own_timer limits dispatch stalled_at permit' recovery_service eligible
          fresh_votes chosen fresh budget service'])
       (simp_all add: start_def)
  then show thesis by (rule that)
qed

theorem stalled_current_checks_leader_completes:
  fixes stalled :: "nat \<Rightarrow> bool" and next_reset :: "nat \<Rightarrow> timer_reset_episode" and extra :: nat
    and bounds :: timer_queue_bounds and loss restore tail retry_bound t0 :: nat
    and r :: replacement_round and healthy RQ :: "node set"
    and eligible_now :: bool and candidate_key :: rank and voter_keys :: "node \<Rightarrow> rank"
    and rselect :: "nat \<Rightarrow> recovery_job option" and rdelay :: nat
    and failed :: "node set" and views :: "node \<Rightarrow> detector_view"
    and detector_select :: "nat \<Rightarrow> node option" and detector_delay detector_horizon :: nat
  assumes candidate: "c \<in> contenders"
    and triggers: "\<And>t. stalled t \<Longrightarrow> t \<le> reset_failed (next_reset t)
      \<and> reset_failed (next_reset t) \<le> t + retry_bound
      \<and> reset_episode_service contenders bounds loss restore tail
        (reset_failed (next_reset t) + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length)
        (next_reset t)"
    and margin: "reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length < first_limit"
    and own_timer: "window_length < duration + next_limit"
    and limits: "0 < first_limit" "first_limit \<le> (2::nat)^63" "0 < next_limit" "next_limit \<le> (2::nat)^63"
    and dispatch: "extra \<le> timer_queue_delay bounds"
    and stalled_at: "stalled t0"
  defines "start \<equiv> reset_armed (next_reset t0) c
      + earliest_safe_draw (reset_armed (next_reset t0) c) (reset_drained bounds loss tail (next_reset t0)) + extra"
  assumes detector_service: "bounded_service failed (\<lambda>_. {}) detector_select detector_delay detector_horizon"
      "detector_delay \<le> detector_horizon"
    and health: "replacement_candidate r \<in> healthy" "RQ \<subseteq> healthy"
    and quorums: "quorum (committed_voters r) RQ" "quorum (accepted_voters r) RQ"
    and reported: "\<And>n. n \<in> RQ \<inter> failed \<Longrightarrow> can_dispatch (views n)"
    and already: "\<And>n. n \<in> RQ - failed \<Longrightarrow>
      ordinary_prevote (replacement_candidate r) (prevote_incumbent (views n))"
    and recovery_service: "bounded_service (recovery_jobs RQ) (recovery_dependencies RQ) rselect rdelay (3 * rdelay)"
    and eligible: eligible_now
    and fresh_votes: "\<And>n. n \<in> RQ \<Longrightarrow> voter_keys n \<le> candidate_key"
    and chosen: "replacement_candidate r = c" "RQ = E" "committed_voters r = V" "accepted_voters r = V"
    and fresh: "fresh"
    and budget: "3 * rdelay + 12 * delay \<le> window_length"
    and service: "\<And>k. opens_attempt_at start
        (retry_episode Current_Checks r healthy RQ eligible_now candidate_key voter_keys (prevote_incumbent \<circ> views_after_leader_failures (completed_work failed (\<lambda>_. {}) detector_select detector_delay) views)
          {} rselect rdelay) k \<Longrightarrow>
      bounded_service jobs deps (schedule k) delay (12 * delay)"
  obtains k where "t0 < start"
    "start \<le> t0 + retry_bound + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds"
    "opens_attempt_at start (retry_episode Current_Checks r healthy RQ eligible_now candidate_key voter_keys (prevote_incumbent \<circ> views_after_leader_failures (completed_work failed (\<lambda>_. {}) detector_select detector_delay) views)
      {} rselect rdelay) k"
    "k + 12 * delay \<le> start + window_length"
    "h \<in> committed (core (finished (schedule k) (12 * delay)))"
    "installed (window_applier (finished (schedule k) (12 * delay))) = Some key"
    "window_slot (finished (schedule k) (12 * delay)) = None"
proof -
  have handled: "completed_work failed (\<lambda>_. {}) detector_select detector_delay = failed"
    by (rule serviced_leader_failure_batch[OF detector_service])
  have permit: "can_open_attempt Current_Checks r (request_generation r) (start + 3 * rdelay) {} healthy RQ
      (prevote_incumbent \<circ> views_after_leader_failures (completed_work failed (\<lambda>_. {}) detector_select detector_delay) views)"
    unfolding handled by (rule partial_leader_failures_open_prevote_quorum[OF health quorums reported already])
  note permit' = permit[unfolded start_def] and service' = service[unfolded start_def]
  obtain k where "t0 < start"
    "start \<le> t0 + retry_bound + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds"
    "opens_attempt_at start (retry_episode Current_Checks r healthy RQ eligible_now candidate_key voter_keys
      (prevote_incumbent \<circ> views_after_leader_failures (completed_work failed (\<lambda>_. {}) detector_select detector_delay) views) {} rselect rdelay) k"
    "k + 12 * delay \<le> start + window_length"
    "h \<in> committed (core (finished (schedule k) (12 * delay)))"
    "installed (window_applier (finished (schedule k) (12 * delay))) = Some key"
    "window_slot (finished (schedule k) (12 * delay)) = None"
    by (rule stalled_policy_leader_completes[where stalled = stalled and next_reset = next_reset and extra = extra
          and bounds = bounds and loss = loss and restore = restore and tail = tail and retry_bound = retry_bound
          and policy = Current_Checks and r = r and healthy = healthy and RQ = RQ and eligible_now = eligible_now
          and candidate_key = candidate_key and voter_keys = voter_keys and remembered = "prevote_incumbent \<circ> views_after_leader_failures (completed_work failed (\<lambda>_. {}) detector_select detector_delay) views" and reports = "{}"
          and rselect = rselect and rdelay = rdelay,
          OF candidate triggers margin own_timer limits dispatch stalled_at permit' recovery_service eligible
          fresh_votes chosen fresh budget service'])
       (simp_all add: start_def)
  then show thesis by (rule that)
qed

end

section \<open>Stall probability from commit completion\<close>

text \<open>
  The probability theorem for serviced retries needs two facts about the stalled
  executions. They shrink, and a successful timer window removes an execution
  from them. Here an execution stays stalled only while no earlier attempt has
  completed a first publication. A successful timer window, with a permitted and
  serviced recovery episode, completes one, so both facts follow.
\<close>

context fixed_publication_window
begin

theorem stalled_mass_tends_to_zero_from_commit:
  fixes mass :: "'execution set \<Rightarrow> real"
    and sampled :: "nat \<Rightarrow> 'execution \<Rightarrow> timer_sample"
    and stalled :: "nat \<Rightarrow> 'execution set"
    and reset :: "nat \<Rightarrow> timer_reset_episode"
    and recov :: "nat \<Rightarrow> 'execution \<Rightarrow> recovery_episode"
    and sched :: "nat \<Rightarrow> 'execution \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> window_operation option"
    and peers :: "node list" and bounds :: timer_queue_bounds and loss restore tail :: nat and delta :: real
  assumes peers: "set peers = contenders" and candidate: "c \<in> contenders"
    and reset_service: "\<And>n. reset_episode_service contenders bounds loss restore tail
      (reset_failed (reset n) + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length) (reset n)"
    and margin: "reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length < first_limit"
    and own_timer: "window_length < duration + next_limit"
    and nonnegative: "\<And>A. 0 \<le> mass A" and initial_mass: "mass (stalled 0) \<le> 1"
    and mono: "\<And>A B. A \<subseteq> B \<Longrightarrow> mass A \<le> mass B"
    and additive: "\<And>A B. A \<inter> B = {} \<Longrightarrow> mass (A \<union> B) = mass A + mass B"
    and delta: "0 < delta" "delta \<le> 1"
  defines "obs \<equiv> \<lambda>n. phase_observations peers c (reset_armed (reset n))
    (reset_drained bounds loss tail (reset n)) (\<lambda>_. first_limit) next_limit (timer_queue_delay bounds)"
  assumes chance: "\<And>n j. j < length (obs n) \<Longrightarrow>
      delta * mass (stalled n \<inter> sampled n -` matching_prefix (obs n) j)
      \<le> mass (stalled n \<inter> sampled n -` matching_prefix (obs n) (Suc j))"
    and recovery: "\<And>n ex. phase_success contenders c (reset_armed (reset n)) duration
        (reset_pending contenders (reset n)) (reset_drained bounds loss tail (reset n)) window_length (sampled n ex) \<Longrightarrow>
      episode_permission (reset_armed (reset n) c + sample_draws (sampled n ex) c + sample_dispatch (sampled n ex) c) (recov n ex)
      \<and> episode_service (recov n ex)
      \<and> replacement_candidate (episode_round (recov n ex)) = c \<and> episode_quorum (recov n ex) = E
      \<and> committed_voters (episode_round (recov n ex)) = V \<and> accepted_voters (episode_round (recov n ex)) = V
      \<and> 3 * episode_delay (recov n ex) + 12 * delay \<le> window_length
      \<and> (\<forall>k. opens_attempt_at
          (reset_armed (reset n) c + sample_draws (sampled n ex) c + sample_dispatch (sampled n ex) c) (recov n ex) k \<longrightarrow>
          bounded_service jobs deps (sched n ex k) delay (12 * delay))"
    and fresh: "fresh"
    and stalled_step: "\<And>n. stalled (Suc n) = stalled n \<inter>
      {ex. \<not> (\<exists>k. opens_attempt_at
          (reset_armed (reset n) c + sample_draws (sampled n ex) c + sample_dispatch (sampled n ex) c) (recov n ex) k \<and>
        h \<in> committed (core (finished (sched n ex k) (12 * delay))))}"
  shows "(\<lambda>n. mass (stalled n)) \<longlonglongrightarrow> 0"
proof -
  have completion: "stalled (Suc n) \<subseteq> stalled n" for n by (simp add: stalled_step)
  have success: "ex \<notin> stalled (Suc n)"
    if "phase_success contenders c (reset_armed (reset n)) duration (reset_pending contenders (reset n))
      (reset_drained bounds loss tail (reset n)) window_length (sampled n ex)" for n ex
  proof -
    from recovery[OF that] have r: "episode_permission (reset_armed (reset n) c + sample_draws (sampled n ex) c
        + sample_dispatch (sampled n ex) c) (recov n ex)" "episode_service (recov n ex)"
      "replacement_candidate (episode_round (recov n ex)) = c" "episode_quorum (recov n ex) = E"
      "committed_voters (episode_round (recov n ex)) = V" "accepted_voters (episode_round (recov n ex)) = V"
      "3 * episode_delay (recov n ex) + 12 * delay \<le> window_length"
      "\<And>k. opens_attempt_at (reset_armed (reset n) c + sample_draws (sampled n ex) c
        + sample_dispatch (sampled n ex) c) (recov n ex) k \<Longrightarrow> bounded_service jobs deps (sched n ex k) delay (12 * delay)"
      by blast+
    from that have window: "timer_window contenders c (reset_armed (reset n)) (sample_draws (sampled n ex))
      (sample_dispatch (sampled n ex)) duration (sample_own_next (sampled n ex))
      (reset_pending contenders (reset n)) (reset_drained bounds loss tail (reset n)) window_length"
      by (simp add: phase_success_def)
    obtain k where "opens_attempt_at (reset_armed (reset n) c + sample_draws (sampled n ex) c
        + sample_dispatch (sampled n ex) c) (recov n ex) k"
      "h \<in> committed (core (finished (sched n ex k) (12 * delay)))"
      by (rule recovered_timer_window_completes[OF window refl r(1,2) r(3,4,5,6) fresh r(7) r(8)]) blast
    then show ?thesis by (auto simp: stalled_step)
  qed
  show ?thesis
    by (rule serviced_timer_retries_tend_to_succeed[where mass = mass and sampled = sampled and stalled = stalled
        and episode = reset and peers = peers and c = c and bounds = bounds and loss = loss and restore = restore
        and tail = tail and first_limit = first_limit and next_limit = next_limit and duration = duration
        and window_length = window_length and delta = delta,
        OF peers candidate reset_service margin own_timer nonnegative initial_mass mono additive delta chance[unfolded obs_def]
        completion success])
qed

end

section \<open>The queue's task machine as a projection of the worker handoff\<close>

text \<open>
  The handoff trace starts once the batch has claimed its task. The queue's
  task machine starts with the task queued. Prefixing the acquisition event and
  mapping each handoff event to the task event it produces gives one input
  stream for the task machine. The two projections then agree at every tick,
  which is what was assumed when the queue theorem's transaction and notify
  premises were left open.
\<close>

definition handoff_queue_input where
  "handoff_queue_input init input j =
    (case j of 0 \<Rightarrow> Some Acquire_Task
     | Suc j' \<Rightarrow> handoff_task_event (input j') (worker_handoff_trace init input j'))"

lemma handoff_queue_projection:
  assumes init: "init = Handoff_Claimed"
    and no_exception: "\<And>j. planned_handoff_verdict (worker_handoff_trace init input j) \<noteq>
      Some (Handoff_Omit Unexpected_Publication_Exception)"
  shows "master_task_trace (handoff_queue_input init input) (Suc j) =
    handoff_master_task (worker_handoff_trace init input j)"
proof (induction j)
  case 0
  show ?case by (simp add: handoff_queue_input_def init)
next
  case (Suc j)
  have step: "worker_handoff_trace init input (Suc j) = worker_handoff_step (input j) (worker_handoff_trace init input j)"
    by simp
  have proj: "handoff_master_task (worker_handoff_trace init input (Suc j)) =
    (case handoff_task_event (input j) (worker_handoff_trace init input j) of
      None \<Rightarrow> handoff_master_task (worker_handoff_trace init input j)
    | Some useful \<Rightarrow> master_task_step useful (handoff_master_task (worker_handoff_trace init input j)))"
    unfolding step by (rule worker_handoff_task_projection) (use no_exception[of "Suc j"] step in simp)
  have M: "master_task_trace (handoff_queue_input init input) (Suc (Suc j)) =
    (case handoff_task_event (input j) (worker_handoff_trace init input j) of
      None \<Rightarrow> master_task_trace (handoff_queue_input init input) (Suc j)
    | Some ev \<Rightarrow> master_task_step ev (master_task_trace (handoff_queue_input init input) (Suc j)))"
    by (simp only: master_task_trace.simps(2) handoff_queue_input_def nat.simps(5))
  show ?case by (simp only: M Suc.IH proj)
qed

lemma published_clear_avoids_unexpected_exception:
  assumes "worker_handoff_trace init input i = Handoff_Cleared Handoff_Published"
  shows "planned_handoff_verdict (worker_handoff_trace init input j) \<noteq>
    Some (Handoff_Omit Unexpected_Publication_Exception)"
proof (cases "i \<le> j")
  case True
  from worker_handoff_verdict_from[OF True, of init input "Handoff_Deliver Task_Published"] assms
  show ?thesis by simp
next
  case False
  then have "j \<le> i" by simp
  from worker_handoff_rank_mono[OF this, of init input] assms
  have rank: "6 \<le> worker_handoff_rank (worker_handoff_trace init input j)" by simp
  show ?thesis
  proof (cases "worker_handoff_rank (worker_handoff_trace init input j) = 6")
    case True
    from worker_handoff_phase_still[OF \<open>j \<le> i\<close>, of init input] True assms
    have "worker_handoff_trace init input i = worker_handoff_trace init input j" by simp
    with assms show ?thesis by simp
  next
    case False
    with rank have "7 \<le> worker_handoff_rank (worker_handoff_trace init input j)" by simp
    then show ?thesis by (cases "worker_handoff_trace init input j") simp_all
  qed
qed

theorem published_clear_delivers_to_queue_task:
  assumes service: "worker_handoff_bounded_service init input B"
    and init: "init = Handoff_Claimed"
    and cleared: "worker_handoff_trace init input i = Handoff_Cleared Handoff_Published"
  shows "master_task_trace (handoff_queue_input init input) (Suc (i + 6 * B)) = Task_Delivered Task_Published"
proof -
  from cleared_publication_to_next_queue_round[OF service cleared] obtain decision where
    task: "handoff_master_task (worker_handoff_trace init input (i + 6 * B)) =
      (case publication_handoff_verdict Handoff_Published of
        Handoff_Deliver result \<Rightarrow> Task_Delivered result | Handoff_Omit why \<Rightarrow> Task_Dropped)" by blast
  have "handoff_master_task (worker_handoff_trace init input (i + 6 * B)) = Task_Delivered Task_Published"
    using task by simp
  then show ?thesis
    by (rule trans[OF handoff_queue_projection[OF init published_clear_avoids_unexpected_exception[OF cleared]]])
qed

lemma worker_clear_callback_clears:
  assumes "worker_handoff_trace init input j = Handoff_Owns_Slot"
    "input j = Clear_Own_Publication out"
  shows "worker_handoff_trace init input (Suc j) = Handoff_Cleared out"
  using assms by simp

lemma worker_install_then_owns:
  assumes "worker_handoff_trace init input j = Handoff_Claimed" "input j = Install_Publication"
  shows "worker_handoff_trace init input (Suc j) = Handoff_Owns_Slot"
  using assms by simp

context fixed_publication_window
begin

theorem stalled_default_task_delivered_in_queue:
  fixes stalled :: "nat \<Rightarrow> bool" and next_reset :: "nat \<Rightarrow> timer_reset_episode"
    and episode :: "nat \<Rightarrow> recovery_episode" and extra :: nat
    and bounds :: timer_queue_bounds and loss restore tail retry_bound :: nat
    and init :: worker_handoff_phase and input :: "nat \<Rightarrow> worker_handoff_event"
    and handoff_bound release_lag :: nat
  assumes candidate: "c \<in> contenders"
    and triggers: "\<And>t0. stalled t0 \<Longrightarrow> t0 \<le> reset_failed (next_reset t0)
      \<and> reset_failed (next_reset t0) \<le> t0 + retry_bound
      \<and> reset_episode_service contenders bounds loss restore tail
        (reset_failed (next_reset t0) + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length)
        (next_reset t0)"
    and margin: "reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length < first_limit"
    and own_timer: "window_length < duration + next_limit"
    and limits: "0 < first_limit" "first_limit \<le> (2::nat)^63" "0 < next_limit" "next_limit \<le> (2::nat)^63"
    and dispatch: "extra \<le> timer_queue_delay bounds"
    and stalled_at: "stalled t0"
  defines "start \<equiv> reset_armed (next_reset t0) c
      + earliest_safe_draw (reset_armed (next_reset t0) c) (reset_drained bounds loss tail (next_reset t0)) + extra"
  assumes permission: "episode_permission start (episode t0)" "episode_service (episode t0)"
    and chosen: "replacement_candidate (episode_round (episode t0)) = c" "episode_quorum (episode t0) = E"
      "committed_voters (episode_round (episode t0)) = V" "accepted_voters (episode_round (episode t0)) = V"
    and fresh: "fresh"
    and budget: "3 * episode_delay (episode t0) + 12 * delay \<le> window_length"
    and service: "\<And>k. opens_attempt_at start (episode t0) k \<Longrightarrow>
      bounded_service jobs deps (schedule k) delay (12 * delay)"
    and worker: "worker_handoff_bounded_service init input handoff_bound"
    and claimed: "init = Handoff_Claimed"
    and holds_slot: "\<And>k. opens_attempt_at start (episode t0) k \<Longrightarrow>
      window_slot (finished (schedule k) (12 * delay)) = None \<Longrightarrow>
      \<exists>tk. tk < k + 12 * delay + release_lag \<and> worker_handoff_trace init input tk = Handoff_Owns_Slot \<and>
        input tk = Clear_Own_Publication Handoff_Published"
  obtains k tk where "t0 < start"
    "opens_attempt_at start (episode t0) k"
    "h \<in> committed (core (finished (schedule k) (12 * delay)))"
    "installed (window_applier (finished (schedule k) (12 * delay))) = Some key"
    "window_slot (finished (schedule k) (12 * delay)) = None"
    "tk < k + 12 * delay + release_lag"
    "master_task_trace (handoff_queue_input init input) (Suc (Suc tk + 6 * handoff_bound)) = Task_Delivered Task_Published"
proof -
  note permission' = permission[unfolded start_def]
  note service' = service[unfolded start_def]
  obtain k where k: "t0 < start" "opens_attempt_at start (episode t0) k"
    "h \<in> committed (core (finished (schedule k) (12 * delay)))"
    "installed (window_applier (finished (schedule k) (12 * delay))) = Some key"
    "window_slot (finished (schedule k) (12 * delay)) = None"
    by (rule stalled_default_leader_completes[where stalled = stalled and next_reset = next_reset and episode = episode
          and extra = extra and bounds = bounds and loss = loss and restore = restore and tail = tail
          and retry_bound = retry_bound, OF candidate triggers margin own_timer limits(1,2,3,4) dispatch
          stalled_at permission' chosen fresh budget service'])
       (simp_all add: start_def)
  from holds_slot[OF k(2) k(5)] obtain tk where tk: "tk < k + 12 * delay + release_lag"
    and owns: "worker_handoff_trace init input tk = Handoff_Owns_Slot"
    and clear: "input tk = Clear_Own_Publication Handoff_Published" by blast
  have cleared: "worker_handoff_trace init input (Suc tk) = Handoff_Cleared Handoff_Published"
    by (rule worker_clear_callback_clears[OF owns clear])
  have "master_task_trace (handoff_queue_input init input) (Suc (Suc tk + 6 * handoff_bound)) = Task_Delivered Task_Published"
    by (rule published_clear_delivers_to_queue_task[OF worker claimed cleared])
  then show thesis by (rule that[OF k(1,2,3,4,5) tk])
qed

end

section \<open>Stateless: from a stall to slot release and the next publication\<close>

text \<open>
  The stall gives a timer window and an attempt start. The candidate then claims
  the lease, searches the changing storage view and publishes under the granted
  term. The publication's slot is released after local application, and the same
  term then publishes a strictly newer descendant. The ticks of the slot trace
  begin at the attempt start. The window budget keeps every rival timer and
  pending deadline outside the whole run.
\<close>

theorem stalled_stateless_to_next_publication:
  fixes stalled :: "nat \<Rightarrow> bool" and next_reset :: "nat \<Rightarrow> timer_reset_episode" and extra :: nat
    and bounds :: timer_queue_bounds and loss restore tail retry_bound t0 :: nat
    and y :: "stateless_slot_state \<Rightarrow> stateless_execution"
    and result :: "lease_bytes option"
    and selected :: "nat \<Rightarrow> state_manifest option"
    and t reads gap A B C B' C' G :: nat
    and prepare prepare' :: "nat \<Rightarrow> nat option" and m m' :: state_manifest
  defines "t \<equiv> lease_term (lease_value result)"
    and "reads \<equiv> stable_probe_count (header_choices selected) (t - 1) + gap + 1"
  assumes candidate: "n \<in> contenders"
    and triggers: "\<And>t. stalled t \<Longrightarrow> t \<le> reset_failed (next_reset t)
      \<and> reset_failed (next_reset t) \<le> t + retry_bound
      \<and> reset_episode_service contenders bounds loss restore tail
        (reset_failed (next_reset t) + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length)
        (next_reset t)"
    and margin: "reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length < first_limit"
    and own_timer: "window_length < duration + next_limit"
    and limits: "0 < first_limit" "first_limit \<le> (2::nat)^63" "0 < next_limit" "next_limit \<le> (2::nat)^63"
    and dispatch: "extra \<le> timer_queue_delay bounds"
    and stalled_at: "stalled t0"
    and reached: "stateless_slot_reachable n st"
    and idle: "active_slot st = None" "\<not> slot_leading st"
    and proposal: "max max_seen (app_term (processes (slot_exec st) n)) < proposed"
    and effect: "lease_effect provider before live expected (Claim_Term (endpoint (slot_exec st) n) proposed) result"
    and rep: "lease_term (lease_value live) = reserved_term (shared_state (slot_exec st))"
    and warm: "warm \<in> insert [] (issued (shared_state (slot_exec st)))"
      "app_accepted (processes (slot_exec st) n) = position warm"
    and claim_service: "bounded_service {..<(5::nat)} (\<lambda>i. {..<i}) claim G claim_horizon"
    and claim_time: "5 * G \<le> claim_horizon"
    and recipe: "\<And>r. stateless_claim_search_start n t warm r \<Longrightarrow>
      changing_view_slot_publication r n (t - 1) t selected views replies gap (y r) warm base payload F m files"
    and search_service: "bounded_service {..<reads} (\<lambda>i. {..<i}) lookups A search_horizon"
    and search_time: "reads * A \<le> search_horizon"
    and publication_service: "bounded_service {..<(16::nat)} (\<lambda>i. {..<i}) prepare B publication_horizon"
    and publication_time: "16 * B \<le> publication_horizon"
    and completion: "bounded_service (completion_jobs (position (manifest_history m)))
      (completion_dependencies (position (manifest_history m))) callbacks C completion_horizon"
    and completion_time: "3 * C \<le> completion_horizon"
    and maximum: "max_seen \<le> t" and retain: "retain"
    and next_recipe: "\<And>r. stateless_claim_search_start n t warm r \<Longrightarrow>
      manifest_history m' = stateless_update (endpoint (y r) n) t payload' F'
        (stateless_update (endpoint (y r) n) t payload F base) \<and> files_match files' m'"
    and next_issue: "bounded_service {..<(16::nat)} (\<lambda>i. {..<i}) prepare' B' issue_horizon'"
    and next_time: "16 * B' \<le> issue_horizon'"
    and next_completion: "bounded_service (completion_jobs (position (manifest_history m')))
      (completion_dependencies (position (manifest_history m'))) callbacks' C' completion_horizon'"
    and next_completion_time: "3 * C' \<le> completion_horizon'"
    and budget: "5 * G + (Suc (reads * A + (16 * B + 3 * C)) + (16 * B' + 3 * C')) \<le> window_length"
  obtains run draws where "t0 < reset_armed (next_reset t0) n + draws n + extra"
    "reset_armed (next_reset t0) n + draws n + extra
      \<le> t0 + retry_bound + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds"
    "run 0 = st" "\<And>j. next_slot_move n (run j) (run (Suc j))"
    "manifest_history m \<in> notifications (shared_state (slot_exec (run (5 * G + (reads * A + (16 * B + 3 * C))))))"
    "installed (processes (slot_exec (run (5 * G + (reads * A + (16 * B + 3 * C))))) n)
      = Some (position (manifest_history m))"
    "active_slot (run (5 * G + (reads * A + (16 * B + 3 * C)))) = None"
    "stateless_next_ready n t (manifest_history m) (run (5 * G + Suc (reads * A + (16 * B + 3 * C))))"
    "prefix (manifest_history m) (manifest_history m')"
    "position (manifest_history m) < position (manifest_history m')"
    "manifest_history m' \<in> notifications (shared_state (slot_exec
      (run (5 * G + (Suc (reads * A + (16 * B + 3 * C)) + (16 * B' + 3 * C'))))))"
    "stateless_next_ready n t (manifest_history m')
      (run (5 * G + (Suc (reads * A + (16 * B + 3 * C)) + (16 * B' + 3 * C'))))"
    "\<And>n'. n' \<in> contenders - {n} \<Longrightarrow>
      reset_armed (next_reset t0) n + draws n + extra
        + (5 * G + (Suc (reads * A + (16 * B + 3 * C)) + (16 * B' + 3 * C')))
      < reset_armed (next_reset t0) n' + draws n' + extra"
proof -
  obtain draws where draws: "draws n = earliest_safe_draw (reset_armed (next_reset t0) n)
      (reset_drained bounds loss tail (next_reset t0))"
    and window: "timer_window contenders n (reset_armed (next_reset t0)) draws (\<lambda>_. extra) duration next_limit
      (reset_pending contenders (next_reset t0)) (reset_drained bounds loss tail (next_reset t0)) window_length"
    and after: "t0 < reset_armed (next_reset t0) n + draws n + extra"
    and before: "reset_armed (next_reset t0) n + draws n + extra
      \<le> t0 + retry_bound + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds"
    by (rule stalled_timer_window[where stalled = stalled and next_reset = next_reset and extra = extra
          and bounds = bounds and loss = loss and restore = restore and tail = tail and retry_bound = retry_bound
          and c = n, OF candidate triggers margin own_timer limits dispatch stalled_at])
  obtain r where r: "r 0 = st" "\<And>j. next_slot_move n (r j) (r (Suc j))"
    and entry: "stateless_claim_search_start n t warm (r (5 * G))"
    unfolding stateless_claim_search_start_def t_def
    by (rule fresh_grant_restarts_changing_view_recovery[
      OF reached idle proposal effect rep warm claim_service claim_time]) blast
  let ?ready = "r (5 * G)"
  interpret recovery: changing_view_slot_publication ?ready n "t - 1" t selected views replies
    gap "y ?ready" warm base payload F m files
    by (rule recipe[OF entry])
  have history: "manifest_history m = stateless_update (endpoint (y ?ready) n) t payload F base"
    by (rule recovery.image(1))
  have search_service': "bounded_service {..<stable_probe_count (header_choices selected) (t - 1) + gap + 1}
      (\<lambda>i. {..<i}) lookups A search_horizon"
    and search_time': "(stable_probe_count (header_choices selected) (t - 1) + gap + 1) * A \<le> search_horizon"
    using search_service search_time by (simp_all add: reads_def)
  have completion': "bounded_service
      (completion_jobs (position (stateless_update (endpoint (y ?ready) n) t payload F base)))
      (completion_dependencies (position (stateless_update (endpoint (y ?ready) n) t payload F base)))
      callbacks C completion_horizon"
    using completion by (simp only: history)
  have nxt: "manifest_history m' = stateless_update (endpoint (y ?ready) n) t payload' F'
      (stateless_update (endpoint (y ?ready) n) t payload F base)" "files_match files' m'"
    using next_recipe[OF entry] by blast+
  have nh: "manifest_history m' = stateless_update (endpoint (y ?ready) n) t payload' F' recovery.h"
    using nxt(1) by simp
  have next_completion': "bounded_service
      (completion_jobs (position (manifest_history m')))
      (completion_dependencies (position (manifest_history m'))) callbacks' C' completion_horizon'"
    by (rule next_completion)
  obtain u where u: "u 0 = ?ready" "\<And>j. next_slot_move n (u j) (u (Suc j))"
    and out: "manifest_history m \<in> notifications (shared_state (slot_exec (u (reads * A + (16 * B + 3 * C)))))"
      "installed (processes (slot_exec (u (reads * A + (16 * B + 3 * C)))) n) = Some (position (manifest_history m))"
      "active_slot (u (reads * A + (16 * B + 3 * C))) = None"
      "stateless_next_ready n t (manifest_history m) (u (Suc (reads * A + (16 * B + 3 * C))))"
      "prefix (manifest_history m) (manifest_history m')"
      "position (manifest_history m) < position (manifest_history m')"
      "manifest_history m' \<in> notifications (shared_state (slot_exec
        (u (Suc (reads * A + (16 * B + 3 * C)) + (16 * B' + 3 * C')))))"
      "stateless_next_ready n t (manifest_history m')
        (u (Suc (reads * A + (16 * B + 3 * C)) + (16 * B' + 3 * C')))"
    unfolding reads_def history
    by (rule recovery.changing_view_recovery_then_next_publication[where h' = "manifest_history m'"
        and payload' = payload' and F' = F' and m' = m' and files' = files',
      OF search_service' search_time' publication_service publication_time completion' completion_time
      maximum retain nh refl nxt(2) next_issue next_time next_completion' next_completion_time]) blast
  have link: "?ready = u 0" by (simp add: u(1))
  note joined = concatenate_next_traces[where r = r and s = u and k = "5 * G", OF r(2) u(2) link]
  let ?run = "\<lambda>j. if j < 5 * G then r j else u (j - 5 * G)"
  have at: "\<And>j. ?run (5 * G + j) = u j" using joined(3) by simp
  have rivals: "\<And>n'. n' \<in> contenders - {n} \<Longrightarrow>
      reset_armed (next_reset t0) n + draws n + extra
        + (5 * G + (Suc (reads * A + (16 * B + 3 * C)) + (16 * B' + 3 * C')))
      < reset_armed (next_reset t0) n' + draws n' + extra"
  proof -
    fix n'
    assume n': "n' \<in> contenders - {n}"
    note cuts = timer_window_deadlines[OF window refl]
    have "reset_armed (next_reset t0) n + draws n + extra + window_length
        < reset_armed (next_reset t0) n' + draws n' + extra"
      using bspec[OF cuts(2) n'] by simp
    with budget show "reset_armed (next_reset t0) n + draws n + extra
        + (5 * G + (Suc (reads * A + (16 * B + 3 * C)) + (16 * B' + 3 * C')))
      < reset_armed (next_reset t0) n' + draws n' + extra" by linarith
  qed
  show thesis
    by (rule that[where run = "?run" and draws = draws, OF after before _ joined(2)])
      (use joined(1) r(1) at out rivals in \<open>simp_all add: add.assoc\<close>)
qed

end
