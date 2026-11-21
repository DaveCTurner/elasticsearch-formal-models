theory Production_Timer_Cut_Recurrence
  imports Production_Timer_Liveness
begin

section \<open>Closing an old scheduler and arming a fresh one\<close>

text \<open>
  The projection is local to each contender. In Coordinator, entering
  candidacy after a failed publication can leave the election scheduler
  open. A peer update processed in candidate mode with no visible
  election quorum closes and clears that scheduler. A later update with
  a visible quorum opens a new scheduler for a master-eligible node,
  with zero grace and attempt zero. The latter uses the initial jitter
  bound, even if the old scheduler had already reached its cap.

  DefaultBuiltInExecutorBuilders supplies one cluster_coordination
  worker per node and an unbounded queue. The finite number of jobs
  ahead of a particular reset callback is a service premise. The
  remaining time of a busy worker and each job's wait for the Coordinator
  mutex and execution time have separate bounds. In particular, another
  thread holding the mutex indefinitely would invalidate the premise.
\<close>

record timer_queue_bounds =
  timer_backlog :: nat
  timer_worker_residual :: nat
  timer_mutex_wait :: nat
  timer_job_run :: nat

definition timer_queue_delay where
  "timer_queue_delay bounds = timer_worker_residual bounds
    + Suc (timer_backlog bounds) * (timer_mutex_wait bounds + timer_job_run bounds)"

definition serviced_timer_job where
  "serviced_timer_job bounds ready done \<longleftrightarrow>
    (\<exists>ahead boundary lock.
      ahead \<le> timer_backlog bounds \<and>
      ready \<le> boundary 0 \<and> boundary 0 \<le> ready + timer_worker_residual bounds \<and>
      boundary (Suc ahead) = done \<and>
      (\<forall>i\<le>ahead. boundary i \<le> lock i \<and> lock i \<le> boundary i + timer_mutex_wait bounds
        \<and> lock i \<le> boundary (Suc i) \<and> boundary (Suc i) \<le> lock i + timer_job_run bounds))"

lemma serviced_timer_job_bounds:
  assumes "serviced_timer_job bounds ready done"
  shows "ready \<le> done" "done \<le> ready + timer_queue_delay bounds"
proof -
  let ?step = "timer_mutex_wait bounds + timer_job_run bounds"
  from assms obtain ahead boundary lock where
    ahead: "ahead \<le> timer_backlog bounds" and initial: "ready \<le> boundary 0"
    "boundary 0 \<le> ready + timer_worker_residual bounds"
    and completed: "boundary (Suc ahead) = done"
    and steps: "\<And>i. i \<le> ahead \<Longrightarrow>
      boundary i \<le> lock i \<and> lock i \<le> boundary i + timer_mutex_wait bounds
        \<and> lock i \<le> boundary (Suc i) \<and> boundary (Suc i) \<le> lock i + timer_job_run bounds"
    unfolding serviced_timer_job_def by blast
  have walk: "ready \<le> boundary i \<and> boundary i \<le> boundary 0 + i * ?step"
    if "i \<le> Suc ahead" for i
    using that
  proof (induction i)
    case 0
    then show ?case using initial by simp
  next
    case (Suc i)
    then have "i \<le> ahead" "i \<le> Suc ahead" by simp_all
    from steps[OF this(1)] Suc.IH[OF this(2)] show ?case
      by (simp add: algebra_simps; arith)
  qed
  from walk[OF le_refl] show "ready \<le> done" unfolding completed by blast
  have "Suc ahead * ?step \<le> Suc (timer_backlog bounds) * ?step"
    by (rule mult_right_mono) (use ahead in simp_all)
  with walk[OF le_refl] initial(2) show "done \<le> ready + timer_queue_delay bounds"
    unfolding completed timer_queue_delay_def by linarith
qed

record timer_peer_view =
  timer_peer_candidate :: bool
  timer_peer_master_eligible :: bool
  timer_peer_quorum_visible :: bool

definition scheduler_after_peer_update :: "timer_peer_view \<Rightarrow> nat \<Rightarrow> nat option \<Rightarrow> nat option" where
  "scheduler_after_peer_update view fresh current_generation =
    (if \<not> timer_peer_candidate view then current_generation
     else if \<not> timer_peer_quorum_visible view then None
     else if current_generation = None \<and> timer_peer_master_eligible view then Some fresh
     else current_generation)"

lemma peer_quorum_loss_and_restore:
  assumes "timer_peer_candidate lost" "\<not> timer_peer_quorum_visible lost"
    "timer_peer_candidate restored" "timer_peer_quorum_visible restored" "timer_peer_master_eligible restored"
  shows "scheduler_after_peer_update lost fresh (Some old) = None"
    "scheduler_after_peer_update restored fresh None = Some fresh"
  using assms by (simp_all add: scheduler_after_peer_update_def)

record timer_reset_episode =
  reset_failed :: nat
  reset_loss_ready :: "node \<Rightarrow> nat"
  reset_closed :: "node \<Rightarrow> nat"
  reset_restore_ready :: "node \<Rightarrow> nat"
  reset_armed :: "node \<Rightarrow> nat"
  reset_old_generation :: "node \<Rightarrow> nat"
  reset_fresh_generation :: "node \<Rightarrow> nat"
  reset_loss_view :: "node \<Rightarrow> timer_peer_view"
  reset_restore_view :: "node \<Rightarrow> timer_peer_view"
  reset_old_work :: "prior_timer_work set"

definition reset_spread where
  "reset_spread bounds loss restore = loss + timer_queue_delay bounds + restore + timer_queue_delay bounds"

definition reset_drain_slack where
  "reset_drain_slack bounds loss tail = loss + timer_queue_delay bounds + timer_queue_delay bounds + tail"

definition reset_episode_service where
  "reset_episode_service contenders bounds loss restore tail early_deadline episode \<longleftrightarrow>
    (\<forall>n\<in>contenders.
      scheduler_after_peer_update (reset_loss_view episode n) (reset_fresh_generation episode n)
        (Some (reset_old_generation episode n)) = None \<and>
      scheduler_after_peer_update (reset_restore_view episode n) (reset_fresh_generation episode n) None
        = Some (reset_fresh_generation episode n) \<and>
      reset_fresh_generation episode n \<notin> reset_old_generation episode ` contenders \<and>
      reset_failed episode \<le> reset_loss_ready episode n \<and>
      reset_loss_ready episode n \<le> reset_failed episode + loss \<and>
      serviced_timer_job bounds (reset_loss_ready episode n) (reset_closed episode n) \<and>
      reset_closed episode n \<le> reset_restore_ready episode n \<and>
      reset_restore_ready episode n \<le> reset_closed episode n + restore \<and>
      serviced_timer_job bounds (reset_restore_ready episode n) (reset_armed episode n)) \<and>
    (\<forall>g due. Queued_Election g due \<in> reset_old_work episode \<longrightarrow>
      g \<in> reset_old_generation episode ` contenders \<or> early_deadline < due) \<and>
    (\<forall>finish. Past_Election_Guard finish \<in> reset_old_work episode \<longrightarrow>
      (\<exists>n\<in>contenders. \<exists>guard returned.
        guard \<le> reset_closed episode n \<and> serviced_timer_job bounds guard returned
        \<and> returned \<le> finish \<and> finish \<le> returned + tail)) \<and>
    (\<forall>due. Publication_Deadline due \<in> reset_old_work episode \<longrightarrow> early_deadline < due)"

text \<open>
  The episode premises describe observed candidate, peer-loss and
  peer-restoration callbacks of the reset path. Generation identities
  refer to scheduler instances across nodes. For the
  guarded timer work, ElectionSchedulerFactory.close only changes
  isClosed. A queued callback for a closed generation still takes a
  worker turn. It has no election effect if it sees closure at its
  first guard. Its worker time is included in the backlog or residual
  estimates. A callback that saw the open generation before closure
  may still run Coordinator's runnable under the mutex and may leave
  an asynchronous pre-vote tail. The projection records that callback
  as Past_Election_Guard and bounds the end of its effects. Work created
  by its re-arm is tracked at its own guard. An independently live
  timer, including any uncancelled publication timeout, keeps its
  deadline.

  Episodes account for all relevant earlier election work and
  deadlines, and the service inside a successful window must exclude
  any further disruptions outside this projection. A peer update that
  observes a quorum throughout does not traverse this reset path.
\<close>

lemma serviced_episode_bounds:
  assumes episode: "reset_episode_service contenders bounds loss restore tail early_deadline e"
  defines "drained \<equiv> reset_failed e + reset_drain_slack bounds loss tail"
    and "open_old \<equiv> -(reset_old_generation e ` contenders)"
  shows "\<And>n. n \<in> contenders \<Longrightarrow>
      reset_failed e \<le> reset_armed e n \<and> reset_armed e n \<le> reset_failed e + reset_spread bounds loss restore"
    "drain_guarantee (reset_old_work e) drained"
    "\<And>due. due \<in> pending_timer_deadlines open_old (reset_old_work e) \<Longrightarrow> early_deadline < due"
proof -
  let ?d = "timer_queue_delay bounds"
  have close_upper: "reset_closed e n \<le> reset_failed e + loss + ?d"
    and close_lower: "reset_failed e \<le> reset_closed e n" if "n \<in> contenders" for n
  proof -
    from episode that have loss: "reset_failed e \<le> reset_loss_ready e n"
      "reset_loss_ready e n \<le> reset_failed e + loss"
      and close: "serviced_timer_job bounds (reset_loss_ready e n) (reset_closed e n)"
      by (auto simp: reset_episode_service_def)
    from serviced_timer_job_bounds[OF close] loss show
      "reset_closed e n \<le> reset_failed e + loss + ?d" "reset_failed e \<le> reset_closed e n"
      by linarith+
  qed
  show "reset_failed e \<le> reset_armed e n \<and> reset_armed e n \<le> reset_failed e + reset_spread bounds loss restore"
    if "n \<in> contenders" for n
  proof -
    from episode that obtain
      "reset_closed e n \<le> reset_restore_ready e n"
      "reset_restore_ready e n \<le> reset_closed e n + restore"
      "serviced_timer_job bounds (reset_restore_ready e n) (reset_armed e n)"
      by (auto simp: reset_episode_service_def)
    from this(1,2) serviced_timer_job_bounds[OF this(3)] close_lower[OF that] close_upper[OF that]
    show ?thesis unfolding reset_spread_def by arith
  qed
  show "drain_guarantee (reset_old_work e) drained"
    unfolding drain_guarantee_def
  proof (intro allI impI)
    fix finish
    assume "Past_Election_Guard finish \<in> reset_old_work e"
    from episode this obtain n guard returned where "n \<in> contenders" "guard \<le> reset_closed e n"
      "serviced_timer_job bounds guard returned" "finish \<le> returned + tail"
      unfolding reset_episode_service_def by blast
    from this(2,4) serviced_timer_job_bounds(2)[OF this(3)] close_upper[OF this(1)]
    show "finish \<le> drained" unfolding drained_def reset_drain_slack_def by linarith
  qed
  show "early_deadline < due" if "due \<in> pending_timer_deadlines open_old (reset_old_work e)" for due
    using episode that unfolding pending_timer_deadlines_def open_old_def reset_episode_service_def by blast
qed

section \<open>Repeated reset opportunities\<close>

definition reset_cut_slack where
  "reset_cut_slack bounds loss restore tail =
    max (reset_spread bounds loss restore + 1) (reset_drain_slack bounds loss tail)"

abbreviation reset_drained where
  "reset_drained bounds loss tail e \<equiv> reset_failed e + reset_drain_slack bounds loss tail"

abbreviation reset_pending where
  "reset_pending contenders e \<equiv>
    pending_timer_deadlines (-(reset_old_generation e ` contenders)) (reset_old_work e)"

theorem serviced_reset_timer_cut:
  assumes candidate: "c \<in> contenders"
    and episode: "reset_episode_service contenders bounds loss restore tail
      (reset_failed e + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length) e"
    and margin: "reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length < first_limit"
    and own_timer: "window_length < duration + next_limit"
  shows "postfailure_cut contenders c (reset_armed e) (reset_drained bounds loss tail e) (\<lambda>_. first_limit)
    next_limit duration (reset_pending contenders e) (timer_queue_delay bounds) window_length"
    "reset_failed e < reset_armed e c + earliest_safe_draw (reset_armed e c) (reset_drained bounds loss tail e)"
    "reset_armed e c + earliest_safe_draw (reset_armed e c) (reset_drained bounds loss tail e)
      \<le> reset_failed e + reset_cut_slack bounds loss restore tail"
proof -
  let ?slack = "reset_cut_slack bounds loss restore tail"
  let ?drained = "reset_drained bounds loss tail e"
  let ?draw = "earliest_safe_draw (reset_armed e c) ?drained"
  let ?due = "reset_armed e c + ?draw"
  from serviced_episode_bounds(1)[OF episode candidate] have c:
    "reset_failed e \<le> reset_armed e c" "reset_armed e c \<le> reset_failed e + reset_spread bounds loss restore"
    by blast+
  have due_bound: "?due \<le> reset_failed e + ?slack"
    using c unfolding earliest_safe_draw_def reset_cut_slack_def max_def by (auto split: if_splits; arith)
  then show "?due \<le> reset_failed e + ?slack" .
  show "reset_failed e < ?due" using earliest_safe_draw_lower_bound(1)[of "reset_armed e c" ?drained] c(1) by linarith
  have first: "?draw \<le> first_limit" using c(1) margin due_bound by linarith
  have peers: "?due + timer_queue_delay bounds + window_length < reset_armed e n + first_limit"
    if "n \<in> contenders - {c}" for n
  proof -
    from that have "n \<in> contenders" by simp
    from serviced_episode_bounds(1)[OF episode this] due_bound margin show ?thesis by arith
  qed
  have pending: "?due + timer_queue_delay bounds + window_length < deadline"
    if "deadline \<in> reset_pending contenders e" for deadline
    using serviced_episode_bounds(3)[OF episode that] due_bound by linarith
  from candidate own_timer first peers pending
  show "postfailure_cut contenders c (reset_armed e) ?drained (\<lambda>_. first_limit)
    next_limit duration (reset_pending contenders e) (timer_queue_delay bounds) window_length"
    unfolding postfailure_cut_def by blast
qed

corollary serviced_reset_has_legal_window:
  assumes candidate: "c \<in> contenders"
    and episode: "reset_episode_service contenders bounds loss restore tail
      (reset_failed e + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length) e"
    and limits: "0 < initial_delay" "0 < cap" "cap \<le> 2^63"
    and margin: "reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length
      < retry_limit initial_delay increment cap 0"
    and own_timer: "window_length < duration + retry_limit initial_delay increment cap 1"
    and dispatch: "extra c \<le> timer_queue_delay bounds"
  defines "first_limits \<equiv> \<lambda>_. retry_limit initial_delay increment cap 0"
    and "next_limit \<equiv> retry_limit initial_delay increment cap 1"
    and "draws \<equiv> phase_draws c (reset_armed e) (reset_drained bounds loss tail e)
      (\<lambda>_. retry_limit initial_delay increment cap 0)"
  shows "\<forall>n\<in>contenders. legal_retry_jitter (first_limits n) (draws n)"
    "legal_retry_jitter next_limit next_limit"
    "timer_window contenders c (reset_armed e) draws extra duration next_limit (reset_pending contenders e)
      (reset_drained bounds loss tail e) window_length"
proof -
  have legal_range: "0 < retry_limit initial_delay increment cap i
    \<and> retry_limit initial_delay increment cap i \<le> 2^63" for i
    using retry_limit_positive[OF limits(1,2), of increment i]
      le_trans[OF retry_limit_capped limits(3), of initial_delay increment i] by blast
  note cut = serviced_reset_timer_cut(1)[OF candidate episode margin own_timer]
  have first_range: "\<And>n. n \<in> contenders \<Longrightarrow> 0 < retry_limit initial_delay increment cap 0
    \<and> retry_limit initial_delay increment cap 0 \<le> 2^63" using legal_range[of 0] .
  note next_range = legal_range[of 1, THEN conjunct1] legal_range[of 1, THEN conjunct2]
  show "\<forall>n\<in>contenders. legal_retry_jitter (first_limits n) (draws n)"
    unfolding first_limits_def draws_def by (rule postfailure_cut_suffices(1)[OF cut first_range next_range])
  show "legal_retry_jitter next_limit next_limit"
    unfolding next_limit_def by (rule postfailure_cut_suffices(2)[OF cut first_range next_range])
  show "timer_window contenders c (reset_armed e) draws extra duration next_limit (reset_pending contenders e)
      (reset_drained bounds loss tail e) window_length"
    unfolding next_limit_def draws_def
    by (rule postfailure_cut_suffices(3)[where extra=extra, OF cut first_range next_range dispatch])
qed

text \<open>
  The time bounded below is the selected nominal due time. The
  dispatch allowance in the cut covers the additional queue delay.
\<close>

theorem recurring_serviced_timer_cuts:
  assumes candidate: "c \<in> contenders"
    and triggers: "\<And>t. stalled t \<Longrightarrow> t \<le> reset_failed (next_reset t)
      \<and> reset_failed (next_reset t) \<le> t + retry_bound
      \<and> reset_episode_service contenders bounds loss restore tail
        (reset_failed (next_reset t) + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length)
        (next_reset t)"
    and margin: "reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length < first_limit"
    and own_timer: "window_length < duration + next_limit"
    and stalled_at: "stalled t"
  defines "e \<equiv> next_reset t"
    and "due \<equiv> reset_armed (next_reset t) c
      + earliest_safe_draw (reset_armed (next_reset t) c) (reset_drained bounds loss tail (next_reset t))"
  shows "t < due"
    "due \<le> t + retry_bound + reset_cut_slack bounds loss restore tail"
    "postfailure_cut contenders c (reset_armed e) (reset_drained bounds loss tail e) (\<lambda>_. first_limit)
      next_limit duration (reset_pending contenders e) (timer_queue_delay bounds) window_length"
proof -
  from triggers[OF stalled_at] have timing: "t \<le> reset_failed e" "reset_failed e \<le> t + retry_bound"
    and service: "reset_episode_service contenders bounds loss restore tail
      (reset_failed e + reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length) e"
    unfolding e_def by blast+
  note cut = serviced_reset_timer_cut[OF candidate service margin own_timer]
  from cut(2,3) timing
  show "t < due" "due \<le> t + retry_bound + reset_cut_slack bounds loss restore tail"
    unfolding due_def e_def by linarith+
  show "postfailure_cut contenders c (reset_armed e) (reset_drained bounds loss tail e) (\<lambda>_. first_limit)
      next_limit duration (reset_pending contenders e) (timer_queue_delay bounds) window_length"
    by (rule cut(1))
qed

section \<open>A synchronised schedule without resets\<close>

abbreviation synchronised_retry_time where
  "synchronised_retry_time duration \<equiv> election_wakeup_times 1 duration (\<lambda>_. 1) (\<lambda>_. 0)"

text \<open>
  Consider two open schedulers on distinct nodes after both observed a
  visible quorum. Each uses a legal draw of one and their workers run
  immediately. If both attempts fail and the visible quorum persists,
  the two schedulers keep re-arming in phase. After the failures both
  next draws have already happened and their timers remain live. This
  is a timer-layer counterexecution. It makes no claim about the
  probability of identical random streams or about which election
  policy or protocol conditions sustain the failed rounds.
\<close>

theorem synchronised_open_schedulers:
  fixes initial increment cap duration window_length :: nat
  assumes initial: "0 < initial" and cap: "0 < cap" "cap \<le> 2^63"
    and member: "c \<in> {0,1}"
  shows "legal_retry_jitter (retry_limit initial increment cap i) 1"
    "rearmed_wakeup duration 1
      \<lparr>retry_due = synchronised_retry_time duration i, retry_handled = synchronised_retry_time duration i\<rparr>
      \<lparr>retry_due = synchronised_retry_time duration (Suc i),
        retry_handled = synchronised_retry_time duration (Suc i)\<rparr>"
    "i \<le> synchronised_retry_time duration i"
    "\<not> timer_window {0,1} c (\<lambda>_. synchronised_retry_time duration i + duration) (\<lambda>_. 1) (\<lambda>_. 0)
      duration 1 {} 0 window_length"
proof -
  show "legal_retry_jitter (retry_limit initial increment cap i) 1"
    using retry_limit_positive[OF initial cap(1), of increment i]
      le_trans[OF retry_limit_capped cap(2), of initial increment i]
    by (simp add: retry_jitter_support)
  show "rearmed_wakeup duration 1
      \<lparr>retry_due = synchronised_retry_time duration i, retry_handled = synchronised_retry_time duration i\<rparr>
      \<lparr>retry_due = synchronised_retry_time duration (Suc i),
        retry_handled = synchronised_retry_time duration (Suc i)\<rparr>"
    by (simp add: rearmed_wakeup_def)
  show "i \<le> synchronised_retry_time duration i"
    by (rule election_wakeup_times_unbounded) simp
  show "\<not> timer_window {0,1} c (\<lambda>_. synchronised_retry_time duration i + duration) (\<lambda>_. 1) (\<lambda>_. 0)
      duration 1 {} 0 window_length"
    using member by (auto simp: timer_window_def Let_def)
qed

section \<open>Conditional probability across serviced resets\<close>

lemma phase_prefix_pullback:
  "matching_prefix (map (\<lambda>E. sample -` E) obs) i = sample -` matching_prefix obs i"
  by (auto simp: matching_prefix_def take_map)

text \<open>
  The reset and timer service contracts give feasible choices for each
  successive episode. A sample of a whole execution can give different
  draws at different episodes. The conditional lower bound still has
  to hold given the stalled history and the observations already made
  in that episode. The successful window also has to complete the
  healthy publication path. These premises permit correlations across
  episodes.
\<close>

theorem serviced_timer_retries_tend_to_succeed:
  fixes mass :: "'execution set \<Rightarrow> real"
    and sampled :: "nat \<Rightarrow> 'execution \<Rightarrow> timer_sample"
  assumes peers: "set peers = contenders" and candidate: "c \<in> contenders"
    and reset: "\<And>n. reset_episode_service contenders bounds loss restore tail
      (reset_failed (episode n) + reset_cut_slack bounds loss restore tail
        + timer_queue_delay bounds + window_length) (episode n)"
    and margin: "reset_cut_slack bounds loss restore tail + timer_queue_delay bounds + window_length < first_limit"
    and own_timer: "window_length < duration + next_limit"
    and nonnegative: "\<And>A. 0 \<le> mass A" and initial_mass: "mass (stalled 0) \<le> 1"
    and mono: "\<And>A B. A \<subseteq> B \<Longrightarrow> mass A \<le> mass B"
    and additive: "\<And>A B. A \<inter> B = {} \<Longrightarrow> mass (A \<union> B) = mass A + mass B"
    and delta: "0 < delta" "delta \<le> 1"
  defines "obs \<equiv> \<lambda>n. phase_observations peers c (reset_armed (episode n))
    (reset_drained bounds loss tail (episode n)) (\<lambda>_. first_limit) next_limit (timer_queue_delay bounds)"
  assumes chance: "\<And>n j. j < length (obs n) \<Longrightarrow>
      delta * mass (stalled n \<inter> sampled n -` matching_prefix (obs n) j)
      \<le> mass (stalled n \<inter> sampled n -` matching_prefix (obs n) (Suc j))"
    and completion: "\<And>n. stalled (Suc n) \<subseteq> stalled n"
    and service_success: "\<And>n execution.
      phase_success contenders c (reset_armed (episode n)) duration (reset_pending contenders (episode n))
        (reset_drained bounds loss tail (episode n)) window_length (sampled n execution)
      \<Longrightarrow> execution \<notin> stalled (Suc n)"
  shows "(\<lambda>n. mass (stalled n)) \<longlonglongrightarrow> 0"
proof -
  let ?observations = "\<lambda>n. map (\<lambda>E. sampled n -` E) (obs n)"
  have length_bound: "length (?observations n) \<le> length peers + 2" for n
    by (simp add: obs_def phase_observations_def)
  have prefix_lower: "delta * mass (stalled n \<inter> matching_prefix (?observations n) j)
    \<le> mass (stalled n \<inter> matching_prefix (?observations n) (Suc j))"
    if "j < length (?observations n)" for n j
    unfolding phase_prefix_pullback by (rule chance) (use that in simp)
  have leaves: "stalled (Suc n) \<subseteq> stalled n - matching_prefix (?observations n) (length (?observations n))" for n
  proof -
    have success: "phase_success contenders c (reset_armed (episode n)) duration (reset_pending contenders (episode n))
        (reset_drained bounds loss tail (episode n)) window_length (sampled n execution)"
      if "execution \<in> matching_prefix (?observations n) (length (?observations n))" for execution
    proof -
      from that have observed: "sampled n execution \<in> matching_prefix (obs n) (length (obs n))"
        by (simp add: phase_prefix_pullback)
      note cut = serviced_reset_timer_cut(1)[OF candidate reset[of n] margin own_timer]
      show ?thesis by (rule phase_observations_imply_success[OF peers cut observed[unfolded obs_def]])
    qed
    from completion[of n] service_success[OF success] show ?thesis by blast
  qed
  show ?thesis
    by (rule retry_observation_bound_tends_to_zero[OF nonnegative initial_mass mono additive delta length_bound prefix_lower leaves])
qed

end
