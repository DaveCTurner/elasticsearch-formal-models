theory Scheduler_Liveness
  imports Fixed_Window_Liveness Recovery_Liveness Complex_Main
begin

section \<open>Capped retry timing and attainable jitter\<close>

definition retry_limit :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "retry_limit initial_delay increment cap attempt = min cap (initial_delay + attempt * increment)"

definition signed_draw where
  "signed_draw x \<longleftrightarrow> -((2::int)^63) \<le> x \<and> x < (2::int)^63"

definition retry_jitter where
  "retry_jitter limit x = nat (if x = -((2::int)^63) then 0 else abs x) mod limit + 1"

definition legal_retry_jitter where
  "legal_retry_jitter limit delay \<longleftrightarrow> (\<exists>x. signed_draw x \<and> delay = retry_jitter limit x)"

lemma retry_limit_positive:
  "0 < initial_delay \<Longrightarrow> 0 < cap \<Longrightarrow> 0 < retry_limit initial_delay increment cap attempt"
  by (simp add: retry_limit_def)

lemma retry_limit_capped:
  "retry_limit initial_delay increment cap attempt \<le> cap"
  by (simp add: retry_limit_def)

lemma retry_limit_reaches_cap:
  assumes "0 < increment" "cap \<le> attempt"
  shows "retry_limit initial_delay increment cap attempt = cap"
proof -
  have increment: "1 \<le> increment" using assms(1) by simp
  have product: "attempt * 1 \<le> attempt * increment" by (rule mult_le_mono2[OF increment])
  have "cap \<le> initial_delay + attempt * increment" using product assms(2) by linarith
  then show ?thesis by (simp add: retry_limit_def min.absorb1)
qed

theorem retry_jitter_support:
  assumes positive: "0 < limit" and long: "limit \<le> (2::nat)^63"
  shows "legal_retry_jitter limit delay \<longleftrightarrow> 1 \<le> delay \<and> delay \<le> limit"
proof
  assume "legal_retry_jitter limit delay"
  then obtain x where "delay = retry_jitter limit x" by (auto simp: legal_retry_jitter_def)
  with positive show "1 \<le> delay \<and> delay \<le> limit"
    by (simp add: retry_jitter_def Suc_le_eq)
next
  assume "1 \<le> delay \<and> delay \<le> limit"
  then have delay: "0 < delay" "delay \<le> limit" by auto
  let ?x = "int (delay - 1)"
  have below: "delay - 1 < limit" using delay by auto
  have nonnegative: "0 \<le> ?x" by simp
  have upper: "?x < (2::int)^63" using less_le_trans[OF below long] by simp
  have in_range: "signed_draw ?x" unfolding signed_draw_def using upper nonnegative by linarith
  have maps: "delay = retry_jitter limit ?x"
    using below delay by (simp add: retry_jitter_def)
  from in_range maps show "legal_retry_jitter limit delay"
    unfolding legal_retry_jitter_def by blast
qed

text \<open>
  ElectionSchedulerFactory draws a signed long, maps its minimum to
  zero, and otherwise takes its absolute value before reduction by the
  capped retry limit. The model uses natural numbers for scheduler time
  and the backoff calculation, in the range before the Java arithmetic
  wraps. The support theorem concerns the mapping of raw draws. It
  supplies neither a distribution nor independence of invocation results.

  The timer callback schedules its successor with election-duration grace
  before it runs Coordinator's callback. That callback may close a prior
  pre-vote round and start another. Hence the candidate's own next wakeup
  is a possible disruption. A wakeup on another node is counted as a
  potential disruption even if Coordinator would in fact decline to start
  a new round. The model allows callback service to add nonnegative delay.
\<close>

section \<open>One window with pending and future timers\<close>

definition timer_window ::
  "node set \<Rightarrow> node \<Rightarrow> (node \<Rightarrow> nat) \<Rightarrow> (node \<Rightarrow> nat)
    \<Rightarrow> (node \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "timer_window contenders c base draws extra duration own_next pending drained window_length \<longleftrightarrow>
    (let start = base c + draws c + extra c in
      drained \<le> start \<and>
      window_length < duration + own_next \<and>
      (\<forall>n\<in>contenders - {c}. start + window_length < base n + draws n + extra n) \<and>
      (\<forall>deadline\<in>pending. start + window_length < deadline))"

text \<open>
  A base includes arming time and any grace for a timer whose jitter is
  still to be drawn. Pending records lower bounds on potentially
  disruptive callbacks whose timers have already been armed. Drained is
  an upper bound on earlier disruptive work outside those pending timers.
  Other sources of disruption must separately be ruled out on the
  window. Nothing here resets the phase of an already-armed timer.
\<close>

theorem timer_window_has_legal_draws:
  fixes contenders :: "node set" and base limit :: "node \<Rightarrow> nat"
  assumes candidate: "c \<in> contenders"
    and limits: "\<And>n. n \<in> contenders \<Longrightarrow> 0 < limit n \<and> limit n \<le> (2::nat)^63"
    and own_limit: "0 < next_limit" "next_limit \<le> (2::nat)^63"
    and drain: "drained \<le> base c + 1"
    and own: "window_length < duration + next_limit"
    and gaps: "\<And>n. n \<in> contenders - {c} \<Longrightarrow>
      base c + 1 + service_lag + window_length < base n + limit n"
    and waiting: "\<And>deadline. deadline \<in> pending \<Longrightarrow>
      base c + 1 + service_lag + window_length < deadline"
  obtains draws own_next where "draws c = 1"
    "\<And>n. n \<in> contenders \<Longrightarrow> legal_retry_jitter (limit n) (draws n)"
    "legal_retry_jitter next_limit own_next"
    "\<And>extra. extra c \<le> service_lag \<Longrightarrow>
      timer_window contenders c base draws extra duration own_next pending drained window_length"
proof -
  let ?draws = "\<lambda>n. if n = c then 1 else limit n"
  have legal: "legal_retry_jitter (limit n) (?draws n)" if "n \<in> contenders" for n
    using limits[OF that] by (auto simp: retry_jitter_support)
  have legal_next: "legal_retry_jitter next_limit next_limit"
    using own_limit by (simp add: retry_jitter_support)
  have window: "timer_window contenders c base ?draws extra duration next_limit pending drained window_length"
    if "extra c \<le> service_lag" for extra
  proof -
    have latest: "base c + 1 + extra c + window_length \<le> base c + 1 + service_lag + window_length"
      using that by simp
    have peers: "base c + 1 + extra c + window_length < base n + limit n + extra n"
      if "n \<in> contenders - {c}" for n
      using le_less_trans[OF latest gaps[OF that]] by linarith
    have armed: "base c + 1 + extra c + window_length < deadline" if "deadline \<in> pending" for deadline
      by (rule le_less_trans[OF latest waiting[OF that]])
    have lower: "drained \<le> base c + 1 + extra c" using drain by linarith
    from peers armed lower own show ?thesis unfolding timer_window_def
      by (auto simp: Let_def)
  qed
  show thesis by (rule that[of ?draws next_limit]) (use legal legal_next window in auto)
qed

lemma early_pending_timer_blocks_window:
  assumes legal: "legal_retry_jitter limit (draws c)" "0 < limit" "limit \<le> (2::nat)^63"
    and pending: "deadline \<in> pending" "deadline \<le> base c + 1 + window_length"
  shows "\<not> timer_window contenders c base draws extra duration own_next pending drained window_length"
proof
  assume window: "timer_window contenders c base draws extra duration own_next pending drained window_length"
  have "1 \<le> draws c" using legal by (simp add: retry_jitter_support)
  moreover have "base c + draws c + extra c + window_length < deadline"
    using window pending(1) unfolding timer_window_def by (simp add: Let_def)
  ultimately show False using pending(2) by linarith
qed

section \<open>Service within a recovered timer window\<close>

lemma timer_window_deadlines:
  assumes "timer_window contenders c base draws extra duration own_next pending drained window_length"
    "start = base c + draws c + extra c"
  shows "start + window_length < start + duration + own_next"
    "\<forall>n\<in>contenders - {c}. start + window_length < base n + draws n + extra n"
    "\<forall>deadline\<in>pending. start + window_length < deadline"
  using assms unfolding timer_window_def by (simp_all add: Let_def add.assoc)

lemma recovered_attempt_fits_timer_window:
  assumes timer: "timer_window contenders c base draws extra duration own_next pending drained window_length"
    and start: "start = base c + draws c + extra c"
    and recovery: "episode_permission start episode" "episode_service episode"
    and budget: "3 * episode_delay episode + work \<le> window_length"
  obtains k where "opens_attempt_at start episode k"
    "k + work \<le> start + window_length"
    "\<And>n. n \<in> contenders - {c} \<Longrightarrow> k + work < base n + draws n + extra n"
    "\<And>deadline. deadline \<in> pending \<Longrightarrow> k + work < deadline"
    "k + work < start + duration + own_next"
proof -
  from serviced_episode_opens_attempt[OF recovery] obtain k where
    k: "k \<le> start + 3 * episode_delay episode" "opens_attempt_at start episode k" by blast
  have fits: "k + work \<le> start + window_length" using k(1) budget by linarith
  note cuts = timer_window_deadlines[OF timer start]
  show thesis
  proof (rule that[OF k(2) fits])
    fix n
    assume "n \<in> contenders - {c}"
    from fits bspec[OF cuts(2) this] show "k + work < base n + draws n + extra n" by (rule le_less_trans)
  next
    fix deadline
    assume "deadline \<in> pending"
    from fits bspec[OF cuts(3) this] show "k + work < deadline" by (rule le_less_trans)
  next
    from fits cuts(1) show "k + work < start + duration + own_next" by (rule le_less_trans)
  qed
qed

text \<open>
  This handoff composes two service projections. A recovery episode
  obtains pre-vote evidence and reaches the attempt boundary. The fixed
  wave schedule can account for the evidence already obtained by the
  episode. Its Prevote jobs at this boundary represent availability of
  that evidence to the fixed proof, and the budget conservatively charges
  their service again. Coordinator does not send a second pre-vote round
  after it starts the election. A source mapping must supply the fixed
  schedule with those evidence jobs and with the subsequent concrete
  operations and timely service.
\<close>

context fixed_publication_window
begin

theorem recovered_timer_window_completes:
  assumes timer: "timer_window contenders c base draws extra duration own_next pending drained window_length"
    and start: "start = base c + draws c + extra c"
    and recovery: "episode_permission start episode" "episode_service episode"
    and chosen: "replacement_candidate (episode_round episode) = c" "episode_quorum episode = E"
      "committed_voters (episode_round episode) = V" "accepted_voters (episode_round episode) = V"
    and fresh: "fresh"
    and budget: "3 * episode_delay episode + 12 * delay \<le> window_length"
    and service: "\<And>k. opens_attempt_at start episode k \<Longrightarrow>
      bounded_service jobs deps (schedule k) delay (12 * delay)"
  obtains k where "replacement_candidate (episode_round episode) = c" "episode_quorum episode = E"
    "opens_attempt_at start episode k"
    "k + 12 * delay \<le> start + window_length"
    "\<And>n. n \<in> contenders - {c} \<Longrightarrow>
      k + 12 * delay < base n + draws n + extra n"
    "\<And>deadline. deadline \<in> pending \<Longrightarrow> k + 12 * delay < deadline"
    "k + 12 * delay < start + duration + own_next"
    "h \<in> committed (core (finished (schedule k) (12 * delay)))"
    "installed (window_applier (finished (schedule k) (12 * delay))) = Some key"
    "window_slot (finished (schedule k) (12 * delay)) = None"
proof -
  obtain k where attempt: "opens_attempt_at start episode k"
    and fits: "k + 12 * delay \<le> start + window_length"
    and peers: "\<And>n. n \<in> contenders - {c} \<Longrightarrow> k + 12 * delay < base n + draws n + extra n"
    and armed: "\<And>deadline. deadline \<in> pending \<Longrightarrow> k + 12 * delay < deadline"
    and own: "k + 12 * delay < start + duration + own_next"
    by (rule recovered_attempt_fits_timer_window[OF timer start recovery budget]) blast
  have complete:
    "h \<in> committed (core (finished (schedule k) (12 * delay)))"
    "installed (window_applier (finished (schedule k) (12 * delay))) = Some key"
    "window_slot (finished (schedule k) (12 * delay)) = None"
    by (rule fixed_first_publication_local_completion[OF fresh service[OF attempt]], simp)+
  show thesis
    by (rule that[OF chosen(1,2) attempt fits peers armed own complete])
qed

end

section \<open>Probability after repeated opportunities\<close>

text \<open>
  Survival is the probability mass of executions still stalled after the
  given opportunities. The shrink premise says that each opportunity
  succeeds with conditional probability at least epsilon given earlier
  failures whenever there is still positive stalled mass. It also applies
  to a zero mass without choosing a conditional probability there.
  This interface needs no independence assumption. An execution model
  must provide later opportunities while stalled and justify the bound
  for useful choices and service in each window. The Java random source,
  timer phases and operating-system delay do not supply that bound here.
\<close>

theorem retry_survival_geometric:
  fixes survival :: "nat \<Rightarrow> real" and epsilon :: real
  assumes initial: "survival 0 \<le> 1"
    and epsilon: "epsilon \<le> 1"
    and shrink: "\<And>n. survival (Suc n) \<le> (1 - epsilon) * survival n"
  shows "survival n \<le> (1 - epsilon)^n"
proof (induction n)
  case 0
  show ?case using initial by simp
next
  case (Suc n)
  have factor: "0 \<le> 1 - epsilon" using epsilon by simp
  from mult_left_mono[OF Suc.IH factor]
  have next_bound: "(1 - epsilon) * survival n \<le> (1 - epsilon)^Suc n"
    by (simp add: mult.commute)
  show ?case by (rule order_trans[OF shrink next_bound])
qed

theorem retry_survival_tends_to_zero:
  fixes survival :: "nat \<Rightarrow> real" and epsilon :: real
  assumes initial: "survival 0 \<le> 1"
    and nonnegative: "\<And>n. 0 \<le> survival n"
    and epsilon: "0 < epsilon" "epsilon \<le> 1"
    and shrink: "\<And>n. survival (Suc n) \<le> (1 - epsilon) * survival n"
  shows "survival \<longlonglongrightarrow> 0"
proof -
  have "norm (1 - epsilon) < 1" using epsilon by simp
  hence upper: "(\<lambda>n. (1 - epsilon)^n) \<longlonglongrightarrow> (0::real)"
    by (rule LIMSEQ_power_zero)
  show ?thesis by (rule tendsto_sandwich[where f="\<lambda>_. 0" and h="\<lambda>n. (1 - epsilon)^n"])
    (use nonnegative retry_survival_geometric[OF initial epsilon(2) shrink] upper in auto)
qed

section \<open>Composing conditional bounds for a usable window\<close>

definition matching_prefix where
  "matching_prefix observations i = \<Inter> (set (take i observations))"

lemma prefix_observations_probability:
  fixes mass :: "'sample set \<Rightarrow> real"
  assumes within: "i \<le> length observations"
    and lower: "0 \<le> delta"
    and each: "\<And>j. j < length observations \<Longrightarrow>
      delta * mass (stalled \<inter> matching_prefix observations j)
        \<le> mass (stalled \<inter> matching_prefix observations (Suc j))"
  shows "delta^i * mass stalled \<le> mass (stalled \<inter> matching_prefix observations i)"
  using within
proof (induction i)
  case 0
  show ?case by (simp add: matching_prefix_def)
next
  case (Suc i)
  have less: "i < length observations" using Suc.prems by simp
  have prior: "delta^i * mass stalled \<le> mass (stalled \<inter> matching_prefix observations i)"
    by (rule Suc.IH) (use less in simp)
  have "delta ^ Suc i * mass stalled \<le> delta * mass (stalled \<inter> matching_prefix observations i)"
    using mult_left_mono[OF prior lower] by (simp add: mult.assoc)
  from order_trans[OF this each[OF less]] show ?case .
qed

text \<open>
  Each list of observations fixes the desired draws for the timers that
  are not yet armed and can include additional observations for dispatch
  and successful service. The list need not have the same length in
  every opportunity. Each probability inequality conditions on still
  being stalled and on the preceding observations in that opportunity.
  The required observations should imply successful completion via the
  timing and bounded-service theorems. The mass laws below are sufficient
  for discrete probability models and apply to measurable events when
  the relevant event algebra is closed under the displayed operations.
\<close>

theorem retry_observation_bound_tends_to_zero:
  fixes mass :: "'sample set \<Rightarrow> real"
    and stalled :: "nat \<Rightarrow> 'sample set"
    and observations :: "nat \<Rightarrow> 'sample set list"
  assumes nonnegative: "\<And>A. 0 \<le> mass A"
    and initial: "mass (stalled 0) \<le> 1"
    and mono: "\<And>A B. A \<subseteq> B \<Longrightarrow> mass A \<le> mass B"
    and additive: "\<And>A B. A \<inter> B = {} \<Longrightarrow> mass (A \<union> B) = mass A + mass B"
    and chance: "0 < delta" "delta \<le> 1"
    and length: "\<And>n. length (observations n) \<le> budget"
    and each: "\<And>n j. j < length (observations n) \<Longrightarrow>
      delta * mass (stalled n \<inter> matching_prefix (observations n) j)
        \<le> mass (stalled n \<inter> matching_prefix (observations n) (Suc j))"
    and completion: "\<And>n. stalled (Suc n) \<subseteq>
      stalled n - matching_prefix (observations n) (length (observations n))"
  shows "(\<lambda>n. mass (stalled n)) \<longlonglongrightarrow> 0"
proof -
  have lower: "0 \<le> delta" using chance by simp
  have epsilon: "0 < delta^budget" "delta^budget \<le> 1"
    using chance by (auto intro: power_le_one)
  have shrink: "mass (stalled (Suc n)) \<le> (1 - delta^budget) * mass (stalled n)" for n
  proof -
    let ?prefix = "matching_prefix (observations n) (length (observations n))"
    have bound: "delta^budget \<le> delta ^ length (observations n)"
      by (rule power_decreasing[OF length lower chance(2)])
    have prefix: "delta ^ length (observations n) * mass (stalled n) \<le> mass (stalled n \<inter> ?prefix)"
      by (rule prefix_observations_probability[OF le_refl lower]) (rule each)
    have all: "delta^budget * mass (stalled n) \<le> mass (stalled n \<inter> ?prefix)"
      by (rule order_trans[OF mult_right_mono[OF bound nonnegative] prefix])
    have disjoint: "(stalled n - ?prefix) \<inter> (stalled n \<inter> ?prefix) = {}" by blast
    have cover: "(stalled n - ?prefix) \<union> (stalled n \<inter> ?prefix) = stalled n" by blast
    from additive[OF disjoint, unfolded cover]
    have split: "mass (stalled n) = mass (stalled n - ?prefix) + mass (stalled n \<inter> ?prefix)"
      .
    have remain: "mass (stalled (Suc n)) \<le> mass (stalled n - ?prefix)"
      by (rule mono[OF completion])
    show ?thesis
      unfolding left_diff_distrib mult_1 using remain split all by linarith
  qed
  show ?thesis by (rule retry_survival_tends_to_zero[OF initial nonnegative epsilon shrink])
qed

end
