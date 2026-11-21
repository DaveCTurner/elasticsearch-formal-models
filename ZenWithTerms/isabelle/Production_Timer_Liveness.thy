theory Production_Timer_Liveness
  imports Scheduler_Liveness Production_Recovery_Retries
begin

section \<open>Pending work and fresh draws after a failed attempt\<close>

datatype prior_timer_work =
    Queued_Election nat nat
  | Past_Election_Guard nat
  | Publication_Deadline nat

definition pending_timer_deadlines where
  "pending_timer_deadlines open_generations work =
    {due. \<exists>g\<in>open_generations. Queued_Election g due \<in> work}
    \<union> {due. Publication_Deadline due \<in> work}"

definition drain_guarantee where
  "drain_guarantee work drained \<longleftrightarrow>
    (\<forall>finish. Past_Election_Guard finish \<in> work \<longrightarrow> finish \<le> drained)"

text \<open>
  Queued_Election records an already armed callback that has yet to read
  ElectionScheduler.isClosed in doRun. Closing its generation before
  that read suppresses its election effect. Work past that read needs a
  completion bound, including any resulting pre-vote activity. An
  uncancelled publication deadline belongs to its own publication and
  keeps its deadline when an election scheduler closes.

  Arming times refer to future draws, including any time needed to
  regain a visible quorum and service the peer update that opens a
  scheduler. Coordinator starts a new scheduler with zero initial
  grace. An open scheduler's existing wakeup uses its own arm time
  and grace, and the next wakeup is armed at the current handler plus
  election duration and fresh jitter. A failed pre-vote alone does
  not reset these timer phases.
\<close>

lemma closed_queued_election_adds_no_deadline:
  assumes "g \<notin> open_generations"
  shows "pending_timer_deadlines open_generations (insert (Queued_Election g due) work) =
    pending_timer_deadlines open_generations work"
  using assms by (auto simp: pending_timer_deadlines_def)

lemma publication_deadline_survives_reset:
  "Publication_Deadline due \<in> work \<Longrightarrow> due \<in> pending_timer_deadlines open_generations work"
  by (simp add: pending_timer_deadlines_def)

lemma own_rearm_excludes_dispatch_until_completion:
  assumes rearm: "rearmed_wakeup duration draw before after"
    and window: "window_length < duration + draw"
  shows "retry_handled before + window_length < retry_due after"
    "retry_handled before + window_length < retry_handled after"
  using assms unfolding rearmed_wakeup_def by linarith+

definition earliest_safe_draw :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "earliest_safe_draw base drained = max 1 (drained - base)"

definition phase_draws where
  "phase_draws c base drained limit n = (if n = c then earliest_safe_draw (base c) drained else limit n)"

definition postfailure_cut where
  "postfailure_cut contenders c base drained limit next_limit duration pending lag window_length
    \<longleftrightarrow>
    c \<in> contenders \<and>
    earliest_safe_draw (base c) drained \<le> limit c \<and>
    window_length < duration + next_limit \<and>
    (\<forall>n\<in>contenders - {c}.
      base c + earliest_safe_draw (base c) drained + lag + window_length < base n + limit n) \<and>
    (\<forall>deadline\<in>pending.
      base c + earliest_safe_draw (base c) drained + lag + window_length < deadline)"

lemma earliest_safe_draw_lower_bound:
  "1 \<le> earliest_safe_draw base drained"
  "drained \<le> base + earliest_safe_draw base drained"
proof -
  show "1 \<le> earliest_safe_draw base drained" by (simp add: earliest_safe_draw_def)
  have "drained \<le> base + (drained - base)" by arith
  also have "... \<le> base + earliest_safe_draw base drained" by (simp add: earliest_safe_draw_def)
  finally show "drained \<le> base + earliest_safe_draw base drained" .
qed

lemma earliest_safe_draw_minimal:
  assumes "1 \<le> draw" "drained \<le> base + draw"
  shows "earliest_safe_draw base drained \<le> draw"
  using assms(1) diff_le_mono[OF assms(2), of base]
  by (simp add: earliest_safe_draw_def add.commute)

theorem postfailure_cut_suffices:
  assumes cut: "postfailure_cut contenders c base drained limit next_limit duration pending lag window_length"
    and limits: "\<And>n. n \<in> contenders \<Longrightarrow> 0 < limit n \<and> limit n \<le> (2::nat)^63"
    and next_limit: "0 < next_limit" "next_limit \<le> (2::nat)^63"
  shows "\<forall>n\<in>contenders. legal_retry_jitter (limit n) (phase_draws c base drained limit n)"
    "legal_retry_jitter next_limit next_limit"
    "\<And>extra. extra c \<le> lag \<Longrightarrow>
      timer_window contenders c base (phase_draws c base drained limit) extra duration next_limit pending drained window_length"
proof -
  have legal: "legal_retry_jitter (limit n) (phase_draws c base drained limit n)" if "n \<in> contenders" for n
    using cut earliest_safe_draw_lower_bound(1) limits[OF that]
    by (auto simp: retry_jitter_support phase_draws_def postfailure_cut_def)
  then show "\<forall>n\<in>contenders. legal_retry_jitter (limit n) (phase_draws c base drained limit n)" by blast
  show "legal_retry_jitter next_limit next_limit" using next_limit by (simp add: retry_jitter_support)
  fix extra :: "node \<Rightarrow> nat"
  assume extra: "extra c \<le> lag"
  let ?start = "base c + earliest_safe_draw (base c) drained"
  from cut have own: "window_length < duration + next_limit"
    and peers: "\<forall>n\<in>contenders - {c}. ?start + lag + window_length < base n + limit n"
    and pending: "\<forall>deadline\<in>pending. ?start + lag + window_length < deadline"
    unfolding postfailure_cut_def by blast+
  have end_bound: "?start + extra c + window_length \<le> ?start + lag + window_length" using extra by simp
  have peer_cut: "?start + extra c + window_length < base n + limit n + extra n" if "n \<in> contenders - {c}" for n
    using le_less_trans[OF end_bound bspec[OF peers that]] by linarith
  have pending_cut: "?start + extra c + window_length < deadline" if "deadline \<in> pending" for deadline
    by (rule le_less_trans[OF end_bound bspec[OF pending that]])
  have drained: "drained \<le> ?start + extra c" using earliest_safe_draw_lower_bound(2)[of drained "base c"] by linarith
  show "timer_window contenders c base (phase_draws c base drained limit) extra duration next_limit pending drained window_length"
    using own drained peer_cut pending_cut by (auto simp: timer_window_def Let_def phase_draws_def)
qed

theorem robust_window_requires_postfailure_cut:
  assumes c: "c \<in> contenders"
    and draws: "\<And>n. n \<in> contenders \<Longrightarrow> 1 \<le> draws n \<and> draws n \<le> limit n"
    and next_bound: "own_next \<le> next_limit"
    and robust: "\<And>extra. extra c \<le> lag \<Longrightarrow>
      timer_window contenders c base draws extra duration own_next pending drained window_length"
  shows "postfailure_cut contenders c base drained limit next_limit duration pending lag window_length"
proof -
  from robust[of "\<lambda>_. 0"] have drain: "drained \<le> base c + draws c"
    and own: "window_length < duration + own_next" by (simp_all add: timer_window_def Let_def)
  have first: "earliest_safe_draw (base c) drained \<le> draws c"
    using earliest_safe_draw_minimal[OF _ drain] draws[OF c] by blast
  from robust[of "\<lambda>n. if n = c then lag else 0"]
  have bounds: "\<forall>n\<in>contenders - {c}. base c + draws c + lag + window_length < base n + draws n"
    "\<forall>deadline\<in>pending. base c + draws c + lag + window_length < deadline"
    by (simp_all add: timer_window_def Let_def)
  have peers: "base c + earliest_safe_draw (base c) drained + lag + window_length < base n + limit n"
    if "n \<in> contenders - {c}" for n
  proof -
    have "draws n \<le> limit n" using draws that by blast
    with bspec[OF bounds(1) that] first show ?thesis by linarith
  qed
  have pending: "base c + earliest_safe_draw (base c) drained + lag + window_length < deadline" if "deadline \<in> pending" for deadline
    using bspec[OF bounds(2) that] first by linarith
  have "earliest_safe_draw (base c) drained \<le> limit c" using first draws[OF c] by linarith
  moreover have "window_length < duration + next_limit" using own next_bound by linarith
  ultimately show ?thesis unfolding postfailure_cut_def using c peers pending by blast
qed

lemma retained_deadline_prevents_cut:
  assumes "due \<in> pending_timer_deadlines open_generations work"
    "due \<le> base c + earliest_safe_draw (base c) drained + lag + window_length"
  shows "\<not> postfailure_cut contenders c base drained limit next_limit duration
    (pending_timer_deadlines open_generations work) lag window_length"
  using assms unfolding postfailure_cut_def by (meson not_less)

corollary postfailure_reset_opens_feasible_window:
  assumes c: "c \<in> contenders"
    and reset: "\<And>n. n \<in> contenders \<Longrightarrow> failed \<le> arm n"
    and drain: "drain_guarantee work drained"
    and cut: "postfailure_cut contenders c (\<lambda>n. arm n + grace n) drained limit next_limit duration
      (pending_timer_deadlines open_generations work) lag window_length"
    and limits: "\<And>n. n \<in> contenders \<Longrightarrow> 0 < limit n \<and> limit n \<le> (2::nat)^63"
    and next_bound: "0 < next_limit" "next_limit \<le> (2::nat)^63"
    and dispatch: "extra c \<le> lag"
  defines "draws \<equiv> phase_draws c (\<lambda>n. arm n + grace n) drained limit"
  shows "timer_window contenders c (\<lambda>n. arm n + grace n) draws extra duration next_limit
      (pending_timer_deadlines open_generations work) drained window_length"
    "failed < arm c + grace c + draws c + extra c"
    "Past_Election_Guard finish \<in> work \<Longrightarrow> finish \<le> arm c + grace c + draws c + extra c"
proof -
  note window = postfailure_cut_suffices(3)[where extra=extra, OF cut limits next_bound dispatch]
  show "timer_window contenders c (\<lambda>n. arm n + grace n) draws extra duration next_limit
      (pending_timer_deadlines open_generations work) drained window_length"
    unfolding draws_def by (rule window)
  have "1 \<le> draws c" unfolding draws_def phase_draws_def using earliest_safe_draw_lower_bound(1) by simp
  with reset[OF c] show "failed < arm c + grace c + draws c + extra c" by linarith
  assume "Past_Election_Guard finish \<in> work"
  with drain have "finish \<le> drained" unfolding drain_guarantee_def by blast
  moreover from window have "drained \<le> arm c + grace c + draws c + extra c"
    unfolding draws_def timer_window_def by (simp add: Let_def)
  ultimately show "finish \<le> arm c + grace c + draws c + extra c" by linarith
qed

theorem capped_postfailure_cut:
  fixes limit :: "node \<Rightarrow> nat"
  assumes candidate: "c \<in> contenders"
    and aligned: "\<And>n. n \<in> contenders \<Longrightarrow> origin \<le> base n \<and> base n \<le> origin + spread"
    and drained: "drained \<le> origin + drain_slack"
    and backoff: "\<And>n. n \<in> contenders \<Longrightarrow>
      limit n = retry_limit initial_delay increment cap (attempt n)"
    and capped: "0 < increment" "\<And>n. n \<in> contenders \<Longrightarrow> cap \<le> attempt n"
    and next_capped: "cap \<le> next_attempt"
      "next_limit = retry_limit initial_delay increment cap next_attempt"
    and gap: "max (spread + 1) drain_slack + lag + window_length < cap"
    and pending: "\<And>due. due \<in> pending \<Longrightarrow>
      origin + max (spread + 1) drain_slack + lag + window_length < due"
  shows "postfailure_cut contenders c base drained limit next_limit duration pending lag window_length"
proof -
  let ?slack = "max (spread + 1) drain_slack"
  have limit: "limit n = cap" if "n \<in> contenders" for n
    unfolding backoff[OF that] by (rule retry_limit_reaches_cap[OF capped(1) capped(2)[OF that]])
  have next_limit: "next_limit = cap"
    unfolding next_capped(2) by (rule retry_limit_reaches_cap[OF capped(1) next_capped(1)])
  have cs: "origin \<le> base c" "base c \<le> origin + spread" using aligned[OF candidate] by auto
  have max_bound: "drained \<le> origin + ?slack" "base c + 1 \<le> origin + ?slack"
    using cs(2) drained by (auto simp: max_def split: if_splits)
  have first: "base c + earliest_safe_draw (base c) drained \<le> origin + ?slack"
    unfolding earliest_safe_draw_def max_def
    using cs(1) max_bound by (auto split: if_splits; arith)
  have draw: "earliest_safe_draw (base c) drained \<le> limit c"
    using first cs(1) gap limit[OF candidate] by linarith
  have own: "window_length < duration + next_limit" using next_limit gap by linarith
  have peers: "base c + earliest_safe_draw (base c) drained + lag + window_length < base n + limit n"
    if "n \<in> contenders - {c}" for n
  proof -
    from that have member: "n \<in> contenders" by simp
    from aligned[OF member] have "origin \<le> base n" by simp
    from this first gap limit[OF member] show ?thesis by linarith
  qed
  have "base c + earliest_safe_draw (base c) drained + lag + window_length < due"
    if "due \<in> pending" for due
    using pending[OF that] first by linarith
  from candidate draw own peers this show ?thesis by (auto simp: postfailure_cut_def)
qed

section \<open>Conditional probability on execution samples\<close>

text \<open>
  An execution sample provides the draws for all fresh contenders, the
  candidate's own next draw, its dispatch lag, and the service outcome.
  The preceding history fixes the timer cut. Pointwise conditional
  lower bounds on the observations apply after that history and after
  previous observations in the same opportunity. No independence is
  needed for their product bound. Legal jitter values alone supply no
  lower bound. A model of the random source and service has to supply
  these probabilities. The service observation includes all the
  healthy-path work and the absence of other disruptions in the window.
\<close>

record timer_sample =
  sample_draws :: "node \<Rightarrow> nat"
  sample_own_next :: nat
  sample_dispatch :: "node \<Rightarrow> nat"
  sample_service :: bool

definition phase_observations where
  "phase_observations peers c base drained limit next_limit lag =
    map (\<lambda>n. {sample. sample_draws sample n = phase_draws c base drained limit n}) peers
    @ [{sample. sample_own_next sample = next_limit},
       {sample. sample_dispatch sample c \<le> lag \<and> sample_service sample}]"

definition phase_success where
  "phase_success contenders c base duration pending drained window_length sample \<longleftrightarrow>
    sample_service sample \<and>
    timer_window contenders c base (sample_draws sample) (sample_dispatch sample) duration
      (sample_own_next sample) pending drained window_length"

lemma phase_observations_imply_success:
  assumes peers: "set peers = contenders"
    and cut: "postfailure_cut contenders c base drained limit next_limit duration pending lag window_length"
    and obs: "sample \<in> matching_prefix (phase_observations peers c base drained limit next_limit lag)
      (length (phase_observations peers c base drained limit next_limit lag))"
  shows "phase_success contenders c base duration pending drained window_length sample"
proof -
  let ?wanted = "phase_draws c base drained limit"
  from obs peers have draws: "sample_draws sample n = ?wanted n" if "n \<in> contenders" for n
    using that by (auto simp: matching_prefix_def phase_observations_def)
  from obs have own: "sample_own_next sample = next_limit" and extra: "sample_dispatch sample c \<le> lag"
    and service: "sample_service sample" by (auto simp: matching_prefix_def phase_observations_def)
  from cut have c: "c \<in> contenders" by (simp add: postfailure_cut_def)
  have finished: "base c + sample_draws sample c + sample_dispatch sample c + window_length
       \<le> base c + earliest_safe_draw (base c) drained + lag + window_length"
    using draws[OF c] extra by (simp add: phase_draws_def)
  have drain: "drained \<le> base c + sample_draws sample c + sample_dispatch sample c"
    using draws[OF c] earliest_safe_draw_lower_bound(2)[of drained "base c"]
    unfolding phase_draws_def by simp
  have rival: "base c + sample_draws sample c + sample_dispatch sample c + window_length
       < base n + sample_draws sample n + sample_dispatch sample n" if "n \<in> contenders - {c}" for n
  proof -
    from that draws[of n] have d: "sample_draws sample n = limit n" by (simp add: phase_draws_def)
    from cut that have "base c + earliest_safe_draw (base c) drained + lag + window_length < base n + limit n"
      unfolding postfailure_cut_def by blast
    from le_less_trans[OF finished this] d show ?thesis by linarith
  qed
  have pending_cut: "base c + sample_draws sample c + sample_dispatch sample c + window_length < deadline"
    if "deadline \<in> pending" for deadline
  proof -
    from cut that have "base c + earliest_safe_draw (base c) drained + lag + window_length < deadline"
      unfolding postfailure_cut_def by blast
    from le_less_trans[OF finished this] show ?thesis .
  qed
  show ?thesis using cut own service drain rival pending_cut
    unfolding phase_success_def timer_window_def postfailure_cut_def by (simp add: Let_def)
qed

theorem postfailure_conditional_success_probability:
  fixes mass :: "timer_sample set \<Rightarrow> real"
  assumes peers: "set peers = contenders"
    and cut: "postfailure_cut contenders c base drained limit next_limit duration pending lag window_length"
    and mono: "\<And>A B. A \<subseteq> B \<Longrightarrow> mass A \<le> mass B"
    and delta: "0 < delta"
    and history: "0 < mass H"
  defines "obs \<equiv> phase_observations peers c base drained limit next_limit lag"
  assumes chance: "\<And>i. i < length obs \<Longrightarrow> delta * mass (H \<inter> matching_prefix obs i)
      \<le> mass (H \<inter> matching_prefix obs (Suc i))"
  shows "delta^(length peers + 2) \<le>
    mass (H \<inter> {sample. phase_success contenders c base duration pending drained window_length sample}) / mass H"
proof -
  have prefix: "delta ^ length obs * mass H \<le> mass (H \<inter> matching_prefix obs (length obs))"
    by (rule prefix_observations_probability[OF le_refl _ chance]) (use delta in simp)
  have success: "H \<inter> matching_prefix obs (length obs)
    \<subseteq> H \<inter> {sample. phase_success contenders c base duration pending drained window_length sample}"
    unfolding obs_def using phase_observations_imply_success[OF peers cut] by blast
  from order_trans[OF prefix mono[OF success]] history show ?thesis
    by (simp add: obs_def phase_observations_def le_divide_eq)
qed

definition finite_timer_mass :: "timer_sample set \<Rightarrow> (timer_sample \<Rightarrow> real) \<Rightarrow> timer_sample set \<Rightarrow> real" where
  "finite_timer_mass support weight event = (\<Sum>sample \<in> support \<inter> event. weight sample)"

theorem finite_postfailure_success_probability:
  assumes support: "finite support" "\<And>sample. sample \<in> support \<Longrightarrow> 0 \<le> weight sample"
      "(\<Sum>sample\<in>support. weight sample) = 1"
    and peers: "distinct peers" "set peers = contenders"
    and cut: "postfailure_cut contenders c base drained limit next_limit duration pending lag window_length"
    and delta: "0 < delta"
  defines "mass \<equiv> finite_timer_mass support weight"
    and "obs \<equiv> phase_observations peers c base drained limit next_limit lag"
  assumes history: "0 < mass H"
    and chance: "\<And>i. i < length obs \<Longrightarrow> delta * mass (H \<inter> matching_prefix obs i)
      \<le> mass (H \<inter> matching_prefix obs (Suc i))"
  defines "prob \<equiv> mass (H \<inter> {sample. phase_success contenders c base duration pending drained window_length sample}) / mass H"
  shows "delta^(card contenders + 2) \<le> prob" "prob \<le> 1" "mass UNIV = 1"
proof -
  have monotone: "mass A \<le> mass B" if "A \<subseteq> B" for A B
    unfolding mass_def finite_timer_mass_def
    by (rule sum_mono2) (use that support(1,2) in auto)
  have size: "card contenders = length peers" using peers by (simp add: distinct_card[symmetric])
  show "delta^(card contenders + 2) \<le> prob"
    unfolding prob_def size
    by (rule postfailure_conditional_success_probability[where peers=peers and mass=mass and H=H,
          OF peers(2) cut monotone delta history])
      (assumption, rule chance[unfolded obs_def], assumption)
  have event: "mass (H \<inter> {sample. phase_success contenders c base duration pending drained window_length sample}) \<le> mass H"
    by (rule monotone) auto
  show "prob \<le> 1" unfolding prob_def using history event by (simp add: divide_le_eq)
  show "mass UNIV = 1" using support(3) by (simp add: mass_def finite_timer_mass_def)
qed

end
