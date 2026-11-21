theory Open_Scheduler_Recurrence
  imports Production_Timer_Liveness
begin

section \<open>A quiet draw with continuously open schedulers\<close>

text \<open>
  ElectionSchedulerFactory arms the next retry in doRun before running
  the election work. On the continuously open path, that nominal due
  time is the handler time plus election duration plus a fresh positive
  draw, capped by the node's settings. In this model the open contenders
  have a common duration and cap and have reached that cap without
  overflowing the attempt arithmetic. Arm times abstract the scheduling
  call; any delay from handler entry to arming must be accounted for in
  the source projection.

  At the selected candidate's arming cut, every rival has one outstanding
  wakeup. Its nominal due time may be in the past. Known earlier entered
  work has a separate drain bound. Each outstanding wake can be placed
  after the window or given enough time to drain before it. The drain
  bound must cover any pre-vote activity, callbacks, or publication
  deadlines it can leave behind that would still disrupt the attempt.
  If an outstanding wake starts before the window, its next draw can
  defer its subsequent wake.
  This models the rearm order, including the case where a rival has not
  yet made its next draw when the candidate makes its own draw.
\<close>

definition wake_collision where
  "wake_collision lag work_tail window_length due start \<longleftrightarrow>
    due \<le> start + lag + window_length \<and> start \<le> due + lag + work_tail"

lemma spaced_wake_avoids_collisions:
  fixes due :: "node \<Rightarrow> nat" and base lag work_tail window_length :: nat
  assumes finite: "finite rivals"
  defines "stride \<equiv> lag + window_length + lag + work_tail + 1"
  obtains j where "j \<le> card rivals"
    "\<And>n. n \<in> rivals \<Longrightarrow> \<not> wake_collision lag work_tail window_length (due n) (base + stride * j)"
proof -
  let ?J = "{..card rivals}"
  let ?bad = "\<lambda>j n. n \<in> rivals \<and> wake_collision lag work_tail window_length (due n) (base + stride * j)"
  have distinct: "j = k" if "?bad j n" "?bad k n" for j k n
  proof (rule antisym)
    show "j \<le> k"
    proof (rule ccontr)
      assume "\<not> j \<le> k"
      then have order: "Suc k \<le> j" by simp
      have "stride * Suc k \<le> stride * j" by (rule mult_le_mono2[OF order])
      with that show False by (simp add: wake_collision_def stride_def algebra_simps; linarith)
    qed
    show "k \<le> j"
    proof (rule ccontr)
      assume "\<not> k \<le> j"
      then have order: "Suc j \<le> k" by simp
      have "stride * Suc j \<le> stride * k" by (rule mult_le_mono2[OF order])
      with that show False by (simp add: wake_collision_def stride_def algebra_simps; linarith)
    qed
  qed
  have "\<exists>j\<in>?J. \<forall>n\<in>rivals. \<not> wake_collision lag work_tail window_length (due n) (base + stride * j)"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have bad: "\<forall>j\<in>?J. \<exists>n. ?bad j n" by blast
    obtain block where blocker: "\<And>j. j \<in> ?J \<Longrightarrow> ?bad j (block j)"
      using bad by metis
    have inj: "inj_on block ?J"
    proof (rule inj_onI)
      fix j k
      assume j: "j \<in> ?J" and k: "k \<in> ?J" and same: "block j = block k"
      show "j = k" by (rule distinct[OF blocker[OF j] blocker[OF k, folded same]])
    qed
    have sub: "block ` ?J \<subseteq> rivals" using blocker by blast
    have "Suc (card rivals) = card (block ` ?J)" by (simp add: card_image[OF inj])
    also have "... \<le> card rivals" by (rule card_mono[OF finite sub])
    finally show False by simp
  qed
  then show thesis by (auto intro: that)
qed

definition next_rival_due where
  "next_rival_due nominal lag work_tail due armed =
    (if due + lag + work_tail < nominal then retry_due armed else due)"

locale continuously_open_draw =
  fixes c :: node and rivals :: "node set"
    and old_due :: "node \<Rightarrow> nat"
    and arm duration cap first lag work_tail window_length drained :: nat
    and pending :: "nat set"
  assumes finite_rivals: "finite rivals"
    and candidate: "c \<notin> rivals"
    and cap_range: "0 < cap" "cap \<le> 2^63"
    and first_draw: "0 < first"
    and drain: "drained \<le> arm + duration + first"
    and headroom: "first + (lag + window_length + lag + work_tail + 1) * card rivals + lag + window_length < cap"
    and deadlines: "\<And>p. p \<in> pending \<Longrightarrow> arm + duration + cap < p"
begin

theorem continuously_open_has_legal_quiet_draw:
  obtains draw where "legal_retry_jitter cap draw" "legal_retry_jitter cap cap"
    "first \<le> draw" "draw + lag + window_length < cap"
    "\<And>n. n \<in> rivals \<Longrightarrow> \<not> wake_collision lag work_tail window_length (old_due n) (arm + duration + draw)"
proof -
  obtain j where j: "j \<le> card rivals"
    and safe: "\<And>n. n \<in> rivals \<Longrightarrow>
      \<not> wake_collision lag work_tail window_length (old_due n)
        (arm + duration + first + (lag + window_length + lag + work_tail + 1) * j)"
    by (rule spaced_wake_avoids_collisions[OF finite_rivals, where due=old_due and
          base="arm + duration + first"]) blast
  let ?draw = "first + (lag + window_length + lag + work_tail + 1) * j"
  have " (lag + window_length + lag + work_tail + 1) * j \<le> (lag + window_length + lag + work_tail + 1) * card rivals"
    by (rule mult_le_mono2[OF j])
  with headroom have room: "?draw + lag + window_length < cap" by linarith
  have first: "first \<le> ?draw" by simp
  have legal: "legal_retry_jitter cap ?draw" "legal_retry_jitter cap cap"
    using cap_range(1) first_draw first room
    unfolding retry_jitter_support[OF cap_range] by (intro conjI; linarith)+
  show thesis by (rule that[OF legal first room]) (use safe in \<open>simp add: add.assoc\<close>)
qed

lemma quiet_draw_delays_every_rival:
  assumes safe: "\<not> wake_collision lag work_tail window_length (old_due n) (arm + duration + draw)"
    and room: "draw + lag + window_length < cap"
    and lag: "extra \<le> lag"
    and early: "old_due n + lag + work_tail < arm + duration + draw \<Longrightarrow>
      arm \<le> handled \<and> handled \<le> old_due n + lag \<and>
      rearmed_wakeup duration cap \<lparr>retry_due = old_due n, retry_handled = handled\<rparr> new_wake"
  shows "arm + duration + draw + extra + window_length <
    next_rival_due (arm + duration + draw) lag work_tail (old_due n) new_wake"
proof (cases "old_due n + lag + work_tail < arm + duration + draw")
  case True
  from early[OF True] have "arm + duration + cap \<le> retry_due new_wake"
    by (simp add: rearmed_wakeup_def; linarith)
  then have bound: "arm + duration + draw + extra + window_length < retry_due new_wake"
    using room lag by linarith
  show ?thesis using bound True
    by (simp add: next_rival_due_def)
next
  case False
  then have "arm + duration + draw \<le> old_due n + lag + work_tail" by linarith
  with safe have "arm + duration + draw + lag + window_length < old_due n"
    unfolding wake_collision_def by linarith
  with lag False show ?thesis by (simp add: next_rival_due_def; linarith)
qed

lemma early_rival_has_drained:
  assumes "old_due n + lag + work_tail < arm + duration + draw" "handled \<le> old_due n + lag"
  shows "handled + work_tail < arm + duration + draw"
  using assms by linarith

theorem continuously_open_draw_supplies_window:
  assumes first: "first \<le> draw" "draw + lag + window_length < cap"
    and safe: "\<And>n. n \<in> rivals \<Longrightarrow>
      \<not> wake_collision lag work_tail window_length (old_due n) (arm + duration + draw)"
    and extra: "extra \<le> lag"
    and early: "\<And>n. n \<in> rivals \<Longrightarrow>
      old_due n + lag + work_tail < arm + duration + draw \<Longrightarrow>
      arm \<le> handled n \<and> handled n \<le> old_due n + lag \<and>
      rearmed_wakeup duration cap \<lparr>retry_due = old_due n, retry_handled = handled n\<rparr> (next_wakes n)"
  shows "timer_window (insert c rivals) c (\<lambda>n. if n = c then arm + duration else 0)
    (\<lambda>n. if n = c then draw else next_rival_due (arm + duration + draw) lag work_tail (old_due n) (next_wakes n))
    (\<lambda>n. if n = c then extra else 0) duration cap pending drained window_length"
proof -
  have previous: "drained \<le> arm + duration + draw + extra" using drain first(1) by linarith
  have own: "window_length < duration + cap" using first(2) by linarith
  have publication: "arm + duration + draw + extra + window_length < p" if "p \<in> pending" for p
    using deadlines[OF that] first(2) extra by linarith
  have rivals: "arm + duration + draw + extra + window_length <
      next_rival_due (arm + duration + draw) lag work_tail (old_due n) (next_wakes n)" if "n \<in> rivals" for n
    by (rule quiet_draw_delays_every_rival[where handled="handled n", OF safe[OF that] first(2) extra early[OF that]])
  show ?thesis using previous own publication rivals candidate
    by (auto simp: timer_window_def Let_def)
qed

end

section \<open>Conditional support for the useful choices\<close>

record open_wake_observation =
  observed_quiet_draw :: nat
  observed_quiet_lag :: nat
  observed_own_rearm :: nat
  observed_rival_handling :: "node \<Rightarrow> nat"
  observed_rival_rearms :: "node \<Rightarrow> retry_wakeup"
  observed_healthy_path :: bool

text \<open>
  In the list of observations, a rival that wakes too late to interfere
  need not draw again. The rearm observations for early rivals include
  their timely handling, and the final observation covers permission to
  attempt recovery and successful publication service. They need not be
  independent. The bounds are conditional on the preceding history and
  observations, including the outstanding wake phases that determine
  the selected draw. Java's finite-state random generator and the legal
  range of its output alone do not supply these conditional bounds.
\<close>

context continuously_open_draw
begin

definition quiet_observations :: "node list \<Rightarrow> nat \<Rightarrow> open_wake_observation set list" where
  "quiet_observations peers draw =
    [{sample. observed_quiet_draw sample = draw}]
    @ map (\<lambda>n. {sample. arm \<le> observed_rival_handling sample n \<and>
          observed_rival_handling sample n \<le> old_due n + lag \<and>
          rearmed_wakeup duration cap
            \<lparr>retry_due = old_due n, retry_handled = observed_rival_handling sample n\<rparr> (observed_rival_rearms sample n)})
        (filter (\<lambda>n. old_due n + lag + work_tail < arm + duration + draw) peers)
    @ [{sample. observed_own_rearm sample = cap},
       {sample. observed_quiet_lag sample \<le> lag \<and> observed_healthy_path sample}]"

definition quiet_sample :: "open_wake_observation \<Rightarrow> bool" where
  "quiet_sample sample \<longleftrightarrow> observed_healthy_path sample \<and>
    timer_window (insert c rivals) c (\<lambda>n. if n = c then arm + duration else 0)
      (\<lambda>n. if n = c then observed_quiet_draw sample else
        next_rival_due (arm + duration + observed_quiet_draw sample) lag work_tail (old_due n)
          (observed_rival_rearms sample n))
      (\<lambda>n. if n = c then observed_quiet_lag sample else 0)
      duration (observed_own_rearm sample) pending drained window_length"

lemma quiet_observations_supply_window:
  assumes peers: "set peers = rivals"
    and first: "first \<le> draw" "draw + lag + window_length < cap"
    and safe: "\<And>n. n \<in> rivals \<Longrightarrow>
      \<not> wake_collision lag work_tail window_length (old_due n) (arm + duration + draw)"
    and sample: "sample \<in> matching_prefix (quiet_observations peers draw)
      (length (quiet_observations peers draw))"
  shows "quiet_sample sample"
proof -
  let ?obs = "quiet_observations peers draw"
  have complete: "take (length ?obs) ?obs = ?obs"
    by (rule take_all[OF order_refl])
  have in_all: "sample \<in> \<Inter> (set ?obs)"
    using sample unfolding matching_prefix_def complete .
  have observe: "sample \<in> E" if "E \<in> set (quiet_observations peers draw)" for E
    by (rule InterD[OF in_all that])
  have draws: "{s. observed_quiet_draw s = draw} \<in> set (quiet_observations peers draw)"
    "{s. observed_own_rearm s = cap} \<in> set (quiet_observations peers draw)"
    "{s. observed_quiet_lag s \<le> lag \<and> observed_healthy_path s} \<in> set (quiet_observations peers draw)"
    by (simp_all add: quiet_observations_def)
  from observe[OF draws(1)] observe[OF draws(2)] observe[OF draws(3)]
  have drawn: "observed_quiet_draw sample = draw" "observed_own_rearm sample = cap"
    and served: "observed_quiet_lag sample \<le> lag" "observed_healthy_path sample" by simp_all
  have early:
    "arm \<le> observed_rival_handling sample n \<and> observed_rival_handling sample n \<le> old_due n + lag \<and>
      rearmed_wakeup duration cap
        \<lparr>retry_due = old_due n, retry_handled = observed_rival_handling sample n\<rparr> (observed_rival_rearms sample n)"
    if "n \<in> rivals" "old_due n + lag + work_tail < arm + duration + draw" for n
  proof -
    have e: "{s. arm \<le> observed_rival_handling s n \<and> observed_rival_handling s n \<le> old_due n + lag \<and>
      rearmed_wakeup duration cap
        \<lparr>retry_due = old_due n, retry_handled = observed_rival_handling s n\<rparr> (observed_rival_rearms s n)}
       \<in> set (quiet_observations peers draw)"
      using that peers by (auto simp: quiet_observations_def)
    from observe[OF e] show ?thesis by simp
  qed
  from continuously_open_draw_supplies_window[where next_wakes="observed_rival_rearms sample"
      and handled="observed_rival_handling sample",
      OF first safe served(1) early] served(2)
  show "quiet_sample sample" unfolding quiet_sample_def drawn by blast
qed

theorem open_cut_conditional_success_bound:
  fixes mass :: "open_wake_observation set \<Rightarrow> real"
  assumes peers: "set peers = rivals"
    and first: "first \<le> draw" "draw + lag + window_length < cap"
    and safe: "\<And>n. n \<in> rivals \<Longrightarrow>
      \<not> wake_collision lag work_tail window_length (old_due n) (arm + duration + draw)"
    and mono: "\<And>A B. A \<subseteq> B \<Longrightarrow> mass A \<le> mass B"
    and history: "0 < mass H"
    and delta: "0 < delta" "delta \<le> 1"
  defines "obs \<equiv> quiet_observations peers draw"
  assumes chance: "\<And>i. i < length obs \<Longrightarrow> delta * mass (H \<inter> matching_prefix obs i)
      \<le> mass (H \<inter> matching_prefix obs (Suc i))"
  shows "delta^(length peers + 3) \<le> mass (H \<inter> {sample. quiet_sample sample}) / mass H"
proof -
  have length: "length obs \<le> length peers + 3"
    by (simp add: obs_def quiet_observations_def length_filter_le)
  have pref: "delta^length obs * mass H \<le> mass (H \<inter> matching_prefix obs (length obs))"
    by (rule prefix_observations_probability[OF le_refl _ chance]) (use delta in simp)
  have lower: "delta^(length peers + 3) \<le> delta^length obs"
    by (rule power_decreasing[OF length _ delta(2)]) (use delta in simp)
  have subset: "H \<inter> matching_prefix obs (length obs) \<subseteq> H \<inter> {sample. quiet_sample sample}"
    using quiet_observations_supply_window[OF peers first safe] unfolding obs_def by blast
  have "0 \<le> mass H" using history by simp
  from order_trans[OF mult_right_mono[OF lower this] order_trans[OF pref mono[OF subset]]] history
  show ?thesis by (simp add: le_divide_eq)
qed

theorem quiet_sample_opens_replacement:
  assumes quiet: "quiet_sample sample"
    and start: "start = arm + duration + observed_quiet_draw sample + observed_quiet_lag sample"
    and recovery: "episode_permission start episode" "episode_service episode"
    and budget: "3 * episode_delay episode + work \<le> window_length"
  obtains k where "opens_attempt_at start episode k"
    "k + work \<le> start + window_length"
    "\<And>n. n \<in> rivals \<Longrightarrow> k + work <
      next_rival_due (arm + duration + observed_quiet_draw sample) lag work_tail (old_due n)
        (observed_rival_rearms sample n)"
    "\<And>p. p \<in> pending \<Longrightarrow> k + work < p"
    "k + work < start + duration + observed_own_rearm sample"
proof -
  from quiet have window: "timer_window (insert c rivals) c
      (\<lambda>n. if n = c then arm + duration else 0)
      (\<lambda>n. if n = c then observed_quiet_draw sample else
        next_rival_due (arm + duration + observed_quiet_draw sample) lag work_tail (old_due n)
          (observed_rival_rearms sample n))
      (\<lambda>n. if n = c then observed_quiet_lag sample else 0)
      duration (observed_own_rearm sample) pending drained window_length"
    unfolding quiet_sample_def by blast
  obtain k where attempt: "opens_attempt_at start episode k"
    and fits: "k + work \<le> start + window_length"
    and peers: "\<And>n. n \<in> insert c rivals - {c} \<Longrightarrow> k + work <
      (if n = c then arm + duration else 0)
      + (if n = c then observed_quiet_draw sample else
          next_rival_due (arm + duration + observed_quiet_draw sample) lag work_tail (old_due n)
            (observed_rival_rearms sample n))
      + (if n = c then observed_quiet_lag sample else 0)"
    and deadline: "\<And>p. p \<in> pending \<Longrightarrow> k + work < p"
    and own: "k + work < start + duration + observed_own_rearm sample"
    by (rule recovered_attempt_fits_timer_window[OF window _ recovery budget]) (use start in auto)
  show thesis
  proof (rule that[OF attempt fits _ deadline own])
    fix n
    assume n: "n \<in> rivals"
    with candidate have distinct: "n \<noteq> c" by blast
    with n have "n \<in> insert c rivals - {c}" by simp
    from peers[OF this] show "k + work <
       next_rival_due (arm + duration + observed_quiet_draw sample) lag work_tail (old_due n)
         (observed_rival_rearms sample n)" by (simp add: distinct)
  qed
qed

end

section \<open>Recurring opportunities while the scheduler stays open\<close>

theorem continuously_open_arming_recurs:
  fixes initial duration :: nat and draw extra :: "nat \<Rightarrow> nat"
  assumes positive: "\<And>i. 0 < draw i"
    and cap: "\<And>i. first_capped \<le> i \<Longrightarrow> draw i \<le> cap"
    and dispatch: "\<And>i. first_capped \<le> i \<Longrightarrow> extra i \<le> lag"
  defines "clock \<equiv> election_wakeup_times initial duration draw extra"
  obtains i where "first_capped \<le> i" "t < clock i"
    "clock i \<le> max t (clock first_capped) + (duration + cap + lag)"
proof (cases "t < clock first_capped")
  case True
  show thesis by (rule that[of first_capped]) (use True in simp_all)
next
  case False
  have bound: "i \<le> clock i" for i
    unfolding clock_def by (rule election_wakeup_times_unbounded[OF positive])
  have ex: "\<exists>i. first_capped \<le> i \<and> t < clock i"
  proof (intro exI[of _ "max first_capped (Suc t)"] conjI)
    show "first_capped \<le> max first_capped (Suc t)" by simp
    have "t < max first_capped (Suc t)" by simp
    from less_le_trans[OF this bound] show "t < clock (max first_capped (Suc t))" .
  qed
  let ?i = "LEAST i. first_capped \<le> i \<and> t < clock i"
  have timing: "first_capped \<le> ?i \<and> t < clock ?i" by (rule LeastI_ex[OF ex])
  have "first_capped \<noteq> ?i" using timing False by auto
  with timing have strict: "first_capped < ?i" by (simp add: less_le)
  then obtain j where i: "?i = Suc j" and j: "first_capped \<le> j"
    by (cases ?i) auto
  have "clock j \<le> t"
  proof (rule ccontr)
    assume "\<not> clock j \<le> t"
    with j have "first_capped \<le> j \<and> t < clock j" by simp
    from Least_le[where P="\<lambda>i. first_capped \<le> i \<and> t < clock i", OF this] i
    show False by simp
  qed
  moreover have "clock (Suc j) = clock j + duration + draw j + extra j"
    unfolding clock_def by simp
  ultimately have "clock (Suc j) \<le> t + (duration + cap + lag)"
    using cap[OF j] dispatch[OF j] by linarith
  then have "clock ?i \<le> max t (clock first_capped) + (duration + cap + lag)"
    using i by (cases "clock first_capped \<le> t") (simp_all add: max_def)
  then show thesis using timing by (intro that[of ?i]) blast+
qed

theorem recurring_open_capped_quiet_draws:
  fixes initial duration :: nat and draw extra :: "nat \<Rightarrow> nat"
  assumes positive: "\<And>i. 0 < draw i"
    and cap: "\<And>i. first_capped \<le> i \<Longrightarrow> draw i \<le> cap"
    and dispatch: "\<And>i. first_capped \<le> i \<Longrightarrow> extra i \<le> lag"
  defines "clock \<equiv> election_wakeup_times initial duration draw extra"
  assumes cuts: "\<And>i. first_capped \<le> i \<Longrightarrow>
    continuously_open_draw c rivals (clock i) duration cap first lag work_tail window_length (drained i) (pending i)"
  obtains i choice where "first_capped \<le> i" "t < clock i"
    "clock i \<le> max t (clock first_capped) + (duration + cap + lag)"
    "legal_retry_jitter cap choice" "legal_retry_jitter cap cap"
    "first \<le> choice" "choice + lag + window_length < cap"
    "\<And>n. n \<in> rivals \<Longrightarrow>
      \<not> wake_collision lag work_tail window_length (old_due i n) (clock i + duration + choice)"
proof -
  obtain i where later: "first_capped \<le> i" "t < clock i"
    "clock i \<le> max t (clock first_capped) + (duration + cap + lag)"
    unfolding clock_def by (rule continuously_open_arming_recurs[OF positive cap dispatch])
  interpret cut: continuously_open_draw c rivals "old_due i" "clock i"
      duration cap first lag work_tail window_length "drained i" "pending i"
    by (rule cuts[OF later(1)])
  show thesis
    by (rule cut.continuously_open_has_legal_quiet_draw) (rule that[OF later])
qed

text \<open>
  Thus no reset or quorum flap is needed for repeated arming. It is
  still necessary that stalled executions keep an eligible open
  scheduler, that its old work drains by the cut, and that retained
  publication deadlines leave room. Arming recurrence alone does not
  ensure any of these conditions. The earlier synchronised execution
  shows that legal draws need not realise the favourable choice.
  A subsequent opportunity can be chosen strictly after the preceding
  window's horizon.
  Given repeated opportunities while stalled, a uniform conditional
  bound on the observations and completion within each window can be
  supplied to retry_observation_bound_tends_to_zero. The timing argument
  does not establish that service, authority or conditional support.
\<close>

end
