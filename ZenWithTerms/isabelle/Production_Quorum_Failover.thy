theory Production_Quorum_Failover
  imports Fixed_Configuration Production_Recovery_Retries Coordination_Transport
begin

section \<open>Quorum-backed pre-vote authorization\<close>

text \<open>
  This is a proposed protocol for the policy discussed in Elasticsearch issue
  80400. LeaderChecker and FollowersChecker probe reachability or health,
  while LagDetector and the publication timeout track other parts of the
  publication path. A responsive incumbent can still be unable to publish.
  A voter in this protocol samples known pending work and its last observed
  committed rank in the same incumbent term. Work must still be pending at
  the second sample and the rank must be unchanged for the observation interval.

  An implementation needs authenticated peer identities, a local source of
  pending-work and commit observations, a fresh generation per round, and a
  bounded validity interval measured in the model clock. The local snapshot
  supplied to each control operation identifies the incumbent, term,
  candidate, accepted and committed voting configurations, and known progress.
  The candidate refreshes this snapshot on progress or a view change. The
  clocks below abstract the deadline comparison. A wire protocol would need
  to implement that comparison, for example by bounding expiry against the
  candidate's own round deadline.

  Report work runs on voters and the candidate, and authorize and open run
  on the candidate. Report delivery represents completion of the voter's
  observation handler and authenticated transport to the candidate. Neither
  delivery nor control invokes incumbent work. The protocol opens at most one
  pre-vote attempt per round when the candidate uses fresh, nonrecurring views.
  Evidence carries no pre-votes and grants no election,
  storage, or publication permission. A stateless lease replacement policy
  would also have to meet the stateless lease requirements.
\<close>

record failover_view =
  live_round :: replacement_round
  live_commit :: rank
  live_pending :: bool

record failover_envelope =
  evidence_view :: failover_view
  evidence_report :: replacement_report

record failover_protocol =
  evidence_inbox :: "failover_envelope set"
  approved_attempt :: "(failover_view \<times> config) option"
  opened_attempt :: "failover_view option"

definition failover_initial where
  "failover_initial = \<lparr>evidence_inbox = {}, approved_attempt = None, opened_attempt = None\<rparr>"

definition observed_evidence where
  "observed_evidence view ttl n after =
    \<lparr>evidence_view = view,
     evidence_report = \<lparr>reporting_voter = n, reported_round = live_round view,
        expires = observed_at after + ttl\<rparr>\<rparr>"

definition view_reports where
  "view_reports view inbox = image evidence_report {e\<in>inbox. evidence_view e = view}"

definition failover_authority where
  "failover_authority healthy view now s Q \<longleftrightarrow> live_pending view \<and>
    alternative_authority (live_round view) (request_generation (live_round view)) now
      (view_reports view (evidence_inbox s)) healthy Q"

datatype failover_job = Deliver_Evidence node | Authorize_Failover | Open_Pre_Vote

inductive failover_control :: "node set \<Rightarrow> (node \<Rightarrow> detector_view) \<Rightarrow> failover_view \<Rightarrow>
    nat \<Rightarrow> failover_job \<Rightarrow> failover_protocol \<Rightarrow> failover_protocol \<Rightarrow> bool"
  for healthy where
  deliver:
    "n \<in> healthy \<Longrightarrow> replacement_candidate (live_round view) \<in> healthy \<Longrightarrow>
     n \<noteq> replaced_leader (live_round view) \<Longrightarrow>
     replacement_candidate (live_round view) \<noteq> replaced_leader (live_round view) \<Longrightarrow>
     can_dispatch (local n) \<Longrightarrow> can_dispatch (local (replacement_candidate (live_round view))) \<Longrightarrow>
     live_pending view \<Longrightarrow>
     observes_stalled_publication (live_round view) threshold (before::progress_observation) (after::progress_observation) \<Longrightarrow>
     observed_committed after = live_commit view \<Longrightarrow>
     observed_at after \<le> now \<Longrightarrow> now < observed_at after + ttl \<Longrightarrow>
     failover_control healthy local view now (Deliver_Evidence n) s
       (s\<lparr>evidence_inbox := insert (observed_evidence view ttl n after) (evidence_inbox s)\<rparr>)"
| authorize:
    "can_dispatch (local (replacement_candidate (live_round view))) \<Longrightarrow>
     failover_authority healthy view now s Q \<Longrightarrow>
     failover_control healthy local view now Authorize_Failover s (s\<lparr>approved_attempt := Some (view,Q)\<rparr>)"
| open_attempt:
    "can_dispatch (local (replacement_candidate (live_round view))) \<Longrightarrow>
     approved_attempt s = Some (view,Q) \<Longrightarrow> opened_attempt s \<noteq> Some view \<Longrightarrow>
     failover_authority healthy view now s Q \<Longrightarrow>
     failover_control healthy local view now Open_Pre_Vote s (s\<lparr>opened_attempt := Some view\<rparr>)"

lemma failover_open_requires_current_quorum:
  assumes "failover_control healthy local view now Open_Pre_Vote s s'"
  obtains Q where "approved_attempt s = Some (view,Q)"
    "quorum (accepted_voters (live_round view)) Q" "quorum (committed_voters (live_round view)) Q"
    "replaced_leader (live_round view) \<notin> Q"
    "\<And>n. n \<in> Q \<Longrightarrow> \<exists>e\<in>evidence_inbox s.
      evidence_view e = view \<and> reporting_voter (evidence_report e) = n \<and>
      reported_round (evidence_report e) = live_round view \<and> now < expires (evidence_report e)"
proof -
  from assms obtain Q where approved: "approved_attempt s = Some (view,Q)"
    and auth: "failover_authority healthy view now s Q"
    by (cases rule: failover_control.cases) auto
  have accepted: "quorum (accepted_voters (live_round view)) Q"
    and committed: "quorum (committed_voters (live_round view)) Q"
    and alternate: "replaced_leader (live_round view) \<notin> Q"
    using auth unfolding failover_authority_def alternative_authority_def by blast+
  have evidence: "\<exists>e\<in>evidence_inbox s.
      evidence_view e = view \<and> reporting_voter (evidence_report e) = n \<and>
      reported_round (evidence_report e) = live_round view \<and> now < expires (evidence_report e)"
    if "n \<in> Q" for n
    using auth that unfolding failover_authority_def alternative_authority_def report_valid_def view_reports_def
    by blast
  show thesis by (rule that[OF approved accepted committed alternate evidence])
qed

lemma expired_or_mismatched_reports_cannot_authorize:
  assumes stale: "\<And>e. e \<in> evidence_inbox s \<Longrightarrow>
    evidence_view e \<noteq> view \<or> now \<ge> expires (evidence_report e)"
  shows "\<not> failover_authority healthy view now s Q"
proof
  assume auth: "failover_authority healthy view now s Q"
  then have quorum: "quorum (committed_voters (live_round view)) Q"
    unfolding failover_authority_def alternative_authority_def by blast
  obtain n where "n \<in> Q" using quorum_intersects[OF quorum quorum] by blast
  with auth obtain e where "e \<in> evidence_inbox s" "evidence_view e = view" "now < expires (evidence_report e)"
    unfolding failover_authority_def alternative_authority_def report_valid_def view_reports_def by blast
  with stale[OF this(1)] show False by simp
qed

lemma stale_authorization_cannot_open:
  assumes "approved_attempt s = Some (old,Q)" "old \<noteq> view"
  shows "\<not> failover_control healthy local view now Open_Pre_Vote s s'"
  using assms by (auto elim: failover_control.cases)

lemma old_configuration_cannot_authorize:
  assumes changed: "accepted_voters (live_round old) \<noteq> accepted_voters (live_round view) \<or>
      committed_voters (live_round old) \<noteq> committed_voters (live_round view)"
    and inbox: "\<And>e. e \<in> evidence_inbox s \<Longrightarrow> evidence_view e = old"
  shows "\<not> failover_authority healthy view now s Q"
proof -
  have "old \<noteq> view" using changed by auto
  with inbox show ?thesis by (intro expired_or_mismatched_reports_cannot_authorize) auto
qed

definition fresh_failover_views where
  "fresh_failover_views live \<longleftrightarrow> (\<forall>i j. (i::nat) \<le> j \<longrightarrow>
    (live i \<noteq> live j \<longrightarrow> request_generation (live_round (live i)) < request_generation (live_round (live j))))"

lemma obsolete_view_never_recurs:
  assumes fresh: "fresh_failover_views live"
    and indices: "i \<le> j" "j \<le> k" and changed: "live i \<noteq> live j"
  shows "live i \<noteq> live k"
proof
  assume same: "live i = live k"
  note increasing = fresh[unfolded fresh_failover_views_def, rule_format]
  have first: "request_generation (live_round (live i)) < request_generation (live_round (live j))"
    by (rule increasing[OF indices(1) changed])
  have distinct: "live j \<noteq> live k" using same changed by auto
  have second: "request_generation (live_round (live j)) < request_generation (live_round (live k))"
    by (rule increasing[OF indices(2) distinct])
  have "request_generation (live_round (live i)) < request_generation (live_round (live k))"
    by (rule less_trans[OF first second])
  then show False using same by simp
qed

section \<open>Bounded service when the incumbent is stalled\<close>

definition failover_jobs where
  "failover_jobs Q = image Deliver_Evidence Q \<union> {Authorize_Failover, Open_Pre_Vote}"

fun failover_dependencies where
  "failover_dependencies Q (Deliver_Evidence n) = {}"
| "failover_dependencies Q Authorize_Failover = image Deliver_Evidence Q"
| "failover_dependencies Q Open_Pre_Vote = {Authorize_Failover}"

definition failover_from_work where
  "failover_from_work view Q ttl after done =
    \<lparr>evidence_inbox = image (\<lambda>n. observed_evidence view ttl n (after n)) {n\<in>Q. Deliver_Evidence n \<in> done},
     approved_attempt = (if Authorize_Failover \<in> done then Some (view,Q) else None),
     opened_attempt = (if Open_Pre_Vote \<in> done then Some view else None)\<rparr>"

lemma failover_from_empty_work:
  "failover_from_work view Q ttl after {} = failover_initial"
  by (simp add: failover_from_work_def failover_initial_def)

lemma delivered_quorum_supplies_authority:
  assumes delivered: "image Deliver_Evidence Q \<subseteq> done"
    and pending: "live_pending view"
    and health: "replacement_candidate (live_round view) \<in> healthy" "Q \<subseteq> healthy"
    and alternate: "replacement_candidate (live_round view) \<noteq> replaced_leader (live_round view)"
      "replaced_leader (live_round view) \<notin> Q"
    and quorum: "quorum (committed_voters (live_round view)) Q" "quorum (accepted_voters (live_round view)) Q"
    and expiry: "\<And>n. n \<in> Q \<Longrightarrow> now < observed_at (after n) + ttl"
  shows "failover_authority healthy view now (failover_from_work view Q ttl after done) Q"
proof -
  have evidence: "\<exists>p\<in>view_reports view (evidence_inbox (failover_from_work view Q ttl after done)).
      reporting_voter p = n \<and> report_valid (live_round view) (request_generation (live_round view)) now p"
    if n: "n \<in> Q" for n
  proof -
    have "Deliver_Evidence n \<in> done" using delivered n by blast
    with n have inbox: "observed_evidence view ttl n (after n) \<in>
        evidence_inbox (failover_from_work view Q ttl after done)"
      by (auto simp: failover_from_work_def)
    have envelope: "observed_evidence view ttl n (after n) \<in>
        {e\<in>evidence_inbox (failover_from_work view Q ttl after done). evidence_view e = view}"
      using inbox by (simp add: observed_evidence_def)
    from imageI[OF envelope, of evidence_report] have report:
      "evidence_report (observed_evidence view ttl n (after n)) \<in>
        view_reports view (evidence_inbox (failover_from_work view Q ttl after done))"
      unfolding view_reports_def .
    show ?thesis
      by (rule bexI[of _ "evidence_report (observed_evidence view ttl n (after n))"])
        (use report expiry[OF n] in \<open>auto simp: observed_evidence_def report_valid_def\<close>)
  qed
  show ?thesis unfolding failover_authority_def alternative_authority_def
    using pending health alternate quorum evidence by blast
qed

lemma failover_service_step:
  assumes sorted: "ordered_work (failover_jobs Q) (failover_dependencies Q) done"
    and ready: "work_ready (failover_jobs Q) (failover_dependencies Q) done job"
    and pending: "live_pending view"
    and health: "replacement_candidate (live_round view) \<in> healthy" "Q \<subseteq> healthy"
    and alternate: "replacement_candidate (live_round view) \<noteq> replaced_leader (live_round view)"
      "replaced_leader (live_round view) \<notin> Q"
    and quorum: "quorum (committed_voters (live_round view)) Q" "quorum (accepted_voters (live_round view)) Q"
    and candidate: "can_dispatch (local (replacement_candidate (live_round view)))"
    and voter: "\<And>n. n \<in> Q \<Longrightarrow> can_dispatch (local n)"
    and observed: "\<And>n. n \<in> Q \<Longrightarrow>
      observes_stalled_publication (live_round view) threshold (before n::progress_observation) (after n::progress_observation)"
    and sampled: "\<And>n. n \<in> Q \<Longrightarrow> observed_committed (after n) = live_commit view"
    and timed: "\<And>n. n \<in> Q \<Longrightarrow> observed_at (after n) \<le> now"
    and expiry: "\<And>n. n \<in> Q \<Longrightarrow> now < observed_at (after n) + ttl"
  shows "failover_control healthy local view now job (failover_from_work view Q ttl after done)
      (failover_from_work view Q ttl after (insert job done))"
proof (cases job)
  case (Deliver_Evidence n)
  with ready have n: "n \<in> Q" by (auto simp: work_ready_def failover_jobs_def)
  have "n \<in> healthy" using n health by blast
  moreover have "n \<noteq> replaced_leader (live_round view)" using n alternate by blast
  ultimately have "failover_control healthy local view now (Deliver_Evidence n)
      (failover_from_work view Q ttl after done)
      ((failover_from_work view Q ttl after done)\<lparr>evidence_inbox :=
         insert (observed_evidence view ttl n (after n)) (evidence_inbox (failover_from_work view Q ttl after done))\<rparr>)"
    by (rule failover_control.deliver[OF _ health(1) _ alternate(1) voter[OF n] candidate pending
      observed[OF n] sampled[OF n] timed[OF n] expiry[OF n]])
  moreover have "{v\<in>Q. Deliver_Evidence v \<in> insert job done} = insert n {v\<in>Q. Deliver_Evidence v \<in> done}"
    using Deliver_Evidence n by auto
  ultimately show ?thesis using Deliver_Evidence by (simp add: failover_from_work_def)
next
  case Authorize_Failover
  with ready have delivered: "image Deliver_Evidence Q \<subseteq> done" by (simp add: work_ready_def)
  have auth: "failover_authority healthy view now (failover_from_work view Q ttl after done) Q"
    by (rule delivered_quorum_supplies_authority[OF delivered pending health alternate quorum expiry])
  from failover_control.authorize[where local=local and view=view, OF candidate auth] show ?thesis
    using Authorize_Failover by (simp add: failover_from_work_def)
next
  case Open_Pre_Vote
  with ready have approved: "Authorize_Failover \<in> done" and not_open: "Open_Pre_Vote \<notin> done"
    by (auto simp: work_ready_def)
  from sorted approved have delivered: "image Deliver_Evidence Q \<subseteq> done"
    unfolding ordered_work_def by (metis failover_dependencies.simps(2))
  have auth: "failover_authority healthy view now (failover_from_work view Q ttl after done) Q"
    by (rule delivered_quorum_supplies_authority[OF delivered pending health alternate quorum expiry])
  have "approved_attempt (failover_from_work view Q ttl after done) = Some (view,Q)"
    and "opened_attempt (failover_from_work view Q ttl after done) \<noteq> Some view"
    using approved not_open by (simp_all add: failover_from_work_def)
  from failover_control.open_attempt[where local=local and view=view, OF candidate this auth] show ?thesis
    using Open_Pre_Vote by (simp add: failover_from_work_def)
qed

theorem healthy_alternative_opens_pre_vote:
  fixes live :: "nat \<Rightarrow> failover_view"
  assumes service: "bounded_service (failover_jobs Q) (failover_dependencies Q) select B H"
    and horizon: "3 * B \<le> H"
    and stable: "\<And>i. i \<le> 3 * B \<Longrightarrow> live (start + i) = view"
    and pending: "live_pending view"
    and health: "replacement_candidate (live_round view) \<in> healthy" "Q \<subseteq> healthy"
    and alternate: "replacement_candidate (live_round view) \<noteq> replaced_leader (live_round view)"
      "replaced_leader (live_round view) \<notin> Q"
    and quorum: "quorum (committed_voters (live_round view)) Q" "quorum (accepted_voters (live_round view)) Q"
    and candidate: "\<And>i. i < 3 * B \<Longrightarrow> can_dispatch (local (start + i) (replacement_candidate (live_round view)))"
    and voters: "\<And>n i. n \<in> Q \<Longrightarrow> i < 3 * B \<Longrightarrow> can_dispatch (local (start + i) n)"
    and observed: "\<And>n. n \<in> Q \<Longrightarrow>
      observes_stalled_publication (live_round view) threshold (before n::progress_observation) (after n::progress_observation)"
    and sampled: "\<And>n. n \<in> Q \<Longrightarrow> observed_committed (after n) = live_commit view"
    and sampled_by_start: "\<And>n. n \<in> Q \<Longrightarrow> observed_at (after n) \<le> start"
    and expiry: "\<And>n. n \<in> Q \<Longrightarrow> start + 3 * B < observed_at (after n) + ttl"
  obtains state where
    "state 0 = failover_initial"
    "\<And>i. i < 3 * B \<Longrightarrow> state (Suc i) = state i \<or>
      (\<exists>job. select i = Some job \<and> failover_control healthy (local (start + i)) (live (start + i))
        (start + i) job (state i) (state (Suc i)))"
    "approved_attempt (state (2 * B)) = Some (view,Q)"
    "opened_attempt (state (3 * B)) = Some view"
proof -
  let ?done = "completed_work (failover_jobs Q) (failover_dependencies Q) select"
  let ?state = "\<lambda>i. failover_from_work view Q ttl after (?done i)"
  have init: "?state 0 = failover_initial" by (simp add: failover_from_empty_work)
  have step: "?state (Suc i) = ?state i \<or> (\<exists>job. select i = Some job \<and>
      failover_control healthy (local (start + i)) (live (start + i)) (start + i) job (?state i) (?state (Suc i)))"
    if i: "i < 3 * B" for i
  proof (cases "?done (Suc i) = ?done i")
    case True
    then show ?thesis by simp
  next
    case False
    then obtain job where selected: "select i = Some job" and
      ready: "work_ready (failover_jobs Q) (failover_dependencies Q) (?done i) job" and
      completed: "?done (Suc i) = insert job (?done i)"
      using completed_work_change[of "failover_jobs Q" "failover_dependencies Q" select i] by blast
    have early: "observed_at (after n) \<le> start + i" and live_evidence: "start + i < observed_at (after n) + ttl"
      if "n \<in> Q" for n
      using sampled_by_start[OF that] expiry[OF that] i by linarith+
    have "failover_control healthy (local (start + i)) view (start + i) job (?state i) (?state (Suc i))"
      unfolding completed
      by (rule failover_service_step[where local="local (start + i)" and view=view and
            before=before and after=after and now="start + i" and ttl=ttl,
            OF ordered_completed_work ready pending health alternate quorum
            candidate[OF i] voters[OF _ i] observed sampled early live_evidence])
    with selected stable[of i] i show ?thesis by auto
  qed
  have first_time: "0 + B \<le> H" using horizon by linarith
  have deliveries: "image Deliver_Evidence Q \<subseteq> failover_jobs Q"
    by (auto simp: failover_jobs_def)
  have enabled_delivery: "failover_dependencies Q a \<subseteq> ?done 0" if "a \<in> image Deliver_Evidence Q" for a
    using that by auto
  have "image Deliver_Evidence Q \<subseteq> ?done (0 + B)"
    by (rule bounded_service_finishes_group[OF service first_time deliveries enabled_delivery])
  then have delivered: "image Deliver_Evidence Q \<subseteq> ?done B" by simp
  have second_time: "B + B \<le> H" using horizon by linarith
  have enabled_auth: "failover_dependencies Q a \<subseteq> ?done B" if "a \<in> {Authorize_Failover}" for a
    using delivered that by simp
  have "{Authorize_Failover} \<subseteq> ?done (B + B)"
    by (rule bounded_service_finishes_group[OF service second_time _ enabled_auth]) (simp add: failover_jobs_def)
  moreover have "B + B = 2 * B" by linarith
  ultimately have authorized: "Authorize_Failover \<in> ?done (2 * B)" by simp
  have third_time: "2 * B + B \<le> H" using horizon by linarith
  have enabled_open: "failover_dependencies Q a \<subseteq> ?done (2 * B)" if "a \<in> {Open_Pre_Vote}" for a
    using authorized that by simp
  have "{Open_Pre_Vote} \<subseteq> ?done (2 * B + B)"
    by (rule bounded_service_finishes_group[OF service third_time _ enabled_open]) (simp add: failover_jobs_def)
  moreover have "2 * B + B = 3 * B" by linarith
  ultimately have opened: "Open_Pre_Vote \<in> ?done (3 * B)" by simp
  show thesis by (rule that[OF init step]) (simp_all add: failover_from_work_def authorized opened)
qed

lemma failover_ignores_incumbent_dispatch:
  assumes "failover_control healthy local view now job s s'"
  shows "failover_control healthy (local(replaced_leader (live_round view) := blocked)) view now job s s'"
proof (use assms in \<open>cases rule: failover_control.cases\<close>)
  case deliver
  then show ?thesis by (metis failover_control.deliver fun_upd_other)
next
  case authorize
  then have "replacement_candidate (live_round view) \<noteq> replaced_leader (live_round view)"
    unfolding failover_authority_def alternative_authority_def by blast
  then show ?thesis using authorize by (metis failover_control.authorize fun_upd_other)
next
  case open_attempt
  then have "replacement_candidate (live_round view) \<noteq> replaced_leader (live_round view)"
    unfolding failover_authority_def alternative_authority_def by blast
  then show ?thesis using open_attempt by (metis failover_control.open_attempt fun_upd_other)
qed

section \<open>Stuttering projection onto existing safety machines\<close>

inductive failover_extension_step for ordinary healthy where
  regular: "ordinary x x' \<Longrightarrow> failover_extension_step ordinary healthy (x,s) (x',s)"
| policy: "failover_control healthy local view now job s s' \<Longrightarrow>
    failover_extension_step ordinary healthy (x,s) (x,s')"

inductive failover_extension_reachable for init ordinary healthy where
  init: "init x \<Longrightarrow> failover_extension_reachable init ordinary healthy (x, failover_initial)"
| advance: "failover_extension_reachable init ordinary healthy u \<Longrightarrow>
    failover_extension_step ordinary healthy u u' \<Longrightarrow>
    failover_extension_reachable init ordinary healthy u'"

lemma failover_extension_stutters:
  assumes "failover_extension_step ordinary healthy u u'"
  shows "fst u' = fst u \<or> ordinary (fst u) (fst u')"
  using assms by (cases rule: failover_extension_step.cases) auto

lemma failover_extension_invariant:
  assumes run: "failover_extension_reachable init ordinary healthy u"
    and initial: "\<And>x. init x \<Longrightarrow> P x"
    and ordinary: "\<And>x x'. P x \<Longrightarrow> ordinary x x' \<Longrightarrow> P x'"
  shows "P (fst u)"
  using run by induction (auto intro: initial ordinary dest!: failover_extension_stutters)

theorem failover_fixed_projection:
  assumes "failover_extension_reachable (\<lambda>x. x = initial) (Fixed_Configuration.step V) healthy (s,p)"
  shows "Fixed_Configuration.reachable V s"
  using failover_extension_invariant[OF assms, of "Fixed_Configuration.reachable V"]
  by (auto intro: Fixed_Configuration.reachable.intros)

theorem failover_dynamic_projection:
  assumes "failover_extension_reachable (\<lambda>x. x = bootstrapped C \<and> finite C \<and> C \<noteq> {})
    (transition C) healthy (s,p)"
  shows "dynamic_reachable C s"
  using failover_extension_invariant[OF assms, of "dynamic_reachable C"]
  by (auto intro: dynamic_reachable.intros)

theorem failover_dynamic_safety:
  assumes run: "failover_extension_reachable (\<lambda>x. x = bootstrapped C \<and> finite C \<and> C \<noteq> {})
    (transition C) healthy (s,p)"
  shows "a \<in> quorum_commits s \<Longrightarrow> b \<in> quorum_commits s \<Longrightarrow> prefix a b \<or> prefix b a"
    "a \<in> publications s \<Longrightarrow> b \<in> publications s \<Longrightarrow> position a = position b \<Longrightarrow> a = b"
    "certificate s (c,t) = Some e \<Longrightarrow> certificate s (d,t) = Some f \<Longrightarrow> c = d"
proof -
  have reach: "dynamic_reachable C s" by (rule failover_dynamic_projection[OF run])
  show "a \<in> quorum_commits s \<Longrightarrow> b \<in> quorum_commits s \<Longrightarrow> prefix a b \<or> prefix b a"
    by (fact dynamic_committed_states_form_chain[OF reach])
  show "a \<in> publications s \<Longrightarrow> b \<in> publications s \<Longrightarrow> position a = position b \<Longrightarrow> a = b"
    by (fact dynamic_unique_publication[OF reach])
  show "certificate s (c,t) = Some e \<Longrightarrow> certificate s (d,t) = Some f \<Longrightarrow> c = d"
    by (fact dynamic_one_election_candidate_per_term[OF reach])
qed

definition transport_pair_step where
  "transport_pair_step N E V C v x y \<longleftrightarrow> transport_step N E V C v (fst x) (snd x) (fst y) (snd y)"

theorem failover_transport_projection:
  assumes run: "failover_extension_reachable
      (\<lambda>x. x = (coordinator_initial v versions, {}) \<and> default_strategy N E C \<and> v \<in> V)
      (transport_pair_step N E V C v) healthy ((s,H),p)"
  shows "transport_reachable N E V C v versions s H"
proof -
  let ?P = "\<lambda>x. transport_reachable N E V C v versions (fst x) (snd x)"
  have initial: "?P x" if "x = (coordinator_initial v versions, {}) \<and> default_strategy N E C \<and> v \<in> V" for x
    using that by (auto intro: transport_reachable.init)
  have advance: "?P x'" if "?P x" "transport_pair_step N E V C v x x'" for x x'
    using that unfolding transport_pair_step_def by (rule transport_reachable.step)
  from failover_extension_invariant[where P="?P", OF run initial advance] show ?thesis by simp
qed

corollary failover_transport_refines_tla:
  assumes "failover_extension_reachable
      (\<lambda>x. x = (coordinator_initial v versions, {}) \<and> default_strategy N E C \<and> v \<in> V)
      (transport_pair_step N E V C v) healthy ((s,H),p)"
  shows "\<exists>t. tla_reachable N V C v versions t \<and> configurations_ok E t \<and> coordination s = project_java E t"
  by (rule transport_refines_tla[OF failover_transport_projection[OF assms]])

end
