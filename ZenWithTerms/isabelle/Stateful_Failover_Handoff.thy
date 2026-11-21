theory Stateful_Failover_Handoff
  imports Production_Quorum_Failover Production_Window_Service
begin

section \<open>Report transport and round lifetime\<close>

text \<open>
  This is a source-level design for a stateful extension. Reports travel as
  replies to a candidate-issued challenge. The receiver must take the voter ID
  from the authenticated connection and match the reply to the outstanding
  request, rather than trusting a sender ID in the payload. The candidate
  starts and checks the deadline on its own monotonic clock. Each voter
  observes elapsed time in its own clock domain. Only the observation order
  relative to receipt of the challenge is checked on that clock. No voter
  timestamp is compared to a candidate timestamp.

  A round binds the candidate incarnation, incumbent, committed rank,
  pending-work condition and both voting configurations. The candidate must
  retire the token on a live-view change and use a new generation even if a
  later view has the same incumbent and configurations. A failed round can
  retire without waiting on the incumbent. An implementation still needs the
  authenticated request/reply path, a source of local publication progress
  observations and a source of non-repeating incarnation identifiers.
\<close>

record stateful_token =
  token_view :: failover_view
  token_incarnation :: nat
  token_issued :: nat
  token_deadline :: nat

record stateful_wire_report =
  echoed_token :: stateful_token
  challenge_observed :: nat
  first_sample :: progress_observation
  last_sample :: progress_observation

definition stateful_token_live where
  "stateful_token_live tok epoch_id view now \<longleftrightarrow>
    token_view tok = view \<and> token_incarnation tok = epoch_id \<and>
    token_issued tok \<le> now \<and> now < token_deadline tok"

definition checked_wire_report where
  "checked_wire_report tok threshold p \<longleftrightarrow>
    echoed_token p = tok \<and> challenge_observed p \<le> observed_at (last_sample p) \<and>
    observed_committed (last_sample p) = live_commit (token_view tok) \<and>
    observes_stalled_publication (live_round (token_view tok)) threshold (first_sample p) (last_sample p)"

definition envelope_from_peer where
  "envelope_from_peer tok n = \<lparr>evidence_view = token_view tok,
    evidence_report = \<lparr>reporting_voter = n, reported_round = live_round (token_view tok),
      expires = token_deadline tok\<rparr>\<rparr>"

definition checked_report_inbox where
  "checked_report_inbox tok threshold received =
    {envelope_from_peer tok n |n p. (n,p) \<in> received \<and> checked_wire_report tok threshold p}"

lemma checked_evidence_binds_authenticated_peer:
  assumes "e \<in> checked_report_inbox tok threshold received"
  shows "\<exists>p. (reporting_voter (evidence_report e),p) \<in> received \<and> checked_wire_report tok threshold p"
    "evidence_view e = token_view tok" "expires (evidence_report e) = token_deadline tok"
  using assms by (auto simp: checked_report_inbox_def envelope_from_peer_def)

theorem stateful_reports_supply_current_authority:
  assumes live: "stateful_token_live tok epoch_id view now" and pending: "live_pending view"
    and alternate: "replacement_candidate (live_round view) \<noteq> replaced_leader (live_round view)"
      "replacement_candidate (live_round view) \<in> healthy" "replaced_leader (live_round view) \<notin> X"
      "X \<subseteq> healthy"
    and q: "quorum (committed_voters (live_round view)) X" "quorum (accepted_voters (live_round view)) X"
    and reports: "\<And>n. n \<in> X \<Longrightarrow> \<exists>p. (n,p) \<in> received \<and> checked_wire_report tok threshold p"
  shows "failover_authority healthy view now
    (failover_initial\<lparr>evidence_inbox := checked_report_inbox tok threshold received\<rparr>) X"
proof -
  have verified: "\<exists>p\<in>view_reports view (checked_report_inbox tok threshold received).
      reporting_voter p = n \<and> report_valid (live_round view) (request_generation (live_round view)) now p"
    if n: "n \<in> X" for n
  proof -
    obtain r where source: "(n,r) \<in> received" "checked_wire_report tok threshold r"
      using reports[OF n] by blast
    have member: "envelope_from_peer tok n \<in> checked_report_inbox tok threshold received"
      unfolding checked_report_inbox_def using source by blast
    have "envelope_from_peer tok n \<in> {e\<in>checked_report_inbox tok threshold received. evidence_view e = view}"
      using live member by (simp add: stateful_token_live_def envelope_from_peer_def)
    then have report: "evidence_report (envelope_from_peer tok n) \<in>
        view_reports view (checked_report_inbox tok threshold received)"
      unfolding view_reports_def by (rule imageI)
    show ?thesis
      by (rule bexI[of _ "evidence_report (envelope_from_peer tok n)"])
        (use live report in \<open>simp_all add: stateful_token_live_def report_valid_def envelope_from_peer_def\<close>)
  qed
  show ?thesis
    using pending alternate q verified unfolding failover_authority_def alternative_authority_def by simp
qed

lemma obsolete_stateful_token_is_unusable:
  assumes "token_incarnation tok \<noteq> epoch_id \<or> token_view tok \<noteq> view \<or> token_deadline tok \<le> now"
  shows "\<not> stateful_token_live tok epoch_id view now"
  using assms by (auto simp: stateful_token_live_def)

lemma old_reply_does_not_match_fresh_challenge:
  assumes "echoed_token p = old"
    "token_incarnation old \<noteq> token_incarnation fresh \<or>
      request_generation (live_round (token_view old)) \<noteq> request_generation (live_round (token_view fresh))"
  shows "\<not> checked_wire_report fresh threshold p"
  using assms by (auto simp: checked_wire_report_def)

section \<open>Entering an authorized round and collecting ordinary pre-votes\<close>

datatype stateful_mode = Stateful_Follower node | Stateful_Candidate | Stateful_Leader

record stateful_coordinator =
  handoff_dispatch :: detector_view
  handoff_mode :: stateful_mode
  handoff_eligible :: bool
  handoff_health :: bool
  handoff_round :: "stateful_token option"
  handoff_current_term :: nat
  handoff_max_seen :: nat

definition stateful_entry_enabled where
  "stateful_entry_enabled healthy p X view epoch_id now tok a \<longleftrightarrow>
    stateful_token_live tok epoch_id view now \<and> opened_attempt p = Some view \<and>
    failover_authority healthy view now p X \<and>
    can_dispatch (handoff_dispatch a) \<and> handoff_health a \<and> handoff_eligible a \<and>
    (handoff_mode a = Stateful_Candidate \<or> handoff_mode a = Stateful_Follower (replaced_leader (live_round view)))"

definition enter_stateful_round where
  "enter_stateful_round tok a = a\<lparr>handoff_mode := Stateful_Candidate, handoff_round := Some tok\<rparr>"

definition retire_stateful_round where
  "retire_stateful_round tok a = (if handoff_round a = Some tok then a\<lparr>handoff_round := None\<rparr> else a)"

lemma old_round_retirement_leaves_replacement:
  assumes "handoff_round a = Some fresh" "old \<noteq> fresh"
  shows "retire_stateful_round old a = a"
  using assms by (simp add: retire_stateful_round_def)

lemma authorization_enters_from_matching_follower:
  assumes "stateful_entry_enabled healthy p X view epoch_id now tok a"
    "handoff_mode a = Stateful_Follower (replaced_leader (live_round view))"
  shows "handoff_mode (enter_stateful_round tok a) = Stateful_Candidate"
    "handoff_round (enter_stateful_round tok a) = Some tok"
    "handoff_current_term (enter_stateful_round tok a) = handoff_current_term a"
  by (simp_all add: enter_stateful_round_def)

theorem stateful_authority_can_open_from_follower:
  assumes token: "stateful_token_live tok epoch_id view now"
    and authority: "failover_authority healthy view now p X"
    and not_opened: "opened_attempt p \<noteq> Some view"
    and dispatch: "local (replacement_candidate (live_round view)) = handoff_dispatch a"
      "can_dispatch (handoff_dispatch a)"
    and candidate: "handoff_health a" "handoff_eligible a"
      "handoff_mode a = Stateful_Follower (replaced_leader (live_round view))"
  obtains p' p'' where
    "failover_control healthy local view now Authorize_Failover p p'"
    "failover_control healthy local view now Open_Pre_Vote p' p''"
    "stateful_entry_enabled healthy p'' X view epoch_id now tok a"
    "handoff_mode (enter_stateful_round tok a) = Stateful_Candidate"
    "handoff_round (enter_stateful_round tok a) = Some tok"
proof -
  let ?p' = "p\<lparr>approved_attempt := Some (view,X)\<rparr>"
  let ?p'' = "?p'\<lparr>opened_attempt := Some view\<rparr>"
  have available: "can_dispatch (local (replacement_candidate (live_round view)))" using dispatch by simp
  have authorize: "failover_control healthy local view now Authorize_Failover p ?p'"
    by (rule failover_control.authorize[where local=local and view=view, OF available authority])
  have open_round: "failover_control healthy local view now Open_Pre_Vote ?p' ?p''"
    by (rule failover_control.open_attempt[where local=local and view=view, OF available])
      (use not_opened authority in \<open>auto simp: failover_authority_def\<close>)
  have entry: "stateful_entry_enabled healthy ?p'' X view epoch_id now tok a"
    using token authority dispatch candidate by (auto simp: stateful_entry_enabled_def failover_authority_def)
  show thesis
    by (rule that[OF authorize open_round entry]) (simp_all add: enter_stateful_round_def)
qed

lemma renewed_round_outlives_a_late_retirement:
  assumes new: "token_incarnation old \<noteq> token_incarnation fresh \<or>
    request_generation (live_round (token_view old)) \<noteq> request_generation (live_round (token_view fresh))"
  shows "retire_stateful_round old (enter_stateful_round fresh a) = enter_stateful_round fresh a"
  using new by (auto simp: enter_stateful_round_def retire_stateful_round_def)

definition authorized_receiver where
  "authorized_receiver healthy p X epoch_id now tok origin view n local \<longleftrightarrow>
    stateful_token_live tok epoch_id view now \<and> origin = replacement_candidate (live_round view) \<and>
    n \<in> healthy \<and> can_dispatch local \<and>
    (ordinary_prevote origin (prevote_incumbent local) \<or>
      (prevote_incumbent local = Some (replaced_leader (live_round view)) \<and>
        opened_attempt p = Some view \<and> failover_authority healthy view now p X))"

lemma authorization_does_not_override_a_new_leader:
  assumes "prevote_incumbent local = Some d" "d \<noteq> origin" "d \<noteq> replaced_leader (live_round view)"
  shows "\<not> authorized_receiver healthy p X epoch_id now tok origin view n local"
  using assms by (simp add: authorized_receiver_def ordinary_prevote_def)

definition stateful_prevote_result where
  "stateful_prevote_result healthy p X epoch_id now tok origin view peer local captured returned
     \<longleftrightarrow>
    authorized_receiver healthy p X epoch_id now tok origin view peer local \<and> returned \<le> captured"

lemma authorized_healthy_voter_can_reply_while_remembering_incumbent:
  assumes live: "stateful_token_live tok epoch_id view now" "opened_attempt p = Some view"
    and authority: "failover_authority healthy view now p X"
    and voter: "n \<in> X" "can_dispatch local" "prevote_incumbent local = Some (replaced_leader (live_round view))"
    and fresh: "returned \<le> captured"
  defines "origin \<equiv> replacement_candidate (live_round view)"
  shows "stateful_prevote_result healthy p X epoch_id now tok origin view n local captured returned"
    "\<not> ordinary_prevote origin (prevote_incumbent local)"
proof -
  from authority have "X \<subseteq> healthy" "origin \<noteq> replaced_leader (live_round view)"
    unfolding failover_authority_def alternative_authority_def origin_def by blast+
  with assms show "stateful_prevote_result healthy p X epoch_id now tok origin view n local captured returned"
    by (auto simp: stateful_prevote_result_def authorized_receiver_def)
  from \<open>origin \<noteq> replaced_leader (live_round view)\<close> voter(3)
  show "\<not> ordinary_prevote origin (prevote_incumbent local)" by (simp add: ordinary_prevote_def)
qed

definition stateful_start_join where
  "stateful_start_join epoch_id now tok view a t \<longleftrightarrow>
    stateful_token_live tok epoch_id view now \<and> handoff_round a = Some tok \<and>
    handoff_mode a = Stateful_Candidate \<and> can_dispatch (handoff_dispatch a) \<and> handoff_eligible a \<and>
    t = Suc (max (handoff_current_term a) (handoff_max_seen a))"

lemma stateful_start_rechecks_mode_and_term:
  assumes "stateful_start_join epoch_id now tok view a t"
  shows "handoff_mode a = Stateful_Candidate" "handoff_current_term a < t" "handoff_max_seen a < t"
  using assms by (simp_all add: stateful_start_join_def)

text \<open>
  Entry represents a dispatched call to becomeCandidate under the candidate's
  own mutex, after revalidating the authorized view; a follower of the named
  incumbent may enter. Mode changes otherwise follow Coordinator. The ordinary
  scheduler in Coordinator checks candidate mode, eligibility and health
  before calling the collector. A proposed separate authorized handler must
  verify the challenge and matched open authority before overriding the
  remembered-incumbent rejection in StatefulPreVoteCollector. It must leave
  the receiver's health gate, the sender's accepted-term/version comparison,
  and the collector's default election-quorum test intact. A claimed sender
  cannot stand in for the transport peer. For example, an override request
  could carry voter attestations signed over the challenge and samples, so
  other voters can verify the authority without trusting forwarded sender
  fields. Voters check the authenticated candidate, proof, and their own
  remembered incumbent; the candidate rejects a returned pre-vote after
  invalidation or expiry against its own monotonic deadline. The model gates
  both checks at one logical successful response step. The candidate still
  rechecks mode and eligibility under its
  mutex on entry to startElection. Its freshly observed term floor determines
  the proposed term, and voters must still accept the ordinary StartJoin.
\<close>

section \<open>Binding the authorized prefix to the ordinary production window\<close>

context dynamic_publication_window
begin

definition stateful_prefix_binding where
  "stateful_prefix_binding healthy p X epoch_id start tok view a live local select limit \<longleftrightarrow>
    view = token_view tok \<and> replacement_candidate (live_round view) = c \<and>
    committed_voters (live_round view) = committed_config s c \<and>
    accepted_voters (live_round view) = config_of C (durable_history s c) \<and>
    (\<forall>i<limit. (\<forall>n. select i = Some (Prevote n) \<longrightarrow>
      handoff_round (a i) = Some tok \<and> handoff_mode (a i) = Stateful_Candidate \<and>
      handoff_health (a i) \<and> handoff_eligible (a i) \<and> can_dispatch (handoff_dispatch (a i)) \<and>
      stateful_prevote_result healthy p X epoch_id (start+i) tok c (live i) n (local i n)
        (position (durable_history s c)) (position (durable_history s n))) \<and>
      (select i = Some Choose_Term \<longrightarrow>
        stateful_start_join epoch_id (start+i) tok (live i) (a i) t))"

lemma selected_vote_matches_current_view_and_freshness:
  assumes bind: "stateful_prefix_binding healthy p X epoch_id start tok view a live local select limit"
    and tick: "i < limit" "select i = Some (Prevote n)"
  shows "live i = view" "position (durable_history s n) \<le> position (durable_history s c)"
proof -
  have result: "stateful_prevote_result healthy p X epoch_id (start+i) tok c (live i) n (local i n)
       (position (durable_history s c)) (position (durable_history s n))"
    using bind tick by (auto simp: stateful_prefix_binding_def)
  have "view = token_view tok" using bind by (simp add: stateful_prefix_binding_def)
  with result show "live i = view"
    by (auto simp: stateful_prevote_result_def authorized_receiver_def stateful_token_live_def)
  show "position (durable_history s n) \<le> position (durable_history s c)"
    by (rule conjunct2[OF result[unfolded stateful_prevote_result_def]])
qed

lemma stateful_first_selection_has_guard:
  assumes bind: "stateful_prefix_binding healthy p X epoch_id start tok view a live local select limit"
    and tick: "i < limit" "select i = Some Choose_Term"
  shows "stateful_start_join epoch_id (start+i) tok (live i) (a i) t"
  using bind tick by (auto simp: stateful_prefix_binding_def)

lemma start_join_step_is_one_shot:
  assumes one: "work_ready jobs deps (finished select i) Choose_Term" "select i = Some Choose_Term"
    and later: "i < j"
  shows "\<not> work_ready jobs deps (finished select j) Choose_Term"
proof -
  have "Choose_Term \<in> finished select (Suc i)"
    using one by (simp add: Let_def)
  moreover have "finished select (Suc i) \<subseteq> finished select j"
    by (rule completed_work_mono) (use later in simp)
  ultimately show ?thesis by (auto simp: work_ready_def)
qed

lemma stateful_work_selection_witness:
  assumes "op \<in> finished select bound"
  shows "\<exists>i<bound. select i = Some op \<and> work_ready jobs deps (finished select i) op"
  using assms
proof (induction bound)
  case 0
  then show ?case by simp
next
  case (Suc i)
  have previous: "\<exists>j<Suc i. select j = Some op \<and> work_ready jobs deps (finished select j) op"
    if "op \<in> finished select i"
    using Suc.IH[OF that] by (auto intro: less_SucI)
  show ?case
    using Suc.prems completed_work_change[of jobs deps select i] previous by (auto intro!: lessI)
qed

theorem authorized_stateful_window_starts_join:
  assumes service: "bounded_service jobs deps select B H" and time: "2 * B \<le> H"
    and bind: "stateful_prefix_binding healthy p X epoch_id start tok view a live local select H"
  obtains i where "i < 2 * B" "select i = Some Choose_Term"
    "stateful_start_join epoch_id (start+i) tok (live i) (a i) t"
    "work_ready jobs deps (finished select i) Choose_Term"
    "quorum (committed_voters (live_round view)) E" "quorum (accepted_voters (live_round view)) E"
    "\<And>n. n \<in> E \<Longrightarrow> \<exists>j<i. select j = Some (Prevote n) \<and>
      stateful_prevote_result healthy p X epoch_id (start+j) tok c (live j) n (local j n)
        (position (durable_history s c)) (position (durable_history s n))"
proof -
  have shape: "waves = take 2 waves @ drop 2 waves" by simp
  have "Choose_Term \<in> finished select (2*B)"
    using dynamic_window_prefix[OF service shape] time by (simp add: dynamic_window_waves_def numeral_eq_Suc)
  then obtain i where i: "i < 2*B" "select i = Some Choose_Term"
    "work_ready jobs deps (finished select i) Choose_Term"
    using stateful_work_selection_witness by blast
  have guard: "stateful_start_join epoch_id (start+i) tok (live i) (a i) t"
    by (rule stateful_first_selection_has_guard[OF bind _ i(2)]) (use time i in linarith)
  have view_q: "committed_voters (live_round view) = committed_config s c"
    "accepted_voters (live_round view) = config_of C (durable_history s c)"
    using bind unfolding stateful_prefix_binding_def by blast+
  have q: "quorum (committed_voters (live_round view)) E" "quorum (accepted_voters (live_round view)) E"
    unfolding view_q by (rule joint_election)+
  show thesis
  proof (rule that[OF i(1,2) guard i(3) q])
    fix n assume n: "n \<in> E"
    have "Prevote n \<in> finished select i"
      using i(3) n by (auto simp: work_ready_def dynamic_dependencies_def)
    then obtain j where j: "j < i" "select j = Some (Prevote n)"
      using stateful_work_selection_witness by blast
    have "j < H" using j i time by linarith
    with bind j show "\<exists>j<i. select j = Some (Prevote n) \<and>
      stateful_prevote_result healthy p X epoch_id (start+j) tok c (live j) n (local j n)
        (position (durable_history s c)) (position (durable_history s n))"
      unfolding stateful_prefix_binding_def by blast
  qed
qed

theorem authorized_stateful_production_window_completes:
  assumes entry: "stateful_entry_enabled healthy p X view epoch_id start tok follower"
    and initial: "a 0 = enter_stateful_round tok follower"
    and service: "production_window_service jobs deps trace_log generation H enq dispatch finish
      queued_before started_before resource_health resources"
    and bind: "stateful_prefix_binding healthy p X epoch_id start tok view a live local
      (successful_selection generation trace_log) H"
    and effects: "source_effects generation trace_log H project
      (\<lambda>K. (dynamic_snapshot K, Run_Local \<in> K, dynamic_window_slot K))"
    and time: "12 * (enq + dispatch + finish) \<le> H"
  defines "B \<equiv> enq + dispatch + finish"
  shows "handoff_mode (a 0) = Stateful_Candidate" "handoff_round (a 0) = Some tok"
    "\<exists>i<2 * B. successful_selection generation trace_log i = Some Choose_Term \<and>
      stateful_start_join epoch_id (start+i) tok (live i) (a i) t"
    "hist \<in> quorum_commits (fst (project (12 * B)))"
    "fst (snd (project (12 * B)))" "snd (snd (project (12 * B))) = None"
proof -
  show "handoff_mode (a 0) = Stateful_Candidate" "handoff_round (a 0) = Some tok"
    using initial by (simp_all add: enter_stateful_round_def)
  have shorter: "2 * (enq + dispatch + finish) \<le> H" using time by linarith
  show "\<exists>i<2 * B. successful_selection generation trace_log i = Some Choose_Term \<and>
      stateful_start_join epoch_id (start+i) tok (live i) (a i) t"
    unfolding B_def
    by (rule authorized_stateful_window_starts_join[OF
        production_window_service.production_supplies_bounded_service[OF service] shorter bind]) blast
  show "hist \<in> quorum_commits (fst (project (12 * B)))"
    "fst (snd (project (12 * B)))" "snd (snd (project (12 * B))) = None"
    unfolding B_def using dynamic_production_window_completes[OF service effects time] by simp_all
qed

end

text \<open>
  The prefix uses the same successful events as the ordinary publication
  window. In particular Choose_Term is the checked call that starts the
  ordinary StartJoin path; the work dependency identifies the pre-vote
  quorum. Persisted joins, election, publication, commit and application
  still use the ordinary state transition and source-effect premises. A
  higher term or a changed view can close the pre-vote round before that
  point. The theorem requires one uninterrupted window for the chosen
  candidate; it neither bounds competing work by itself nor implies that
  an old certificate can be kept alive by a fresh election timer tick.
\<close>

end
