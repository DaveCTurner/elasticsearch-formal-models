theory Stateless_Failover_Recovery
  imports Stateless_Failover_Authority Stateless_Recovery_Handoff
begin

section \<open>Launching an authorized replacement\<close>

text \<open>
  This is a proposed additional path. AtomicRegisterPreVoteCollector
  suppresses the ordinary start callback after a recent store heartbeat.
  Coordinator starts pre-voting only in candidate mode, checks health and
  eligibility there, and checks candidate mode and eligibility again under
  its mutex at startElection. A replacement path needs to admit a follower
  of the named incumbent into candidate mode, as well as bypass the
  heartbeat test. The step below represents those two operations and the
  capture of the compare-and-set input at the replacement's mutex boundary,
  after gathering evidence and reading the lease. Discovery, successful
  candidate entry, and dispatch still require their own service.
\<close>

datatype stateless_attempt_mode =
  Failover_Following incarnation_id | Failover_Candidate | Failover_Leading

record stateless_claim_ticket =
  claim_view :: stateless_failover_view
  claim_snapshot :: "lease_bytes option"
  claim_proposal :: nat

record stateless_failover_control =
  sf_mode :: stateless_attempt_mode
  sf_active_claim :: "stateless_claim_ticket option"
  sf_consumed_rounds :: "(incarnation_id \<times> nat) set"

definition stateless_round_key where
  "stateless_round_key view = (sf_candidate view, sf_round view)"

definition stateless_claim_open where
  "stateless_claim_open threshold healthy now live_view view inbox Q eligible dispatchable n
    max_seen snapshot st control ticket control' \<longleftrightarrow>
    live_view = view \<and>
    stateless_failover_authority threshold healthy now live_view inbox Q \<and>
    eligible \<and> dispatchable \<and>
    (sf_mode control = Failover_Candidate \<or>
     sf_mode control = Failover_Following (sf_incumbent view)) \<and>
    sf_active_claim control = None \<and>
    stateless_round_key view \<notin> sf_consumed_rounds control \<and>
    sf_candidate view = endpoint (slot_exec st) n \<and>
    active_slot st = None \<and> \<not> slot_leading st \<and>
    lease_term (lease_value snapshot) = sf_lease_term view \<and>
    ticket = \<lparr>claim_view = view, claim_snapshot = snapshot,
      claim_proposal = Suc (max max_seen (app_term (processes (slot_exec st) n)))\<rparr> \<and>
    control' = control\<lparr>sf_mode := Failover_Candidate, sf_active_claim := Some ticket,
      sf_consumed_rounds := insert (stateless_round_key view) (sf_consumed_rounds control)\<rparr>"

theorem stateless_opens_despite_recent_heartbeat:
  assumes auth: "stateless_failover_authority threshold healthy now view inbox Q"
    and source: "eligible" "dispatchable"
    and mode: "sf_mode control = Failover_Candidate \<or>
      sf_mode control = Failover_Following (sf_incumbent view)"
    and unused: "sf_active_claim control = None"
      "stateless_round_key view \<notin> sf_consumed_rounds control"
    and candidate: "sf_candidate view = endpoint (slot_exec st) n"
      "active_slot st = None" "\<not> slot_leading st"
    and lease: "lease_term (lease_value snapshot) = sf_lease_term view"
  obtains ticket control' where
    "stateless_attempt_permitted False threshold healthy now view inbox"
    "stateless_claim_open threshold healthy now view view inbox Q eligible dispatchable n
      max_seen snapshot st control ticket control'"
    "sf_mode control' = Failover_Candidate"
    "sf_active_claim control' = Some ticket"
proof -
  let ?ticket = "\<lparr>claim_view = view, claim_snapshot = snapshot,
    claim_proposal = Suc (max max_seen (app_term (processes (slot_exec st) n)))\<rparr>"
  let ?entered = "control\<lparr>sf_mode := Failover_Candidate, sf_active_claim := Some ?ticket,
    sf_consumed_rounds := insert (stateless_round_key view) (sf_consumed_rounds control)\<rparr>"
  show thesis by (rule that[of ?ticket ?entered])
    (use auth source mode unused candidate lease in
      \<open>auto simp: stateless_claim_open_def stateless_attempt_permitted_def\<close>)
qed

lemma stateless_open_revalidates_full_view:
  assumes "stateless_claim_open threshold healthy now live_view view inbox Q eligible dispatchable n
    max_seen snapshot st control ticket control'"
  shows "claim_view ticket = live_view"
    "now < sf_deadline live_view"
    "claim_snapshot ticket = snapshot"
    "lease_term (lease_value snapshot) = sf_lease_term live_view"
    "sf_candidate live_view = endpoint (slot_exec st) n"
    "max max_seen (app_term (processes (slot_exec st) n)) < claim_proposal ticket"
    "active_slot st = None" "\<not> slot_leading st"
proof -
  have auth: "stateless_failover_authority threshold healthy now live_view inbox Q"
    using assms by (auto simp: stateless_claim_open_def)
  show "now < sf_deadline live_view"
    using auth expired_stateless_evidence_cannot_open not_le by blast
  show "claim_view ticket = live_view" "claim_snapshot ticket = snapshot"
    "lease_term (lease_value snapshot) = sf_lease_term live_view"
    "sf_candidate live_view = endpoint (slot_exec st) n"
    "max max_seen (app_term (processes (slot_exec st) n)) < claim_proposal ticket"
    "active_slot st = None" "\<not> slot_leading st"
    using assms by (simp_all add: stateless_claim_open_def)
qed

definition retire_stateless_claim where
  "retire_stateless_claim control = control\<lparr>sf_active_claim := None\<rparr>"

lemma retiring_attempt_requires_new_round:
  assumes "stateless_claim_open threshold healthy now live_view view inbox Q eligible dispatchable n
    max_seen snapshot st control ticket control'"
  shows "\<not> stateless_claim_open threshold healthy now' live_view' view inbox' Q' eligible' dispatchable' n
    max_seen' snapshot' st' (retire_stateless_claim control') ticket' control''"
  using assms by (auto simp: stateless_claim_open_def retire_stateless_claim_def)

lemma fresh_round_can_retry_after_retirement:
  assumes old: "stateless_claim_open threshold healthy now live_view view inbox Q eligible dispatchable n
    max_seen snapshot st control ticket control'"
    and auth: "stateless_failover_authority threshold healthy' now' view' inbox' Q'"
    and fresh: "stateless_round_key view' \<notin> insert (stateless_round_key view) (sf_consumed_rounds control)"
    and guards: "eligible'" "dispatchable'" "sf_candidate view' = endpoint (slot_exec st') n"
      "active_slot st' = None" "\<not> slot_leading st'"
      "lease_term (lease_value snapshot') = sf_lease_term view'"
  obtains ticket' control'' where
    "stateless_claim_open threshold healthy' now' view' view' inbox' Q' eligible' dispatchable' n
       max_seen' snapshot' st' (retire_stateless_claim control') ticket' control''"
proof -
  have mode: "sf_mode (retire_stateless_claim control') = Failover_Candidate"
    and unused: "sf_active_claim (retire_stateless_claim control') = None"
      "stateless_round_key view' \<notin> sf_consumed_rounds (retire_stateless_claim control')"
    using old fresh by (auto simp: stateless_claim_open_def retire_stateless_claim_def)
  show thesis
    by (rule stateless_opens_despite_recent_heartbeat[OF auth guards(1,2) _ unused guards(3-6)])
      (use mode that in auto)
qed

section \<open>Pinned lease effects and late callbacks\<close>

text \<open>
  The existing onNewElection computes a new term from whatever lease its
  read returns. An authorized alternative cannot call that entry unchanged:
  it must submit the observed full expected bytes, using the existing
  provider's conditional replacement guard, with no retry against updated
  bytes under the same authority. In particular, the authorization's term
  does not license a later claim against a newer incarnation of the lease.
  The model pins the logical bytes and relies on the existing provider
  guard for the physical update. It does not require the report transport
  to carry a provider-specific ETag or Azure lease handle.

  Revalidation is at launch. The provider can complete after expiry,
  timeout, view change, or restart. Those changes do not undo an admitted
  effect. Report expiry restricts launching, while local retirement
  restricts use of the callback; any intervening view invalidation must
  retire the token locally. Storage effects and callbacks remain separate.
\<close>

definition stateless_ticket_effect where
  "stateless_ticket_effect provider ticket live result \<longleftrightarrow>
    lease_effect provider (claim_snapshot ticket) live (lease_value (claim_snapshot ticket))
      (Claim_Term (sf_candidate (claim_view ticket)) (claim_proposal ticket)) result"

lemma stateless_ticket_pins_snapshot:
  assumes "stateless_ticket_effect provider ticket live result"
  shows "live = claim_snapshot ticket"
  using assms unfolding stateless_ticket_effect_def lease_effect_def
  by (cases provider; cases "claim_snapshot ticket = None"; simp add: valid_guard_def)

theorem launched_claim_cannot_rebase:
  assumes launch: "stateless_claim_open threshold healthy now live_view view inbox Q eligible dispatchable n
    max_seen snapshot st control ticket control'"
    and change: "live \<noteq> snapshot"
  shows "\<not> stateless_ticket_effect provider ticket live result"
  using stateless_open_revalidates_full_view(3)[OF launch] change stateless_ticket_pins_snapshot by metis

definition stateless_claim_reservation where
  "stateless_claim_reservation ticket result s =
    (let t = lease_term (lease_value result)
     in s\<lparr>reserved_term := t, granted_to := (granted_to s)(t := Some (sf_candidate (claim_view ticket)))\<rparr>)"

lemma stateless_ticket_effect_refines_reserve:
  assumes "stateless_ticket_effect provider ticket live result"
    "lease_term (lease_value live) = reserved_term s"
  shows "stateless_step s (stateless_claim_reservation ticket result s)"
    "reserved_term s < lease_term (lease_value result)"
  using lease_claim_refines_reserve[OF _ assms(2)] assms(1)
  by (auto simp: stateless_ticket_effect_def stateless_claim_reservation_def Let_def)

definition stateless_claim_callback_usable where
  "stateless_claim_callback_usable n ticket result st control \<longleftrightarrow>
    sf_active_claim control = Some ticket \<and> sf_mode control = Failover_Candidate \<and>
    sf_candidate (claim_view ticket) = endpoint (slot_exec st) n \<and>
    active_slot st = None \<and> \<not> slot_leading st \<and>
    (let t = lease_term (lease_value result); s = shared_state (slot_exec st)
     in app_term (processes (slot_exec st) n) < t \<and> reserved_term s = t \<and>
        granted_to s t = Some (endpoint (slot_exec st) n))"

lemma retired_or_restarted_claim_cannot_use_callback:
  assumes "sf_active_claim control \<noteq> Some ticket \<or>
    sf_candidate (claim_view ticket) \<noteq> endpoint (slot_exec st) n"
  shows "\<not> stateless_claim_callback_usable n ticket result st control"
  using assms by (auto simp: stateless_claim_callback_usable_def)

lemma superseded_claim_cannot_use_callback:
  assumes "lease_term (lease_value result) < reserved_term (shared_state (slot_exec st))"
  shows "\<not> stateless_claim_callback_usable n ticket result st control"
  using assms by (auto simp: stateless_claim_callback_usable_def Let_def)

lemma lost_or_retired_claim_still_reserves:
  assumes "stateless_ticket_effect provider ticket live result"
    "lease_term (lease_value live) = reserved_term s"
  shows "stateless_step s (stateless_claim_reservation ticket result s)"
    "confirmed_terms (stateless_claim_reservation ticket result s) = confirmed_terms s"
    "notifications (stateless_claim_reservation ticket result s) = notifications s"
    "\<not> stateless_claim_callback_usable n ticket result st (retire_stateless_claim control)"
  using stateless_ticket_effect_refines_reserve(1)[OF assms]
    retired_or_restarted_claim_cannot_use_callback[of "retire_stateless_claim control" ticket n st result]
  by (simp_all add: stateless_claim_reservation_def retire_stateless_claim_def Let_def)

lemma old_term_claim_cannot_follow_new_effect:
  assumes old: "stateless_ticket_effect provider ticket live first"
    and second: "stateless_ticket_effect provider ticket first second"
  shows False
proof -
  have old_bytes: "live = claim_snapshot ticket" and new_bytes: "first = claim_snapshot ticket"
    by (rule stateless_ticket_pins_snapshot[OF old], rule stateless_ticket_pins_snapshot[OF second])
  have cas: "lease_effect provider (claim_snapshot ticket) live (lease_value (claim_snapshot ticket))
      (Claim_Term (sf_candidate (claim_view ticket)) (claim_proposal ticket)) first"
    using old by (simp add: stateless_ticket_effect_def)
  have "lease_term (lease_value live) < lease_term (lease_value first)"
    using effective_lease_write(1,2)[OF cas] by (simp add: lease_value_def)
  with old_bytes new_bytes show False by simp
qed

definition stateless_authorized_move where
  "stateless_authorized_move n x y \<longleftrightarrow>
    (next_slot_move n (fst x) (fst y) \<and> snd x = snd y) \<or>
    (fst x = fst y \<and> (snd y = retire_stateless_claim (snd x) \<or>
      (\<exists>threshold healthy now live_view view Q eligible dispatchable max_seen snapshot ticket.
        \<exists>inbox :: (node \<times> stateless_failover_report) set.
        stateless_claim_open threshold healthy now live_view view inbox Q eligible dispatchable n
          max_seen snapshot (fst x) (snd x) ticket (snd y))))"

lemma authorized_lease_effect_is_core_move:
  assumes effect: "stateless_ticket_effect provider ticket live result"
    and rep: "lease_term (lease_value live) = reserved_term (shared_state (slot_exec st))"
  defines "x' \<equiv> (slot_exec st)\<lparr>shared_state :=
    stateless_claim_reservation ticket result (shared_state (slot_exec st))\<rparr>"
  shows "stateless_authorized_move n (st,control) (st\<lparr>slot_exec := x'\<rparr>,control)"
proof -
  have store: "stateless_exec_step (slot_exec st) x'"
    unfolding x'_def
    by (rule stateless_exec_step.storage[OF stateless_ticket_effect_refines_reserve(1)[OF effect rep]])
      (simp add: stateless_claim_reservation_def Let_def)
  have "next_slot_move n st (st\<lparr>slot_exec := x'\<rparr>)"
    by (rule next_slot_core_move[OF window_move_real[OF store]])
      (simp_all add: x'_def stateless_claim_reservation_def Let_def)
  then show ?thesis by (simp add: stateless_authorized_move_def)
qed

lemma stateless_policy_preserves_slot_reachability:
  assumes "rtranclp (stateless_authorized_move n) (st,control) (st',control')"
    "stateless_slot_reachable n st"
  shows "stateless_slot_reachable n st'"
proof -
  have advance: "stateless_slot_reachable n (fst y)"
    if "stateless_authorized_move n x y" "stateless_slot_reachable n (fst x)" for x y
    using that by (auto simp: stateless_authorized_move_def next_slot_move_def intro: stateless_slot_reachable.step)
  have "stateless_slot_reachable n (fst (st',control'))"
    using assms(1) by (induction rule: rtranclp_induct) (use assms(2) in \<open>auto intro: advance\<close>)
  then show ?thesis by simp
qed

section \<open>Enough observation time for a healthy attempt\<close>

text \<open>
  For a new reserve, a truthful observation of its term cannot precede
  that reserve. An observer's sample clock need only preserve the length
  of the evidence interval up to the required rate bound. The translated
  sample times below express that assumption without comparing different
  local clock offsets. A matching-term report cannot launch another
  authorized request before the service budget expires if that budget is
  at most the lower bound on the evidence interval. Older in-flight
  authorized requests are rejected by the pinned-term check. Ordinary
  claims remain enabled, and their quiet-window premise is still required.
\<close>

lemma reports_cannot_supersede_before_service_budget:
  assumes auth: "stateless_failover_authority threshold healthy now view inbox Q"
    and rate: "\<And>n r. (n,r) \<in> inbox \<Longrightarrow> stateless_report_valid threshold now view r \<Longrightarrow>
      grant_tick \<le> before n r \<and> before n r + budget \<le> after n r \<and> after n r \<le> now"
  shows "grant_tick + budget \<le> now"
proof -
  obtain n r where v: "(n,r) \<in> inbox" "stateless_report_valid threshold now view r"
    using stateless_authority_has_live_report[OF auth] by blast
  from rate[OF v] show ?thesis by linarith
qed

lemma mismatched_term_rejects_in_flight_claim:
  assumes "lease_term (lease_value live) \<noteq> lease_term (lease_value (claim_snapshot ticket))"
  shows "\<not> stateless_ticket_effect provider ticket live result"
  using assms stateless_ticket_pins_snapshot by blast

lemma protected_lease_excludes_competing_authorized_effect:
  assumes open_attempt: "stateless_claim_open threshold healthy dispatch live_view view inbox Q eligible dispatchable n
      max_seen snapshot st control ticket control'"
    and effect: "stateless_ticket_effect provider ticket live result"
    and time: "dispatch \<le> effect_tick" "effect_tick < grant_tick + budget"
    and rate: "\<And>n r. lease_term (lease_value live) = sf_lease_term live_view \<Longrightarrow>
      (n,r) \<in> inbox \<Longrightarrow> stateless_report_valid threshold dispatch live_view r \<Longrightarrow>
      grant_tick \<le> before n r \<and> before n r + budget \<le> after n r \<and> after n r \<le> dispatch"
  shows False
proof -
  have auth: "stateless_failover_authority threshold healthy dispatch live_view inbox Q"
    using open_attempt by (auto simp: stateless_claim_open_def)
  have matching: "lease_term (lease_value live) = sf_lease_term live_view"
    using stateless_ticket_pins_snapshot[OF effect] stateless_open_revalidates_full_view(3,4)[OF open_attempt]
    by simp
  have bound: "grant_tick + budget \<le> dispatch"
  proof (rule reports_cannot_supersede_before_service_budget[OF auth, where before=before and after=after])
    fix n r
    assume "(n,r) \<in> inbox" "stateless_report_valid threshold dispatch live_view r"
    then show "grant_tick \<le> before n r \<and> before n r + budget \<le> after n r \<and> after n r \<le> dispatch"
      by (rule rate[OF matching])
  qed
  from bound time show False by linarith
qed

section \<open>From opened attempt to locally applied publication\<close>

definition stateless_claim_search_start where
  "stateless_claim_search_start n t warm r \<longleftrightarrow>
    stateless_slot_reachable n r \<and> active_slot r = None \<and> slot_leading r \<and>
    reserved_term (shared_state (slot_exec r)) = t \<and>
    holds_grant (shared_state (slot_exec r)) (endpoint (slot_exec r) n) t \<and>
    searches (shared_state (slot_exec r)) t = Some (Probe (t - 1)) \<and>
    latest_issued (shared_state (slot_exec r)) t = None \<and>
    warm \<in> insert [] (issued (shared_state (slot_exec r))) \<and>
    term_of warm < t \<and> app_accepted (processes (slot_exec r) n) = position warm"

text \<open>
  The serviced claim path assumes the candidate remains eligible, its
  callback is live_view, and the provider completes the pinned CAS within
  the lease stage. It cannot derive these from an evidence quorum. The
  manifest plan is indexed by the actual state after the grant; a bound
  for each workload stage is explicit. There is no fixed repository view
  in the search. The quiet interval includes service of the exact-term
  fence, local apply, and the matching publication's slot clear.
\<close>

theorem stateless_authorized_first_publication:
  fixes y :: "stateless_slot_state \<Rightarrow> stateless_execution"
    and result :: "lease_bytes option"
    and selected :: "nat \<Rightarrow> state_manifest option"
    and t reads finish gap A B C G :: nat
  defines "t \<equiv> lease_term (lease_value result)"
    and "reads \<equiv> stable_probe_count (header_choices selected) (t - 1) + gap + 1"
    and "finish \<equiv> 5 * G + (reads * A + (16 * B + 3 * C))"
  assumes launch: "stateless_claim_open threshold healthy now live_view view inbox Q eligible dispatchable n
    max_seen snapshot st control ticket control'"
    and reached: "stateless_slot_reachable n st"
    and effect: "stateless_ticket_effect provider ticket live result"
    and rep: "lease_term (lease_value live) = reserved_term (shared_state (slot_exec st))"
    and warm: "warm \<in> insert [] (issued (shared_state (slot_exec st)))"
      "app_accepted (processes (slot_exec st) n) = position warm"
    and claim_service: "bounded_service {..<(5::nat)} (\<lambda>i. {..<i}) claim G claim_horizon"
    and claim_time: "5 * G \<le> claim_horizon"
    and recipe: "\<And>r. stateless_claim_search_start n t warm r \<Longrightarrow>
      changing_view_slot_publication r n (t - 1) t selected views replies gap (y r) warm base payload F m files"
    and search_service: "bounded_service {..<reads} (\<lambda>i. {..<i}) lookups A search_horizon"
    and search_time: "reads * A \<le> search_horizon"
    and publication_service: "bounded_service {..<(16::nat)} (\<lambda>i. {..<i}) issue B publication_horizon"
    and publication_time: "16 * B \<le> publication_horizon"
    and completion: "bounded_service (completion_jobs (position (manifest_history m)))
      (completion_dependencies (position (manifest_history m))) callbacks C completion_horizon"
    and completion_time: "3 * C \<le> completion_horizon"
  obtains run where "run 0 = st"
    "\<And>j. next_slot_move n (run j) (run (Suc j))"
    "stateless_claim_search_start n t warm (run (5 * G))"
    "manifest_history m \<in> notifications (shared_state (slot_exec (run finish)))"
    "installed (processes (slot_exec (run finish)) n) = Some (position (manifest_history m))"
    "stateless_next_ready n t (manifest_history m) (run finish)"
proof -
  have who: "sf_candidate (claim_view ticket) = endpoint (slot_exec st) n"
    using stateless_open_revalidates_full_view(1,5)[OF launch] by simp
  have cas: "lease_effect provider (claim_snapshot ticket) live (lease_value (claim_snapshot ticket))
      (Claim_Term (endpoint (slot_exec st) n) (claim_proposal ticket)) result"
    using effect by (simp add: stateless_ticket_effect_def who)
  note admitted = stateless_open_revalidates_full_view[OF launch]
  obtain r where r: "r 0 = st" "\<And>j. next_slot_move n (r j) (r (Suc j))"
    and entry: "stateless_claim_search_start n t warm (r (5 * G))"
    unfolding stateless_claim_search_start_def t_def
    by (rule fresh_grant_restarts_changing_view_recovery[
      OF reached admitted(7,8,6) cas rep warm claim_service claim_time]) blast
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
  let ?duration = "reads * A + (16 * B + 3 * C)"
  obtain s where s: "s 0 = ?ready" "\<And>j. next_slot_move n (s j) (s (Suc j))"
    and outcome: "manifest_history m \<in> notifications (shared_state (slot_exec (s ?duration)))"
      "installed (processes (slot_exec (s ?duration)) n) = Some (position (manifest_history m))"
      "stateless_next_ready n t (manifest_history m) (s ?duration)"
    unfolding reads_def history
    by (rule recovery.changing_view_recovery_releases_slot[
      OF search_service' search_time' publication_service publication_time completion' completion_time]) blast
  let ?run = "\<lambda>j. if j < 5 * G then r j else s (j - 5 * G)"
  have link: "?ready = s 0" by (simp add: s(1))
  note joined = concatenate_next_traces[OF r(2) s(2) link]
  have start_eq: "?run 0 = st" using joined(1) r(1) by simp
  have search: "?run (5 * G) = ?ready" using s(1) by simp
  have end_eq: "?run finish = s ?duration" unfolding finish_def by (rule joined(3))
  show thesis by (rule that[OF start_eq joined(2)]) (use search entry end_eq outcome in simp_all)
qed

end
