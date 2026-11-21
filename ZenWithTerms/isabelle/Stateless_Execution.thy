theory Stateless_Execution
  imports Stateless_Single_Page_Recovery Commit_Application
begin

section \<open>Authenticated delivery and per-process application\<close>

definition stateless_request where
  "stateless_request h = request (owner h) (term_of h) (rank_version (position h)) {} {}"

lemma stateless_request_fields [simp]:
  "request_key (stateless_request h) = position h"
  "pub_term (stateless_request h) = term_of h"
  "pub_version (stateless_request h) = rank_version (position h)"
  by (simp_all add: stateless_request_def request_def prod.collapse)

definition stateless_application_history :: "stateless_state \<Rightarrow> nat transport_item set" where
  "stateless_application_history s =
    ((\<lambda>h. Registered_State (stateless_request h) 0) ` issued s) \<union>
    ((\<lambda>h. Returned_Commit (owner h) (position h)) ` notifications s)"

lemma stateless_history_grows:
  "stateless_step s s' \<Longrightarrow> stateless_application_history s \<subseteq> stateless_application_history s'"
  by (cases rule: stateless_step.cases) (auto simp: stateless_application_history_def)

datatype stateless_packet = State_Packet lineage incarnation_id | Commit_Packet lineage incarnation_id

record stateless_execution =
  shared_state :: stateless_state
  processes :: "node \<Rightarrow> application_state"
  in_flight :: "stateless_packet set"

abbreviation endpoint where "endpoint x n \<equiv> (n, incarnation (processes x n))"

definition stateless_exec_initial where
  "stateless_exec_initial = \<lparr>shared_state = stateless_initial,
    processes = (\<lambda>_. application_initial 0 rank_zero), in_flight = {}\<rparr>"

text \<open>
  Packet enqueue projects an authenticated send. Delivery matches the
  selected receiver and its live process incarnation. The sender's
  identity is the owner of the registered history. The synthetic
  transport history carries only the fields needed by the applier model.
  The shared-state interface is the safety projection of storage calls.
  First publication uses the proved recovery-base interface with the
  live accepted key. Restart clears local state and pending application;
  it leaves the shared register, manifests, and queued network sends intact.
\<close>

inductive stateless_exec_step where
  storage:
    "stateless_step (shared_state x) s \<Longrightarrow> issued s = issued (shared_state x) \<Longrightarrow>
     stateless_exec_step x (x\<lparr>shared_state := s\<rparr>)"
| join:
    "holds_grant (shared_state x) who t \<Longrightarrow> app_term (processes x n) < t \<Longrightarrow>
     stateless_exec_step x (x\<lparr>processes := (processes x)
       (n := (processes x n)\<lparr>app_term := t\<rparr>)\<rparr>)"
| first_publish:
    "s = shared_state x \<Longrightarrow> holds_grant s (endpoint x n) t \<Longrightarrow>
     app_term (processes x n) = t \<Longrightarrow> app_accepted (processes x n) = position warm \<Longrightarrow>
     latest_issued s t = None \<Longrightarrow> warm \<in> insert [] (issued s) \<Longrightarrow> term_of warm < t \<Longrightarrow>
     election_base s t warm base \<Longrightarrow> h = stateless_update (endpoint x n) t payload F base \<Longrightarrow>
     stateless_exec_step x (x\<lparr>shared_state := s\<lparr>issued := insert h (issued s), latest_issued := (latest_issued s)(t := Some h)\<rparr>\<rparr>)"
| next_publish:
    "s = shared_state x \<Longrightarrow> holds_grant s (endpoint x n) t \<Longrightarrow>
     app_term (processes x n) = t \<Longrightarrow> app_accepted (processes x n) = position base \<Longrightarrow>
     latest_issued s t = Some base \<Longrightarrow> base \<in> approvals s \<Longrightarrow>
     h = stateless_update (endpoint x n) t payload F base \<Longrightarrow>
     stateless_exec_step x (x\<lparr>shared_state := s\<lparr>issued := insert h (issued s), latest_issued := (latest_issued s)(t := Some h)\<rparr>\<rparr>)"
| send_state:
    "h \<in> issued (shared_state x) \<Longrightarrow>
     stateless_exec_step x (x\<lparr>in_flight := insert (State_Packet h (endpoint x n)) (in_flight x)\<rparr>)"
| send_commit:
    "h \<in> notifications (shared_state x) \<Longrightarrow>
     stateless_exec_step x (x\<lparr>in_flight := insert (Commit_Packet h (endpoint x n)) (in_flight x)\<rparr>)"
| receive_state:
    "State_Packet h (endpoint x n) \<in> in_flight x \<Longrightarrow> a = processes x n \<Longrightarrow>
     term_of h = app_term a \<Longrightarrow> (rank_term (app_accepted a) = term_of h \<longrightarrow> app_accepted a < position h) \<Longrightarrow>
     stateless_exec_step x (x\<lparr>processes := (processes x)(n := a\<lparr>app_accepted := position h\<rparr>)\<rparr>)"
| receive_commit:
    "Commit_Packet h (endpoint x n) \<in> in_flight x \<Longrightarrow> a = processes x n \<Longrightarrow>
     term_of h = app_term a \<Longrightarrow> position h = app_accepted a \<Longrightarrow>
     b = (if owner h = n then a\<lparr>offered := Some (position h), self_ready := insert (Apply_Request n (position h)) (self_ready a)\<rparr>
          else a\<lparr>offered := Some (position h), queued_applications := insert (Apply_Request (owner h) (position h)) (queued_applications a)\<rparr>) \<Longrightarrow>
     stateless_exec_step x (x\<lparr>processes := (processes x)(n := b)\<rparr>)"
| worker:
    "application_step n (stateless_application_history (shared_state x)) (processes x n) b \<Longrightarrow>
     applier_only (processes x n) b \<Longrightarrow>
     stateless_exec_step x (x\<lparr>processes := (processes x)(n := b)\<rparr>)"
| reboot:
    "stateless_exec_step x (x\<lparr>processes := (processes x)(n := restart_application (processes x n) 0 rank_zero)\<rparr>)"

lemma stateless_exec_reservation:
  assumes effect: "lease_effect backend before live expected (Claim_Term who proposed) result"
    and rep: "lease_term (lease_value live) = reserved_term (shared_state x)"
  defines "t \<equiv> lease_term (lease_value result)"
  shows "stateless_exec_step x (x\<lparr>shared_state := (shared_state x)
    \<lparr>reserved_term := t, granted_to := (granted_to (shared_state x))(t := Some who)\<rparr>\<rparr>)"
  unfolding t_def by (rule stateless_exec_step.storage[OF lease_claim_refines_reserve(1)[OF effect rep]]) simp

lemma stateless_exec_fence_approval:
  assumes "production_lease_revisions revisions" "r < length revisions" "\<forall>k\<in>returned. k \<le> r" "finite returned"
    "confirmed_floor (shared_state x) = callback_floor revisions returned"
    "lease_term (lease_value (revisions ! r)) = t"
    "latest_issued (shared_state x) t = Some h" "visible_image (shared_state x) t = Some h"
  shows "stateless_exec_step x (x\<lparr>shared_state := (shared_state x)
    \<lparr>approvals := insert h (approvals (shared_state x)), frontier := h\<rparr>\<rparr>)"
  by (rule stateless_exec_step.storage[OF successful_before_commit_refines[OF assms]]) simp

lemma stateless_exec_manifest_install:
  assumes "stateless_reachable (shared_state x)"
    "latest_issued (shared_state x) t = Some (manifest_history m)" "files_match files m"
  defines "s \<equiv> shared_state x"
  shows "stateless_exec_step x (x\<lparr>shared_state := s\<lparr>
    completed_images := insert (manifest_history m) (completed_images s),
    visible_image := (visible_image s)(t := Some (manifest_history m))\<rparr>\<rparr>)"
  unfolding s_def by (rule stateless_exec_step.storage[OF manifest_install_refines_upload(1)[OF assms(1-3)]]) simp

lemma complete_response_supplies_election_base:
  assumes search: "searches s election = Some (Found seen)"
    and remote: "manifest_history selected \<in> completed_images s"
      "term_of (manifest_history selected) = term_of seen"
    and reply: "first_listing_contract view reply" "checked_first_listing reply = Some rows"
    and pick: "newest_manifest rows (Some selected)"
    and present: "anchor \<in> original"
    and anchor: "term_of seen = term_of (frontier s) \<Longrightarrow> manifest_history anchor = frontier s"
    and first: "is_first \<Longrightarrow> \<forall>m\<in>original. extends_manifest anchor m"
    and trace: "rtranclp (fenced_manifest_step is_first anchor) ([], original) (renames, view)"
    and order: "\<And>m. m \<in> rows \<Longrightarrow> manifest_generation m \<le> manifest_generation selected
        \<Longrightarrow> extends_manifest m selected"
  shows "election_base s election warm (newer_image warm (manifest_history selected))"
proof -
  have bound: "position (frontier s) \<le> position (manifest_history selected)"
    if "term_of seen = term_of (frontier s)"
    using checked_live_term_listing(2)[OF reply present first trace order pick] anchor[OF that]
    unfolding extends_manifest_def by simp
  have guard: "position seen \<le> position (manifest_history selected) \<or> term_of seen \<noteq> term_of (frontier s) \<or>
    position (frontier s) \<le> position (manifest_history selected)" using bound by blast
  show ?thesis by (rule election_base.downloaded[OF search remote guard])
qed

inductive stateless_execution_reachable where
  init: "stateless_execution_reachable stateless_exec_initial"
| step: "stateless_execution_reachable x \<Longrightarrow> stateless_exec_step x y \<Longrightarrow> stateless_execution_reachable y"

fun packet_registered where
  "packet_registered s (State_Packet h dest) = (h \<in> issued s)"
| "packet_registered s (Commit_Packet h dest) = (h \<in> notifications s)"

definition stateless_packets_ok where
  "stateless_packets_ok x \<longleftrightarrow> (\<forall>p\<in>in_flight x. packet_registered (shared_state x) p)"

lemma stateless_execution_projects_step:
  assumes "stateless_exec_step x y"
  shows "shared_state x = shared_state y \<or> stateless_step (shared_state x) (shared_state y)"
  using assms by cases (auto intro: stateless_step.publish publish_parent.first publish_parent.subsequent)

lemma stateless_packets_preserved:
  assumes step: "stateless_exec_step x y" and old: "stateless_packets_ok x"
  shows "stateless_packets_ok y"
proof -
  have grows: "issued (shared_state x) \<subseteq> issued (shared_state y) \<and>
    notifications (shared_state x) \<subseteq> notifications (shared_state y)"
    using stateless_execution_projects_step[OF step] by (elim disjE stateless_step.cases) auto
  have registered: "packet_registered (shared_state y) p" if "p \<in> in_flight x" for p
  proof -
    from old that have "packet_registered (shared_state x) p" unfolding stateless_packets_ok_def by blast
    then show ?thesis using grows by (cases p) auto
  qed
  have sent: "p \<in> in_flight x \<or> packet_registered (shared_state y) p"
    if "p \<in> in_flight y" for p
    using step that by cases auto
  show ?thesis unfolding stateless_packets_ok_def using sent registered by blast
qed

lemma stateless_exec_application_step:
  assumes step: "stateless_exec_step x y" and wire: "stateless_packets_ok x"
  shows "processes x n = processes y n \<or>
    application_step n (stateless_application_history (shared_state x)) (processes x n) (processes y n)"
  using step
proof cases
  case (receive_state h target a)
  have issued: "h \<in> issued (shared_state x)" using receive_state(2) wire unfolding stateless_packets_ok_def by force
  have registered: "Registered_State (stateless_request h) 0 \<in> stateless_application_history (shared_state x)"
    using issued unfolding stateless_application_history_def by blast
  have key: "\<lparr>rank_term = app_term a, rank_version = rank_version (position h)\<rparr> = position h"
    using receive_state(4) by (cases "position h") simp
  have accept: "application_step target (stateless_application_history (shared_state x)) a
    (a\<lparr>app_accepted := position h\<rparr>)"
    using application_step.accept[OF registered, where a=a and n=target] receive_state(4,5)
    by (simp add: rank_less_iff key)
  from receive_state(1,3) accept show ?thesis by (cases "n = target") simp_all
next
  case (receive_commit h target a b)
  have notified: "h \<in> notifications (shared_state x)" using receive_commit(2) wire unfolding stateless_packets_ok_def by force
  have sent: "Returned_Commit (owner h) (position h) \<in> stateless_application_history (shared_state x)"
    using notified unfolding stateless_application_history_def by blast
  have delivery: "application_step target (stateless_application_history (shared_state x)) a b"
  proof (cases "owner h = target")
    case True
    with sent have "Returned_Commit target (position h) \<in> stateless_application_history (shared_state x)" by simp
    from application_step.handle_self[OF this receive_commit(4,5)] True receive_commit(6) show ?thesis by simp
  next
    case False
    from application_step.handle_remote[OF False sent receive_commit(4,5)] False receive_commit(6) show ?thesis by simp
  qed
  from delivery receive_commit(1,3) show ?thesis by (cases "n = target") simp_all
qed (auto intro: application_step.advance_term application_step.restart)

theorem stateless_execution_projection:
  assumes "stateless_execution_reachable x"
  shows "stateless_reachable (shared_state x) \<and> stateless_packets_ok x \<and>
    (\<forall>n. application_reachable n (stateless_application_history (shared_state x)) 0 rank_zero (processes x n))"
  using assms
proof induction
  case init
  show ?case
    by (simp add: stateless_exec_initial_def stateless_packets_ok_def stateless_reachable.init application_reachable.initial)
next
  case (step x y)
  then have prev: "stateless_reachable (shared_state x)" "stateless_packets_ok x"
    "\<And>n. application_reachable n (stateless_application_history (shared_state x)) 0 rank_zero (processes x n)" by auto
  note proj = stateless_execution_projects_step[OF step.hyps(2)]
  have shared: "stateless_reachable (shared_state y)"
    using proj by (elim disjE) (use prev(1) in simp, rule stateless_reachable.step[OF prev(1)])
  have grows: "stateless_application_history (shared_state x) \<subseteq> stateless_application_history (shared_state y)"
    using proj by (elim disjE) (simp, rule stateless_history_grows)
  have app: "application_reachable n (stateless_application_history (shared_state x)) 0 rank_zero (processes y n)" for n
    using stateless_exec_application_step[OF step.hyps(2) prev(2), of n] prev(3)[of n]
    by (elim disjE) (simp, blast intro: application_reachable.step)
  show ?case
  proof (intro conjI allI)
    show "stateless_reachable (shared_state y)" by (rule shared)
    show "stateless_packets_ok y" by (rule stateless_packets_preserved[OF step.hyps(2) prev(2)])
    fix n
    show "application_reachable n (stateless_application_history (shared_state y)) 0 rank_zero (processes y n)"
      by (rule application_reachable_weaken[OF app grows])
  qed
qed

lemma stateless_approval_prefix_order:
  assumes "stateless_reachable s"
  shows "\<forall>h\<in>approvals s. \<forall>p\<in>approvals s. position h \<le> position p \<longrightarrow> prefix h p"
  using assms
proof induction
  case init
  show ?case by (simp add: stateless_initial_def)
next
  case (step s s')
  show ?case using step.hyps(2)
  proof cases
    case (approve t tip)
    have ok: "stateless_ok s" by (rule stateless_invariants[OF step.hyps(1)])
    then have ii: "issued_ok s" and lo: "lease_ok s" and fo: "frontier_ok s"
      unfolding stateless_ok_def by auto
    note top = approval_reaches_top[OF ii lo approve(2,4)]
    have old: "p \<in> issued s" "prefix p (frontier s)" if "p \<in> approvals s" for p
      using fo that unfolding frontier_ok_def by blast+
    have bound: "position (frontier s) \<le> position tip"
      using top(3) frontier_issued[OF fo] by (cases "frontier s = []") (auto simp: zero_key_le)
    have edge: "prefix (frontier s) tip" using fo top(1) bound unfolding frontier_ok_def by blast
    have before: "prefix p tip" if "p \<in> approvals s" for p
      by (rule prefix_order.trans[OF old(2)[OF that] edge])
    have after: "prefix tip p" if "p \<in> approvals s" "position tip \<le> position p" for p
    proof -
      have "position p = position tip" by (rule order_antisym[OF top(3)[OF old(1)[OF that(1)]] that(2)])
      from issued_key_eq[OF ii old(1)[OF that(1)] top(1) this] show ?thesis by simp
    qed
    from step.IH before after show ?thesis by (auto simp: approve(1))
  qed (use step.IH in auto)
qed

theorem stateless_node_acknowledges_committed_prefix:
  assumes run: "stateless_execution_reachable x"
    and ack: "(e,q,k) \<in> node_acknowledgements (processes x n)"
  obtains h p where "h \<in> notifications (shared_state x)" "p \<in> notifications (shared_state x)"
    "owner h = apply_source q" "position h = apply_key q" "position p = k" "prefix h p"
proof -
  let ?s = "shared_state x"
  from stateless_execution_projection[OF run] have reach: "stateless_reachable ?s"
    and app: "application_reachable n (stateless_application_history ?s) 0 rank_zero (processes x n)" by auto
  note witness = successful_node_ack[OF app ack]
  from witness(2,3) obtain h p where h: "h \<in> notifications ?s" "owner h = apply_source q" "position h = apply_key q"
    and p: "p \<in> notifications ?s" "position p = k"
    by (auto simp: authentic_request_def quorum_key_def stateless_application_history_def)
  from stateless_invariants[OF reach] have subset: "notifications ?s \<subseteq> approvals ?s"
    by (simp add: stateless_ok_def frontier_ok_def)
  have "prefix h p"
    using bspec[OF bspec[OF stateless_approval_prefix_order[OF reach] subsetD[OF subset h(1)]] subsetD[OF subset p(1)]]
      witness(4) h(3) p(2) by simp
  from that[OF h(1) p(1) h(2,3) p(2) this] show thesis .
qed

end
