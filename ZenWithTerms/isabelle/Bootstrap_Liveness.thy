theory Bootstrap_Liveness
  imports Bootstrap_Agreement Fixed_Window_Liveness
begin

section \<open>Configured snapshots and the live quorum check\<close>

lemma configured_retry_quorum_iff:
  assumes stable: "stable_requirements R matches bind"
    and capture: "configured_bootstrap R old matches c C"
  shows "initial_quorum C known \<longleftrightarrow>
    card R < 2 * card ((bind ` R \<inter> old) \<inter> known)"
proof -
  obtain lookup where finite: "finite R" and matching: "view_matching R old matches lookup"
    and config: "C = discovered_configuration R lookup"
    using capture unfolding configured_bootstrap_def by blast
  have counts: "finite C" "card C = card R"
    using finite configured_count[OF matching] unfolding config by (simp_all add: discovered_configuration_def)
  have voters: "card (C \<inter> Discovered_ID ` known) = card ((bind ` R \<inter> old) \<inter> known)"
    unfolding config configuration_actual_nodes stable_matched_ids[OF stable matching] by simp
  show ?thesis unfolding initial_quorum_def using counts voters by simp
qed

lemma captured_attempt_blocked_despite_recent_majority:
  assumes "stable_requirements R matches bind" "configured_bootstrap R old matches c C"
    and recent: "card R < 2 * card (bind ` R \<inter> known)"
    and lost: "2 * card ((bind ` R \<inter> old) \<inter> known) \<le> card R"
  shows "card R < 2 * card (bind ` R \<inter> known) \<and>
         \<not> installation_allowed False True known c C"
  using recent lost configured_retry_quorum_iff[OF assms(1,2)]
  unfolding installation_allowed_def by auto

section \<open>Startup service after discovery stabilizes\<close>

datatype 'r bootstrap_phase =
    Await_View "'r initial_member set option"
  | Ready_To_Claim
  | Pending_Install "'r initial_member set"
  | Durable_Config "'r initial_member set"
  | Armed_Scheduler "'r initial_member set"
  | Startup_PreVote "'r initial_member set"

inductive startup_step for allows known c eligible candidate where
  discover: "startup_step allows known c eligible candidate (Await_View None) Ready_To_Claim"
| resume: "startup_step allows known c eligible candidate (Await_View (Some C)) (Pending_Install C)"
| capture: "allows C \<Longrightarrow> startup_step allows known c eligible candidate Ready_To_Claim (Pending_Install C)"
| retry: "startup_step allows known c eligible candidate (Pending_Install C) (Await_View (Some C))"
| persist: "installation_allowed False eligible known c C \<Longrightarrow>
    startup_step allows known c eligible candidate (Pending_Install C) (Durable_Config C)"
| arm: "startup_step allows known c eligible candidate (Durable_Config C) (Armed_Scheduler C)"
| prevote: "candidate \<Longrightarrow> initial_quorum C known \<Longrightarrow>
    startup_step allows known c eligible candidate (Armed_Scheduler C) (Startup_PreVote C)"

text \<open>
  Coordinator's installer rechecks its live view under the mutex and
  persists the configuration before starting its scheduler. Splitting
  these effects into two proof actions gives a conservative delay bound.
  The window contains no competing installation, restart, mode change or
  scheduler cancellation. An already-installed call does not enter this
  startup path. A candidate wake-up requires the healthy and eligible
  candidate branch. A usable shared view is supplied by discovery, and
  the install action represents a successful durable write including its
  completion. This service premise excludes a write that hangs forever.

  A failed installer invocation can leave the captured proposal pending.
  ClusterBootstrapService retries an exception with that proposal, so
  discovering a new roster majority need not repair an earlier capture.
  The retry case starts after the original capture and before installation.
  Delayed retries and stable discovery enter the bounded-service premise.
\<close>

lemma startup_retry_retains_capture:
  "startup_step allows known c eligible candidate (Pending_Install C) (Await_View p)
   \<Longrightarrow> p = Some C"
  by (erule startup_step.cases) auto

lemma startup_retry_cannot_install_without_live_quorum:
  assumes "startup_step allows known c eligible candidate (Pending_Install C) (Durable_Config C')"
  shows "C' = C" "initial_quorum C known"
  using assms by (auto elim: startup_step.cases simp: installation_allowed_def)

lemma blocked_capture_remains_pending:
  assumes blocked: "\<not> initial_quorum C known"
    and trace: "rtranclp (startup_step allows known c eligible candidate) (Await_View (Some C)) phase"
  shows "phase = Await_View (Some C) \<or> phase = Pending_Install C"
  using trace
proof (induction rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  from step.IH show ?case
  proof
    assume "y = Await_View (Some C)"
    with step.hyps(2) show ?thesis by (auto elim: startup_step.cases)
  next
    assume "y = Pending_Install C"
    with step.hyps(2) blocked show ?thesis by (auto elim: startup_step.cases simp: installation_allowed_def)
  qed
qed

lemma replacing_a_discovered_peer_can_block_retry:
  "configured_bootstrap demo_requirements {0,1} (=) 1 left_config"
  "card demo_requirements < 2 * card ({1,2} :: node set)"
  "\<not> installation_allowed False True {1,2} 1 left_config"
proof -
  have stable: "stable_requirements demo_requirements (=) id"
    by (simp add: stable_requirements_def inj_on_def)
  have "configured_bootstrap demo_requirements {0,1} (=) 1
      (discovered_configuration demo_requirements (view_lookup id {0,1}))"
    by (rule configured_stable_attempt[OF stable]) (simp_all add: demo_requirements_def Int_insert_left)
  then show cap: "configured_bootstrap demo_requirements {0,1} (=) 1 left_config"
    by (simp add: demo_requirements_def left_config_def discovered_configuration_def slot_member_def view_lookup_def)
  show "card demo_requirements < 2 * card ({1,2} :: node set)" by (simp add: demo_requirements_def)
  from configured_retry_quorum_iff[OF stable cap, of "{1,2}"]
  show "\<not> installation_allowed False True {1,2} 1 left_config"
    by (simp add: installation_allowed_def demo_requirements_def left_config_def Int_insert_left)
qed

datatype bootstrap_work = Observe_View | Claim_Config | Persist_Config | Arm_Scheduler | Start_PreVote

definition bootstrap_jobs where
  "bootstrap_jobs retrying =
    {Observe_View, Persist_Config, Arm_Scheduler, Start_PreVote} \<union>
    (if retrying then {} else {Claim_Config})"

fun bootstrap_prerequisites where
  "bootstrap_prerequisites retrying Observe_View = {}"
| "bootstrap_prerequisites retrying Claim_Config = {Observe_View}"
| "bootstrap_prerequisites retrying Persist_Config =
    (if retrying then {Observe_View} else {Observe_View, Claim_Config})"
| "bootstrap_prerequisites retrying Arm_Scheduler = {Persist_Config}"
| "bootstrap_prerequisites retrying Start_PreVote = {Arm_Scheduler}"

definition bootstrap_projection where
  "bootstrap_projection retrying C D =
    (if Start_PreVote \<in> D then Startup_PreVote C
     else if Arm_Scheduler \<in> D then Armed_Scheduler C
     else if Persist_Config \<in> D then Durable_Config C
     else if Claim_Config \<in> D then Pending_Install C
     else if Observe_View \<in> D then (if retrying then Pending_Install C else Ready_To_Claim)
     else Await_View (if retrying then Some C else None))"

abbreviation startup_finished where
  "startup_finished retrying sel i \<equiv>
    completed_work (bootstrap_jobs retrying) (bootstrap_prerequisites retrying) sel i"

lemma bootstrap_project_step:
  assumes capture: "\<not> retrying \<Longrightarrow> allows C"
    and install: "installation_allowed False eligible known c C"
    and candidacy: "candidate"
    and order: "ordered_work (bootstrap_jobs retrying) (bootstrap_prerequisites retrying) D"
    and ready: "work_ready (bootstrap_jobs retrying) (bootstrap_prerequisites retrying) D a"
  shows "startup_step allows known c eligible candidate
     (bootstrap_projection retrying C D) (bootstrap_projection retrying C (insert a D))"
proof -
  from ready have absent: "a \<notin> D" and job: "a \<in> bootstrap_jobs retrying"
    and enabled: "bootstrap_prerequisites retrying a \<subseteq> D"
    unfolding work_ready_def by blast+
  from order have prior: "\<And>b. b \<in> D \<Longrightarrow> bootstrap_prerequisites retrying b \<subseteq> D"
    unfolding ordered_work_def by blast
  from order have known: "D \<subseteq> bootstrap_jobs retrying" unfolding ordered_work_def by simp
  have quorum: "initial_quorum C known" using install unfolding installation_allowed_def by simp
  have claim_prior: "Claim_Config \<in> D \<Longrightarrow> Observe_View \<in> D"
    using prior[of Claim_Config] by simp
  have disk_prior: "Persist_Config \<in> D \<Longrightarrow> Observe_View \<in> D"
    "\<not> retrying \<Longrightarrow> Persist_Config \<in> D \<Longrightarrow> Claim_Config \<in> D"
    using prior[of Persist_Config] by (auto split: if_splits)
  have arm_prior: "Arm_Scheduler \<in> D \<Longrightarrow> Persist_Config \<in> D"
    using prior[of Arm_Scheduler] by simp
  have prevote_prior: "Start_PreVote \<in> D \<Longrightarrow> Arm_Scheduler \<in> D"
    using prior[of Start_PreVote] by simp
  from absent job enabled known claim_prior disk_prior arm_prior prevote_prior capture install candidacy quorum show ?thesis
    by (cases a; cases retrying)
      (auto simp: bootstrap_jobs_def bootstrap_projection_def
        intro: startup_step.discover startup_step.resume startup_step.capture startup_step.persist
          startup_step.arm startup_step.prevote)
qed

lemma bootstrap_service_projects_trace:
  assumes capture: "\<not> retrying \<Longrightarrow> allows C"
    and install: "installation_allowed False eligible known c C"
    and candidacy: "candidate"
  shows "rtranclp (startup_step allows known c eligible candidate)
    (Await_View (if retrying then Some C else None)) (bootstrap_projection retrying C (startup_finished retrying sel i))"
proof (induction i)
  case 0
  show ?case by (simp add: bootstrap_projection_def)
next
  case (Suc i)
  let ?D = "startup_finished retrying sel i"
  from completed_work_change[of "bootstrap_jobs retrying" "bootstrap_prerequisites retrying" sel i]
  show ?case
  proof (elim disjE)
    assume "startup_finished retrying sel (Suc i) = ?D"
    then show ?case using Suc.IH by simp
  next
    assume "\<exists>a. sel i = Some a \<and>
        work_ready (bootstrap_jobs retrying) (bootstrap_prerequisites retrying) ?D a \<and>
        startup_finished retrying sel (Suc i) = insert a ?D"
    then obtain a where
      ready: "work_ready (bootstrap_jobs retrying) (bootstrap_prerequisites retrying) ?D a" and
      completed: "startup_finished retrying sel (Suc i) = insert a ?D" by blast
    have "startup_step allows known c eligible candidate
       (bootstrap_projection retrying C ?D) (bootstrap_projection retrying C (insert a ?D))"
    proof (rule bootstrap_project_step)
      show "\<not> retrying \<Longrightarrow> allows C" by (fact capture)
      show "installation_allowed False eligible known c C" by (fact install)
      show "candidate" by (fact candidacy)
      show "ordered_work (bootstrap_jobs retrying) (bootstrap_prerequisites retrying) ?D"
        by (rule ordered_completed_work)
      show "work_ready (bootstrap_jobs retrying) (bootstrap_prerequisites retrying) ?D a" by (fact ready)
    qed
    then show ?case unfolding completed by (rule rtranclp.rtrancl_into_rtrancl[OF Suc.IH])
  qed
qed

definition bootstrap_waves where
  "bootstrap_waves retrying = [{Observe_View}] @ (if retrying then [] else [{Claim_Config}])
      @ [{Persist_Config}, {Arm_Scheduler}, {Start_PreVote}]"

lemma bootstrap_wave_dependencies:
  assumes shape: "bootstrap_waves retrying = before @ batch # after"
    and member: "a \<in> batch"
  shows "a \<in> bootstrap_jobs retrying \<and> bootstrap_prerequisites retrying a \<subseteq> \<Union>(set before)"
  using shape member
  unfolding bootstrap_waves_def bootstrap_jobs_def
  by (cases retrying; cases before)
    (auto simp: Cons_eq_append_conv)

lemma bootstrap_service_finishes:
  assumes service: "bounded_service (bootstrap_jobs retrying) (bootstrap_prerequisites retrying) sel delay horizon"
    and time: "length (bootstrap_waves retrying) * delay \<le> horizon"
  shows "bootstrap_projection retrying C
      (startup_finished retrying sel (length (bootstrap_waves retrying) * delay)) = Startup_PreVote C"
proof -
  have "\<Union>(set (bootstrap_waves retrying)) \<subseteq>
      startup_finished retrying sel (length (bootstrap_waves retrying) * delay)"
    by (rule bounded_service_finishes_plan[OF service bootstrap_wave_dependencies, where rest="[]"])
      (simp_all add: time)
  then have "Start_PreVote \<in> startup_finished retrying sel (length (bootstrap_waves retrying) * delay)"
    unfolding bootstrap_waves_def by auto
  then show ?thesis unfolding bootstrap_projection_def by simp
qed

theorem configured_startup_opens_prevote:
  assumes capture: "configured_bootstrap R captured_view matches c C"
    and eligible: "eligible"
    and healthy: "candidate"
    and live: "initial_quorum C known"
    and service: "bounded_service (bootstrap_jobs retrying) (bootstrap_prerequisites retrying) sel delay horizon"
    and time: "(if retrying then 4 else 5) * delay \<le> horizon"
  shows "bootstrap_projection retrying C
      (startup_finished retrying sel ((if retrying then 4 else 5) * delay)) = Startup_PreVote C"
    "rtranclp (startup_step (configured_bootstrap R captured_view matches c) known c eligible candidate)
      (Await_View (if retrying then Some C else None)) (Startup_PreVote C)"
proof -
  have length: "length (bootstrap_waves retrying) = (if retrying then 4 else 5)"
    by (simp add: bootstrap_waves_def)
  show phase: "bootstrap_projection retrying C
      (startup_finished retrying sel ((if retrying then 4 else 5) * delay)) = Startup_PreVote C"
    using bootstrap_service_finishes[OF service, of C] time by (simp add: length)
  have install: "installation_allowed False eligible known c C"
    using configured_known_quorum(1)[OF capture] eligible live unfolding installation_allowed_def by simp
  have permits: "\<not> retrying \<Longrightarrow> configured_bootstrap R captured_view matches c C" by (rule capture)
  have "rtranclp (startup_step (configured_bootstrap R captured_view matches c) known c eligible candidate)
      (Await_View (if retrying then Some C else None))
      (bootstrap_projection retrying C (startup_finished retrying sel ((if retrying then 4 else 5) * delay)))"
  proof (rule bootstrap_service_projects_trace)
    show "\<not> retrying \<Longrightarrow> configured_bootstrap R captured_view matches c C" by (fact permits)
    show "installation_allowed False eligible known c C" by (fact install)
    show "candidate" by (fact healthy)
  qed
  with phase
  show "rtranclp (startup_step (configured_bootstrap R captured_view matches c) known c eligible candidate)
      (Await_View (if retrying then Some C else None)) (Startup_PreVote C)"
    by simp
qed

section \<open>Handoff to a fresh fixed-configuration election\<close>

lemma fully_resolved_capture:
  assumes stable: "stable_requirements R matches bind"
    and capture: "configured_bootstrap R view matches n C"
    and complete: "bind ` R \<subseteq> view"
  shows "C = Discovered_ID ` (bind ` R)"
proof -
  have member: "slot_member (view_lookup bind view) r = Discovered_ID (bind r)"
    if "r \<in> R" for r
  proof -
    have "bind r \<in> view" using imageI[OF that, of bind] complete by blast
    then show ?thesis by (simp add: slot_member_def view_lookup_def)
  qed
  show ?thesis unfolding configured_view_form[OF stable capture] discovered_configuration_def image_image
    by (rule image_cong[OF refl member])
qed

text \<open>
  This handoff starts with the fresh fixed core. In particular no earlier
  election term has been installed and no non-bootstrap state has been
  accepted. Each participant in the healthy quorum and the candidate has
  captured a fully resolved roster and uses the resulting installed
  configuration. The candidate's current discovery view contains the real
  healthy quorum. The startup and election service bounds apply to
  successive windows. Installation of the candidate's roster does not itself
  generate fresh pre-votes, advance the term, or schedule remote writes.

  The completeness condition avoids treating inert placeholders as voters.
  Configured bootstrap has initial quorum intersection in the less restrictive
  case where discovery views disagree. That is separate from equality of the
  configurations installed at the voters in this fixed window.
\<close>

theorem configured_startup_to_fixed_election:
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
    and election_service: "bounded_service (window_jobs True H H (insert c H) c False)
      (window_dependencies True H H (insert c H) c False) election_sel election_delay election_horizon"
    and election_time: "4 * election_delay \<le> election_horizon"
  shows "\<forall>n\<in>insert c H. C n = Discovered_ID ` V"
    "rtranclp (startup_step (configured_bootstrap R (view c) matches c) H c eligible candidate)
      (Await_View (if retrying then Some (C c) else None)) (Startup_PreVote (C c))"
    "leader (window_state initial c t H (window_history initial c t v u)
      (completed_work (window_jobs True H H (insert c H) c False)
        (window_dependencies True H H (insert c H) c False) election_sel (4 * election_delay))) t = Some c"
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
  show "leader (window_state initial c t H (window_history initial c t v u)
      (completed_work (window_jobs True H H (insert c H) c False)
        (window_dependencies True H H (insert c H) c False) election_sel (4 * election_delay))) t = Some c"
    by (rule window.fixed_candidate_wins_by_deadline(1)[OF TrueI election_service election_time])
qed

text \<open>
  Best-effort discovery has no fixed configured roster from which to derive
  this handoff. Disjoint discovered groups can each have a local majority
  and select disjoint configurations, as shown by best_effort_disjoint_views.
  An earlier configured capture can also remain blocked after discovery
  finds a different roster majority. The live guard uses the original real
  IDs. The startup deadline requires a quorum of that captured configuration.
\<close>

end
