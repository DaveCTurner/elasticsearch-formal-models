theory Stalled_Operation_Isolation
  imports Recovery_Liveness Bounded_Service Stateless_Storage
begin

section \<open>Resources on the healthy path\<close>

datatype coordination_resource = Coord_Mutex node | Coord_Worker node | Applier_Worker node
  | Lease_Worker node | State_IO_Worker node | Download_Permit node | Local_Client node
  | Shared_Register | Shared_Manifest_Store

datatype isolation_job = Discovery_Transition node | Report_Handler node | Local_Apply node
  | Apply_Completion node | Publish_Deadline node | Submit_Claim node | Inspect_Lease node
  | Register_Exchange node | Complete_Claim node | Start_Download node | Read_Image node
  | Complete_Recovery node

fun isolation_needs where
  "isolation_needs (Discovery_Transition n) = {Coord_Mutex n, Coord_Worker n}"
| "isolation_needs (Report_Handler n) = {Coord_Mutex n, Coord_Worker n}"
| "isolation_needs (Local_Apply n) = {Applier_Worker n}"
| "isolation_needs (Apply_Completion n) = {Applier_Worker n, Coord_Mutex n}"
| "isolation_needs (Publish_Deadline n) = {Coord_Mutex n, Coord_Worker n}"
| "isolation_needs (Submit_Claim n) = {Coord_Mutex n, Coord_Worker n}"
| "isolation_needs (Inspect_Lease n) = {Lease_Worker n, Local_Client n, Shared_Register}"
| "isolation_needs (Register_Exchange n) = {Local_Client n, Shared_Register}"
| "isolation_needs (Complete_Claim n) = {Coord_Mutex n, Coord_Worker n}"
| "isolation_needs (Start_Download n) = {Download_Permit n, State_IO_Worker n}"
| "isolation_needs (Read_Image n) = {State_IO_Worker n, Local_Client n, Shared_Manifest_Store}"
| "isolation_needs (Complete_Recovery n) = {Coord_Mutex n, Coord_Worker n}"

text \<open>
  A job is a service boundary, not a claim that its resources are held by
  one Java stack frame. Complete_Claim includes the successful StartJoin
  broadcast and entry to the candidate's local join. Report_Handler is the
  proposed report path on the voter or candidate, with their local resources
  provisioned as stipulated here. Its authenticated transport and observation
  still need bounded service. Local_Apply and Apply_Completion describe the
  successful leader's local application and its callback entering Coordinator.
  The model deals with existing node processes; the durability and callback
  identity theories handle restart and changes of incarnation.

  Coordinator holds its mutex in handlePublishRequest until the
  CoordinationState persistence setter returns. For self-publication the
  PublicationTransportHandler runs this on CLUSTER_COORDINATION, which is also
  the publication timeout executor. Discovery after a leader failure requires
  Coordinator mutex entry. LeaderChecker's direct request handler uses the
  saved discovery nodes and the health service, so a healthy reply need not
  imply that the Coordinator mutex or executor is available.

  StatelessElectionStrategy.readLease submits on SNAPSHOT_META, and
  onNewElection uses an async read followed by compareAndSetRegister. An
  invocation that has submitted the async work can return without waiting for
  the backend. By contrast updateLease uses FutureUtils.get and is called from
  the accepted-state write for changes to either tracked generation. A waiter
  can therefore retain the caller's mutex and worker while lease work is
  pending elsewhere. StatelessPersistedState holds a permit in the capacity-one
  readStateTaskRunner until the completion listener releases it, including
  across async file downloads. Local lease and download executors are distinct;
  a claim can start without a free download permit, but election recovery cannot
  finish without its image. The resource split distinguishes the local client
  from admission at the shared store. Actual provider worker lifetimes and
  the available capacity at either boundary are separate assumptions.
\<close>

definition slot_available :: "(coordination_resource \<Rightarrow> nat) \<Rightarrow>
    (coordination_resource \<Rightarrow> nat) \<Rightarrow> coordination_resource set \<Rightarrow> coordination_resource \<Rightarrow> bool" where
  "slot_available capacity other held r \<longleftrightarrow>
    other r + (if r \<in> held then 1 else 0) < capacity r"

definition isolation_ready where
  "isolation_ready capacity other held job \<longleftrightarrow>
    (\<forall>r\<in>isolation_needs job. slot_available capacity other held r)"

lemma untargeted_hold_preserves_availability:
  assumes "isolation_needs job \<inter> held = {}"
  shows "isolation_ready capacity other held job \<longleftrightarrow> isolation_ready capacity other {} job"
  using assms by (auto simp: isolation_ready_def slot_available_def)

lemma guarded_capacity_admits_job:
  assumes "\<And>r. r \<in> isolation_needs job \<Longrightarrow>
    other r + (if r \<in> held then 1 else 0) < capacity r"
  shows "isolation_ready capacity other held job"
  using assms by (simp add: isolation_ready_def slot_available_def)

lemma saturated_resource_prevents_service:
  assumes needed: "r \<in> isolation_needs job" and held: "r \<in> held" and full: "capacity r \<le> Suc (other r)"
  shows "\<not> isolation_ready capacity other held job"
proof -
  have "\<not> slot_available capacity other held r" using held full by (simp add: slot_available_def)
  then show ?thesis using needed unfolding isolation_ready_def by blast
qed

lemma stalled_incumbent_does_not_hold_replacement_resources:
  fixes incumbent :: node
  defines "held \<equiv> {Coord_Mutex incumbent, Coord_Worker incumbent, Lease_Worker incumbent,
    State_IO_Worker incumbent, Download_Permit incumbent, Local_Client incumbent, Applier_Worker incumbent}"
  assumes independent: "n \<noteq> incumbent"
    and route: "job \<in> {Discovery_Transition n, Report_Handler n, Local_Apply n, Apply_Completion n,
      Submit_Claim n, Inspect_Lease n, Register_Exchange n, Complete_Claim n, Start_Download n,
      Read_Image n, Complete_Recovery n}"
  shows "isolation_ready capacity other held job \<longleftrightarrow> isolation_ready capacity other {} job"
  by (rule untargeted_hold_preserves_availability) (use independent route in \<open>auto simp: held_def\<close>)

lemma local_lease_claim_can_bypass_stalled_download:
  shows "isolation_ready capacity other {Download_Permit n} (Submit_Claim n) \<longleftrightarrow>
    isolation_ready capacity other {} (Submit_Claim n)"
    "isolation_ready capacity other {Download_Permit n} (Inspect_Lease n) \<longleftrightarrow>
    isolation_ready capacity other {} (Inspect_Lease n)"
    "isolation_ready capacity other {Download_Permit n} (Register_Exchange n) \<longleftrightarrow>
    isolation_ready capacity other {} (Register_Exchange n)"
  by (rule untargeted_hold_preserves_availability; simp)+

lemma stalled_download_blocks_recovery_on_same_runner:
  assumes "capacity (Download_Permit n) = 1"
  shows "\<not> isolation_ready capacity other {Download_Permit n} (Start_Download n)"
  using assms by (simp add: isolation_ready_def slot_available_def)

lemma stalled_shared_store_can_block_replacement:
  assumes "capacity Shared_Register \<le> Suc (other Shared_Register)"
  shows "\<not> isolation_ready capacity other {Shared_Register} (Register_Exchange n)"
  using assms by (simp add: isolation_ready_def slot_available_def)

section \<open>Caller timeout and late operation effects\<close>

record pending_coordination_operation =
  reply_registered :: bool
  operation_running :: bool
  operation_hold :: "coordination_resource set"

definition caller_timeout where
  "caller_timeout p = p\<lparr>reply_registered := False\<rparr>"

definition operation_return where
  "operation_return p = p\<lparr>reply_registered := False, operation_running := False, operation_hold := {}\<rparr>"

text \<open>
  TransportService.TimeoutHandler removes the local response handler and
  notifies it of the timeout if it wins the removal. This action does not
  join or interrupt the remote handler and cannot release the remote mutex or
  remote executor slot. The timeout callback itself must be serviced. The
  self-publication path is a direct local dispatch without a receive timeout;
  it can keep the coordination worker as well as the mutex. The
  same distinction between abandonment and provider completion is used for
  a caller-side storage timeout where the provider contract permits an
  unobserved write. This model does not add such a timeout to updateLease.
\<close>

lemma caller_timeout_keeps_operation_pending:
  "\<not> reply_registered (caller_timeout p)"
  "operation_running (caller_timeout p) = operation_running p"
  "operation_hold (caller_timeout p) = operation_hold p"
  by (simp_all add: caller_timeout_def)

lemma late_return_does_not_restore_old_listener:
  "\<not> reply_registered (operation_return (caller_timeout p))"
  "operation_hold (operation_return (caller_timeout p)) = {}"
  by (simp_all add: operation_return_def)

fun stalled_deadline_trace where
  "stalled_deadline_trace key p d 0 = (p,d)"
| "stalled_deadline_trace key p d (Suc k) =
    (caller_timeout (fst (stalled_deadline_trace key p d k)),
     dispatch_signal (Publication_Deadline key) (snd (stalled_deadline_trace key p d k)))"

theorem timeout_cannot_unblock_synchronous_publication:
  fixes d :: detector_view
  assumes locked: "\<not> coordinator_mutex_free d"
    and running: "operation_running p"
    and held: "{Coord_Mutex n, Coord_Worker n} \<subseteq> operation_hold p"
    and worker: "capacity (Coord_Worker n) = 1"
  shows "snd (stalled_deadline_trace key p d k) = d"
    "operation_running (fst (stalled_deadline_trace key p d k))"
    "\<not> isolation_ready capacity other (operation_hold (fst (stalled_deadline_trace key p d k))) (Publish_Deadline n)"
    "k > 0 \<Longrightarrow> \<not> reply_registered (fst (stalled_deadline_trace key p d k))"
proof -
  have eq: "snd (stalled_deadline_trace key p d k) = d" and
    holds: "operation_hold (fst (stalled_deadline_trace key p d k)) = operation_hold p" and
    active: "operation_running (fst (stalled_deadline_trace key p d k)) = operation_running p"
    using locked by (induction k) (simp_all add: can_dispatch_def caller_timeout_def)
  show "snd (stalled_deadline_trace key p d k) = d" by (rule eq)
  show "operation_running (fst (stalled_deadline_trace key p d k))" using active running by simp
  show "\<not> isolation_ready capacity other (operation_hold (fst (stalled_deadline_trace key p d k))) (Publish_Deadline n)"
    unfolding holds by (rule saturated_resource_prevents_service[where r="Coord_Worker n"]) (use held worker in auto)
  show "k > 0 \<Longrightarrow> \<not> reply_registered (fst (stalled_deadline_trace key p d k))"
    by (cases k) (simp_all add: caller_timeout_def)
qed

theorem abandoned_claim_can_still_reserve:
  assumes running: "operation_running p"
    and effect: "lease_effect backend before live expected (Claim_Term who proposed) result"
    and rep: "lease_term (lease_value live) = reserved_term s"
  defines "t \<equiv> lease_term (lease_value result)"
  shows "operation_running (caller_timeout p)"
    "\<not> reply_registered (operation_return (caller_timeout p))"
    "stateless_step s (s\<lparr>reserved_term := t, granted_to := (granted_to s)(t := Some who)\<rparr>)"
    "reserved_term s < t"
  using running lease_claim_refines_reserve[OF effect rep, folded t_def]
  by (simp_all add: caller_timeout_def operation_return_def)

section \<open>Bounded service from separated admission and dispatch\<close>

definition isolated_successes where
  "isolated_successes capacity other held selected i =
    (case selected i of None \<Rightarrow> None
      | Some job \<Rightarrow> if isolation_ready capacity (other i) (held i) job then Some job else None)"

lemma independent_blockers_leave_service_trace_unchanged:
  assumes independent: "\<And>i job. selected i = Some job \<Longrightarrow> isolation_needs job \<inter> held i = {}"
  shows "isolated_successes capacity other held selected = isolated_successes capacity other (\<lambda>_. {}) selected"
proof (rule ext)
  fix i
  show "isolated_successes capacity other held selected i = isolated_successes capacity other (\<lambda>_. {}) selected i"
  proof (cases "selected i")
    case None
    then show ?thesis by (simp add: isolated_successes_def)
  next
    case (Some job)
    then show ?thesis using untargeted_hold_preserves_availability[OF independent[OF Some]]
      by (simp add: isolated_successes_def)
  qed
qed

lemma stalled_download_defeats_every_direct_retry:
  assumes "capacity (Download_Permit n) = 1"
  shows "isolated_successes capacity other (\<lambda>_. {Download_Permit n}) (\<lambda>_. Some (Start_Download n)) i = None"
proof -
  have "\<not> isolation_ready capacity (other i) {Download_Permit n} (Start_Download n)"
    by (rule stalled_download_blocks_recovery_on_same_runner) (rule assms)
  then show ?thesis by (simp add: isolated_successes_def)
qed

text \<open>
  selected records successful service of the chosen operation conditional on
  local and shared resources being available. In particular, it does not treat
  arrival at an executor, a timeout, or an abandoned write as a success.
  Availability is required only for the selected healthy path when it is
  causally ready. Scheduler, transport, and repository service are still
  needed, so free capacity alone gives no time bound. Other operations can
  retain their resources forever. For several blocked operations, held is one
  explicit reserved occupancy and other accounts for all additional occupancy.
\<close>

theorem isolated_dispatch_supplies_work_service:
  fixes capacity :: "coordination_resource \<Rightarrow> nat"
    and other :: "nat \<Rightarrow> coordination_resource \<Rightarrow> nat"
    and held :: "nat \<Rightarrow> coordination_resource set"
    and selected :: "nat \<Rightarrow> isolation_job option"
  defines "select \<equiv> isolated_successes capacity other held selected"
  assumes reserves: "\<And>i j job r. i + B \<le> H \<Longrightarrow> i \<le> j \<Longrightarrow> j < i + B \<Longrightarrow>
      work_ready jobs dependencies (completed_work jobs dependencies select i) job \<Longrightarrow>
      r \<in> isolation_needs job \<Longrightarrow>
      other j r + (if r \<in> held j then 1 else 0) < capacity r"
    and service: "\<And>i job. i + B \<le> H \<Longrightarrow>
      work_ready jobs dependencies (completed_work jobs dependencies select i) job \<Longrightarrow>
      \<exists>j. i \<le> j \<and> j < i + B \<and> selected j = Some job"
  shows "bounded_service jobs dependencies select B H"
  unfolding bounded_service_def
proof (intro allI impI)
  fix i job
  assume time: "i + B \<le> H" and ready: "work_ready jobs dependencies (completed_work jobs dependencies select i) job"
  obtain j where bounds: "i \<le> j" "j < i + B" and choice: "selected j = Some job"
    using service[OF time ready] by blast
  have "isolation_ready capacity (other j) (held j) job"
    by (rule guarded_capacity_admits_job[OF reserves[OF time bounds ready]])
  with bounds choice show "\<exists>j\<ge>i. j < i + B \<and> select j = Some job"
    by (auto simp: select_def isolated_successes_def)
qed

end
