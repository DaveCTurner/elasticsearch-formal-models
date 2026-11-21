theory Coordination_Persistence
  imports Coordination_Transport
begin

section \<open>The coordination projection of a Lucene commit\<close>

record coordination_metadata =
  stored_accepted_term :: nat
  stored_accepted_config :: config
  stored_committed_config :: config

record disk_image =
  stored_current_term :: nat
  stored_version :: nat
  stored_metadata :: coordination_metadata

definition disk_key where
  "disk_key d = \<lparr>rank_term = stored_accepted_term (stored_metadata d), rank_version = stored_version d\<rparr>"

definition disk_projection :: "'v local_node \<Rightarrow> disk_image" where
  "disk_projection x = \<lparr>stored_current_term = current_term x, stored_version = rank_version (accepted_key x),
    stored_metadata = \<lparr>stored_accepted_term = rank_term (accepted_key x),
      stored_accepted_config = accepted_config x, stored_committed_config = local_committed x\<rparr>\<rparr>"

definition node_disk where
  "node_disk s n = disk_projection (java_nodes (coordination s) n)"

definition restore_node where
  "restore_node d value = \<lparr>current_term = stored_current_term d, accepted_key = disk_key d,
    accepted_value = value, accepted_config = stored_accepted_config (stored_metadata d),
    local_committed = stored_committed_config (stored_metadata d), join_votes = {},
    started_join = False, election_won = False, published_version = 0,
    published_config = stored_accepted_config (stored_metadata d), publish_votes = {}\<rparr>"

text \<open>
  The accepted value is a ghost publication identity. Recovery reads the
  accepted key, rather than the state's transient ClusterState.stateUUID.
  The Java constructor resets the election and publication fields.
\<close>

lemma restore_projects:
  "disk_projection (restore_node d value) = d"
  by (cases d) (simp add: disk_projection_def restore_node_def disk_key_def)

lemma restore_java_restart:
  "restore_node (disk_projection x) (accepted_value x) = java_reset x"
  by (cases x) (simp add: disk_projection_def restore_node_def disk_key_def java_reset_def)

definition publication_value where
  "publication_value J k u \<longleftrightarrow> (\<exists>d p. Publish_Msg d p u \<in> J \<and> request_key p = k)"

definition replay_value where
  "replay_value initial_value J k = (if rank_term k = 0 then initial_value else (THE u. publication_value J k u))"

lemma accepted_value_origin:
  assumes "tla_reachable N V C initial_value versions s"
  shows "(rank_term (accepted_key (nodes_at s n)) = 0 \<and> accepted_value (nodes_at s n) = initial_value) \<or>
    publication_value (messages s) (accepted_key (nodes_at s n)) (accepted_value (nodes_at s n))"
  using assms
proof induction
  case init
  then show ?case by (simp add: tla_initial_def)
next
  case (advance s a)
  then show ?case by (cases a)
    (auto simp: publication_value_def tla_initial_def put_node_def reset_transient_def Let_def split: if_splits)
qed

lemma published_value_positive:
  assumes "tla_reachable N V C initial_value versions s" "Publish_Msg d p u \<in> messages s"
  shows "0 < pub_term p"
proof -
  obtain a where a: "dynamic_reachable C a" "linked C s a" using tla_dynamic_refinement[OF assms(1)] by blast
  obtain h where h: "h @ [p] \<in> publications a" using linkedD(3)[OF a(2) assms(2)] by auto
  have ok: "publications_ok C a" using dynamic_invariants[OF a(1)] by auto
  from publication_positive[OF ok h] show ?thesis by simp
qed

lemma recovered_value_from_journal:
  assumes "transport_reachable N E V C initial_value versions s H"
  shows "replay_value initial_value (journal s) (disk_key (node_disk s n)) = accepted_value (java_nodes (coordination s) n)"
proof -
  obtain t where r: "tla_reachable N V C initial_value versions t" and p: "coordination s = project_java E t"
    using transport_refines_tla[OF assms] by blast
  let ?x = "nodes_at t n"
  let ?k = "accepted_key ?x"
  let ?u = "accepted_value ?x"
  have origin: "(rank_term ?k = 0 \<and> ?u = initial_value) \<or> publication_value (messages t) ?k ?u"
    by (rule accepted_value_origin[OF r])
  have replay: "replay_value initial_value (messages t) ?k = ?u"
  proof (cases "rank_term ?k = 0")
    case True
    have "\<not> publication_value (messages t) ?k ?u"
    proof
      assume "publication_value (messages t) ?k ?u"
      then obtain d p where msg: "Publish_Msg d p ?u \<in> messages t" and key: "request_key p = ?k"
        unfolding publication_value_def by blast
      have "pub_term p = rank_term ?k" using key[symmetric] by simp
      with True published_value_positive[OF r msg] show False by simp
    qed
    with True origin show ?thesis by (simp add: replay_value_def)
  next
    case False
    then have known: "publication_value (messages t) ?k ?u" using origin by simp
    have "(THE u. publication_value (messages t) ?k u) = ?u"
    proof (rule the_equality)
      show "publication_value (messages t) ?k ?u" by (rule known)
      fix u
      assume "publication_value (messages t) ?k u"
      with known show "u = ?u" using tla_log_matching[OF r]
        unfolding publication_value_def by metis
    qed
    then show ?thesis using False by (simp add: replay_value_def)
  qed
  then show ?thesis by (simp add: p node_disk_def disk_projection_def disk_key_def mask_votes_def)
qed

datatype disk_write = Term_Write nat | State_Write rank config config | Mark_Committed

fun write_effect where
  "write_effect (Term_Write t) d = d\<lparr>stored_current_term := t\<rparr>"
| "write_effect (State_Write k D F) d =
    d\<lparr>stored_version := rank_version k, stored_metadata :=
      \<lparr>stored_accepted_term = rank_term k, stored_accepted_config = D, stored_committed_config = F\<rparr>\<rparr>"
| "write_effect Mark_Committed d = d\<lparr>stored_metadata := (stored_metadata d)\<lparr>
    stored_committed_config := stored_accepted_config (stored_metadata d)\<rparr>\<rparr>"

datatype write_mode = Full_Write | Term_Only | Incremental_State | No_Write

fun writer_mode where
  "writer_mode retry old (Term_Write t) = (if retry then Full_Write else Term_Only)"
| "writer_mode retry old (State_Write k D F) =
    (if retry \<or> rank_term k \<noteq> rank_term (disk_key old) then Full_Write else Incremental_State)"
| "writer_mode retry old Mark_Committed =
    (if stored_committed_config (stored_metadata old) = stored_accepted_config (stored_metadata old)
     then No_Write else if retry then Full_Write else Incremental_State)"

text \<open>
  Marking the cluster UUID committed may trigger an actual write even when
  the projected image is unchanged. No_Write represents this projected
  stutter as well as the identity branch of withLastCommittedValues.
  Global metadata equality includes CoordinationMetadata. Thus a skipped
  global document rewrite preserves the coordination projection.
\<close>

fun writer_commit where
  "writer_commit Full_Write old target = target"
| "writer_commit Term_Only old target = old\<lparr>stored_current_term := stored_current_term target\<rparr>"
| "writer_commit Incremental_State old target =
    old\<lparr>stored_current_term := stored_current_term target, stored_version := stored_version target,
      stored_metadata := (if stored_metadata old = stored_metadata target then stored_metadata old
        else stored_metadata target)\<rparr>"
| "writer_commit No_Write old target = old"

lemma writer_matches_setter:
  "writer_commit (writer_mode retry d op) d (write_effect op d) = write_effect op d"
  by (cases op; cases d) (auto simp: disk_key_def split: if_splits)

fun method_write where
  "method_write (Java_Bootstrap n k u D F) = Some (State_Write k D F)"
| "method_write (Java_Start_Join n c t) = Some (Term_Write t)"
| "method_write (Java_Publish n p u) = Some (State_Write (request_key p) (pub_config p) (pub_previous p))"
| "method_write (Java_Commit n c k) = Some Mark_Committed"
| "method_write _ = None"

fun optional_write where
  "optional_write None d = d"
| "optional_write (Some op) d = write_effect op d"

lemma core_disk_effect:
  "disk_projection (java_nodes (java_execute N E j a) i) =
    (if i = receiver a then optional_write (method_write a) (disk_projection (java_nodes j i))
     else disk_projection (java_nodes j i))"
  by (cases a) (simp_all add: disk_projection_def java_reset_def java_put_def Let_def)

lemma coordinator_disk_effect:
  "node_disk (coordinator_execute N E s (Dispatch a enter)) i =
    (if i = receiver a then optional_write (method_write a) (node_disk s i) else node_disk s i)"
  unfolding node_disk_def by (simp add: put_lifecycle_def core_disk_effect)

lemma dispatch_keeps_disk:
  assumes "method_write a = None"
  shows "node_disk (coordinator_execute N E s (Dispatch a enter)) = node_disk s"
proof (rule ext)
  fix i
  show "node_disk (coordinator_execute N E s (Dispatch a enter)) i = node_disk s i"
    by (simp only: coordinator_disk_effect assms optional_write.simps if_cancel)
qed

lemma non_dispatch_keeps_disk:
  assumes "\<And>a enter. event \<noteq> Dispatch a enter"
  shows "node_disk (coordinator_execute N E s event) = node_disk s"
  using assms by (cases event)
    (auto simp: node_disk_def disk_projection_def put_lifecycle_def java_put_def Let_def fun_eq_iff)

section \<open>Write-all and restart selection\<close>

definition recovery_rank where
  "recovery_rank d = (disk_key d, stored_current_term d)"

lemma loader_order:
  "recovery_rank x < recovery_rank y \<longleftrightarrow>
    stored_accepted_term (stored_metadata x) < stored_accepted_term (stored_metadata y) \<or>
    (stored_accepted_term (stored_metadata x) = stored_accepted_term (stored_metadata y) \<and>
      (stored_version x < stored_version y \<or>
        (stored_version x = stored_version y \<and> stored_current_term x < stored_current_term y)))"
  by (auto simp: recovery_rank_def disk_key_def less_prod_def rank_less_iff rank_le_iff order_le_less)

text \<open>
  The loader maximizes accepted term, accepted version, then current term.
  It separately rejects a best image with a lower current term than another
  image. Equal ranks may be resolved by data path iteration order. A
  successful load also passes the index integrity, node ID and cluster UUID
  checks, which can further restrict this relation.
\<close>

definition recovers where
  "recovers images d \<longleftrightarrow> d \<in> images \<and>
    (\<forall>x\<in>images. recovery_rank x \<le> recovery_rank d \<and> stored_current_term x \<le> stored_current_term d)"

definition images_for where
  "images_for paths copies = copies ` paths"

definition complete_paths where
  "complete_paths completed old target = (\<lambda>path. if path \<in> completed then target else old path)"

lemma recover_completed_write:
  assumes "paths \<noteq> {}" "paths \<subseteq> completed"
  shows "recovers (images_for paths (complete_paths completed copies target)) d \<longleftrightarrow> d = target"
proof -
  have "images_for paths (complete_paths completed copies target) = {target}"
    using assms unfolding images_for_def complete_paths_def by auto
  then show ?thesis by (auto simp: recovers_def)
qed

lemma recover_interrupted_write:
  assumes same: "\<And>p. p \<in> paths \<Longrightarrow> copies p = old"
    and recover: "recovers (images_for paths (complete_paths completed copies target)) d"
  shows "d = old \<or> d = target"
  using recover same unfolding recovers_def images_for_def complete_paths_def by force

lemma recover_with_stale_paths:
  assumes retained: "target \<in> images"
    and stale: "\<And>q. q \<in> images \<Longrightarrow> q \<noteq> target \<Longrightarrow> recovery_rank q < recovery_rank target"
    and terms: "\<And>q. q \<in> images \<Longrightarrow> stored_current_term q \<le> stored_current_term target"
  shows "recovers images d \<longleftrightarrow> d = target"
proof
  assume "recovers images d"
  then have "d \<in> images" and "recovery_rank target \<le> recovery_rank d"
    using retained by (auto simp: recovers_def)
  with stale show "d = target" by (meson less_le_not_le)
next
  assume "d = target"
  with retained stale terms show "recovers images d"
    by (auto simp: recovers_def intro: less_imp_le)
qed

lemma commit_copies_tie:
  "recovery_rank (write_effect Mark_Committed old) = recovery_rank old"
  by (simp add: recovery_rank_def disk_key_def)

lemma same_rank_config_divergence:
  assumes "stored_committed_config (stored_metadata old) \<noteq> stored_accepted_config (stored_metadata old)"
  shows "write_effect Mark_Committed old \<noteq> old"
    "recovers {old, write_effect Mark_Committed old} old"
    "recovers {old, write_effect Mark_Committed old} (write_effect Mark_Committed old)"
proof -
  show "write_effect Mark_Committed old \<noteq> old"
  proof
    assume "write_effect Mark_Committed old = old"
    from arg_cong[OF this, of "\<lambda>d. stored_committed_config (stored_metadata d)"]
    show False using assms by simp
  qed
  show "recovers {old, write_effect Mark_Committed old} old"
    "recovers {old, write_effect Mark_Committed old} (write_effect Mark_Committed old)"
    by (auto simp: recovers_def recovery_rank_def disk_key_def)
qed

section \<open>Composition at transport call boundaries\<close>

text \<open>
  A call is serialized with the local coordination state. A durable change
  is one term write, one accepted-state write, or the commit-only update.
  Preparing writers alone does not alter their committed images. Once all
  commits finish, the memory update and result can be exposed. An
  interrupted operation can leave either image on each path.
\<close>

lemma dispatch_disk_transition:
  "node_disk (coordinator_execute N E s (Dispatch a enter)) = node_disk s \<or>
    (\<exists>n op. node_disk (coordinator_execute N E s (Dispatch a enter)) =
      (node_disk s)(n := write_effect op (node_disk s n)))"
proof (cases "method_write a")
  case None
  then show ?thesis by (blast intro!: dispatch_keeps_disk)
next
  case (Some op)
  have "node_disk (coordinator_execute N E s (Dispatch a enter)) =
      (node_disk s)(receiver a := write_effect op (node_disk s (receiver a)))"
  proof (rule ext)
    fix i
    show "node_disk (coordinator_execute N E s (Dispatch a enter)) i =
      ((node_disk s)(receiver a := write_effect op (node_disk s (receiver a)))) i"
      by (cases "i = receiver a")
        (simp_all only: coordinator_disk_effect Some optional_write.simps fun_upd_apply if_True if_False)
  qed
  then show ?thesis by blast
qed

lemma transport_disk_effect:
  assumes step: "transport_step N E V C v s H s' H'"
  shows "node_disk s' = node_disk s \<or>
    (\<exists>n op. node_disk s' = (node_disk s)(n := write_effect op (node_disk s n)))"
  using step
proof cases
  case (control a)
  then show ?thesis using dispatch_disk_transition non_dispatch_keeps_disk by (cases a) blast+
next
  case start_join
  then show ?thesis using dispatch_disk_transition by metis
next
  case receive_publish
  then show ?thesis using dispatch_disk_transition by metis
next
  case receive_commit
  then show ?thesis using dispatch_disk_transition by metis
qed (auto simp: fun_eq_iff node_disk_def disk_projection_def put_lifecycle_def java_put_def Let_def)

definition disks_agree where
  "disks_agree paths s copies \<longleftrightarrow> (\<forall>n p. p \<in> paths n \<longrightarrow> copies n p = node_disk s n)"

definition install_write where
  "install_write copies n completed d =
    copies(n := complete_paths completed (copies n) d)"

lemma disks_agree_write:
  assumes agree: "disks_agree paths s copies" and all: "paths n \<subseteq> completed"
    and update: "node_disk s' = (node_disk s)(n := d)"
  shows "disks_agree paths s' (install_write copies n completed d)"
  using assms unfolding disks_agree_def install_write_def complete_paths_def by auto

lemma interrupted_image:
  assumes agree: "disks_agree paths s copies" and retained: "available \<subseteq> paths n"
    and cut: "node_disk s' = (node_disk s)(n := target)"
    and load: "recovers (images_for available (install_write copies n completed target n)) d"
  shows "d = node_disk s n \<or> d = node_disk s' n"
proof -
  have same: "copies n p = node_disk s n" if "p \<in> available" for p
    using agree that retained unfolding disks_agree_def by auto
  have valid: "recovers (images_for available (complete_paths completed (copies n) target)) d"
    using load by (simp add: install_write_def)
  from recover_interrupted_write[OF same valid] cut show ?thesis by simp
qed

lemma recovered_node_restarts:
  assumes step: "s' = coordinator_execute N E s (Dispatch (Java_Restart n) False)"
    and disk: "d = node_disk s n"
  shows "java_nodes (coordination s') n = restore_node d (accepted_value (java_nodes (coordination s) n))"
  using assms by (simp add: node_disk_def put_lifecycle_def java_put_def restore_java_restart)

lemma successful_restart_transport:
  assumes "transport_reachable N E V C v versions s H" "n \<in> N"
  shows "transport_reachable N E V C v versions
    (coordinator_execute N E s (Dispatch (Java_Restart n) False)) H"
  by (rule transport_reachable.step[OF assms(1)], rule transport_step.control) (use assms(2) in simp_all)

theorem restart_after_acknowledged_write:
  assumes run: "transport_reachable N E V C v versions s H"
    and call: "transport_step N E V C v s H s' H'"
    and retained: "available \<noteq> {}" "available \<subseteq> paths n"
    and cut: "node_disk s' = (node_disk s)(n := write_effect op (node_disk s n))"
    and recovered: "recovers (images_for available
      (install_write copies n (paths n) (write_effect op (node_disk s n)) n)) d"
    and member: "n \<in> N"
  defines "restarted \<equiv> coordinator_execute N E s' (Dispatch (Java_Restart n) False)"
  shows "d = node_disk s' n"
    "java_nodes (coordination restarted) n =
      restore_node d (replay_value v (journal s') (disk_key d))"
    "transport_reachable N E V C v versions restarted H'"
proof -
  have post: "node_disk s' n = write_effect op (node_disk s n)" using cut by simp
  have "d = write_effect op (node_disk s n)"
    using recover_completed_write[OF retained, of "copies n" "write_effect op (node_disk s n)" d]
      recovered by (simp add: install_write_def)
  then have disk: "d = node_disk s' n" by (simp add: post)
  then show "d = node_disk s' n" .
  have "transport_reachable N E V C v versions s' H'" by (rule transport_reachable.step[OF run call])
  then have r: "transport_reachable N E V C v versions s' H'" .
  have restored: "java_nodes (coordination restarted) n =
      restore_node d (accepted_value (java_nodes (coordination s') n))"
    unfolding restarted_def by (rule recovered_node_restarts[OF refl disk])
  from restored recovered_value_from_journal[OF r, of n] disk
  show "java_nodes (coordination restarted) n = restore_node d (replay_value v (journal s') (disk_key d))"
    by simp
  from successful_restart_transport[OF r member] show "transport_reachable N E V C v versions restarted H'"
    unfolding restarted_def .
qed

theorem restart_during_write:
  assumes run: "transport_reachable N E V C v versions s H"
    and call: "transport_step N E V C v s H s' H'"
    and agree: "disks_agree paths s copies" and retained: "available \<subseteq> paths n"
    and cut: "node_disk s' = (node_disk s)(n := write_effect op (node_disk s n))"
    and recovered: "recovers (images_for available
      (install_write copies n completed (write_effect op (node_disk s n)) n)) d"
    and member: "n \<in> N"
  obtains base traffic where "(base = s \<and> traffic = H) \<or> (base = s' \<and> traffic = H')"
    "d = node_disk base n"
    "transport_reachable N E V C v versions
      (coordinator_execute N E base (Dispatch (Java_Restart n) False)) traffic"
proof -
  from interrupted_image[OF agree retained cut recovered] show thesis
  proof
    assume old: "d = node_disk s n"
    show thesis by (rule that[of s H]) (use old successful_restart_transport[OF run member] in auto)
  next
    assume new: "d = node_disk s' n"
    have post_reachable: "transport_reachable N E V C v versions s' H'" by (rule transport_reachable.step[OF run call])
    have "transport_reachable N E V C v versions (coordinator_execute N E s' (Dispatch (Java_Restart n) False)) H'"
      by (rule successful_restart_transport[OF post_reachable member])
    then show thesis using new by (intro that[of s' H']) auto
  qed
qed

text \<open>
  These are quiescent boundaries for synchronous nodes with configured
  data paths. A crash during an outstanding operation selects a valid
  image and rewrites it on startup before restarting coordination.
  If recovery selects the new image, the transport post-state is a
  ghost linearization of the interrupted call. Its extra outputs are
  overapproximation; the concrete execution need not deliver them.
\<close>

inductive durable_execution for N E V C v versions paths where
  init:
    "default_strategy N E C \<Longrightarrow> v \<in> V \<Longrightarrow> (\<And>n. n \<in> N \<Longrightarrow> paths n \<noteq> {}) \<Longrightarrow>
     durable_execution N E V C v versions paths (coordinator_initial v versions) {}
       (\<lambda>n p. node_disk (coordinator_initial v versions) n)"
| transient:
    "durable_execution N E V C v versions paths s H copies \<Longrightarrow>
     transport_step N E V C v s H s' H' \<Longrightarrow> node_disk s' = node_disk s \<Longrightarrow>
     durable_execution N E V C v versions paths s' H' copies"
| written:
    "durable_execution N E V C v versions paths s H copies \<Longrightarrow>
     transport_step N E V C v s H s' H' \<Longrightarrow>
     node_disk s' = (node_disk s)(n := write_effect op (node_disk s n)) \<Longrightarrow>
     durable_execution N E V C v versions paths s' H'
       (install_write copies n (paths n) (writer_commit (writer_mode retry (node_disk s n) op)
          (node_disk s n) (write_effect op (node_disk s n))))"
| recovered:
    "durable_execution N E V C v versions paths s H copies \<Longrightarrow>
     transport_step N E V C v s H s' H' \<Longrightarrow> n \<in> N \<Longrightarrow> available \<subseteq> paths n \<Longrightarrow>
     node_disk s' = (node_disk s)(n := write_effect op (node_disk s n)) \<Longrightarrow>
     recovers (images_for available (install_write copies n completed (write_effect op (node_disk s n)) n)) d \<Longrightarrow>
     durable_execution N E V C v versions paths
       (coordinator_execute N E (if d = node_disk s n then s else s') (Dispatch (Java_Restart n) False))
       (if d = node_disk s n then H else H')
       (install_write copies n (paths n) d)"

lemma durable_execution_invariants:
  assumes "durable_execution N E V C v versions paths s H copies"
  shows "transport_reachable N E V C v versions s H \<and> disks_agree paths s copies"
  using assms
proof induction
  case init
  then show ?case by (auto simp: disks_agree_def intro: transport_reachable.init)
next
  case transient
  then show ?case by (auto simp: disks_agree_def intro: transport_reachable.step)
next
  case (written s H copies s' H' n op retry)
  then show ?case by (auto simp: writer_matches_setter intro: transport_reachable.step disks_agree_write)
next
  case (recovered s H copies s' H' n available op completed d)
  let ?base = "if d = node_disk s n then s else s'"
  let ?traffic = "if d = node_disk s n then H else H'"
  from recovered.IH have agree: "disks_agree paths s copies" and pre: "transport_reachable N E V C v versions s H"
    by auto
  from transport_reachable.step[OF pre recovered.hyps(2)] pre
  have transport: "transport_reachable N E V C v versions ?base ?traffic" by simp
  from interrupted_image[OF agree recovered.hyps(4-6)] recovered.hyps(5)
  have disk: "node_disk ?base = (node_disk s)(n := d)" by (auto simp: fun_eq_iff)
  have restart: "node_disk (coordinator_execute N E ?base (Dispatch (Java_Restart n) False)) = node_disk ?base"
    by (rule dispatch_keeps_disk) simp
  show ?case
    using successful_restart_transport[OF transport recovered.hyps(3)] restart disk agree
    by (auto intro: disks_agree_write)
qed

theorem durable_execution_refines_tla:
  assumes "durable_execution N E V C v versions paths s H copies"
  shows "\<exists>t. tla_reachable N V C v versions t \<and> configurations_ok E t \<and> coordination s = project_java E t"
  using durable_execution_invariants[OF assms] by (blast intro: transport_refines_tla)

theorem restart_from_current_disk:
  assumes run: "durable_execution N E V C v versions paths s H copies" and member: "n \<in> N"
    and subset: "available \<subseteq> paths n" and load: "recovers (images_for available (copies n)) d"
  shows "java_nodes (coordination (coordinator_execute N E s (Dispatch (Java_Restart n) False))) n =
    restore_node d (replay_value v (journal s) (disk_key d))"
    "transport_reachable N E V C v versions (coordinator_execute N E s (Dispatch (Java_Restart n) False)) H"
proof -
  from durable_execution_invariants[OF run]
  have reachable: "transport_reachable N E V C v versions s H" and agree: "disks_agree paths s copies" by auto
  have disk: "d = node_disk s n" using load agree subset by (auto simp: recovers_def images_for_def disks_agree_def)
  from recovered_node_restarts[OF refl disk, of N E] disk recovered_value_from_journal[OF reachable, of n]
  show "java_nodes (coordination (coordinator_execute N E s (Dispatch (Java_Restart n) False))) n =
    restore_node d (replay_value v (journal s) (disk_key d))" by simp
  show "transport_reachable N E V C v versions (coordinator_execute N E s (Dispatch (Java_Restart n) False)) H"
    by (rule successful_restart_transport[OF reachable member])
qed

section \<open>Nonsynchronous backends\<close>

definition stale_config where
  "stale_config marker d = d\<lparr>stored_metadata := (stored_metadata d)\<lparr>
    stored_accepted_config := {marker}, stored_committed_config := {marker}\<rparr>\<rparr>"

theorem async_restart_may_lose_returned_term:
  assumes "stored_current_term d < t"
  shows "restore_node d value \<noteq> restore_node (write_effect (Term_Write t) d) value"
proof
  assume "restore_node d value = restore_node (write_effect (Term_Write t) d) value"
  from arg_cong[OF this, of current_term] show False using assms by (simp add: restore_node_def)
qed

theorem memory_only_restart_may_lose_returned_term:
  assumes "stored_current_term d > 0"
  shows "restore_node d value \<noteq> java_nodes (java_initial initial_value (\<lambda>_. 0)) n"
proof
  assume "restore_node d value = java_nodes (java_initial initial_value (\<lambda>_. 0)) n"
  from arg_cong[OF this, of current_term] show False
    using assms by (simp add: restore_node_def java_initial_def)
qed

lemma async_flush_can_change_configuration:
  assumes "stored_accepted_config (stored_metadata d) \<noteq> {marker}"
  shows "stale_config marker d \<noteq> d"
proof
  assume "stale_config marker d = d"
  from arg_cong[OF this, of "\<lambda>d. stored_accepted_config (stored_metadata d)"]
  show False using assms by (simp add: stale_config_def)
qed

lemma stale_marker_has_no_eligible_quorum:
  assumes "marker \<notin> E" "Q \<subseteq> E"
  shows "\<not> java_has_quorum {marker} Q"
proof -
  have "{marker} \<inter> Q = {}" using assms by blast
  then show ?thesis by (simp add: java_has_quorum_def signed_int_def)
qed

end
