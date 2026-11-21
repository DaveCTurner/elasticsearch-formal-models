theory Master_Service_Executors
  imports Publication_Ancestry
begin

section \<open>Cluster-state copying and framed edits\<close>

record ('v, 'body) executor_state =
  executor_parent :: "rank \<times> 'v \<times> config \<times> config"
  executor_term :: nat
  executor_version :: nat
  executor_metadata_version :: nat
  executor_master :: "node option"
  executor_accepted :: config
  executor_committed :: config
  executor_body :: 'body

definition executor_snapshot where
  "executor_snapshot s n master mv body =
    \<lparr>executor_parent = accepted_base (batch_node s n),
     executor_term = rank_term (accepted_key (batch_node s n)),
     executor_version = rank_version (accepted_key (batch_node s n)),
     executor_metadata_version = mv, executor_master = master,
     executor_accepted = accepted_config (batch_node s n),
     executor_committed = local_committed (batch_node s n), executor_body = body\<rparr>"

text \<open>
  The parent is a ghost of the state used to seed the builder. The body
  abstracts fields such as projects, settings, customs, blocks, routing,
  exclusions, and node membership other than the advertised master.
  Content edits can depend on external inputs, for example restored snapshot
  settings. The ClusterState and Metadata copy builders copy the coordination
  fields. The CoordinationMetadata copy builder copies the committed
  configuration even when the accepted configuration, term, or exclusions
  are changed. Payload correctness for a particular task is a separate issue.
\<close>

datatype (dead 'body) state_edit = Edit_Content "('body \<Rightarrow> 'body)" | Propose_Configuration config

fun edit_state where
  "edit_state (Edit_Content f) s = s\<lparr>executor_body := f (executor_body s)\<rparr>"
| "edit_state (Propose_Configuration D) s = s\<lparr>executor_accepted := D\<rparr>"

definition edit_sequence where
  "edit_sequence edits s = fold edit_state edits s"

definition state_frame where
  "state_frame s r \<longleftrightarrow>
    executor_parent r = executor_parent s \<and> executor_committed r = executor_committed s \<and>
    executor_term r = executor_term s \<and> executor_master r = executor_master s \<and>
    executor_version r = executor_version s \<and> executor_metadata_version r = executor_metadata_version s"

lemma edits_frame:
  "state_frame s (edit_sequence edits s)"
  unfolding edit_sequence_def
proof (induction edits arbitrary: s)
  case Nil
  show ?case by (simp add: state_frame_def)
next
  case (Cons edit edits)
  have "state_frame s (edit_state edit s)" by (cases edit) (simp_all add: state_frame_def)
  with Cons.IH[of "edit_state edit s"] show ?case by (simp add: state_frame_def)
qed

lemma state_frame_trans:
  "state_frame s r \<Longrightarrow> state_frame r t \<Longrightarrow> state_frame s t"
  unfolding state_frame_def by simp

lemma state_frameD:
  assumes "state_frame s r"
  shows "executor_parent r = executor_parent s" "executor_committed r = executor_committed s"
    "executor_term r = executor_term s" "executor_master r = executor_master s"
    "executor_version r = executor_version s" "executor_metadata_version r = executor_metadata_version s"
  using assms unfolding state_frame_def by auto

text \<open>
  Each successful task passes its result to the next task. If execution
  fails before producing a state, the simple wrappers keep the previous
  accumulator. The post-batch hook receives the final accumulator. A
  failure of the whole batch returns the input and starts no publication.
\<close>

fun accumulate_task where
  "accumulate_task None s = s"
| "accumulate_task (Some edits) s = edit_sequence edits s"

definition accumulate_tasks where
  "accumulate_tasks tasks s = fold accumulate_task tasks s"

lemma tasks_frame:
  "state_frame s (accumulate_tasks tasks s)"
  unfolding accumulate_tasks_def
proof (induction tasks arbitrary: s)
  case Nil
  show ?case by (simp add: state_frame_def)
next
  case (Cons task tasks)
  have "state_frame s (accumulate_task task s)"
  proof (cases task)
    case None
    then show ?thesis by (simp add: state_frame_def)
  next
    case (Some edits)
    show ?thesis unfolding Some accumulate_task.simps by (rule edits_frame)
  qed
  with Cons.IH[of "accumulate_task task s"] show ?case by (simp add: state_frame_def)
qed

section \<open>Election completion and MasterService publication\<close>

definition executor_key where
  "executor_key s = \<lparr>rank_term = executor_term s, rank_version = executor_version s\<rparr>"

definition select_join_base where
  "select_join_base s alternative =
    (case alternative of None \<Rightarrow> s | Some a \<Rightarrow> if executor_key s < executor_key a then a else s)"

datatype builtin_persistence = Lucene_Backend | Async_Backend | Memory_Backend

text \<open>
  The three stock backends inherit the null getLatestStoredState result.
  JoinHelper attaches this result to the election-completion task.
  NodeJoinExecutor can choose a fresher alternate input when a backend
  provides one. For the stock backends all such task inputs are absent.
\<close>

fun latest_join_state where
  "latest_join_state Lucene_Backend = None"
| "latest_join_state Async_Backend = None"
| "latest_join_state Memory_Backend = None"

lemma builtin_join_seed:
  "select_join_base s (latest_join_state backend) = s"
  by (cases backend) (simp_all add: select_join_base_def)

datatype (dead 'body) builtin_executor =
    Read_Only
  | Unbatched "'body state_edit list"
  | Batched "'body state_edit list option list" "'body state_edit list"
  | Complete_Election builtin_persistence node nat "'body state_edit list"

definition elected_seed where
  "elected_seed backend n t s =
    (select_join_base s (latest_join_state backend))\<lparr>executor_term := t, executor_master := Some n\<rparr>"

fun execute_builtin where
  "execute_builtin Read_Only s = s"
| "execute_builtin (Unbatched edits) s = edit_sequence edits s"
| "execute_builtin (Batched tasks tail_edits) s = edit_sequence tail_edits (accumulate_tasks tasks s)"
| "execute_builtin (Complete_Election backend n t edits) s = edit_sequence edits (elected_seed backend n t s)"

lemma batched_frame:
  "state_frame s (edit_sequence tail_edits (accumulate_tasks tasks s))"
  by (rule state_frame_trans[OF tasks_frame edits_frame])

fun executor_seed where
  "executor_seed (Complete_Election backend n t edits) s = elected_seed backend n t s"
| "executor_seed _ s = s"

lemma builtin_result_frame:
  "state_frame (executor_seed task s) (execute_builtin task s)"
proof (cases task)
  case Read_Only
  then show ?thesis by (simp add: state_frame_def)
qed (simp_all only: execute_builtin.simps executor_seed.simps edits_frame batched_frame)

lemma builtin_executor_preserves_base:
  "executor_parent (execute_builtin task s) = executor_parent s"
  "executor_committed (execute_builtin task s) = executor_committed s"
  "executor_version (execute_builtin task s) = executor_version s"
  "executor_metadata_version (execute_builtin task s) = executor_metadata_version s"
proof -
  have frame: "state_frame (executor_seed task s) (execute_builtin task s)" by (rule builtin_result_frame)
  have "executor_parent (executor_seed task s) = executor_parent s \<and>
    executor_committed (executor_seed task s) = executor_committed s \<and>
    executor_version (executor_seed task s) = executor_version s \<and>
    executor_metadata_version (executor_seed task s) = executor_metadata_version s"
    by (cases task) (simp_all add: elected_seed_def builtin_join_seed)
  with state_frameD[OF frame]
  show "executor_parent (execute_builtin task s) = executor_parent s"
    "executor_committed (execute_builtin task s) = executor_committed s"
    "executor_version (execute_builtin task s) = executor_version s"
    "executor_metadata_version (execute_builtin task s) = executor_metadata_version s"
    by simp_all
qed

definition executable_task_for where
  "executable_task_for s n capture task \<longleftrightarrow>
    (case task of Read_Only \<Rightarrow> False
       | Complete_Election backend elected t edits \<Rightarrow>
           executor_master s = None \<and> elected = n \<and> executor_term s \<le> t \<and> t \<le> capture
       | _ \<Rightarrow> executor_master s = Some n \<and> executor_term s \<le> capture)"

lemma producer_term_and_owner:
  assumes "executable_task_for s n capture task"
  shows "executor_master (execute_builtin task s) = Some n"
    "executor_term (execute_builtin task s) \<le> capture"
proof -
  have frame: "state_frame (executor_seed task s) (execute_builtin task s)" by (rule builtin_result_frame)
  have "executor_master (executor_seed task s) = Some n \<and> executor_term (executor_seed task s) \<le> capture"
    using assms by (cases task) (simp_all add: executable_task_for_def elected_seed_def builtin_join_seed)
  with state_frameD[OF frame]
  show "executor_master (execute_builtin task s) = Some n"
    "executor_term (execute_builtin task s) \<le> capture" by simp_all
qed

lemma established_join_term:
  assumes "executor_term s = capture" "executor_term s \<le> task_term" "task_term \<le> capture"
  shows "task_term = executor_term s"
  using assms by (meson order_antisym)

text \<open>
  MasterService skips publication when the returned object is the same
  reference. For a changed object it copies the returned state and
  increments the version. The metadata version also increases if the
  metadata object changed. The booleans here model those reference tests.
  The version arithmetic is in the nonnegative, non-overflowing long
  range used by the surrounding refinement.
\<close>

definition patch_executor_versions where
  "patch_executor_versions changed metadata_changed s =
    (if changed then s\<lparr>executor_version := Suc (executor_version s),
      executor_metadata_version := (if metadata_changed then Suc (executor_metadata_version s)
        else executor_metadata_version s)\<rparr> else s)"

definition builtin_result where
  "builtin_result task metadata_changed s = patch_executor_versions True metadata_changed (execute_builtin task s)"

lemma builtin_publication_fields:
  assumes "executable_task_for s n capture task"
  shows "executor_parent (builtin_result task metadata_changed s) = executor_parent s"
    "executor_committed (builtin_result task metadata_changed s) = executor_committed s"
    "executor_master (builtin_result task metadata_changed s) = Some n"
    "executor_term (builtin_result task metadata_changed s) \<le> capture"
    "executor_version (builtin_result task metadata_changed s) = Suc (executor_version s)"
  using builtin_executor_preserves_base[of task s] producer_term_and_owner[OF assms]
  by (simp_all add: builtin_result_def patch_executor_versions_def)

section \<open>Discharging the producer contract\<close>

theorem admitted_builtin_executor_refines_publication:
  fixes metadata_changed :: bool
  assumes trace: "rtranclp (batch_step N E V C v n) start finish"
    and reach: "coordinator_reachable N E V C v versions start"
    and free: "batch_slot start n = None"
    and winner: "election_won (batch_node start n)"
    and task: "executable_task_for (executor_snapshot start n master mv body) n
      (current_term (batch_node start n)) program"
  defines "r \<equiv> builtin_result program metadata_changed (executor_snapshot start n master mv body)"
  assumes admission: "runtime_publication_admission finish n (executor_term r) (executor_version r)
      u (executor_accepted r) (executor_committed r)"
    and domain: "n \<in> N" "u \<in> V" "executor_accepted r \<subseteq> E"
  shows "executor_parent r = accepted_base (batch_node finish n)"
    "coordinator_enabled N E V C v finish (Begin_Publication n (executor_term r) (executor_version r)
      u (executor_accepted r) (executor_committed r) install)"
proof -
  have fields: "executor_parent r = accepted_base (batch_node start n)"
    "executor_committed r = local_committed (batch_node start n)"
    "executor_term r \<le> current_term (batch_node start n)"
    using builtin_publication_fields[OF task, of metadata_changed] unfolding r_def executor_snapshot_def by simp_all
  from admitted_batch_refines_begin[OF trace reach free winner fields(3) admission fields(1,2) refl domain]
  show "executor_parent r = accepted_base (batch_node finish n)"
    "coordinator_enabled N E V C v finish (Begin_Publication n (executor_term r) (executor_version r)
      u (executor_accepted r) (executor_committed r) install)"
    by simp_all
qed

theorem admitted_builtin_executor_has_tla_parent:
  fixes metadata_changed :: bool
  assumes trace: "rtranclp (batch_step N E V C v n) start finish"
    and reach: "coordinator_reachable N E V C v versions start"
    and free: "batch_slot start n = None"
    and winner: "election_won (batch_node start n)"
    and task: "executable_task_for (executor_snapshot start n master mv body) n
      (current_term (batch_node start n)) program"
  defines "r \<equiv> builtin_result program metadata_changed (executor_snapshot start n master mv body)"
  assumes admission: "runtime_publication_admission finish n (executor_term r) (executor_version r)
      u (executor_accepted r) (executor_committed r)"
    and domain: "n \<in> N" "u \<in> V" "executor_accepted r \<subseteq> E"
  shows "\<exists>a a'. tla_reachable N V C v versions a \<and> tla_reachable N V C v versions a' \<and>
    coordination finish = project_java E a \<and>
    coordination (coordinator_execute N E finish (Begin_Publication n (executor_term r) (executor_version r)
      u (executor_accepted r) (executor_committed r) install)) = project_java E a' \<and>
    (accepted_key (batch_node start n), executor_key r) \<in> descendant a'"
proof -
  have fields: "executor_committed r = local_committed (batch_node start n)"
    "executor_term r \<le> current_term (batch_node start n)"
    using builtin_publication_fields[OF task, of metadata_changed] unfolding r_def executor_snapshot_def by simp_all
  from admitted_batch_uses_captured_parent_in_tla[OF trace reach free winner fields(2) admission fields(1) domain]
  show ?thesis by (simp add: executor_key_def)
qed

lemma newer_alternate_can_change_base:
  assumes "executor_key s < executor_key a" "executor_parent a \<noteq> executor_parent s"
    "executor_committed a \<noteq> executor_committed s"
  shows "executor_parent (select_join_base s (Some a)) \<noteq> executor_parent s"
    "executor_committed (select_join_base s (Some a)) \<noteq> executor_committed s"
  using assms by (simp_all add: select_join_base_def)

end
