theory Mixed_Role_Durability
  imports Coordination_Persistence
begin

section \<open>Replaying the eligible evidence\<close>

abbreviation local_core where "local_core s n \<equiv> java_nodes (coordination s) n"

definition vote_evidence where
  "vote_evidence s H \<longleftrightarrow>
    (\<forall>c n. n \<in> join_votes (local_core s c) \<longrightarrow>
      (\<exists>k. Sent_Vote c (Vote n c (current_term (local_core s c)) k) \<in> H \<and> k \<le> accepted_key (local_core s c))) \<and>
    (\<forall>c n. n \<in> publish_votes (local_core s c) \<longrightarrow>
      election_won (local_core s c) \<and> Routed_Response n c (published_key (local_core s c)) \<in> H)"

lemma vote_evidence_mono:
  "vote_evidence s H \<Longrightarrow> H \<subseteq> H' \<Longrightarrow> vote_evidence s H'"
  unfolding vote_evidence_def by blast

lemma java_vote_evidence:
  assumes old: "vote_evidence s H"
    and checks: "java_checks (coordination s) a"
    and reach: "java_reachable N E V C v versions (coordination s)"
    and inputs: "dispatch_input N E V C v s a"
    and join_packet: "\<And>n c t k. a = Java_Join n c t k \<Longrightarrow> Sent_Vote c (Vote n c t k) \<in> H"
    and ack_packet: "\<And>n c k. a = Java_Response n c k \<Longrightarrow> Routed_Response n c k \<in> H"
  shows "vote_evidence (coordinator_execute N E s (Dispatch a enter)) H"
proof (cases a)
  case (Java_Bootstrap n k u D F)
  then have key: "k = accepted_key (local_core s n)" using inputs by (simp add: Let_def)
  show ?thesis using old key by (simp add: Java_Bootstrap vote_evidence_def put_lifecycle_def java_put_def)
next
  case (Java_Join n c t k)
  have keep: "election_won (local_core s c) \<Longrightarrow>
      election_won (java_nodes (java_execute N E (coordination s) (Java_Join n c t k)) c)"
    by (rule join_keeps_election[OF reach])
  from checks join_packet[OF Java_Join] old keep show ?thesis
    by (auto simp: Java_Join vote_evidence_def put_lifecycle_def java_put_def add_vote_def Let_def
      simp del: split_paired_Ex
      split: if_splits)
next
  case (Java_Publish n p u)
  have newer: "accepted_key (local_core s n) < request_key p"
    by (rule checked_publish_is_newer[OF reach]) (use checks Java_Publish in simp)
  have advanced: "\<exists>k. Sent_Vote n (Vote i n (current_term (local_core s n)) k) \<in> H \<and> k \<le> request_key p"
    if "i \<in> join_votes (local_core s n)" for i
  proof -
    from old that obtain k where "Sent_Vote n (Vote i n (current_term (local_core s n)) k) \<in> H"
      and "k \<le> accepted_key (local_core s n)" unfolding vote_evidence_def by blast
    then show ?thesis using less_imp_le[OF le_less_trans[OF _ newer], of k] by blast
  qed
  from old advanced show ?thesis
    by (auto simp: Java_Publish vote_evidence_def put_lifecycle_def java_put_def
      simp del: split_paired_Ex less_eq_prod_simp)
next
  case (Java_Response n c k)
  with ack_packet[OF Java_Response] checks old show ?thesis
    by (auto simp: vote_evidence_def put_lifecycle_def java_put_def add_vote_def Let_def)
qed (use old in \<open>auto simp: vote_evidence_def put_lifecycle_def java_put_def java_reset_def Let_def\<close>)

lemma non_dispatch_vote_evidence:
  assumes "vote_evidence s H" "\<And>a enter. event \<noteq> Dispatch a enter"
  shows "vote_evidence (coordinator_execute N E s event) H"
  using assms by (cases event)
    (auto simp: vote_evidence_def put_lifecycle_def java_put_def Let_def)

lemma transport_history_grows:
  assumes "transport_step N E V C v s H s' H'"
  shows "H \<subseteq> H'"
  using assms
proof cases
  case (publish_callback c i n p u actual k opt)
  then show ?thesis by (cases opt) auto
qed (auto split: if_splits)

lemma transport_step_vote_evidence:
  assumes step: "transport_step N E V C v s H s' H'"
    and run: "transport_reachable N E V C v versions s H"
    and old: "vote_evidence s H"
  shows "vote_evidence s' H'"
proof -
  have c: "coordinator_reachable N E V C v versions s"
    and support: "msg \<in> H \<Longrightarrow> supported N E s msg" for msg
    using transport_invariants[OF run] by blast+
  have j: "java_reachable N E V C v versions (coordination s)" using coordinator_invariants[OF c] by blast
  have dispatch: "vote_evidence (coordinator_execute N E s (Dispatch a enter)) H"
    if "java_checks (coordination s) a" "dispatch_input N E V C v s a"
      "\<And>n c t k. a = Java_Join n c t k \<Longrightarrow> Sent_Vote c (Vote n c t k) \<in> H"
      "\<And>n c k. a = Java_Response n c k \<Longrightarrow> Routed_Response n c k \<in> H" for a enter
    by (rule java_vote_evidence[OF old that(1) j that(2-4)])
  have preserved: "vote_evidence s' H" using step
  proof cases
    case (control a)
    have "vote_evidence (coordinator_execute N E s a) H"
    proof (cases a)
      case (Dispatch action enter)
      have enabled: "coordinator_enabled N E V C v s (Dispatch action enter)"
        using control(4) Dispatch by simp
      have control_action: "local_event (Dispatch action enter)" using control(3) Dispatch by simp
      show ?thesis unfolding Dispatch
        by (rule dispatch) (use enabled control_action in auto)
    qed (use old in \<open>auto simp: vote_evidence_def put_lifecycle_def java_put_def Let_def\<close>)
    then show ?thesis unfolding control(1) .
  next
    case (start_join n c t)
    show ?thesis unfolding start_join(1)
      by (rule dispatch) (use start_join(3) in auto)
  next
    case (receive_vote d n c t k enter)
    from support[OF receive_vote(3)] have "d = c" "Join_Msg n d t k \<in> journal s" by auto
    with receive_vote(3,4) show ?thesis unfolding receive_vote(1) by (intro dispatch) auto
  next
    case (begin_publication c t w u D F)
    show ?thesis unfolding begin_publication(1)
      by (rule non_dispatch_vote_evidence[OF old]) simp
  next
    case (receive_publish c i n p u wire decoded opt)
    have decoded: "decoded = p" by (rule decode_publication_correct[OF receive_publish(5,6)])
    from support[OF receive_publish(3)] decoded
    have allowed: "dispatch_input N E V C v s (Java_Publish n decoded u)" by (simp add: publish_from_def)
    show ?thesis unfolding receive_publish(1)
      by (rule dispatch[OF receive_publish(7) allowed]) simp_all
  next
    case (count_response n c k)
    show ?thesis unfolding count_response(1)
      by (rule dispatch[OF count_response(4)]) (use count_response(3) support[OF count_response(3)] in auto)
  next
    case (receive_commit c n k)
    show ?thesis unfolding receive_commit(1)
      by (rule dispatch[OF receive_commit(4)]) (use support[OF receive_commit(3)] in auto)
  qed (use old in simp_all)
  show ?thesis by (rule vote_evidence_mono[OF preserved transport_history_grows[OF step]])
qed

lemma eligible_vote_evidence:
  "transport_reachable N E V C v versions s H \<Longrightarrow> vote_evidence s H"
proof (induction rule: transport_reachable.induct)
  case init
  then show ?case by (simp add: vote_evidence_def coordinator_initial_def java_initial_def)
next
  case step
  then show ?case by (blast intro: transport_step_vote_evidence)
qed

lemma transport_java_reachable:
  assumes "transport_reachable N E V C v versions s H"
  shows "java_reachable N E V C v versions (coordination s)"
  by (rule conjunct1[OF coordinator_invariants[OF conjunct1[OF transport_invariants[OF assms]]]])

lemma quorum_needs_vote:
  assumes run: "transport_reachable N E V C v versions s H"
    and quorum: "java_has_quorum (local_committed (local_core s c)) Q"
  shows "Q \<noteq> {}"
proof -
  interpret default_strategy N E C by (rule java_reachable_default_strategy[OF transport_java_reachable[OF run]])
  have sub: "local_committed (local_core s c) \<subseteq> N"
    using past_configs[OF conjunct1[OF transport_invariants[OF run]], of c] elig by blast
  show ?thesis
  proof
    assume "Q = {}"
    with quorum show False by (simp add: java_quorum_eq[OF finite_nodes int_bound sub] quorum_def majority_def)
  qed
qed

text \<open>
  An ineligible join can still make the core recheck its quorum predicate.
  An ineligible response can also observe a quorum that already exists.
  Replaying an eligible member of that quorum produces the same core
  effect, including leader entry or a commit notification.
\<close>

lemma ineligible_join_replay:
  assumes run: "transport_reachable N E V C v versions s H"
    and outsider: "n \<notin> E"
    and checks: "java_checks (coordination s) (Java_Join n c t k)"
    and entry: "enter \<Longrightarrow> leader_entry N E (coordination s) (Java_Join n c t k)"
  defines "after \<equiv> coordinator_execute N E s (Dispatch (Java_Join n c t k) enter)"
  shows "after = s \<or> transport_step N E V C v s H after H"
proof (cases "java_election (local_core s c) (join_votes (local_core s c))")
  case False
  have jr: "java_reachable N E V C v versions (coordination s)" by (rule transport_java_reachable[OF run])
  have unwon: "\<not> election_won (local_core s c)" using join_keeps_election[OF jr, of c n t k] False outsider
    by (auto simp: java_put_def Let_def add_vote_def)
  have no_entry: "\<not> enter" using False entry outsider by (auto simp: java_put_def Let_def add_vote_def)
  have unchanged: "(local_core s c)\<lparr>election_won := False\<rparr> = local_core s c"
    using unwon by (cases "local_core s c") auto
  show ?thesis using False outsider no_entry unchanged
    by (simp add: after_def java_put_def Let_def add_vote_def put_lifecycle_def)
next
  case True
  then have "java_has_quorum (local_committed (local_core s c)) (join_votes (local_core s c))"
    by (simp add: java_election_def)
  from quorum_needs_vote[OF run this] obtain i where voter: "i \<in> join_votes (local_core s c)" by blast
  have "t = current_term (local_core s c)" using checks by (simp add: Let_def)
  with eligible_vote_evidence[OF run] voter obtain r where
    packet: "Sent_Vote c (Vote i c t r) \<in> H" and fresh: "r \<le> accepted_key (local_core s c)"
    unfolding vote_evidence_def by blast
  have add_i: "add_vote E i (join_votes (local_core s c)) = join_votes (local_core s c)"
    using voter by (simp add: add_vote_def insert_absorb)
  have add_n: "add_vote E n (join_votes (local_core s c)) = join_votes (local_core s c)"
    using outsider by (simp add: add_vote_def)
  have same: "java_execute N E (coordination s) (Java_Join i c t r) =
    java_execute N E (coordination s) (Java_Join n c t k)"
    by (simp add: Let_def add_i add_n)
  have "transport_step N E V C v s H (coordinator_execute N E s (Dispatch (Java_Join i c t r) enter)) H"
    by (rule transport_step.receive_vote[OF packet])
      (use checks fresh entry same in \<open>auto simp only: java_checks.simps leader_entry.simps Let_def\<close>)
  then have "transport_step N E V C v s H after H"
    using same by (simp only: after_def coordinator_execute.simps receiver.simps lifecycle_after_dispatch.simps)
  then show ?thesis by (rule disjI2)
qed

lemma ineligible_response_replay:
  assumes run: "transport_reachable N E V C v versions s H"
    and outsider: "n \<notin> E"
    and checks: "java_checks (coordination s) (Java_Response n c k)"
  defines "after \<equiv> coordinator_execute N E s (Dispatch (Java_Response n c k) False)"
  defines "out \<equiv> if response_quorum E s n c then insert (Returned_Commit c k) H else H"
  shows "(after = s \<and> out = H) \<or> transport_step N E V C v s H after out"
proof (cases "response_quorum E s n c")
  case False
  with outsider show ?thesis
    by (simp add: after_def out_def response_quorum_def java_put_def Let_def add_vote_def put_lifecycle_def)
next
  case True
  then have "java_has_quorum (local_committed (local_core s c)) (publish_votes (local_core s c))"
    using outsider by (simp add: response_quorum_def java_publication_def Let_def add_vote_def)
  from quorum_needs_vote[OF run this] obtain i where voter: "i \<in> publish_votes (local_core s c)" by blast
  have "k = published_key (local_core s c)" using checks by (simp add: Let_def)
  with eligible_vote_evidence[OF run] voter have packet: "Routed_Response i c k \<in> H"
    unfolding vote_evidence_def by blast
  have i_checks: "java_checks (coordination s) (Java_Response i c k)" using checks by simp
  have add_i: "add_vote E i (publish_votes (local_core s c)) = publish_votes (local_core s c)"
    using voter by (simp add: add_vote_def insert_absorb)
  have add_n: "add_vote E n (publish_votes (local_core s c)) = publish_votes (local_core s c)"
    using outsider by (simp add: add_vote_def)
  have state: "coordinator_execute N E s (Dispatch (Java_Response i c k) False) = after"
    by (simp add: after_def Let_def add_i add_n)
  have same_output: "(if response_quorum E s i c then insert (Returned_Commit c k) H else H) = out"
    by (simp add: out_def response_quorum_def Let_def add_i add_n)
  from transport_step.count_response[OF packet i_checks, where N=N and E=E and V=V and C=C and v=v]
  show ?thesis unfolding state same_output by blast
qed


section \<open>Non-master recovery\<close>

datatype observer_backend = Async_Observer | Memory_Observer

record 'v observer =
  obs_live :: "'v local_node"
  obs_saved :: disk_image
  term_queued :: bool
  state_queued :: bool
  worker :: "disk_write list"

datatype observer_packet = Observer_Vote node node nat rank | Observer_Ack node node rank

definition empty_observer_node where
  "empty_observer_node v = java_nodes (java_initial v (\<lambda>_. 0)) 0"

definition observer_initial where
  "observer_initial v = \<lparr>obs_live = empty_observer_node v, obs_saved = disk_projection (empty_observer_node v),
    term_queued = False, state_queued = False, worker = []\<rparr>"

definition observer_view where
  "observer_view x = \<lparr>java_nodes = (\<lambda>_. obs_live x), java_journal = {}\<rparr>"

fun observer_call where
  "observer_call N H n (Java_Start_Join i c t) = (i = n \<and> c \<in> N)"
| "observer_call N H n (Java_Publish i p u) = (i = n \<and> Registered_State p u \<in> H)"
| "observer_call N H n (Java_Commit i c k) = (i = n \<and> Returned_Commit c k \<in> H)"
| "observer_call N H n _ = False"

fun observer_output where
  "observer_output x (Java_Start_Join n c t) = {Observer_Vote n c t (accepted_key (obs_live x))}"
| "observer_output x (Java_Publish n p u) = {Observer_Ack n (pub_owner p) (request_key p)}"
| "observer_output x _ = {}"

definition observer_execute where
  "observer_execute N E backend n x a flush_commit =
    (let y = java_nodes (java_execute N E (observer_view x) a) n in
      x\<lparr>obs_live := y,
        term_queued := (term_queued x \<or> (backend = Async_Observer \<and> (\<exists>t. method_write a = Some (Term_Write t)))),
        state_queued := (state_queued x \<or> (backend = Async_Observer \<and>
          ((\<exists>k D F. method_write a = Some (State_Write k D F)) \<or>
            (method_write a = Some Mark_Committed \<and>
              (disk_projection y \<noteq> disk_projection (obs_live x) \<or> flush_commit)))))\<rparr>)"

definition observer_snapshot where
  "observer_snapshot marker x =
    (if term_queued x then [Term_Write (current_term (obs_live x))] else []) @
    (if state_queued x then [State_Write (accepted_key (obs_live x)) {marker} {marker}] else [])"

definition async_recovered where
  "async_recovered v J d = \<lparr>obs_live = restore_node d (replay_value v J (disk_key d)), obs_saved = d,
    term_queued = False, state_queued = False, worker = []\<rparr>"

definition observer_disk_at_cut where
  "observer_disk_at_cut x completed =
    (case worker x of [] \<Rightarrow> (\<lambda>_. obs_saved x)
      | op # rest \<Rightarrow> complete_paths completed (\<lambda>_. obs_saved x) (write_effect op (obs_saved x)))"

text \<open>
  Async setters return after updating memory and queueing flags. One worker
  snapshots both flags, and writes the captured term before the captured
  accepted state when both are pending. New calls may queue another batch.
  An exception before commit may discard the remainder of a captured batch.
  Interruption during a commit allows an old or new copy at each path.
  Restart reloads the selected copy and clears the queue and the worker.
\<close>

inductive observer_step for N E v J H marker paths backend n where
  call:
    "observer_call N H n a \<Longrightarrow> java_checks (observer_view x) a \<Longrightarrow>
     observer_step N E v J H marker paths backend n x G
       (observer_execute N E backend n x a flush_commit) (G \<union> observer_output x a)"
| capture:
    "backend = Async_Observer \<Longrightarrow> worker x = [] \<Longrightarrow> observer_snapshot marker x \<noteq> [] \<Longrightarrow>
     observer_step N E v J H marker paths backend n x G
       (x\<lparr>term_queued := False, state_queued := False, worker := observer_snapshot marker x\<rparr>) G"
| write_next:
    "backend = Async_Observer \<Longrightarrow> worker x = op # rest \<Longrightarrow>
     observer_step N E v J H marker paths backend n x G
       (x\<lparr>obs_saved := write_effect op (obs_saved x), worker := rest\<rparr>) G"
| abandon_batch:
    "backend = Async_Observer \<Longrightarrow> worker x \<noteq> [] \<Longrightarrow>
     observer_step N E v J H marker paths backend n x G (x\<lparr>worker := []\<rparr>) G"
| async_restart:
    "backend = Async_Observer \<Longrightarrow> available \<subseteq> paths \<Longrightarrow>
     recovers (images_for available (observer_disk_at_cut x completed)) d \<Longrightarrow>
     observer_step N E v J H marker paths backend n x G (async_recovered v J d) G"
| memory_restart:
    "backend = Memory_Observer \<Longrightarrow>
     observer_step N E v J H marker paths backend n x G (observer_initial v) G"

lemma snapshot_term_first:
  "term_queued x \<Longrightarrow> state_queued x \<Longrightarrow>
    observer_snapshot marker x =
      [Term_Write (current_term (obs_live x)), State_Write (accepted_key (obs_live x)) {marker} {marker}]"
  by (simp add: observer_snapshot_def)

lemma observer_crash_images:
  assumes "recovers (images_for available (observer_disk_at_cut x completed)) d"
  shows "d = obs_saved x \<or> (\<exists>op rest. worker x = op # rest \<and> d = write_effect op (obs_saved x))"
proof (cases "worker x")
  case Nil
  then show ?thesis using assms by (auto simp: observer_disk_at_cut_def recovers_def images_for_def)
next
  case (Cons op rest)
  then have "recovers (images_for available (complete_paths completed (\<lambda>_. obs_saved x)
      (write_effect op (obs_saved x)))) d" using assms by (simp add: observer_disk_at_cut_def)
  from recover_interrupted_write[OF refl this] Cons show ?thesis by blast
qed

section \<open>Composition with the synchronous voting nodes\<close>

text \<open>
  N contains the synchronous participant IDs and any inert bootstrap IDs.
  Observer IDs are disjoint from N, and therefore from the eligible IDs E.
  Publication targets outside N receive the registered state and can apply
  commit notifications. Those deliveries do not change the voting state.
  The observer packet history retains old messages across restart.
\<close>

record ('v, 'p) mixed_cluster =
  voting :: "'v coordinator_state"
  voting_traffic :: "'v transport_item set"
  voting_disks :: "node \<Rightarrow> 'p \<Rightarrow> disk_image"
  observers :: "node \<Rightarrow> 'v observer"
  observer_traffic :: "observer_packet set"

definition mixed_initial where
  "mixed_initial v versions = \<lparr>voting = coordinator_initial v versions, voting_traffic = {},
    voting_disks = (\<lambda>n p. node_disk (coordinator_initial v versions) n),
    observers = (\<lambda>_. observer_initial v), observer_traffic = {}\<rparr>"

inductive mixed_step for N E V C v marker paths roles where
  voting_transient:
    "transport_step N E V C v (voting s) (voting_traffic s) u H \<Longrightarrow>
     node_disk u = node_disk (voting s) \<Longrightarrow>
     mixed_step N E V C v marker paths roles s (s\<lparr>voting := u, voting_traffic := H\<rparr>)"
| voting_write:
    "transport_step N E V C v (voting s) (voting_traffic s) u H \<Longrightarrow>
     node_disk u = (node_disk (voting s))(n := write_effect op (node_disk (voting s) n)) \<Longrightarrow>
     mixed_step N E V C v marker paths roles s (s\<lparr>voting := u, voting_traffic := H,
       voting_disks := install_write (voting_disks s) n (paths n)
         (writer_commit (writer_mode retry (node_disk (voting s) n) op)
           (node_disk (voting s) n) (write_effect op (node_disk (voting s) n)))\<rparr>)"
| voting_interrupted:
    "transport_step N E V C v (voting s) (voting_traffic s) u H \<Longrightarrow>
     n \<in> N \<Longrightarrow> available \<subseteq> paths n \<Longrightarrow>
     node_disk u = (node_disk (voting s))(n := write_effect op (node_disk (voting s) n)) \<Longrightarrow>
     recovers (images_for available
       (install_write (voting_disks s) n completed (write_effect op (node_disk (voting s) n)) n)) d \<Longrightarrow>
     mixed_step N E V C v marker paths roles s
       (s\<lparr>voting := coordinator_execute N E (if d = node_disk (voting s) n then voting s else u)
          (Dispatch (Java_Restart n) False),
         voting_traffic := (if d = node_disk (voting s) n then voting_traffic s else H),
         voting_disks := install_write (voting_disks s) n (paths n) d\<rparr>)"
| observer:
    "roles n = Some backend \<Longrightarrow>
     observer_step N E v (journal (voting s)) (voting_traffic s) marker (paths n) backend n
       (observers s n) (observer_traffic s) x G \<Longrightarrow>
     mixed_step N E V C v marker paths roles s (s\<lparr>observers := (observers s)(n := x), observer_traffic := G\<rparr>)"
| observer_join:
    "roles n \<noteq> None \<Longrightarrow> c \<in> N \<Longrightarrow> Observer_Vote n c t k \<in> observer_traffic s \<Longrightarrow>
     java_checks (coordination (voting s)) (Java_Join n c t k) \<Longrightarrow>
     (enter \<Longrightarrow> leader_entry N E (coordination (voting s)) (Java_Join n c t k)) \<Longrightarrow>
     mixed_step N E V C v marker paths roles s
       (s\<lparr>voting := coordinator_execute N E (voting s) (Dispatch (Java_Join n c t k) enter)\<rparr>)"
| observer_response:
    "roles n \<noteq> None \<Longrightarrow> c \<in> N \<Longrightarrow> Observer_Ack n c k \<in> observer_traffic s \<Longrightarrow>
     java_checks (coordination (voting s)) (Java_Response n c k) \<Longrightarrow>
     mixed_step N E V C v marker paths roles s
       (s\<lparr>voting := coordinator_execute N E (voting s) (Dispatch (Java_Response n c k) False),
        voting_traffic := (if response_quorum E (voting s) n c then insert (Returned_Commit c k) (voting_traffic s)
          else voting_traffic s)\<rparr>)"

lemma mixed_preserves_voting_execution:
  assumes separated: "\<And>n. roles n \<noteq> None \<Longrightarrow> n \<notin> N"
    and step: "mixed_step N E V C v marker paths roles s s'"
    and run: "durable_execution N E V C v versions paths (voting s) (voting_traffic s) (voting_disks s)"
  shows "durable_execution N E V C v versions paths (voting s') (voting_traffic s') (voting_disks s')"
proof -
  have reach: "transport_reachable N E V C v versions (voting s) (voting_traffic s)"
    using durable_execution_invariants[OF run] by blast
  have subset: "E \<subseteq> N"
  proof -
    have c: "coordinator_reachable N E V C v versions (voting s)" using transport_invariants[OF reach] by blast
    have j: "java_reachable N E V C v versions (coordination (voting s))"
      using coordinator_invariants[OF c] by blast
    from java_reachable_default_strategy[OF j] show ?thesis by (rule default_strategy.elig)
  qed
  have ineligible: "n \<notin> E" if "roles n \<noteq> None" for n using subset separated[OF that] by blast
  show ?thesis using step
  proof cases
    case voting_interrupted
    from durable_execution.recovered[OF run voting_interrupted(2-6)]
    show ?thesis unfolding voting_interrupted(1) by simp
  next
    case (observer_join n c t k enter)
    from ineligible_join_replay[OF reach ineligible[OF observer_join(2)] observer_join(5,6)]
    have replay: "coordinator_execute N E (voting s) (Dispatch (Java_Join n c t k) enter) = voting s \<or>
      transport_step N E V C v (voting s) (voting_traffic s)
        (coordinator_execute N E (voting s) (Dispatch (Java_Join n c t k) enter)) (voting_traffic s)" .
    have disk: "node_disk (coordinator_execute N E (voting s) (Dispatch (Java_Join n c t k) enter)) = node_disk (voting s)"
      by (rule dispatch_keeps_disk) simp
    from observer_join(1) replay disk run show ?thesis
      by (auto simp del: coordinator_execute.simps intro: durable_execution.transient)
  next
    case (observer_response n c k)
    let ?a = "coordinator_execute N E (voting s) (Dispatch (Java_Response n c k) False)"
    let ?H = "if response_quorum E (voting s) n c then insert (Returned_Commit c k) (voting_traffic s) else voting_traffic s"
    have replay: "(?a = voting s \<and> ?H = voting_traffic s) \<or> transport_step N E V C v (voting s) (voting_traffic s) ?a ?H"
      by (rule ineligible_response_replay[OF reach ineligible[OF observer_response(2)] observer_response(5)])
    have disk: "node_disk ?a = node_disk (voting s)" by (rule dispatch_keeps_disk) simp
    from observer_response(1) replay disk run show ?thesis
      by (auto simp del: coordinator_execute.simps intro: durable_execution.transient)
  qed (use run in \<open>auto simp del: coordinator_execute.simps
    intro: durable_execution.transient durable_execution.written\<close>)
qed

inductive mixed_reachable for N E V C v versions marker paths roles where
  init:
    "default_strategy N E C \<Longrightarrow> v \<in> V \<Longrightarrow> (\<And>n. n \<in> N \<Longrightarrow> paths n \<noteq> {}) \<Longrightarrow>
     mixed_reachable N E V C v versions marker paths roles (mixed_initial v versions)"
| step:
    "mixed_reachable N E V C v versions marker paths roles s \<Longrightarrow>
     mixed_step N E V C v marker paths roles s s' \<Longrightarrow> mixed_reachable N E V C v versions marker paths roles s'"

theorem mixed_role_durability:
  assumes "\<And>n. roles n \<noteq> None \<Longrightarrow> n \<notin> N"
    "mixed_reachable N E V C v versions marker paths roles s"
  shows "durable_execution N E V C v versions paths (voting s) (voting_traffic s) (voting_disks s)"
  using assms(2)
proof induction
  case init
  then show ?case by (auto simp: mixed_initial_def intro: durable_execution.init)
next
  case step
  then show ?case by (blast intro: mixed_preserves_voting_execution[OF assms(1)])
qed

theorem mixed_role_refines_tla:
  assumes "\<And>n. roles n \<noteq> None \<Longrightarrow> n \<notin> N"
    "mixed_reachable N E V C v versions marker paths roles s"
  shows "\<exists>t. tla_reachable N V C v versions t \<and> configurations_ok E t \<and> coordination (voting s) = project_java E t"
  by (rule durable_execution_refines_tla[OF mixed_role_durability[OF assms]])

end
