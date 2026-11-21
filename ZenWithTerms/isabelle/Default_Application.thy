theory Default_Application
  imports Commit_Application Stock_Coordination_Execution
begin

section \<open>Voting-node handler boundaries\<close>

abbreviation voting_node where
  "voting_node s n \<equiv> java_nodes (coordination s) n"

definition application_matches_voter where
  "application_matches_voter a s n \<longleftrightarrow>
    app_term a = current_term (voting_node s n) \<and> app_accepted a = accepted_key (voting_node s n)"

definition offer_commit where
  "offer_commit n c k a = (if n = c
     then a\<lparr>offered := Some k, self_ready := insert (Apply_Request c k) (self_ready a)\<rparr>
     else a\<lparr>offered := Some k, queued_applications := insert (Apply_Request c k) (queued_applications a)\<rparr>)"

fun after_voting_call where
  "after_voting_call n (Java_Start_Join i c t) a =
    (if n = i then a\<lparr>app_term := t\<rparr> else a)"
| "after_voting_call n (Java_Publish i p u) a =
    (if n = i then a\<lparr>app_accepted := request_key p\<rparr> else a)"
| "after_voting_call n (Java_Commit i c k) a =
    (if n = i then offer_commit n c k a else a)"
| "after_voting_call n (Java_Restart i) a =
    (if n = i then restart_application a (app_term a) (app_accepted a) else a)"
| "after_voting_call n _ a = a"

fun voter_application_input where
  "voter_application_input H (Java_Publish n p u) =
    (Registered_State p u \<in> H \<and> (\<exists>i. Publish_RPC (pub_owner p) i n p u \<in> H))"
| "voter_application_input H (Java_Commit n c k) = (Sent_Commit c n k \<in> H \<and> Returned_Commit c k \<in> H)"
| "voter_application_input H _ = True"

fun application_input where
  "application_input H (Java_Publish n p u) = (Registered_State p u \<in> H)"
| "application_input H (Java_Commit n c k) = (Returned_Commit c k \<in> H)"
| "application_input H _ = True"

fun after_voting_event where
  "after_voting_event n (Dispatch call enter) a = after_voting_call n call a"
| "after_voting_event n _ a = a"

fun voter_event_input where
  "voter_event_input H (Dispatch call enter) = voter_application_input H call"
| "voter_event_input H _ = True"

lemma voting_call_matches:
  assumes match: "application_matches_voter a s n"
    and bootstrap: "\<And>i k u D F. call = Java_Bootstrap i k u D F \<Longrightarrow> k = accepted_key (voting_node s i)"
  shows "application_matches_voter (after_voting_call n call a) (coordinator_execute N E s (Dispatch call enter)) n"
  using assms by (cases call)
    (auto simp: application_matches_voter_def java_put_def java_reset_def put_lifecycle_def
      offer_commit_def restart_application_def Let_def)

lemma voting_call_refines_application:
  assumes match: "application_matches_voter a s n"
    and checks: "java_checks (coordination s) call"
    and input: "application_input H call"
  shows "after_voting_call n call a = a \<or> application_step n H a (after_voting_call n call a)"
  using checks input match
proof (cases call)
  case (Java_Publish i p u)
  show ?thesis
  proof (cases "n = i")
    case True
    with Java_Publish assms have packet: "Registered_State p u \<in> H"
      and current: "pub_term p = app_term a"
      and fresh: "rank_term (app_accepted a) = pub_term p \<longrightarrow> rank_version (app_accepted a) < pub_version p"
      by (auto simp: application_matches_voter_def Let_def)
    from Java_Publish True application_step.accept[OF packet current fresh, of n] show ?thesis by simp
  next
    case False
    with Java_Publish show ?thesis by simp
  qed
next
  case (Java_Commit i c k)
  have returned: "Returned_Commit c k \<in> H" using Java_Commit input by simp
  have checked: "rank_term k = app_term a" "k = app_accepted a" if "n = i"
    using Java_Commit assms that by (auto simp: application_matches_voter_def Let_def)
  show ?thesis
  proof (cases "n = i")
    case False
    with Java_Commit show ?thesis by simp
  next
    case True
    note checked = checked[OF True]
    show ?thesis
    proof (cases "n = c")
      case False
      from application_step.handle_remote[OF not_sym[OF False] returned checked] False True Java_Commit show ?thesis
        by (simp add: offer_commit_def)
    next
      case True
      with returned have "Returned_Commit n k \<in> H" by simp
      from application_step.handle_self[OF this checked] True \<open>n = i\<close> Java_Commit show ?thesis
        by (simp add: offer_commit_def)
    qed
  qed
qed (auto simp: application_matches_voter_def intro: application_step.advance_term application_step.restart)

lemma voting_event_projects:
  assumes match: "application_matches_voter a s n"
    and enabled: "coordinator_enabled N E V C v s ev"
    and input: "voter_event_input H ev"
  shows "application_matches_voter (after_voting_event n ev a) (coordinator_execute N E s ev) n \<and>
    (after_voting_event n ev a = a \<or> application_step n H a (after_voting_event n ev a))"
  using assms
proof (cases ev)
  case (Dispatch call enter)
  with enabled have checks: "java_checks (coordination s) call" and bootstrap:
    "\<And>i k u D F. call = Java_Bootstrap i k u D F \<Longrightarrow> k = accepted_key (voting_node s i)"
    by (auto simp: Let_def)
  have local_match: "application_matches_voter (after_voting_event n ev a) (coordinator_execute N E s ev) n"
    using voting_call_matches[where call=call and N=N and E=E and enter=enter, OF match bootstrap] Dispatch by simp
  have supported: "application_input H call" using input Dispatch by (cases call) auto
  have "after_voting_event n ev a = a \<or> application_step n H a (after_voting_event n ev a)"
    using voting_call_refines_application[OF match checks supported] Dispatch by simp
  with local_match show ?thesis by blast
qed (auto simp: application_matches_voter_def put_lifecycle_def java_put_def Let_def)

section \<open>Publication and applier callbacks\<close>

text \<open>
  The worker rules project the concrete queue, live supplier, application
  result, and response send. A self RPC reply only permits the publication
  completion callback to queue local work. Remote work is queued by the
  commit handler itself. The successful response event is recorded in the
  process that applied the state; the publication target can consume its
  evidence later. An already installed sample also completes successfully.
\<close>

inductive default_worker_step for n local_pub where
  queue_local:
    "local_pub = Some (apply_key q) \<Longrightarrow> apply_source q = n \<Longrightarrow> q \<in> self_ready a \<Longrightarrow>
     default_worker_step n local_pub a (a\<lparr>self_ready := self_ready a - {q},
       queued_applications := insert q (queued_applications a)\<rparr>)"
| sample:
    "q \<in> queued_applications a \<Longrightarrow> running_application a = None \<Longrightarrow> offered a = Some k \<Longrightarrow>
     default_worker_step n local_pub a (a\<lparr>queued_applications := queued_applications a - {q},
       running_application := Some (q,k)\<rparr>)"
| apply_ok:
    "running_application a = Some (q,k) \<Longrightarrow>
     default_worker_step n local_pub a (a\<lparr>running_application := None, installed := Some k,
       application_successes := insert (incarnation a,q,k) (application_successes a)\<rparr>)"
| fail:
    "running_application a = Some (q,k) \<Longrightarrow>
     default_worker_step n local_pub a (a\<lparr>running_application := None,
       installed := (if stored then Some k else installed a)\<rparr>)"
| background:
    "running_application a = None \<Longrightarrow> offered a = Some k \<Longrightarrow>
     default_worker_step n local_pub a (a\<lparr>installed := Some k\<rparr>)"
| respond:
    "(incarnation a,q,k) \<in> application_successes a \<Longrightarrow>
     default_worker_step n local_pub a (a\<lparr>node_acknowledgements := insert (incarnation a,q,k) (node_acknowledgements a)\<rparr>)"

lemma default_worker_refines:
  assumes "default_worker_step n local_pub a b"
  shows "application_step n H a b" "applier_only a b"
proof -
  from assms show "application_step n H a b"
  proof cases
    case (fail q k stored)
    show ?thesis unfolding fail(1)
      by (rule application_step.apply_failure[OF fail(2)])
  qed (auto intro: application_step.queue_self application_step.read_supplier application_step.apply_success
    application_step.install_background application_step.observe_ack)
  from assms show "applier_only a b" by cases (auto simp: applier_only_def)
qed

section \<open>Transport origin and mixed-role application effects\<close>

definition application_origins where
  "application_origins H \<longleftrightarrow>
   (\<forall>c i n p u. Publish_RPC c i n p u \<in> H \<longrightarrow> c = pub_owner p \<and> Registered_State p u \<in> H) \<and>
   (\<forall>c n k. Sent_Commit c n k \<in> H \<longrightarrow> Returned_Commit c k \<in> H)"

lemma transport_application_origins:
  assumes "transport_reachable N E V C v versions s H"
  shows "application_origins H"
  using assms
proof induction
  case init
  show ?case by (simp add: application_origins_def)
next
  case (step s H s' H')
  from step.hyps(2) step.IH show ?case
  proof (cases rule: transport_step.cases)
    case (publish_callback c i n p u actual k opt)
    then show ?thesis using step.IH by (cases opt) (auto simp: application_origins_def)
  qed (auto simp: application_origins_def split: if_splits)
qed

datatype 'v voting_boundary = No_Voter_Call | Voter_Call "'v coordinator_event"

fun voter_boundary where
  "voter_boundary N E V C v H s s' No_Voter_Call = (s' = s)"
| "voter_boundary N E V C v H s s' (Voter_Call ev) =
    (coordinator_enabled N E V C v s ev \<and> voter_event_input H ev \<and> s' = coordinator_execute N E s ev)"

fun voter_application where
  "voter_application n No_Voter_Call a = a"
| "voter_application n (Voter_Call ev) a = after_voting_event n ev a"

lemma transport_voter_boundary:
  assumes step: "transport_step N E V C v s H s' H'"
    and reach: "transport_reachable N E V C v versions s H"
  shows "\<exists>call. voter_boundary N E V C v H s s' call"
proof -
  from transport_invariants[OF reach] have supported: "m \<in> H \<Longrightarrow> supported N E s m" for m by blast
  from transport_application_origins[OF reach] have origins:
    "Publish_RPC c i n p u \<in> H \<Longrightarrow> c = pub_owner p \<and> Registered_State p u \<in> H"
    "Sent_Commit c n k \<in> H \<Longrightarrow> Returned_Commit c k \<in> H" for c i n p u k
    unfolding application_origins_def by blast+
  show ?thesis using step
  proof cases
    case (control ev)
    have "voter_event_input H ev"
    proof (cases ev)
      case (Dispatch act enter)
      with control(3) show ?thesis by (cases act) auto
    qed simp_all
    with control show ?thesis by (intro exI[of _ "Voter_Call ev"]) simp
  next
    case (start_join n c t)
    then show ?thesis by (intro exI[of _ "Voter_Call (Dispatch (Java_Start_Join n c t) False)"]) simp
  next
    case (receive_vote d n c t k enter)
    from supported[OF receive_vote(3)] receive_vote
    show ?thesis by (intro exI[of _ "Voter_Call (Dispatch (Java_Join n d t k) enter)"]) auto
  next
    case (begin_publication c t w u D F)
    then show ?thesis by (intro exI[of _ "Voter_Call (Begin_Publication c t w u D F True)"]) simp
  next
    case (receive_publish c i n p u wire decoded opt)
    have decoded: "decoded = p" by (rule decode_publication_correct[OF receive_publish(5,6)])
    from origins(1)[OF receive_publish(3)] supported[OF receive_publish(3)] receive_publish decoded
    show ?thesis by (intro exI[of _ "Voter_Call (Dispatch (Java_Publish n decoded u) False)"])
      (auto simp: publish_from_def)
  next
    case (count_response n c k)
    from supported[OF count_response(3)] count_response
    show ?thesis by (intro exI[of _ "Voter_Call (Dispatch (Java_Response n c k) False)"]) simp
  next
    case (receive_commit c n k)
    from supported[OF receive_commit(3)] origins(2)[OF receive_commit(3)] receive_commit
    show ?thesis by (intro exI[of _ "Voter_Call (Dispatch (Java_Commit n c k) False)"]) simp
  qed (auto intro!: exI[of _ No_Voter_Call])
qed

lemma voter_boundary_projects:
  assumes "voter_boundary N E V C v H s s' call" "application_matches_voter a s n"
  shows "application_matches_voter (voter_application n call a) s' n \<and>
    (voter_application n call a = a \<or> application_step n H a (voter_application n call a))"
  using assms by (cases call) (auto dest: voting_event_projects)

definition default_application_matches where
  "default_application_matches roles s n a \<longleftrightarrow>
   (if roles n = None then application_matches_voter a (voting s) n
    else application_matches_observer a (observers s n))"

definition default_application_initial where
  "default_application_initial roles versions n =
    application_initial 0 \<lparr>rank_term = 0, rank_version = (if roles n = None then versions n else 0)\<rparr>"

definition restart_voter where
  "restart_voter u n a = restart_application a (current_term (voting_node u n)) (accepted_key (voting_node u n))"

text \<open>
  Each voting step carries its actual handler boundary as a witness.
  Across interrupted persistence, the process resets on the selected
  side of the write. The restarted process never exposes an application
  callback from inside that write. Other processes can retain the effects
  of a completed handler. Observer worker and restart events use the
  asynchronous or in-memory recovery rules.
\<close>

inductive default_coordination_effect for N E V C v marker paths roles s s' n where
  voter:
    "roles n = None \<Longrightarrow> voter_boundary N E V C v (voting_traffic s) (voting s) (voting s') call \<Longrightarrow>
     default_coordination_effect N E V C v marker paths roles s s' n a (voter_application n call a)"
| interrupted:
    "roles n = None \<Longrightarrow> voting s' = coordinator_execute N E u (Dispatch (Java_Restart n) False) \<Longrightarrow>
     default_coordination_effect N E V C v marker paths roles s s' n a (restart_voter u n a)"
| interrupted_other:
    "roles n = None \<Longrightarrow> i \<noteq> n \<Longrightarrow>
     voting s' = coordinator_execute N E u (Dispatch (Java_Restart i) False) \<Longrightarrow>
     voter_boundary N E V C v (voting_traffic s) (voting s) u call \<Longrightarrow>
     default_coordination_effect N E V C v marker paths roles s s' n a (voter_application n call a)"
| voter_unchanged:
    "roles n = None \<Longrightarrow> current_term (voting_node (voting s') n) = current_term (voting_node (voting s) n) \<Longrightarrow>
     accepted_key (voting_node (voting s') n) = accepted_key (voting_node (voting s) n) \<Longrightarrow>
     default_coordination_effect N E V C v marker paths roles s s' n a a"
| observer_call:
    "roles n = Some backend \<Longrightarrow> observer_call N (voting_traffic s) n act \<Longrightarrow>
     java_checks (observer_view (observers s n)) act \<Longrightarrow>
     observers s' n = observer_execute N E backend n (observers s n) act flush_commit \<Longrightarrow>
     default_coordination_effect N E V C v marker paths roles s s' n a (after_voting_call n act a)"
| async_restart:
    "roles n = Some Async_Observer \<Longrightarrow> available \<subseteq> paths n \<Longrightarrow>
     recovers (images_for available (observer_disk_at_cut (observers s n) completed)) d \<Longrightarrow>
     observers s' n = async_recovered v (journal (voting s)) d \<Longrightarrow>
     default_coordination_effect N E V C v marker paths roles s s' n a
       (restart_application a (stored_current_term d) (disk_key d))"
| memory_restart:
    "roles n = Some Memory_Observer \<Longrightarrow> observers s' n = observer_initial v \<Longrightarrow>
     default_coordination_effect N E V C v marker paths roles s s' n a (restart_application a 0 rank_zero)"
| observer_unchanged:
    "roles n \<noteq> None \<Longrightarrow> obs_live (observers s' n) = obs_live (observers s n) \<Longrightarrow>
     default_coordination_effect N E V C v marker paths roles s s' n a a"

lemma default_coordination_effect_projects:
  assumes eff: "default_coordination_effect N E V C v marker paths roles s s' n a b"
    and match: "default_application_matches roles s n a"
  shows "default_application_matches roles s' n b \<and> (b = a \<or> application_step n (voting_traffic s) a b)"
  using eff
proof cases
  case (voter call)
  have old: "application_matches_voter a (voting s) n"
    using match voter by (simp add: default_application_matches_def)
  from voter_boundary_projects[OF voter(3) old] voter
  show ?thesis
    by (simp_all add: default_application_matches_def)
next
  case (interrupted u)
  have "application_step n (voting_traffic s) a b"
    unfolding interrupted(1) restart_voter_def by (rule application_step.restart)
  with interrupted show ?thesis
    by (simp add: default_application_matches_def application_matches_voter_def restart_voter_def
      restart_application_def put_lifecycle_def java_put_def java_reset_def)
next
  case (interrupted_other i u call)
  have old: "application_matches_voter a (voting s) n"
    using match interrupted_other by (simp add: default_application_matches_def)
  from voter_boundary_projects[OF interrupted_other(5) old] interrupted_other
  show ?thesis
    by (simp_all add: default_application_matches_def application_matches_voter_def put_lifecycle_def java_put_def)
next
  case (observer_call backend act flush_commit)
  let ?x = "observers s n"
  let ?s = "(voting s)\<lparr>coordination := observer_view ?x\<rparr>"
  have old: "application_matches_voter a ?s n"
    using match observer_call by (simp add: default_application_matches_def application_matches_voter_def
      application_matches_observer_def observer_view_def)
  have input: "application_input (voting_traffic s) act"
    using observer_call(3) by (cases act) auto
  have step: "after_voting_call n act a = a \<or> application_step n (voting_traffic s) a (after_voting_call n act a)"
    by (rule voting_call_refines_application[OF old _ input]) (simp add: observer_call(4))
  have matched: "application_matches_voter (after_voting_call n act a) (coordinator_execute N E ?s (Dispatch act False)) n"
    by (rule voting_call_matches[OF old]) (use observer_call(3) in auto)
  from matched step observer_call show ?thesis
    by (simp_all add: default_application_matches_def application_matches_voter_def
      application_matches_observer_def observer_execute_def put_lifecycle_def Let_def)
next
  case async_restart
  have "application_step n (voting_traffic s) a b" unfolding async_restart(1) by (rule application_step.restart)
  with async_restart show ?thesis
    by (simp add: default_application_matches_def application_matches_observer_def restart_application_def
      async_recovered_def restore_node_def)
next
  case memory_restart
  have "application_step n (voting_traffic s) a b" unfolding memory_restart(1) by (rule application_step.restart)
  with memory_restart show ?thesis
    by (simp add: default_application_matches_def application_matches_observer_def restart_application_def
      observer_initial_def empty_observer_node_def java_initial_def)
qed (use match in \<open>auto simp: default_application_matches_def application_matches_observer_def application_matches_voter_def\<close>)

lemma mixed_step_supplies_application_effect:
  assumes step: "mixed_step N E V C v marker paths roles s s'"
    and transport: "transport_reachable N E V C v versions (voting s) (voting_traffic s)"
  shows "\<exists>b. default_coordination_effect N E V C v marker paths roles s s' n a b"
proof -
  have voting_effect: "\<exists>b. default_coordination_effect N E V C v marker paths roles s s' n a b"
    if obs: "observers s' n = observers s n"
      and bound: "\<exists>call. voter_boundary N E V C v (voting_traffic s) (voting s) (voting s') call"
  proof (cases "roles n = None")
    case True
    obtain call where boundary: "voter_boundary N E V C v (voting_traffic s) (voting s) (voting s') call"
      using bound by blast
    have "default_coordination_effect N E V C v marker paths roles s s' n a (voter_application n call a)"
      by (rule default_coordination_effect.voter) (rule True, rule boundary)
    then show ?thesis by blast
  next
    case False
    have "default_coordination_effect N E V C v marker paths roles s s' n a a"
      by (rule default_coordination_effect.observer_unchanged) (rule False, simp add: obs)
    then show ?thesis by blast
  qed
  have unchanged_effect: "\<exists>b. default_coordination_effect N E V C v marker paths roles s s' n a b"
    if same: "obs_live (observers s' n) = obs_live (observers s n)"
      "current_term (voting_node (voting s') n) = current_term (voting_node (voting s) n)"
      "accepted_key (voting_node (voting s') n) = accepted_key (voting_node (voting s) n)"
  proof (rule exI[of _ a])
    show "default_coordination_effect N E V C v marker paths roles s s' n a a"
    proof (cases "roles n = None")
      case True
      show ?thesis by (rule default_coordination_effect.voter_unchanged) (rule True, rule same(2), rule same(3))
    next
      case False
      show ?thesis by (rule default_coordination_effect.observer_unchanged) (rule False, rule same(1))
    qed
  qed
  show ?thesis using step
  proof cases
    case voting_transient
    show ?thesis by (rule voting_effect) (use voting_transient(1) transport_voter_boundary[OF voting_transient(2) transport] in simp_all)
  next
    case voting_write
    show ?thesis by (rule voting_effect) (use voting_write(1) transport_voter_boundary[OF voting_write(2) transport] in simp_all)
  next
    case (voting_interrupted u H i available op completed d)
    let ?r = "if d = node_disk (voting s) i then voting s else u"
    have boundary: "\<exists>call. voter_boundary N E V C v (voting_traffic s) (voting s) ?r call"
      using transport_voter_boundary[OF voting_interrupted(2) transport] by (auto intro: exI[of _ No_Voter_Call])
    have recovery: "voting s' = coordinator_execute N E ?r (Dispatch (Java_Restart i) False)"
      unfolding voting_interrupted(1) by simp
    show ?thesis
    proof (cases "roles n = None")
      case False
      show ?thesis by (intro exI[of _ a] default_coordination_effect.observer_unchanged)
        (use False voting_interrupted(1) in simp_all)
    next
      case True
      show ?thesis
      proof (cases "i = n")
        case True
        with recovery \<open>roles n = None\<close> show ?thesis
          by (intro exI[of _ "restart_voter ?r n a"] default_coordination_effect.interrupted) simp_all
      next
        case False
        from boundary False recovery True show ?thesis by (blast intro: default_coordination_effect.interrupted_other)
      qed
    qed
  next
    case (observer i backend x G)
    show ?thesis
    proof (cases "i = n")
      case False
      show ?thesis
      proof (rule voting_effect)
        show "observers s' n = observers s n" using False by (simp add: observer(1))
        show "\<exists>call. voter_boundary N E V C v (voting_traffic s) (voting s) (voting s') call"
          by (rule exI[of _ No_Voter_Call]) (simp add: observer(1))
      qed
    next
      case True
      have "observer_step N E v (journal (voting s)) (voting_traffic s) marker (paths n) backend n
        (observers s n) (observer_traffic s) x G" using observer(3) True by simp
      then show ?thesis
      proof cases
        case (call act flush_commit)
        show ?thesis
          by (intro exI[of _ "after_voting_call n act a"]
            default_coordination_effect.observer_call[where backend=backend and act=act and flush_commit=flush_commit])
            (use call observer(1,2) True in simp_all)
      next
        case (async_restart available completed d)
        show ?thesis
          by (intro exI[of _ "restart_application a (stored_current_term d) (disk_key d)"]
            default_coordination_effect.async_restart[where available=available and completed=completed and d=d])
            (use async_restart observer(1,2) True in simp_all)
      next
        case memory_restart
        show ?thesis by (intro exI[of _ "restart_application a 0 rank_zero"] default_coordination_effect.memory_restart)
          (use memory_restart observer(1,2) True in simp_all)
      qed (rule unchanged_effect; use observer(1) True in simp)+
    qed
  qed (rule unchanged_effect; auto simp: put_lifecycle_def java_put_def Let_def split: if_splits)+
qed

section \<open>Application traces in the stock execution\<close>

lemma stock_step_projects_mixed:
  assumes step: "stock_step N E V C v marker paths roles x y"
    and batches: "valid_stock_batches N E V C v versions x"
  shows "mixed_state x = mixed_state y \<or> mixed_step N E V C v marker paths roles (mixed_state x) (mixed_state y)"
  using step
proof cases
  case install
  from stock_install_is_mixed_step[OF batches install(2)] install(1,3) show ?thesis by simp
qed auto

inductive stock_applier_step for N E V C v marker paths roles where
  coordination:
    "stock_step N E V C v marker paths roles x y \<Longrightarrow>
     (\<And>n. (mixed_state y = mixed_state x \<and> B n = A n) \<or>
       default_coordination_effect N E V C v marker paths roles (mixed_state x) (mixed_state y) n (A n) (B n)) \<Longrightarrow>
     stock_applier_step N E V C v marker paths roles x A y B"
| worker:
    "default_worker_step n (current_publication (lifecycle_at (voting (mixed_state x)) n)) (A n) b \<Longrightarrow>
     stock_applier_step N E V C v marker paths roles x A x (A(n := b))"

inductive stock_applier_execution for N E V C v versions marker paths roles where
  initial:
    "stock_reachable N E V C v versions marker paths roles (stock_initial v versions) \<Longrightarrow>
     stock_applier_execution N E V C v versions marker paths roles (stock_initial v versions)
       (default_application_initial roles versions)"
| advance:
    "stock_applier_execution N E V C v versions marker paths roles x A \<Longrightarrow>
     stock_applier_step N E V C v marker paths roles x A y B \<Longrightarrow>
     stock_applier_execution N E V C v versions marker paths roles y B"

lemma default_application_initial_matches:
  "default_application_matches roles (mixed_state (stock_initial v versions)) n (default_application_initial roles versions n)"
  by (simp add: default_application_matches_def default_application_initial_def application_initial_def
    application_matches_voter_def application_matches_observer_def stock_initial_def mixed_initial_def
    coordinator_initial_def java_initial_def observer_initial_def empty_observer_node_def)

theorem stock_applier_projection:
  assumes run: "stock_applier_execution N E V C v versions marker paths roles x A"
    and separated: "\<And>n. roles n \<noteq> None \<Longrightarrow> n \<notin> N"
  shows "stock_reachable N E V C v versions marker paths roles x \<and>
    (\<forall>n. default_application_matches roles (mixed_state x) n (A n) \<and>
      application_reachable n (voting_traffic (mixed_state x)) 0 \<lparr>rank_term = 0, rank_version = (if roles n = None then versions n else 0)\<rparr> (A n))"
  using run
proof induction
  case initial
  show ?case
  proof (intro conjI allI)
    show "stock_reachable N E V C v versions marker paths roles (stock_initial v versions)" by (rule initial)
    fix n
    show "default_application_matches roles (mixed_state (stock_initial v versions)) n
      (default_application_initial roles versions n)" by (rule default_application_initial_matches)
    show "application_reachable n (voting_traffic (mixed_state (stock_initial v versions))) 0
      \<lparr>rank_term = 0, rank_version = (if roles n = None then versions n else 0)\<rparr> (default_application_initial roles versions n)"
      unfolding default_application_initial_def by (rule application_reachable.initial)
  qed
next
  case (advance x A y B)
  show ?case using advance.hyps(2)
  proof cases
    case coordination
    let ?s = "mixed_state x"
    let ?u = "mixed_state y"
    have run: "stock_reachable N E V C v versions marker paths roles x" using advance.IH by blast
    have batches: "valid_stock_batches N E V C v versions x"
      using stock_execution_projection[OF separated run] by blast
    have traffic: "voting_traffic ?s \<subseteq> voting_traffic ?u"
      using stock_step_projects_mixed[OF coordination(1) batches]
      by (elim disjE) (simp, erule mixed_application_traffic_grows)
    have applications: "default_application_matches roles ?u n (B n) \<and>
      application_reachable n (voting_traffic ?u) 0 \<lparr>rank_term = 0, rank_version = (if roles n = None then versions n else 0)\<rparr> (B n)" for n
    proof -
      have matches: "default_application_matches roles ?s n (A n)" and trace:
        "application_reachable n (voting_traffic ?s) 0 \<lparr>rank_term = 0, rank_version = (if roles n = None then versions n else 0)\<rparr> (A n)"
        using advance.IH by blast+
      have app_step: "default_application_matches roles ?u n (B n) \<and>
        (B n = A n \<or> application_step n (voting_traffic ?s) (A n) (B n))"
        using coordination(2)[of n]
      proof (elim disjE)
        assume "?u = ?s \<and> B n = A n"
        then show ?thesis using matches by simp
      next
        assume effect: "default_coordination_effect N E V C v marker paths roles ?s ?u n (A n) (B n)"
        show ?thesis by (rule default_coordination_effect_projects[OF effect matches])
      qed
      have trace': "application_reachable n (voting_traffic ?s) 0 \<lparr>rank_term = 0, rank_version = (if roles n = None then versions n else 0)\<rparr> (B n)"
        using app_step[THEN conjunct2]
        by (elim disjE) (simp add: trace, rule application_reachable.step[OF trace])
      show ?thesis by (rule conjI[OF app_step[THEN conjunct1] application_reachable_weaken[OF trace' traffic]])
    qed
    show ?thesis by (rule conjI[OF stock_reachable.step[OF run coordination(1)]], rule allI, rule applications)
  next
    case (worker n b)
    have old: "default_application_matches roles (mixed_state x) n (A n)"
      and trace: "application_reachable n (voting_traffic (mixed_state x)) 0
        \<lparr>rank_term = 0, rank_version = (if roles n = None then versions n else 0)\<rparr> (A n)" using advance.IH by blast+
    have "default_application_matches roles (mixed_state x) n b"
      using default_worker_refines(2)[OF worker(3)] old
      by (auto simp: applier_only_def default_application_matches_def application_matches_voter_def application_matches_observer_def)
    moreover have "application_reachable n (voting_traffic (mixed_state x)) 0
      \<lparr>rank_term = 0, rank_version = (if roles n = None then versions n else 0)\<rparr> b"
      by (rule application_reachable.step[OF trace default_worker_refines(1)[OF worker(3)]])
    ultimately show ?thesis using advance.IH worker(1,2) by (auto simp: fun_upd_apply)
  qed
qed

lemma stock_step_supplies_applier_step:
  assumes run: "stock_applier_execution N E V C v versions marker paths roles x A"
    and separated: "\<And>n. roles n \<noteq> None \<Longrightarrow> n \<notin> N"
    and step: "stock_step N E V C v marker paths roles x y"
  shows "\<exists>B. stock_applier_step N E V C v marker paths roles x A y B"
proof -
  from stock_applier_projection[OF run separated] have "stock_reachable N E V C v versions marker paths roles x" by blast
  from stock_execution_projection[OF separated this] have batches: "valid_stock_batches N E V C v versions x"
    and mixed: "mixed_reachable N E V C v versions marker paths roles (mixed_state x)" by blast+
  have transport: "transport_reachable N E V C v versions (voting (mixed_state x)) (voting_traffic (mixed_state x))"
    by (rule durable_execution_invariants[THEN conjunct1], rule mixed_role_durability[OF _ mixed], rule separated)
  from stock_step_projects_mixed[OF step batches] show ?thesis
  proof
    assume same: "mixed_state x = mixed_state y"
    show ?thesis by (intro exI[of _ A] stock_applier_step.coordination[OF step] disjI1 conjI)
      (rule same[symmetric], rule refl)
  next
    assume ms: "mixed_step N E V C v marker paths roles (mixed_state x) (mixed_state y)"
    have "\<forall>n. \<exists>b. default_coordination_effect N E V C v marker paths roles
        (mixed_state x) (mixed_state y) n (A n) b"
      by (intro allI mixed_step_supplies_application_effect[OF ms transport])
    obtain B where effect: "\<And>n. default_coordination_effect N E V C v marker paths roles
        (mixed_state x) (mixed_state y) n (A n) (B n)"
      using choice[OF \<open>\<forall>n. \<exists>b. default_coordination_effect N E V C v marker paths roles
        (mixed_state x) (mixed_state y) n (A n) b\<close>] by blast
    show ?thesis by (intro exI[of _ B] stock_applier_step.coordination[OF step]) (simp add: effect)
  qed
qed

lemma stock_applier_ack_history_grows:
  assumes step: "stock_applier_step N E V C v marker paths roles x A y B"
    and match: "default_application_matches roles (mixed_state x) n (A n)"
  shows "node_acknowledgements (A n) \<subseteq> node_acknowledgements (B n)"
  using step
proof cases
  case coordination
  from coordination(2)[of n] show ?thesis
  proof
    assume "mixed_state y = mixed_state x \<and> B n = A n"
    then show ?thesis by simp
  next
    assume effect: "default_coordination_effect N E V C v marker paths roles (mixed_state x) (mixed_state y) n (A n) (B n)"
    from default_coordination_effect_projects[OF effect match, THEN conjunct2] show ?thesis
      by (elim disjE) (simp, erule application_step_grows_history[THEN conjunct2])
  qed
next
  case (worker i b)
  from default_worker_refines(1)[OF worker(3), where H="voting_traffic (mixed_state x)"]
  have "node_acknowledgements (A i) \<subseteq> node_acknowledgements b"
    by (rule application_step_grows_history[THEN conjunct2])
  with worker(2) show ?thesis by (cases "i = n") simp_all
qed

corollary stock_execution_can_follow_application:
  assumes run: "stock_reachable N E V C v versions marker paths roles x"
    and separated: "\<And>n. roles n \<noteq> None \<Longrightarrow> n \<notin> N"
  shows "\<exists>A. stock_applier_execution N E V C v versions marker paths roles x A"
  using run
proof induction
  case init
  from stock_reachable.init[OF init.hyps] show ?case
    by (blast intro: stock_applier_execution.initial)
next
  case (step x y)
  then obtain A where app: "stock_applier_execution N E V C v versions marker paths roles x A" by blast
  from stock_step_supplies_applier_step[OF app separated step.hyps(2)] app
  show ?case by (blast intro: stock_applier_execution.advance)
qed

end
