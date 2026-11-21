theory Commit_Application
  imports Mixed_Role_Durability
begin

section \<open>Apply-commit callbacks and the applier's live supplier\<close>

datatype apply_request = Apply_Request node rank

fun apply_source where
  "apply_source (Apply_Request c k) = c"

fun apply_key where
  "apply_key (Apply_Request c k) = k"

definition quorum_key where
  "quorum_key H k \<longleftrightarrow> (\<exists>c. Returned_Commit c k \<in> H)"

record application_state =
  app_term :: nat
  app_accepted :: rank
  incarnation :: nat
  offered :: "rank option"
  installed :: "rank option"
  self_ready :: "apply_request set"
  queued_applications :: "apply_request set"
  running_application :: "(apply_request \<times> rank) option"
  application_successes :: "(nat \<times> apply_request \<times> rank) set"
  node_acknowledgements :: "(nat \<times> apply_request \<times> rank) set"

definition application_initial where
  "application_initial t k = \<lparr>app_term = t, app_accepted = k, incarnation = 0,
    offered = None, installed = None, self_ready = {}, queued_applications = {}, running_application = None,
    application_successes = {}, node_acknowledgements = {}\<rparr>"

definition restart_application where
  "restart_application a t k = a\<lparr>app_term := t, app_accepted := k, incarnation := Suc (incarnation a),
    offered := None, installed := None, self_ready := {}, queued_applications := {}, running_application := None\<rparr>"

definition offered_at_least where
  "offered_at_least a k \<longleftrightarrow> (\<exists>p. offered a = Some p \<and> k \<le> p)"

text \<open>
  The offered key projects Coordinator.applierState. Removing the master or
  hiding unrecovered metadata preserves this key. None is the startup
  placeholder, even when PersistedState has an accepted image. A successful
  commit handler sets the offered key before replying locally or scheduling
  remote application. The applier reads the live supplier when its task
  starts, and can store the same reference or install a different state.
  An early self reply only makes a later local application task possible.
  The abstract acknowledgement can be observed later at the publication
  target, after successful application, subject to that target still
  accepting a response. History can outlive the acknowledging process.
\<close>

inductive application_step for n H where
  advance_term:
    "app_term a < t \<Longrightarrow> application_step n H a (a\<lparr>app_term := t\<rparr>)"
| accept:
    "Registered_State p u \<in> H \<Longrightarrow> pub_term p = app_term a \<Longrightarrow>
     (rank_term (app_accepted a) = pub_term p \<longrightarrow> rank_version (app_accepted a) < pub_version p) \<Longrightarrow>
     application_step n H a (a\<lparr>app_accepted := request_key p\<rparr>)"
| handle_remote:
    "c \<noteq> n \<Longrightarrow> Returned_Commit c k \<in> H \<Longrightarrow>
     rank_term k = app_term a \<Longrightarrow> k = app_accepted a \<Longrightarrow>
     application_step n H a (a\<lparr>offered := Some k,
       queued_applications := insert (Apply_Request c k) (queued_applications a)\<rparr>)"
| handle_self:
    "Returned_Commit n k \<in> H \<Longrightarrow> rank_term k = app_term a \<Longrightarrow> k = app_accepted a \<Longrightarrow>
     application_step n H a (a\<lparr>offered := Some k, self_ready := insert (Apply_Request n k) (self_ready a)\<rparr>)"
| queue_self:
    "q \<in> self_ready a \<Longrightarrow>
     application_step n H a (a\<lparr>self_ready := self_ready a - {q},
       queued_applications := insert q (queued_applications a)\<rparr>)"
| read_supplier:
    "q \<in> queued_applications a \<Longrightarrow> running_application a = None \<Longrightarrow> offered a = Some p \<Longrightarrow>
     application_step n H a (a\<lparr>queued_applications := queued_applications a - {q}, running_application := Some (q,p)\<rparr>)"
| install_background:
    "running_application a = None \<Longrightarrow> offered a = Some p \<Longrightarrow>
     application_step n H a (a\<lparr>installed := Some p\<rparr>)"
| apply_success:
    "running_application a = Some (q,p) \<Longrightarrow>
     application_step n H a (a\<lparr>running_application := None, installed := Some p,
       application_successes := insert (incarnation a,q,p) (application_successes a)\<rparr>)"
| apply_failure:
    "running_application a = Some (q,p) \<Longrightarrow>
     application_step n H a (a\<lparr>running_application := None, installed := (if stored then Some p else installed a)\<rparr>)"
| observe_ack:
    "(e,q,p) \<in> application_successes a \<Longrightarrow>
     application_step n H a (a\<lparr>node_acknowledgements := insert (e,q,p) (node_acknowledgements a)\<rparr>)"
| restart:
    "application_step n H a (restart_application a t k)"

inductive application_reachable for n H t k where
  initial: "application_reachable n H t k (application_initial t k)"
| step: "application_reachable n H t k a \<Longrightarrow> application_step n H a b \<Longrightarrow>
    application_reachable n H t k b"

definition authentic_request where
  "authentic_request H q \<longleftrightarrow> Returned_Commit (apply_source q) (apply_key q) \<in> H"

definition live_application_ok where
  "live_application_ok H a \<longleftrightarrow>
    (\<forall>p. offered a = Some p \<longrightarrow> quorum_key H p \<and>
      p \<le> app_accepted a \<and> rank_term (app_accepted a) \<le> app_term a) \<and>
    (\<forall>p. installed a = Some p \<longrightarrow> quorum_key H p \<and> offered_at_least a p) \<and>
    (\<forall>q\<in>self_ready a \<union> queued_applications a. authentic_request H q \<and> offered_at_least a (apply_key q)) \<and>
    (\<forall>q p. running_application a = Some (q,p) \<longrightarrow>
      authentic_request H q \<and> quorum_key H p \<and> apply_key q \<le> p \<and> offered_at_least a p \<and>
      (\<forall>x. installed a = Some x \<longrightarrow> x \<le> p))"

definition application_history_ok where
  "application_history_ok H a \<longleftrightarrow> node_acknowledgements a \<subseteq> application_successes a \<and>
    (\<forall>(e,q,p) \<in> application_successes a. authentic_request H q \<and> quorum_key H p \<and> apply_key q \<le> p)"

lemma application_offer_le_accepted:
  assumes "live_application_ok H a" "offered_at_least a r"
  shows "r \<le> app_accepted a"
proof -
  from assms(2) obtain p where "offered a = Some p" and r: "r \<le> p"
    unfolding offered_at_least_def by blast
  with assms(1) have "p \<le> app_accepted a" unfolding live_application_ok_def by blast
  from r this show ?thesis by (rule order_trans)
qed

lemma commit_offer_keeps_floor:
  assumes live: "live_application_ok H a" and key: "k = app_accepted a"
  shows "installed a = Some p \<Longrightarrow> p \<le> k"
    "q \<in> self_ready a \<union> queued_applications a \<Longrightarrow> apply_key q \<le> k"
    "running_application a = Some (q,p) \<Longrightarrow> p \<le> k"
proof -
  have floor: "offered_at_least a r \<Longrightarrow> r \<le> k" for r
    unfolding key by (rule application_offer_le_accepted[OF live])
  show "installed a = Some p \<Longrightarrow> p \<le> k"
    using live unfolding live_application_ok_def by (blast intro: floor)
  show "q \<in> self_ready a \<union> queued_applications a \<Longrightarrow> apply_key q \<le> k"
    using live unfolding live_application_ok_def by (blast intro: floor)
  show "running_application a = Some (q,p) \<Longrightarrow> p \<le> k"
    using live unfolding live_application_ok_def by (blast intro: floor)
qed

lemma application_step_preserves:
  assumes step: "application_step n H a b" and live: "live_application_ok H a" and history: "application_history_ok H a"
  shows "live_application_ok H b \<and> application_history_ok H b"
  using step
proof cases
  case (advance_term t)
  have "rank_term (app_accepted a) \<le> t" if "offered a = Some p" for p
  proof -
    have "rank_term (app_accepted a) \<le> app_term a" using live that unfolding live_application_ok_def by blast
    from this advance_term(2) show ?thesis by (rule le_less_trans[THEN less_imp_le])
  qed
  then show ?thesis using advance_term(1) live history by (auto simp: live_application_ok_def application_history_ok_def offered_at_least_def)
next
  case (accept p u)
  then have key: "rank_term (app_accepted a) \<le> app_term a \<Longrightarrow> app_accepted a < request_key p"
    by (auto simp: rank_less_iff)
  have "r \<le> request_key p" if "offered a = Some r" for r
  proof -
    from live that have "r \<le> app_accepted a" "rank_term (app_accepted a) \<le> app_term a"
      unfolding live_application_ok_def by blast+
    from this(1) key[OF this(2)] show ?thesis by (rule le_less_trans[THEN less_imp_le])
  qed
  with accept(1,3) live history show ?thesis
    by (auto simp: live_application_ok_def application_history_ok_def offered_at_least_def
      simp del: split_paired_All less_eq_prod_simp)
next
  case (handle_remote c k)
  from handle_remote live history commit_offer_keeps_floor[OF live handle_remote(5)] show ?thesis
    by (auto simp: live_application_ok_def application_history_ok_def offered_at_least_def authentic_request_def
      quorum_key_def simp del: split_paired_All less_eq_prod_simp)
next
  case (handle_self k)
  from handle_self live history commit_offer_keeps_floor[OF live handle_self(4)] show ?thesis
    by (auto simp: live_application_ok_def application_history_ok_def offered_at_least_def authentic_request_def
      quorum_key_def simp del: split_paired_All less_eq_prod_simp)
qed (use live history in \<open>auto simp: live_application_ok_def application_history_ok_def offered_at_least_def
  authentic_request_def quorum_key_def restart_application_def simp del: split_paired_All less_eq_prod_simp split: if_splits\<close>)

theorem application_invariants:
  assumes "application_reachable n H t k a"
  shows "live_application_ok H a \<and> application_history_ok H a"
  using assms
proof induction
  case initial
  then show ?case by (simp add: application_initial_def live_application_ok_def application_history_ok_def)
next
  case (step a b)
  from step.IH have "live_application_ok H a" and "application_history_ok H a" by auto
  from application_step_preserves[OF step.hyps(2) this] show ?case .
qed

theorem successful_node_ack:
  assumes run: "application_reachable n H t k a"
    and ack: "(e,q,p) \<in> node_acknowledgements a"
  shows "(e,q,p) \<in> application_successes a" "authentic_request H q" "quorum_key H p" "apply_key q \<le> p"
  using application_invariants[OF run] ack by (auto simp: application_history_ok_def)

lemma success_installs_sample:
  assumes "running_application a = Some (q,p)"
  defines "b \<equiv> a\<lparr>running_application := None, installed := Some p,
      application_successes := insert (incarnation a,q,p) (application_successes a)\<rparr>"
  shows "application_step n H a b" "installed b = Some p"
  using application_step.apply_success[OF assms(1)] unfolding b_def by simp_all

lemma self_reply_does_not_install:
  assumes "Returned_Commit n k \<in> H" "rank_term k = app_term a" "k = app_accepted a"
  defines "b \<equiv> a\<lparr>offered := Some k, self_ready := insert (Apply_Request n k) (self_ready a)\<rparr>"
  shows "application_step n H a b" "installed b = installed a"
    "node_acknowledgements b = node_acknowledgements a"
  using application_step.handle_self[OF assms(1-3)] unfolding b_def by simp_all

lemma application_step_grows_history:
  "application_step n H a b \<Longrightarrow>
    application_successes a \<subseteq> application_successes b \<and> node_acknowledgements a \<subseteq> node_acknowledgements b"
  by (cases rule: application_step.cases) (auto simp: restart_application_def)

lemma restart_application_keeps_only_history:
  "incarnation (restart_application a t k) = Suc (incarnation a)"
  "installed (restart_application a t k) = None"
  "offered (restart_application a t k) = None"
  "queued_applications (restart_application a t k) = {}"
  "running_application (restart_application a t k) = None"
  "node_acknowledgements (restart_application a t k) = node_acknowledgements a"
  by (simp_all add: restart_application_def)

lemma application_step_weaken:
  assumes "application_step n H a b" "H \<subseteq> H'"
  shows "application_step n H' a b"
  using assms by (cases rule: application_step.cases) (blast intro: application_step.intros)+

lemma application_reachable_weaken:
  assumes "application_reachable n H t k a" and subset: "H \<subseteq> H'"
  shows "application_reachable n H' t k a"
  using assms(1)
proof induction
  case initial
  show ?case by (rule application_reachable.initial)
next
  case (step a b)
  show ?case by (rule application_reachable.step[OF step.IH application_step_weaken[OF step.hyps(2) subset]])
qed

section \<open>Observer restart and quorum ancestry\<close>

definition application_matches_observer where
  "application_matches_observer a x \<longleftrightarrow>
    app_term a = current_term (obs_live x) \<and> app_accepted a = accepted_key (obs_live x)"

lemma observer_application_step:
  assumes observer: "observer_step N E v J H marker paths backend n x G y G'"
    and match: "application_matches_observer a x"
  obtains b where "application_matches_observer b y" "b = a \<or> application_step n H a b"
  using observer
proof cases
  case (call act flush_commit)
  show thesis using call
  proof (cases act)
    case (Java_Start_Join i c t)
    then have "t > app_term a" using call match by (simp add: application_matches_observer_def observer_view_def)
    then have step: "application_step n H a (a\<lparr>app_term := t\<rparr>)" by (rule application_step.advance_term)
    show thesis
      by (rule that[of "a\<lparr>app_term := t\<rparr>"])
        (use call Java_Start_Join match step in \<open>auto simp: application_matches_observer_def observer_execute_def
          observer_view_def java_put_def java_reset_def Let_def\<close>)
  next
    case (Java_Publish i p u)
    have step: "application_step n H a (a\<lparr>app_accepted := request_key p\<rparr>)"
      by (rule application_step.accept[of p u])
        (use call Java_Publish match in \<open>auto simp: observer_view_def application_matches_observer_def Let_def\<close>)
    show thesis
      by (rule that[of "a\<lparr>app_accepted := request_key p\<rparr>"])
        (use call Java_Publish match step in \<open>auto simp: application_matches_observer_def observer_execute_def
          observer_view_def java_put_def Let_def\<close>)
  next
    case (Java_Commit i c k)
    with call match have packet: "Returned_Commit c k \<in> H" and current: "rank_term k = app_term a" and key: "k = app_accepted a"
      by (auto simp: observer_view_def application_matches_observer_def Let_def)
    show thesis
    proof (cases "c = n")
      case True
      with packet have step: "application_step n H a (a\<lparr>offered := Some k,
        self_ready := insert (Apply_Request n k) (self_ready a)\<rparr>)"
        by (auto intro: application_step.handle_self[OF _ current key])
      show thesis
        by (rule that[of "a\<lparr>offered := Some k, self_ready := insert (Apply_Request n k) (self_ready a)\<rparr>"])
          (use call Java_Commit match step in \<open>auto simp: application_matches_observer_def observer_execute_def
            observer_view_def java_put_def Let_def\<close>)
    next
      case False
      from application_step.handle_remote[OF False packet current key]
      show thesis
        by (intro that[of "a\<lparr>offered := Some k,
          queued_applications := insert (Apply_Request c k) (queued_applications a)\<rparr>"])
          (use call Java_Commit match in \<open>auto simp: application_matches_observer_def observer_execute_def
            observer_view_def java_put_def Let_def\<close>)
    qed
  qed auto
next
  case (async_restart available completed d)
  let ?b = "restart_application a (stored_current_term d) (disk_key d)"
  show thesis
  proof (rule that[of ?b])
    show "application_matches_observer ?b y"
      using async_restart by (simp add: application_matches_observer_def async_recovered_def restart_application_def restore_node_def)
    show "?b = a \<or> application_step n H a ?b"
      by (intro disjI2 application_step.restart)
  qed
next
  case memory_restart
  let ?b = "restart_application a 0 rank_zero"
  show thesis
  proof (rule that[of ?b])
    show "application_matches_observer ?b y"
      using memory_restart by (simp add: application_matches_observer_def restart_application_def observer_initial_def
        empty_observer_node_def java_initial_def)
    show "?b = a \<or> application_step n H a ?b"
      by (intro disjI2 application_step.restart)
  qed
qed (use match that[of a] in \<open>auto simp: application_matches_observer_def\<close>)

lemma mixed_application_traffic_grows:
  assumes "mixed_step N E V C v marker paths roles s s'"
  shows "voting_traffic s \<subseteq> voting_traffic s'"
  using assms by (cases rule: mixed_step.cases) (auto dest: transport_history_grows split: if_splits)

lemma mixed_application_can_follow:
  assumes step: "mixed_step N E V C v marker paths roles s s'"
    and match: "application_matches_observer a (observers s n)"
  obtains b where "application_matches_observer b (observers s' n)"
    "b = a \<or> application_step n (voting_traffic s) a b"
  using step
proof cases
  case (observer i backend x G)
  show thesis
  proof (cases "i = n")
    case True
    have obs: "observer_step N E v (journal (voting s)) (voting_traffic s) marker (paths n) backend n
      (observers s n) (observer_traffic s) x G" using observer(3) True by simp
    obtain b where "application_matches_observer b x" "b = a \<or> application_step n (voting_traffic s) a b"
      by (rule observer_application_step[OF obs match])
    then show thesis by (intro that[of b]) (use observer(1) True in simp_all)
  next
    case False
    show thesis by (rule that[of a]) (use observer(1) False match in simp_all)
  qed
qed (use that[of a] match in auto)

text \<open>
  The combined relation uses the observer's live term and accepted key at
  Java call boundaries. A mixed coordination step can carry its
  corresponding application-side effect, with observer restart represented
  by a change of incarnation. Application worker steps leave the
  coordination projection and the offered key in place. The latter also
  forbids creating a new remote task without a coordination-side event.
\<close>

definition applier_only where
  "applier_only a b \<longleftrightarrow>
    app_term b = app_term a \<and> app_accepted b = app_accepted a \<and> incarnation b = incarnation a \<and>
    offered b = offered a \<and> self_ready b \<subseteq> self_ready a \<and>
    queued_applications b \<subseteq> queued_applications a \<union> self_ready a"

inductive mixed_application_reachable for N E V C v versions marker paths roles n where
  start:
    "roles n \<noteq> None \<Longrightarrow>
     mixed_reachable N E V C v versions marker paths roles (mixed_initial v versions) \<Longrightarrow>
     mixed_application_reachable N E V C v versions marker paths roles n (mixed_initial v versions) (application_initial 0 rank_zero)"
| coordination:
    "mixed_application_reachable N E V C v versions marker paths roles n s a \<Longrightarrow>
     mixed_step N E V C v marker paths roles s s' \<Longrightarrow>
     (b = a \<or> application_step n (voting_traffic s) a b) \<Longrightarrow>
     application_matches_observer b (observers s' n) \<Longrightarrow>
     mixed_application_reachable N E V C v versions marker paths roles n s' b"
| application:
    "mixed_application_reachable N E V C v versions marker paths roles n s a \<Longrightarrow>
     application_step n (voting_traffic s) a b \<Longrightarrow> applier_only a b \<Longrightarrow>
     mixed_application_reachable N E V C v versions marker paths roles n s b"

lemma mixed_application_projection:
  assumes "mixed_application_reachable N E V C v versions marker paths roles n s a"
  shows "mixed_reachable N E V C v versions marker paths roles s \<and>
    application_reachable n (voting_traffic s) 0 rank_zero a \<and> application_matches_observer a (observers s n)"
  using assms
proof induction
  case start
  have "application_reachable n (voting_traffic (mixed_initial v versions)) 0 rank_zero (application_initial 0 rank_zero)"
    by (rule application_reachable.initial)
  with start show ?case by (simp add: mixed_initial_def application_initial_def application_matches_observer_def
    observer_initial_def empty_observer_node_def java_initial_def)
next
  case (coordination s a s' b)
  then have run: "mixed_reachable N E V C v versions marker paths roles s" and
    app: "application_reachable n (voting_traffic s) 0 rank_zero a" by auto
  have mixed: "mixed_reachable N E V C v versions marker paths roles s'"
    by (rule mixed_reachable.step[OF run coordination.hyps(2)])
  have "application_reachable n (voting_traffic s) 0 rank_zero b"
    using coordination.hyps(3) app application_reachable.step by blast
  from application_reachable_weaken[OF this mixed_application_traffic_grows[OF coordination.hyps(2)]]
    mixed coordination.hyps(4) show ?case by blast
next
  case application
  then show ?case
    by (auto simp: applier_only_def application_matches_observer_def intro: application_reachable.step)
qed

lemma returned_commit_has_quorum_history:
  assumes run: "transport_reachable N E V C v versions s H"
    and refinements: "linked C t d" "coordination s = project_java E t"
    and packet: "Returned_Commit c k \<in> H"
  obtains h where "h \<in> quorum_commits d" "position h = k" "owner h = c"
proof -
  interpret default_strategy N E C
    by (rule java_reachable_default_strategy[OF transport_java_reachable[OF run]])
  have "N \<noteq> {}" using initial_config elig by blast
  then obtain n where member: "n \<in> N" by blast
  have "supported N E s (Returned_Commit c k)"
    using transport_invariants[OF run] packet by blast
  with member have "Commit_Msg c n k \<in> messages t" by (simp add: refinements(2))
  from linkedD(3)[OF refinements(1) this] show thesis using that by auto
qed

theorem mixed_node_acknowledges_committed_prefix:
  assumes run: "mixed_reachable N E V C v versions marker paths roles s"
    and roles: "\<And>n. roles n \<noteq> None \<Longrightarrow> n \<notin> N"
    and app: "application_reachable n (voting_traffic s) initial_term initial_key a"
    and ack: "(e,q,p) \<in> node_acknowledgements a"
  obtains d h h' where "dynamic_reachable C d" "h \<in> quorum_commits d" "h' \<in> quorum_commits d"
    "position h = apply_key q" "owner h = apply_source q" "position h' = p" "prefix h h'"
proof -
  have durable: "durable_execution N E V C v versions paths (voting s) (voting_traffic s) (voting_disks s)"
    by (rule mixed_role_durability[OF roles run])
  have transport: "transport_reachable N E V C v versions (voting s) (voting_traffic s)"
    using durable_execution_invariants[OF durable] by blast
  obtain t where reachable: "tla_reachable N V C v versions t" and projection: "coordination (voting s) = project_java E t"
    using transport_refines_tla[OF transport] by blast
  obtain d where d: "dynamic_reachable C d" "linked C t d" using tla_dynamic_refinement[OF reachable] by blast
  from successful_node_ack(2)[OF app ack] have request: "Returned_Commit (apply_source q) (apply_key q) \<in> voting_traffic s"
    unfolding authentic_request_def .
  obtain h where h: "h \<in> quorum_commits d" "position h = apply_key q" "owner h = apply_source q"
    by (rule returned_commit_has_quorum_history[OF transport d(2) projection request])
  from successful_node_ack(3)[OF app ack] obtain c where sampled: "Returned_Commit c p \<in> voting_traffic s"
    unfolding quorum_key_def by blast
  obtain h' where h': "h' \<in> quorum_commits d" "position h' = p" "owner h' = c"
    by (rule returned_commit_has_quorum_history[OF transport d(2) projection sampled])
  have ord: "position h \<le> position h'" using successful_node_ack(4)[OF app ack] h(2) h'(2) by simp
  have ok: "publications_ok C d" using dynamic_invariants[OF d(1)] by blast
  have hp: "h \<in> insert [] (publications d)" using publicationsD(5)[OF ok h(1)] by blast
  have "prefix h h'"
    using dynamic_committed_states_form_chain[OF d(1) h(1) h'(1)]
      lineage_prefix[OF ok hp, of h'] ord by (auto simp: not_less)
  then show thesis by (rule that[OF d(1) h(1) h'(1) h(2,3) h'(2)])
qed

corollary coupled_node_acknowledges_committed_prefix:
  assumes run: "mixed_application_reachable N E V C v versions marker paths roles n s a"
    and roles: "\<And>i. roles i \<noteq> None \<Longrightarrow> i \<notin> N"
    and ack: "(e,q,p) \<in> node_acknowledgements a"
  obtains d h h' where "dynamic_reachable C d" "h \<in> quorum_commits d" "h' \<in> quorum_commits d"
    "position h = apply_key q" "owner h = apply_source q" "position h' = p" "prefix h h'"
proof -
  from mixed_application_projection[OF run] have mixed: "mixed_reachable N E V C v versions marker paths roles s"
    and app: "application_reachable n (voting_traffic s) 0 rank_zero a" by auto
  show thesis by (rule mixed_node_acknowledges_committed_prefix[OF mixed roles app ack that])
qed

end
