theory Dynamic_Window_Liveness
  imports Scheduler_Liveness
begin

section \<open>A quiet window with dynamic voting configurations\<close>

text \<open>
  The selected election voters E satisfy the candidate's committed and
  accepted configurations. J supplies fresh joins for the proposed
  configuration, and may include votes obtained after election. Q supplies
  publication receipts under the carried and proposed configurations.
  Their unions determine which processes must join the term. The protocol's
  reconfiguration guard applies even when both configurations can obtain
  votes. The candidate performs its own durable acceptance and apply-commit
  whether or not it is needed in Q.

  This isolated window projects successful operations of the selected
  participants. Pre-vote, discovery, term selection and transport must make
  the chosen joins available without intervening conflicting actions. After
  quorum commit, the publisher waits for terminal targets or a post-commit
  cancellation, its own reply and local application. The service bound
  covers those operations, including any callback needed to end the wait.
\<close>

definition dynamic_window_waves where
  "dynamic_window_waves E J Q T c cancel_wait =
    [Prevote ` E, {Choose_Term}, Persist_Join ` insert c (E \<union> J \<union> Q),
     {Collect_Votes}, {Register}, Persist_Accept ` insert c Q, {Collect_Receipts},
     insert Handle_Self_Commit (if cancel_wait then {End_Target_Wait} else Finish_Target ` (T - {c})),
     {Queue_Local}, {Sample_Local}, {Run_Local}, {Release_Slot}]"

definition dynamic_dependencies where
  "dynamic_dependencies E J Q T c cancel_wait a =
    (if a = Register then insert Collect_Votes (Persist_Join ` J)
     else window_dependencies True E Q T c cancel_wait a)"

lemma dynamic_window_wave_dependencies:
  assumes waves: "dynamic_window_waves E J Q T c cancel =
     before @ batch # after"
    and member: "a \<in> batch"
  shows "a \<in> \<Union>(set (dynamic_window_waves E J Q T c cancel)) \<and>
    dynamic_dependencies E J Q T c cancel a \<subseteq> \<Union>(set before)"
  using waves member unfolding dynamic_window_waves_def
  by (auto simp: Cons_eq_append_conv dynamic_dependencies_def split: if_splits)

lemma certificate_term_is_durable:
  assumes "dynamic_reachable C s"
  shows "\<forall>c t e. certificate s (c,t) = Some e \<longrightarrow> t \<le> node_term s c"
  using assms
proof (induction rule: dynamic_reachable.induct)
  case boot
  then show ?case by (simp add: bootstrapped_def)
next
  case (advance s s')
  from advance.hyps(2) show ?case
  proof cases
    case start_join
    then have same: "certificate s' = certificate s"
      and mono: "node_term s n \<le> node_term s' n" for n by auto
    show ?thesis
    proof (intro allI impI)
      fix c t e
      assume "certificate s' (c,t) = Some e"
      with same advance.IH have "t \<le> node_term s c" by metis
      then show "t \<le> node_term s' c" by (rule le_trans[OF _ mono])
    qed
  qed (use advance.IH in auto)
qed

locale dynamic_publication_window =
  fixes C E J Q T D :: config and c :: node and t v payload :: nat
    and s :: dynamic_state and cancel_wait :: bool
  assumes reach: "dynamic_reachable C s"
    and targets: "c \<in> T" "Q \<subseteq> T" "finite T"
    and joint_election: "quorum (committed_config s c) E"
      "quorum (config_of C (durable_history s c)) E"
    and proposal: "quorum D J"
      "D \<noteq> config_of C (durable_history s c) \<Longrightarrow>
       committed_config s c = config_of C (durable_history s c)"
    and joint_publication: "quorum (committed_config s c) Q" "quorum D Q"
    and fresh_term: "n \<in> insert c (E \<union> J \<union> Q) \<Longrightarrow> node_term s n < t"
    and fresh_votes_from: "n \<in> E \<union> J \<Longrightarrow> position (durable_history s n) \<le> position (durable_history s c)"
    and version_increases: "rank_version (position (durable_history s c)) < v"
begin

abbreviation waves where "waves \<equiv> dynamic_window_waves E J Q T c cancel_wait"
abbreviation jobs where "jobs \<equiv> \<Union>(set waves)"
abbreviation deps where "deps \<equiv> dynamic_dependencies E J Q T c cancel_wait"
abbreviation finished where "finished sel \<equiv> completed_work jobs deps sel"
abbreviation base where "base \<equiv> durable_history s c"
abbreviation item where "item \<equiv> \<lparr>pub_term = t, pub_version = v, pub_payload = payload,
    pub_owner = c, pub_config = D, pub_previous = committed_config s c\<rparr>"
abbreviation hist where "hist \<equiv> base @ [item]"
abbreviation ballot where "ballot \<equiv> \<lparr>elected_from = base, elected_committed = committed_config s c, elected_votes = E\<rparr>"

lemma no_certificate_in_window_term:
  "certificate s (c,t) = None"
proof (rule ccontr)
  assume "certificate s (c,t) \<noteq> None"
  then obtain e where "certificate s (c,t) = Some e" by (cases "certificate s (c,t)") auto
  with certificate_term_is_durable[OF reach] have "t \<le> node_term s c" by blast
  with fresh_term[of c] show False by simp
qed

lemma dynamic_window_history_is_new:
  "hist \<notin> publications s" "hist \<notin> quorum_commits s"
proof -
  have led: "leadership_ok C s" and pub: "publications_ok C s"
    using dynamic_invariants[OF reach] by blast+
  show "hist \<notin> publications s"
  proof
    assume "hist \<in> publications s"
    from leadershipD(8)[OF led this] no_certificate_in_window_term show False by simp
  qed
  then show "hist \<notin> quorum_commits s" using publicationsD(5)[OF pub, of hist] by blast
qed

definition dynamic_snapshot where
  "dynamic_snapshot K = s\<lparr>
      node_term := (\<lambda>n. if Persist_Join n \<in> K then t else node_term s n),
      durable_history := (\<lambda>n. if Persist_Accept n \<in> K then hist else durable_history s n),
      committed_config := (\<lambda>n. if n = c \<and> Handle_Self_Commit \<in> K then D
          else if Persist_Accept n \<in> K then committed_config s c else committed_config s n),
      sent_joins := sent_joins s \<union> {(n,c,t,position (durable_history s n)) |n. Persist_Join n \<in> K},
      joined_since_restart := joined_since_restart s \<union> {n. Persist_Join n \<in> K},
      certificate := (if Collect_Votes \<in> K then (certificate s)((c,t) := Some ballot) else certificate s),
      publication_tip := (if Register \<in> K then (publication_tip s)((c,t) := hist)
          else if Collect_Votes \<in> K then (publication_tip s)((c,t) := base) else publication_tip s),
      publications := (if Register \<in> K then insert hist (publications s) else publications s),
      acknowledgements := acknowledgements s \<union> {(n,hist) |n. Persist_Accept n \<in> K},
      quorum_commits := (if Collect_Receipts \<in> K then insert hist (quorum_commits s) else quorum_commits s)\<rparr>"

definition dynamic_window_slot where
  "dynamic_window_slot K = (if Register \<in> K \<and> Release_Slot \<notin> K then Some hist else None)"

lemma ready_window_job:
  assumes "work_ready jobs deps K a"
  shows "a \<in> jobs" "a \<notin> K" "deps a \<subseteq> K"
  using assms by (simp_all add: work_ready_def)

lemma window_predecessors:
  assumes "ordered_work jobs deps K" "a \<in> K"
  shows "deps a \<subseteq> K"
  using assms unfolding ordered_work_def by blast

lemma dynamic_candidate_active:
  assumes ord: "ordered_work jobs deps K" and win: "Collect_Votes \<in> K"
  shows "node_term (dynamic_snapshot K) c = t" "active_leader (dynamic_snapshot K) c"
proof -
  have self: "Persist_Join c \<in> K"
    using window_predecessors[OF ord win] unfolding dynamic_dependencies_def by auto
  from self win show "node_term (dynamic_snapshot K) c = t" "active_leader (dynamic_snapshot K) c"
    by (simp_all add: dynamic_snapshot_def active_leader_def)
qed

lemma dynamic_snapshot_votes:
  assumes joined: "Persist_Join ` X \<subseteq> K" and fresh: "X \<subseteq> E \<union> J"
    and no_accept: "Persist_Accept c \<notin> K"
  shows "fresh_votes (dynamic_snapshot K) c t (durable_history (dynamic_snapshot K) c) X"
proof -
  have vote: "(n,c,t,position (durable_history s n)) \<in> sent_joins (dynamic_snapshot K)" if "n \<in> X" for n
    using joined that by (auto simp: dynamic_snapshot_def)
  have "position (durable_history s n) \<le> position (durable_history (dynamic_snapshot K) c)" if "n \<in> X" for n
    using fresh_votes_from fresh that no_accept by (auto simp: dynamic_snapshot_def)
  with vote show ?thesis unfolding fresh_votes_def by blast
qed

lemma dynamic_apply_requires_accept:
  assumes ord: "ordered_work jobs deps K"
  shows "Handle_Self_Commit \<in> K \<Longrightarrow> Persist_Accept c \<in> K"
  using window_predecessors[OF ord, of Handle_Self_Commit]
  by (auto simp: dynamic_dependencies_def)

lemma dynamic_snapshot_step:
  assumes ord: "ordered_work jobs deps K" and ready: "work_ready jobs deps K a"
  shows "dynamic_snapshot (insert a K) = dynamic_snapshot K \<or>
    transition C (dynamic_snapshot K) (dynamic_snapshot (insert a K))"
proof (cases a)
  case (Persist_Join n)
  from ready_window_job[OF ready] Persist_Join have participates: "n \<in> insert c (E \<union> J \<union> Q)"
    and absent: "Persist_Join n \<notin> K" by (auto simp: dynamic_window_waves_def split: if_splits)
  have no_accept: "Persist_Accept n \<notin> K"
    using window_predecessors[OF ord, of "Persist_Accept n"] absent by (auto simp: dynamic_dependencies_def)
  let ?b = "dynamic_snapshot K"
  have term_check: "node_term ?b n < t" using fresh_term[OF participates] absent by (simp add: dynamic_snapshot_def)
  have step: "transition C ?b (?b\<lparr>node_term := (node_term ?b)(n := t),
    sent_joins := insert (n,c,t,position (durable_history ?b n)) (sent_joins ?b),
    joined_since_restart := insert n (joined_since_restart ?b)\<rparr>)"
    by (rule transition.start_join[OF term_check])
  have "dynamic_snapshot (insert a K) = ?b\<lparr>node_term := (node_term ?b)(n := t),
    sent_joins := insert (n,c,t,position (durable_history ?b n)) (sent_joins ?b),
    joined_since_restart := insert n (joined_since_restart ?b)\<rparr>"
    by (rule dynamic_state.equality)
      (use Persist_Join no_accept in \<open>auto simp: dynamic_snapshot_def fun_eq_iff\<close>)
  with step show ?thesis by simp
next
  case Collect_Votes
  from ready_window_job[OF ready] Collect_Votes have never: "Collect_Votes \<notin> K"
    and joined: "Persist_Join ` insert c E \<subseteq> K" by (auto simp: dynamic_dependencies_def)
  have unregistered: "Register \<notin> K"
    using window_predecessors[OF ord, of Register] never by (auto simp: dynamic_dependencies_def)
  then have no_accept: "Persist_Accept c \<notin> K"
    using window_predecessors[OF ord, of "Persist_Accept c"] by (auto simp: dynamic_dependencies_def)
  let ?b = "dynamic_snapshot K"
  have started: "c \<in> joined_since_restart ?b" and current: "node_term ?b c = t"
    using joined by (auto simp: dynamic_snapshot_def)
  have none: "certificate ?b (c,node_term ?b c) = None"
    using no_certificate_in_window_term never current by (simp add: dynamic_snapshot_def)
  have unchanged: "durable_history ?b c = base" "committed_config ?b c = committed_config s c"
    using no_accept dynamic_apply_requires_accept[OF ord] by (auto simp: dynamic_snapshot_def)
  have votes: "fresh_votes ?b c (node_term ?b c) (durable_history ?b c) E"
    using dynamic_snapshot_votes[of E K] joined no_accept current by auto
  have step: "transition C ?b (?b\<lparr>certificate := (certificate ?b)((c,t) := Some ballot),
    publication_tip := (publication_tip ?b)((c,t) := base)\<rparr>)"
    using transition.win[OF started none _ _ votes] joint_election unchanged current by simp
  have "dynamic_snapshot (insert a K) = ?b\<lparr>certificate := (certificate ?b)((c,t) := Some ballot),
    publication_tip := (publication_tip ?b)((c,t) := base)\<rparr>"
    by (rule dynamic_state.equality)
      (use Collect_Votes unregistered in \<open>auto simp: dynamic_snapshot_def fun_eq_iff\<close>)
  with step show ?thesis by simp
next
  case Register
  from ready_window_job[OF ready] Register have absent: "Register \<notin> K"
    and elect: "Collect_Votes \<in> K" and joined: "Persist_Join ` J \<subseteq> K"
    by (auto simp: dynamic_dependencies_def)
  have no_accept: "Persist_Accept c \<notin> K"
    using window_predecessors[OF ord, of "Persist_Accept c"] absent by (auto simp: dynamic_dependencies_def)
  let ?b = "dynamic_snapshot K"
  note current = dynamic_candidate_active(1)[OF ord elect]
  have unchanged: "durable_history ?b c = base" "committed_config ?b c = committed_config s c"
    using no_accept dynamic_apply_requires_accept[OF ord] by (auto simp: dynamic_snapshot_def)
  have tip: "publication_tip ?b (c,node_term ?b c) = durable_history ?b c"
    using absent elect current unchanged by (simp add: dynamic_snapshot_def)
  have inc: "rank_version (position (durable_history ?b c)) < v" using unchanged version_increases by simp
  have guard: "D \<noteq> config_of C (durable_history ?b c) \<longrightarrow>
      committed_config ?b c = config_of C (durable_history ?b c)" using unchanged proposal(2) by simp
  have votes: "fresh_votes ?b c (node_term ?b c) (durable_history ?b c) J"
    using dynamic_snapshot_votes[of J K] current joined no_accept by auto
  have step: "transition C ?b (?b\<lparr>publication_tip := (publication_tip ?b)((c,t) := hist),
     publications := insert hist (publications ?b)\<rparr>)"
    using transition.publish[OF dynamic_candidate_active(2)[OF ord elect] tip inc guard proposal(1) votes]
      unchanged current by simp
  have "dynamic_snapshot (insert a K) = ?b\<lparr>publication_tip := (publication_tip ?b)((c,t) := hist),
     publications := insert hist (publications ?b)\<rparr>"
    by (rule dynamic_state.equality) (use Register absent in \<open>auto simp: dynamic_snapshot_def fun_eq_iff\<close>)
  with step show ?thesis by simp
next
  case (Persist_Accept n)
  from ready_window_job[OF ready] Persist_Accept have reg: "Register \<in> K" and join: "Persist_Join n \<in> K"
    and absent: "Persist_Accept n \<notin> K" and part: "n \<in> insert c Q"
    by (auto simp: dynamic_dependencies_def dynamic_window_waves_def split: if_splits)
  let ?b = "dynamic_snapshot K"
  have inv: "journal_ok C s" using dynamic_invariants[OF reach] by blast
  have "term_of (durable_history s n) < t"
    using fresh_term[of n] part journalD(2)[OF inv, of n] by auto
  then have rank: "position (durable_history ?b n) < position hist"
    using absent by (simp add: dynamic_snapshot_def rank_less_iff)
  have pub: "hist \<in> publications ?b" and current: "term_of hist = node_term ?b n"
    using reg join by (simp_all add: dynamic_snapshot_def)
  have step: "transition C ?b (?b\<lparr>durable_history := (durable_history ?b)(n := hist),
    committed_config := (committed_config ?b)(n := carried C hist),
    acknowledgements := insert (n,hist) (acknowledgements ?b)\<rparr>)"
    by (rule transition.receive[OF pub current rank])
  have "dynamic_snapshot (insert a K) = ?b\<lparr>durable_history := (durable_history ?b)(n := hist),
    committed_config := (committed_config ?b)(n := carried C hist),
    acknowledgements := insert (n,hist) (acknowledgements ?b)\<rparr>"
    by (rule dynamic_state.equality)
      (use Persist_Accept absent dynamic_apply_requires_accept[OF ord] in \<open>auto simp: dynamic_snapshot_def fun_eq_iff\<close>)
  with step show ?thesis by simp
next
  case Collect_Receipts
  from ready_window_job[OF ready] Collect_Receipts have accepts: "Persist_Accept ` Q \<subseteq> K"
    and absent: "Collect_Receipts \<notin> K" by (auto simp: dynamic_dependencies_def)
  have "Q \<noteq> {}" using joint_publication(1) by (auto simp: quorum_def majority_def)
  then obtain n where "n \<in> Q" by blast
  with accepts have "Persist_Accept n \<in> K" by blast
  from window_predecessors[OF ord this] have reg: "Register \<in> K"
    by (simp add: dynamic_dependencies_def)
  have elect: "Collect_Votes \<in> K" using window_predecessors[OF ord reg] by (auto simp: dynamic_dependencies_def)
  let ?b = "dynamic_snapshot K"
  note current = dynamic_candidate_active(1)[OF ord elect]
  have tip: "hist = publication_tip ?b (c,node_term ?b c)" and pub: "hist \<in> publications ?b"
    and term_check: "term_of hist = node_term ?b c" and owner: "owner hist = c"
    using current reg by (simp_all add: dynamic_snapshot_def)
  have got: "(n,hist) \<in> acknowledgements ?b" if "n \<in> Q" for n
    using accepts that by (auto simp: dynamic_snapshot_def)
  have received: "joint_receipts C ?b hist"
    unfolding joint_receipts_def by (rule exI[of _ Q]) (simp add: joint_publication got)
  have step: "transition C ?b (?b\<lparr>quorum_commits := insert hist (quorum_commits ?b)\<rparr>)"
    by (rule transition.certify[OF dynamic_candidate_active(2)[OF ord elect] tip pub term_check owner received])
  have "dynamic_snapshot (insert a K) = ?b\<lparr>quorum_commits := insert hist (quorum_commits ?b)\<rparr>"
    by (rule dynamic_state.equality) (use Collect_Receipts absent in \<open>simp_all add: dynamic_snapshot_def fun_eq_iff\<close>)
  with step show ?thesis by simp
next
  case Handle_Self_Commit
  from ready_window_job[OF ready] Handle_Self_Commit have commit: "Collect_Receipts \<in> K" and self: "Persist_Accept c \<in> K"
    by (auto simp: dynamic_dependencies_def)
  from window_predecessors[OF ord self] have reg: "Register \<in> K" and join: "Persist_Join c \<in> K"
    by (auto simp: dynamic_dependencies_def)
  let ?b = "dynamic_snapshot K"
  have committed: "durable_history ?b c \<in> quorum_commits ?b"
    and term_check: "term_of (durable_history ?b c) = node_term ?b c"
    and guard: "active_leader ?b c \<longrightarrow> durable_history ?b c = publication_tip ?b (c,node_term ?b c)"
    using commit self join reg by (simp_all add: dynamic_snapshot_def)
  have step: "transition C ?b (?b\<lparr>committed_config := (committed_config ?b)(c := config_of C (durable_history ?b c))\<rparr>)"
    by (rule transition.apply_commit[OF committed term_check guard])
  have "dynamic_snapshot (insert a K) = ?b\<lparr>committed_config := (committed_config ?b)(c := config_of C (durable_history ?b c))\<rparr>"
    by (rule dynamic_state.equality) (use Handle_Self_Commit self in \<open>auto simp: dynamic_snapshot_def fun_eq_iff\<close>)
  with step show ?thesis by simp
qed (simp_all add: dynamic_snapshot_def fun_eq_iff)

lemma dynamic_window_reachable:
  "dynamic_reachable C (dynamic_snapshot (finished sel i))"
proof (induction i)
  case 0
  show ?case using reach by (simp add: dynamic_snapshot_def)
next
  case (Suc i)
  from completed_work_change[of jobs deps sel i] show ?case
  proof (elim disjE exE conjE)
    assume "finished sel (Suc i) = finished sel i"
    then show ?thesis using Suc.IH by simp
  next
    fix a
    assume ready: "work_ready jobs deps (finished sel i) a"
      and update: "finished sel (Suc i) = insert a (finished sel i)"
    from dynamic_snapshot_step[OF ordered_completed_work ready] show ?thesis
      unfolding update by (elim disjE) (use Suc.IH in simp, rule dynamic_reachable.advance[OF Suc.IH])
  qed
qed

lemma dynamic_window_prefix:
  assumes service: "bounded_service jobs deps sel delay horizon"
    and waves: "waves = before @ rest" and time: "length before * delay \<le> horizon"
  shows "\<Union>(set before) \<subseteq> finished sel (length before * delay)"
  by (rule bounded_service_finishes_plan[OF service dynamic_window_wave_dependencies waves time])

theorem dynamic_window_elects:
  assumes "bounded_service jobs deps sel delay horizon" "4 * delay \<le> horizon"
  shows "certificate (dynamic_snapshot (finished sel (4 * delay))) (c,t) = Some ballot"
    "dynamic_reachable C (dynamic_snapshot (finished sel (4 * delay)))"
proof -
  from dynamic_window_prefix[OF assms(1), where before="take 4 waves" and rest="drop 4 waves"] assms(2)
  have "Collect_Votes \<in> finished sel (4 * delay)"
    by (auto simp: dynamic_window_waves_def numeral_eq_Suc)
  then show "certificate (dynamic_snapshot (finished sel (4 * delay))) (c,t) = Some ballot" by (simp add: dynamic_snapshot_def)
  show "dynamic_reachable C (dynamic_snapshot (finished sel (4 * delay)))" by (rule dynamic_window_reachable)
qed

theorem dynamic_window_commits:
  assumes "bounded_service jobs deps sel delay horizon" "7 * delay \<le> horizon"
  shows "hist \<in> quorum_commits (dynamic_snapshot (finished sel (7 * delay)))"
    "dynamic_reachable C (dynamic_snapshot (finished sel (7 * delay)))"
proof -
  from dynamic_window_prefix[OF assms(1), where before="take 7 waves" and rest="drop 7 waves"] assms(2)
  have "Collect_Receipts \<in> finished sel (7 * delay)"
    by (auto simp: dynamic_window_waves_def numeral_eq_Suc)
  then show "hist \<in> quorum_commits (dynamic_snapshot (finished sel (7 * delay)))" by (simp add: dynamic_snapshot_def)
  show "dynamic_reachable C (dynamic_snapshot (finished sel (7 * delay)))" by (rule dynamic_window_reachable)
qed

theorem dynamic_window_local_completion:
  assumes "bounded_service jobs deps sel delay horizon" "12 * delay \<le> horizon"
  shows "hist \<in> quorum_commits (dynamic_snapshot (finished sel (12 * delay)))"
    "durable_history (dynamic_snapshot (finished sel (12 * delay))) c = hist"
    "committed_config (dynamic_snapshot (finished sel (12 * delay))) c = D"
    "Run_Local \<in> finished sel (12 * delay)" "dynamic_window_slot (finished sel (12 * delay)) = None"
proof -
  from dynamic_window_prefix[OF assms(1), where before=waves and rest="[]"] assms(2)
  have all_work: "jobs \<subseteq> finished sel (12 * delay)"
    by (simp add: dynamic_window_waves_def numeral_eq_Suc)
  show "hist \<in> quorum_commits (dynamic_snapshot (finished sel (12 * delay)))"
    "durable_history (dynamic_snapshot (finished sel (12 * delay))) c = hist"
    "committed_config (dynamic_snapshot (finished sel (12 * delay))) c = D"
    "Run_Local \<in> finished sel (12 * delay)" "dynamic_window_slot (finished sel (12 * delay)) = None"
    using all_work by (auto simp: dynamic_snapshot_def dynamic_window_waves_def dynamic_window_slot_def)
qed

section \<open>Local application after the dynamic commit\<close>

definition dynamic_window_traffic :: "window_operation set \<Rightarrow> nat transport_item set" where
  "dynamic_window_traffic K =
    (if Register \<in> K then {Registered_State item payload} else {}) \<union>
    (if Collect_Receipts \<in> K then {Returned_Commit c \<lparr>rank_term = t, rank_version = v\<rparr>} else {})"

lemma dynamic_completed_worker_trace:
  assumes ord: "ordered_work jobs deps K" and ran: "Run_Local \<in> K"
  shows "\<exists>a. application_reachable c (dynamic_window_traffic K) (node_term s c) (position base) a
    \<and> installed a = Some \<lparr>rank_term = t, rank_version = v\<rparr>"
proof -
  from window_predecessors[OF ord ran] have sample: "Sample_Local \<in> K" by (simp add: dynamic_dependencies_def)
  from window_predecessors[OF ord sample] have queue: "Queue_Local \<in> K" by (simp add: dynamic_dependencies_def)
  from window_predecessors[OF ord queue] have handled: "Handle_Self_Commit \<in> K"
    by (simp add: dynamic_dependencies_def)
  from window_predecessors[OF ord handled] have "Collect_Receipts \<in> K" and self: "Persist_Accept c \<in> K"
    by (auto simp: dynamic_dependencies_def)
  from window_predecessors[OF ord self] have "Register \<in> K" by (auto simp: dynamic_dependencies_def)
  let ?H = "dynamic_window_traffic K"
  let ?k = "\<lparr>rank_term = t, rank_version = v\<rparr>"
  let ?q = "Apply_Request c ?k"
  let ?a = "application_initial (node_term s c) (position base)"
  let ?j = "?a\<lparr>app_term := t\<rparr>"
  let ?p = "?j\<lparr>app_accepted := ?k\<rparr>"
  let ?h = "?p\<lparr>offered := Some ?k, self_ready := insert ?q (self_ready ?p)\<rparr>"
  let ?u = "?h\<lparr>self_ready := self_ready ?h - {?q}, queued_applications := insert ?q (queued_applications ?h)\<rparr>"
  let ?m = "?u\<lparr>queued_applications := queued_applications ?u - {?q}, running_application := Some (?q,?k)\<rparr>"
  let ?f = "?m\<lparr>running_application := None, installed := Some ?k,
    application_successes := insert (incarnation ?m,?q,?k) (application_successes ?m)\<rparr>"
  have new: "node_term s c < t" by (rule fresh_term) simp
  have old: "term_of base < t"
    using dynamic_invariants[OF reach] journalD(2)[of C s c] new by (meson le_less_trans)
  have packet: "Registered_State item payload \<in> ?H" and returned: "Returned_Commit c ?k \<in> ?H"
    using \<open>Register \<in> K\<close> \<open>Collect_Receipts \<in> K\<close> by (simp_all add: dynamic_window_traffic_def)
  have join: "application_step c ?H ?a ?j"
    by (rule application_step.advance_term) (use new in \<open>simp add: application_initial_def\<close>)
  have accepted: "application_step c ?H ?j ?p"
    using application_step.accept[OF packet, where n=c and a="?j"] old by (simp add: application_initial_def)
  have handler: "application_step c ?H ?p ?h"
    by (rule application_step.handle_self[OF returned]) simp_all
  have queued: "application_step c ?H ?h ?u"
    by (rule application_step.queue_self) simp
  have sampled: "application_step c ?H ?u ?m"
    by (rule application_step.read_supplier) (simp_all add: application_initial_def)
  have applied: "application_step c ?H ?m ?f"
    by (rule application_step.apply_success) simp
  have "application_reachable c ?H (node_term s c) (position base) ?f"
    by (rule application_reachable.step[OF _ applied],
        rule application_reachable.step[OF _ sampled],
        rule application_reachable.step[OF _ queued],
        rule application_reachable.step[OF _ handler],
        rule application_reachable.step[OF _ accepted],
        rule application_reachable.step[OF _ join],
        rule application_reachable.initial)
  then show ?thesis by (intro exI[of _ ?f]) simp
qed

corollary dynamic_window_commits_and_applies:
  assumes "bounded_service jobs deps sel delay horizon" "12 * delay \<le> horizon"
  defines "K \<equiv> finished sel (12 * delay)"
  shows "dynamic_reachable C (dynamic_snapshot K)"
    "hist \<in> quorum_commits (dynamic_snapshot K) - quorum_commits s"
    "committed_config (dynamic_snapshot K) c = D" "dynamic_window_slot K = None"
    "\<exists>a. application_reachable c (dynamic_window_traffic K) (node_term s c) (position base) a
      \<and> installed a = Some \<lparr>rank_term = t, rank_version = v\<rparr>"
  using dynamic_window_local_completion[OF assms(1,2)] dynamic_window_reachable[of sel "12 * delay"] dynamic_window_history_is_new
    dynamic_completed_worker_trace[OF ordered_completed_work, of sel "12 * delay"]
  unfolding K_def by blast+

theorem recovered_dynamic_window_completes:
  assumes timer: "timer_window contenders c timer_base draws extra duration own_next pending drained window_length"
    and start: "start = timer_base c + draws c + extra c"
    and recovery: "episode_permission start episode" "episode_service episode"
    and chosen: "replacement_candidate (episode_round episode) = c" "episode_quorum episode = E"
      "committed_voters (episode_round episode) = committed_config s c"
      "accepted_voters (episode_round episode) = config_of C base"
    and budget: "3 * episode_delay episode + 12 * delay \<le> window_length"
    and service: "\<And>k. opens_attempt_at start episode k \<Longrightarrow>
      bounded_service jobs deps (schedule k) delay (12 * delay)"
  obtains k where "opens_attempt_at start episode k"
    "replacement_candidate (episode_round episode) = c" "episode_quorum episode = E"
    "k + 12 * delay \<le> start + window_length"
    "\<And>n. n \<in> contenders - {c} \<Longrightarrow> k + 12 * delay < timer_base n + draws n + extra n"
    "\<And>deadline. deadline \<in> pending \<Longrightarrow> k + 12 * delay < deadline"
    "k + 12 * delay < start + duration + own_next"
    "hist \<in> quorum_commits (dynamic_snapshot (finished (schedule k) (12 * delay))) - quorum_commits s"
    "committed_config (dynamic_snapshot (finished (schedule k) (12 * delay))) c = D"
    "dynamic_window_slot (finished (schedule k) (12 * delay)) = None"
    "\<exists>a. application_reachable c (dynamic_window_traffic (finished (schedule k) (12 * delay))) (node_term s c) (position base) a
      \<and> installed a = Some \<lparr>rank_term = t, rank_version = v\<rparr>"
proof -
  obtain k where attempt: "opens_attempt_at start episode k"
    and fits: "k + 12 * delay \<le> start + window_length"
    and peers: "\<And>n. n \<in> contenders - {c} \<Longrightarrow> k + 12 * delay < timer_base n + draws n + extra n"
    and armed: "\<And>deadline. deadline \<in> pending \<Longrightarrow> k + 12 * delay < deadline"
    and own: "k + 12 * delay < start + duration + own_next"
    by (rule recovered_attempt_fits_timer_window[OF timer start recovery budget]) blast
  note complete = dynamic_window_commits_and_applies[OF service[OF attempt] le_refl]
  show thesis by (rule that[OF attempt chosen(1,2) fits peers armed own complete(2-5)])
qed

end

end
