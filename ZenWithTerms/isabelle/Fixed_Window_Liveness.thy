theory Fixed_Window_Liveness
  imports Bounded_Service Fixed_Configuration Commit_Application
begin

section \<open>Work in one fixed-configuration window\<close>

datatype window_operation =
    Prevote node
  | Choose_Term
  | Persist_Join node
  | Collect_Votes
  | Register
  | Persist_Accept node
  | Collect_Receipts
  | Handle_Self_Commit
  | Finish_Target node
  | End_Target_Wait
  | Queue_Local
  | Sample_Local
  | Run_Local
  | Release_Slot

definition window_jobs where
  "window_jobs fresh E Q T c cancel_wait =
    (if fresh then Prevote ` E \<union> {Choose_Term, Collect_Votes} \<union> Persist_Join ` (insert c (E \<union> Q)) else {})
    \<union> {Register, Collect_Receipts, Handle_Self_Commit, Queue_Local, Sample_Local, Run_Local, Release_Slot}
    \<union> Persist_Accept ` (insert c Q)
    \<union> (if cancel_wait then {End_Target_Wait} else Finish_Target ` (T - {c}))"

fun window_dependencies where
  "window_dependencies fresh E Q T c cancel_wait (Prevote n) = {}"
| "window_dependencies fresh E Q T c cancel_wait Choose_Term = Prevote ` E"
| "window_dependencies fresh E Q T c cancel_wait (Persist_Join n) = {Choose_Term}"
| "window_dependencies fresh E Q T c cancel_wait Collect_Votes = Persist_Join ` (insert c E)"
| "window_dependencies fresh E Q T c cancel_wait Register = (if fresh then {Collect_Votes} else {})"
| "window_dependencies fresh E Q T c cancel_wait (Persist_Accept n) =
    (if fresh then {Register, Persist_Join n} else {Register})"
| "window_dependencies fresh E Q T c cancel_wait Collect_Receipts = Persist_Accept ` Q"
| "window_dependencies fresh E Q T c cancel_wait Handle_Self_Commit = {Collect_Receipts, Persist_Accept c}"
| "window_dependencies fresh E Q T c cancel_wait (Finish_Target n) = {Collect_Receipts}"
| "window_dependencies fresh E Q T c cancel_wait End_Target_Wait = {Collect_Receipts}"
| "window_dependencies fresh E Q T c cancel_wait Queue_Local =
    insert Handle_Self_Commit (if cancel_wait then {End_Target_Wait} else Finish_Target ` (T - {c}))"
| "window_dependencies fresh E Q T c cancel_wait Sample_Local = {Queue_Local}"
| "window_dependencies fresh E Q T c cancel_wait Run_Local = {Sample_Local}"
| "window_dependencies fresh E Q T c cancel_wait Release_Slot = {Run_Local}"

definition window_history where
  "window_history s c t v u = accepted s c @ [(t,v,u)]"

definition window_state where
  "window_state s c t E h D = s\<lparr>
     current := (\<lambda>n. if Persist_Join n \<in> D then t else current s n),
     accepted := (\<lambda>n. if Persist_Accept n \<in> D then h else accepted s n),
     joins := joins s \<union> {(n,c,t,accepted s n) |n. Persist_Join n \<in> D},
     started := started s \<union> {n. Persist_Join n \<in> D},
     active := (active s - {n. Persist_Join n \<in> D}) \<union> (if Collect_Votes \<in> D then {c} else {}),
     leader := (if Collect_Votes \<in> D then (leader s)(t := Some c) else leader s),
     electors := (if Collect_Votes \<in> D then (electors s)(t := E) else electors s),
     tip := (if Register \<in> D then (tip s)(t := h)
       else if Collect_Votes \<in> D then (tip s)(t := accepted s c) else tip s),
     published := (if Register \<in> D then insert h (published s) else published s),
     receipts := receipts s \<union> {(n,h) |n. Persist_Accept n \<in> D},
     committed := (if Collect_Receipts \<in> D then insert h (committed s) else committed s)\<rparr>"

text \<open>
  Prevote abstracts a response from a discovered healthy peer whose
  leader observation does not veto this candidate. The chosen term
  exceeds the participating peers' durable current terms. Persist_Join
  records an actual durable term advance. The certificate transitions
  use the same majority tests as the fixed-configuration safety model.
  The other election and publication work which would invalidate this
  window belongs to the recovery and scheduling interface.

  After quorum commit the publisher still needs its self reply and the
  publication-completion callback. In the normal path all other targets
  must become terminal. In the cancellation path the target wait ends
  without those replies, but the publisher still needs its self reply
  and its local application callback. The cancellation path models
  post-commit cancellation only. The pre-commit deadline is a separate
  bound, and must exclude cancellation before quorum commit.
\<close>

locale fixed_publication_window =
  fixes V E Q T :: "node set" and c :: node and t v u :: nat and s :: coordination
    and fresh cancel_wait :: bool
  assumes reach: "reachable V s"
    and election_quorum: "majority V E"
    and publication_quorum: "majority V Q"
    and viable_candidate: "c \<in> V" "c \<in> T" "finite T" "Q \<subseteq> T"
    and newer_version: "version (accepted s c) < v"
    and clean_term: "\<And>n. fresh \<Longrightarrow> n \<in> insert c (E \<union> Q) \<Longrightarrow> current s n < t"
    and vote_freshness: "\<And>n. fresh \<Longrightarrow> n \<in> E \<Longrightarrow> accepted s n \<preceq> accepted s c"
    and incumbent: "\<not> fresh \<Longrightarrow> c \<in> active s \<and> leader s t = Some c \<and> tip s t = accepted s c"
    and acceptance_term: "\<And>n. \<not> fresh \<Longrightarrow> n \<in> insert c Q \<Longrightarrow>
      current s n = t \<and> (epoch (accepted s n) < t \<or> (epoch (accepted s n) = t \<and> version (accepted s n) < v))"
begin

abbreviation jobs where "jobs \<equiv> window_jobs fresh E Q T c cancel_wait"
abbreviation deps where "deps \<equiv> window_dependencies fresh E Q T c cancel_wait"
abbreviation h where "h \<equiv> window_history s c t v u"
abbreviation core where "core \<equiv> window_state s c t E h"
abbreviation finished where "finished select \<equiv> completed_work jobs deps select"

lemma window_history_fields [simp]: "epoch h = t" "version h = v"
  by (simp_all add: window_history_def)

lemma clean_term_has_no_leader:
  assumes fresh: fresh
  shows "leader s t = None"
proof (cases "leader s t")
  case (Some d)
  have inv: "well_formed V s" by (rule reachable_wf[OF reach])
  from majority_intersects[OF election_quorum wfD(9)[OF inv Some]] obtain n where
    q: "n \<in> E" "n \<in> electors s t" by blast
  from wfD(11)[OF inv Some q(2)] obtain a where "(n,d,t,a) \<in> joins s" by blast
  from wfD(5)[OF inv this] clean_term[OF fresh, of n] q(1) show ?thesis by auto
qed simp

lemma window_orderD:
  assumes "ordered_work jobs deps D"
  shows "a \<in> D \<Longrightarrow> a \<in> jobs"
    "a \<in> D \<Longrightarrow> deps a \<subseteq> D"
  using assms unfolding ordered_work_def by blast+

lemma window_readyD:
  assumes "work_ready jobs deps D a"
  shows "a \<in> jobs" "a \<notin> D" "deps a \<subseteq> D"
  using assms by (simp_all add: work_ready_def)

lemma election_snapshot:
  assumes ord: "ordered_work jobs deps D" and either: "\<not> fresh \<or> Collect_Votes \<in> D"
  shows "c \<in> active (core D)" "leader (core D) t = Some c" "current (core D) c = t"
proof -
  have "c \<in> active (core D) \<and> leader (core D) t = Some c \<and> current (core D) c = t"
  proof (cases fresh)
    case True
    with either have elected: "Collect_Votes \<in> D" by simp
    have joined: "Persist_Join c \<in> D" using window_orderD(2)[OF ord elected] by auto
    from elected joined show ?thesis by (simp add: window_state_def)
  next
    case False
    from window_orderD(1)[OF ord, of Collect_Votes] window_orderD(1)[OF ord, of "Persist_Join c"] False
    have absent: "Collect_Votes \<notin> D" "Persist_Join c \<notin> D"
      by (auto simp: window_jobs_def split: if_splits)
    from absent incumbent[OF False] acceptance_term[OF False, of c]
    show ?thesis by (auto simp: window_state_def)
  qed
  then show "c \<in> active (core D)" "leader (core D) t = Some c" "current (core D) c = t" by simp_all
qed

lemma window_core_step:
  assumes ord: "ordered_work jobs deps D" and ready_op: "work_ready jobs deps D a"
  shows "core (insert a D) = core D \<or> step V (core D) (core (insert a D))"
proof (cases a)
  case (Persist_Join n)
  from window_readyD[OF ready_op] Persist_Join have fresh: fresh and part: "n \<in> insert c (E \<union> Q)" and absent: "Persist_Join n \<notin> D"
    by (auto simp: window_jobs_def split: if_splits)
  have unaccepted: "Persist_Accept n \<notin> D"
    using window_orderD(2)[OF ord, of "Persist_Accept n"] fresh absent by auto
  have own: "Collect_Votes \<in> D \<Longrightarrow> n \<noteq> c"
    using window_orderD(2)[OF ord, of Collect_Votes] absent by auto
  have cur: "current (core D) n < t"
    using clean_term[OF fresh part] absent by (simp add: window_state_def)
  have action: "step V (core D) ((core D)\<lparr>current := (current (core D))(n := t),
    joins := insert (n,c,t,accepted (core D) n) (joins (core D)),
    started := insert n (started (core D)), active := active (core D) - {n}\<rparr>)"
    by (rule step.join[OF cur])
  have "core (insert a D) = (core D)\<lparr>current := (current (core D))(n := t),
    joins := insert (n,c,t,accepted (core D) n) (joins (core D)),
    started := insert n (started (core D)), active := active (core D) - {n}\<rparr>"
    by (rule coordination.equality) (use Persist_Join unaccepted own in \<open>auto simp: window_state_def fun_eq_iff\<close>)
  with action show ?thesis by simp
next
  case Collect_Votes
  from window_readyD[OF ready_op] Collect_Votes have fresh: fresh and never: "Collect_Votes \<notin> D"
    and joined: "n \<in> insert c E \<Longrightarrow> Persist_Join n \<in> D" for n
    by (auto simp: window_jobs_def split: if_splits)
  have unregistered: "Register \<notin> D"
    using window_orderD(2)[OF ord, of Register] fresh never by auto
  have unaccepted: "Persist_Accept c \<notin> D"
    using window_orderD(2)[OF ord, of "Persist_Accept c"] unregistered by (cases fresh) auto
  let ?b = "core D"
  have cterm: "t = current ?b c" and started: "c \<in> started ?b" and own: "(c,c,t,accepted s c) \<in> joins ?b"
    using joined[of c] by (auto simp: window_state_def)
  have none: "leader ?b t = None"
    using clean_term_has_no_leader[OF fresh] never by (simp add: window_state_def)
  have votes: "\<forall>n\<in>E. \<exists>b. (n,c,t,b) \<in> joins ?b \<and> b \<preceq> accepted ?b c"
    using vote_freshness[OF fresh] joined unaccepted by (auto simp: window_state_def)
  have action: "step V ?b (?b\<lparr>leader := (leader ?b)(t := Some c), electors := (electors ?b)(t := E),
    tip := (tip ?b)(t := accepted ?b c), active := insert c (active ?b)\<rparr>)"
    by (rule step.elect[OF started cterm none election_quorum votes]) (use own in blast)
  have "core (insert a D) = ?b\<lparr>leader := (leader ?b)(t := Some c), electors := (electors ?b)(t := E),
    tip := (tip ?b)(t := accepted ?b c), active := insert c (active ?b)\<rparr>"
    by (rule coordination.equality)
      (use Collect_Votes never unregistered unaccepted in \<open>auto simp: window_state_def\<close>)
  with action show ?thesis by simp
next
  case Register
  from window_readyD[OF ready_op] Register have not_registered: "Register \<notin> D" and elected: "\<not> fresh \<or> Collect_Votes \<in> D"
    by (auto split: if_splits)
  have not_accepted: "Persist_Accept c \<notin> D"
    using window_orderD(2)[OF ord, of "Persist_Accept c"] not_registered by (cases fresh) auto
  let ?b = "core D"
  have tip: "tip ?b t = accepted ?b c" "accepted ?b c = accepted s c"
    using incumbent not_registered not_accepted elected by (auto simp: window_state_def)
  have grow: "version (tip ?b t) < v" using tip newer_version by simp
  have action: "step V ?b (?b\<lparr>tip := (tip ?b)(t := h), published := insert h (published ?b)\<rparr>)"
    by (rule step.propose[OF election_snapshot(1)[OF ord elected] _ election_snapshot(2)[OF ord elected] tip(1) grow])
      (use election_snapshot(3)[OF ord elected] tip in \<open>simp_all add: window_history_def\<close>)
  have "core (insert a D) = ?b\<lparr>tip := (tip ?b)(t := h), published := insert h (published ?b)\<rparr>"
    by (rule coordination.equality) (use Register not_registered in \<open>auto simp: window_state_def\<close>)
  with action show ?thesis by simp
next
  case (Persist_Accept n)
  from window_readyD[OF ready_op] Persist_Accept have ready: "Register \<in> D" "Persist_Accept n \<notin> D"
    "n \<in> insert c Q" "fresh \<Longrightarrow> Persist_Join n \<in> D"
    by (auto simp: window_jobs_def split: if_splits)
  let ?b = "core D"
  have pub: "h \<in> published ?b" using ready(1) by (simp add: window_state_def)
  have checked: "epoch h = current ?b n \<and>
    (epoch (accepted ?b n) < epoch h \<or>
     epoch (accepted ?b n) = epoch h \<and> version (accepted ?b n) < version h)"
  proof (cases fresh)
    case True
    have "epoch (accepted s n) < t"
      using le_less_trans[OF wfD(2)[OF reachable_wf[OF reach], of n] clean_term[OF True, of n]] ready(3) by auto
    with True ready show ?thesis by (simp add: window_state_def)
  next
    case False
    from window_orderD(1)[OF ord, of "Persist_Join n"] False have no_join: "Persist_Join n \<notin> D"
      by (auto simp: window_jobs_def split: if_splits)
    from acceptance_term[OF False ready(3)] ready(2) no_join show ?thesis
      by (simp add: window_state_def)
  qed
  have action: "step V ?b (?b\<lparr>accepted := (accepted ?b)(n := h), receipts := insert (n,h) (receipts ?b)\<rparr>)"
    by (rule step.accept[OF pub checked[THEN conjunct1] checked[THEN conjunct2]])
  have "core (insert a D) = ?b\<lparr>accepted := (accepted ?b)(n := h), receipts := insert (n,h) (receipts ?b)\<rparr>"
    by (rule coordination.equality) (use Persist_Accept in \<open>auto simp: window_state_def fun_eq_iff\<close>)
  with action show ?thesis by simp
next
  case Collect_Receipts
  from window_readyD[OF ready_op] Collect_Receipts have no_commit: "Collect_Receipts \<notin> D" and accepted: "n \<in> Q \<Longrightarrow> Persist_Accept n \<in> D" for n by auto
  have "Q \<noteq> {}" using publication_quorum unfolding majority_def by auto
  then obtain n where "n \<in> Q" by blast
  from window_orderD(2)[OF ord accepted[OF this]] have registered: "Register \<in> D" by (cases fresh) auto
  from window_orderD(2)[OF ord registered] have elect: "\<not> fresh \<or> Collect_Votes \<in> D" by (cases fresh) auto
  let ?b = "core D"
  have pub: "tip ?b t \<in> published ?b" "epoch (tip ?b t) = t"
    using registered by (simp_all add: window_state_def)
  have receipts: "\<forall>n\<in>Q. (n,tip ?b t) \<in> receipts ?b"
    using registered accepted by (auto simp: window_state_def)
  have action: "step V ?b (?b\<lparr>committed := insert (tip ?b t) (committed ?b)\<rparr>)"
    by (rule step.commit[OF election_snapshot(1)[OF ord elect] _ election_snapshot(2)[OF ord elect] pub publication_quorum receipts])
      (simp add: election_snapshot(3)[OF ord elect])
  have "core (insert a D) = ?b\<lparr>committed := insert (tip ?b t) (committed ?b)\<rparr>"
    by (rule coordination.equality) (use Collect_Receipts registered no_commit in \<open>auto simp: window_state_def\<close>)
  with action show ?thesis by simp
qed (simp_all add: window_state_def)

lemma window_core_trace:
  "core (finished select (Suc i)) = core (finished select i) \<or> step V (core (finished select i)) (core (finished select (Suc i)))"
  using completed_work_change[of jobs deps select i]
proof (elim disjE)
  assume "finished select (Suc i) = finished select i"
  then show ?thesis by simp
next
  assume "\<exists>a. select i = Some a \<and> work_ready jobs deps (finished select i) a \<and>
    finished select (Suc i) = insert a (finished select i)"
  then obtain a where ready: "work_ready jobs deps (finished select i) a"
    and update: "finished select (Suc i) = insert a (finished select i)" by blast
  show ?thesis unfolding update by (rule window_core_step[OF ordered_completed_work ready])
qed

lemma window_core_reachable: "reachable V (core (finished select i))"
proof (induction i)
  case 0
  show ?case using reach by (simp add: window_state_def)
next
  case (Suc i)
  from window_core_trace[of select i] show ?case
    by (elim disjE) (use Suc.IH in simp, rule reachable.advance[OF Suc.IH])
qed


section \<open>Election and publication deadlines\<close>

definition window_slot where
  "window_slot D = (if Register \<in> D \<and> Release_Slot \<notin> D then Some h else None)"

lemma scheduled_group:
  assumes "bounded_service jobs deps select delay horizon" "i + delay \<le> horizon"
    and "\<And>a. a \<in> A \<Longrightarrow> a \<in> jobs"
    and "\<And>a. a \<in> A \<Longrightarrow> deps a \<subseteq> finished select i"
  shows "A \<subseteq> finished select (i + delay)"
  using assms by (intro bounded_service_finishes_group) auto

lemma scheduled_one:
  assumes "bounded_service jobs deps select delay horizon" "i + delay \<le> horizon"
    "a \<in> jobs" "deps a \<subseteq> finished select i"
  shows "a \<in> finished select (i + delay)"
  using scheduled_group[OF assms(1,2), of "{a}"] assms(3,4) by simp

lemma window_election_work:
  assumes fresh: fresh and service: "bounded_service jobs deps select delay horizon" and time: "4 * delay \<le> horizon"
  shows "Collect_Votes \<in> finished select (4 * delay)"
    "Persist_Join ` insert c (E \<union> Q) \<subseteq> finished select (4 * delay)"
proof -
  have bounds: "0 + delay \<le> horizon" "delay + delay \<le> horizon"
    "(delay + delay) + delay \<le> horizon" "((delay + delay) + delay) + delay \<le> horizon"
    using time by linarith+
  have prevote: "Prevote ` E \<subseteq> finished select (0 + delay)"
    by (rule scheduled_group[OF service bounds(1)]) (use fresh in \<open>auto simp: window_jobs_def split: if_splits\<close>)
  have term_fact: "Choose_Term \<in> finished select (delay + delay)"
    by (rule scheduled_one[OF service bounds(2)]) (use fresh prevote in \<open>auto simp: window_jobs_def split: if_splits\<close>)
  have joins: "Persist_Join ` insert c (E \<union> Q) \<subseteq> finished select ((delay + delay) + delay)"
    by (rule scheduled_group[OF service bounds(3)]) (use term_fact fresh in \<open>auto simp: window_jobs_def split: if_splits\<close>)
  have votes: "Collect_Votes \<in> finished select (((delay + delay) + delay) + delay)"
    by (rule scheduled_one[OF service bounds(4)]) (use joins fresh in \<open>auto simp: window_jobs_def split: if_splits\<close>)
  have "((delay + delay) + delay) + delay = 4 * delay" by linarith
  with votes show "Collect_Votes \<in> finished select (4 * delay)" by simp
  have "((delay + delay) + delay) \<le> 4 * delay" by linarith
  from joins completed_work_mono[OF this, of jobs deps select]
  show "Persist_Join ` insert c (E \<union> Q) \<subseteq> finished select (4 * delay)" by blast
qed

theorem fixed_candidate_wins_by_deadline:
  assumes "fresh" "bounded_service jobs deps select delay horizon" "4 * delay \<le> horizon"
  shows "leader (core (finished select (4 * delay))) t = Some c"
    "c \<in> active (core (finished select (4 * delay)))"
    "reachable V (core (finished select (4 * delay)))"
proof -
  have "\<not> fresh \<or> Collect_Votes \<in> finished select (4 * delay)" using window_election_work[OF assms] by simp
  from election_snapshot[OF ordered_completed_work this]
  show "leader (core (finished select (4 * delay))) t = Some c"
    "c \<in> active (core (finished select (4 * delay)))" by simp_all
  show "reachable V (core (finished select (4 * delay)))" by (rule window_core_reachable)
qed

lemma window_commit_work:
  assumes service: "bounded_service jobs deps select delay horizon"
    and time: "i + 3 * delay \<le> horizon"
    and elected: "\<not> fresh \<or> Collect_Votes \<in> finished select i"
    and joined: "fresh \<Longrightarrow> Persist_Join ` insert c Q \<subseteq> finished select i"
  shows "Register \<in> finished select (i + delay)"
    "Persist_Accept ` insert c Q \<subseteq> finished select ((i + delay) + delay)"
    "Collect_Receipts \<in> finished select (i + 3 * delay)"
proof -
  have bounds: "i + delay \<le> horizon" "(i + delay) + delay \<le> horizon"
    "((i + delay) + delay) + delay \<le> horizon" using time by linarith+
  show registered: "Register \<in> finished select (i + delay)"
    by (rule scheduled_one[OF service bounds(1)]) (use elected in \<open>auto simp: window_jobs_def split: if_splits\<close>)
  have growth: "finished select i \<subseteq> finished select (i + delay)"
    by (rule completed_work_mono) simp
  have joined': "fresh \<Longrightarrow> Persist_Join ` insert c Q \<subseteq> finished select (i + delay)"
    using joined growth by blast
  show accepted: "Persist_Accept ` insert c Q \<subseteq> finished select ((i + delay) + delay)"
  proof (rule scheduled_group[OF service bounds(2)])
    fix a
    assume a: "a \<in> Persist_Accept ` insert c Q"
    then show "a \<in> jobs" by (auto simp: window_jobs_def)
    from a obtain n where n: "n \<in> insert c Q" and op: "a = Persist_Accept n" by blast
    show "deps a \<subseteq> finished select (i + delay)"
    proof (cases fresh)
      case True
      have "Persist_Join n \<in> finished select (i + delay)"
        by (rule subsetD[OF joined'[OF True] imageI[OF n]])
      with True op registered show ?thesis by simp
    next
      case False
      with op registered show ?thesis by simp
    qed
  qed
  have "Persist_Accept ` Q \<subseteq> finished select ((i + delay) + delay)" using accepted by blast
  have cert: "Collect_Receipts \<in> finished select (((i + delay) + delay) + delay)"
    by (rule scheduled_one[OF service bounds(3)]) (use \<open>Persist_Accept ` Q \<subseteq> finished select ((i + delay) + delay)\<close>
      in \<open>simp_all add: window_jobs_def\<close>)
  have "((i + delay) + delay) + delay = i + 3 * delay" by linarith
  with cert show "Collect_Receipts \<in> finished select (i + 3 * delay)" by simp
qed

theorem fixed_first_publication_commits_by_deadline:
  assumes fresh: fresh and service: "bounded_service jobs deps select delay horizon"
    and time: "7 * delay \<le> horizon"
  shows "h \<in> committed (core (finished select (7 * delay)))"
    "reachable V (core (finished select (7 * delay)))"
proof -
  have time4: "4 * delay \<le> horizon" and time7: "4 * delay + 3 * delay \<le> horizon" using time by linarith+
  from window_election_work[OF fresh service time4] have elected:
    "\<not> fresh \<or> Collect_Votes \<in> finished select (4 * delay)"
    and joined: "fresh \<Longrightarrow> Persist_Join ` insert c Q \<subseteq> finished select (4 * delay)" by auto
  have eq: "4 * delay + 3 * delay = 7 * delay" by linarith
  from window_commit_work(3)[OF service time7 elected joined] show "h \<in> committed (core (finished select (7 * delay)))"
    by (simp add: window_state_def eq)
  show "reachable V (core (finished select (7 * delay)))" by (rule window_core_reachable)
qed

theorem fixed_incumbent_commits_by_deadline:
  assumes not_fresh: "\<not> fresh" and service: "bounded_service jobs deps select delay horizon"
    and time: "3 * delay \<le> horizon"
  shows "h \<in> committed (core (finished select (3 * delay)))"
    "reachable V (core (finished select (3 * delay)))"
proof -
  have elected: "\<not> fresh \<or> Collect_Votes \<in> finished select 0"
    and joined: "fresh \<Longrightarrow> Persist_Join ` insert c Q \<subseteq> finished select 0" using not_fresh by auto
  have time3: "0 + 3 * delay \<le> horizon" using time by simp
  from window_commit_work(3)[OF service time3 elected joined]
  show "h \<in> committed (core (finished select (3 * delay)))" by (simp add: window_state_def)
  show "reachable V (core (finished select (3 * delay)))" by (rule window_core_reachable)
qed

lemma window_completion_work:
  assumes service: "bounded_service jobs deps select delay horizon"
    and time: "i + 5 * delay \<le> horizon"
    and committed: "Collect_Receipts \<in> finished select i"
    and self: "Persist_Accept c \<in> finished select i"
  shows "Run_Local \<in> finished select (i + 4 * delay)"
    "Release_Slot \<in> finished select (i + 5 * delay)"
proof -
  let ?i1 = "i + delay"
  let ?i2 = "?i1 + delay"
  let ?i3 = "?i2 + delay"
  let ?i4 = "?i3 + delay"
  let ?i5 = "?i4 + delay"
  have bound: "?i1 \<le> horizon" "?i2 \<le> horizon" "?i3 \<le> horizon" "?i4 \<le> horizon" "?i5 \<le> horizon"
    using time by linarith+
  have first: "deps Queue_Local \<subseteq> finished select ?i1"
    by (rule scheduled_group[OF service bound(1)]) (use committed self in \<open>auto simp: window_jobs_def split: if_splits\<close>)
  have local_queue: "Queue_Local \<in> finished select ?i2"
    by (rule scheduled_one[OF service bound(2) _ first]) (simp add: window_jobs_def)
  have sampled: "Sample_Local \<in> finished select ?i3"
    by (rule scheduled_one[OF service bound(3)]) (use local_queue in \<open>auto simp: window_jobs_def split: if_splits\<close>)
  have applied: "Run_Local \<in> finished select ?i4"
    by (rule scheduled_one[OF service bound(4)]) (use sampled in \<open>auto simp: window_jobs_def split: if_splits\<close>)
  have released: "Release_Slot \<in> finished select ?i5"
    by (rule scheduled_one[OF service bound(5)]) (use applied in \<open>auto simp: window_jobs_def split: if_splits\<close>)
  have eq: "?i4 = i + 4 * delay" "?i5 = i + 5 * delay" by linarith+
  show "Run_Local \<in> finished select (i + 4 * delay)" using applied eq(1) by metis
  show "Release_Slot \<in> finished select (i + 5 * delay)" using released eq(2) by metis
qed

lemma window_publication_finishes:
  assumes service: "bounded_service jobs deps select delay horizon"
    and time: "i + 8 * delay \<le> horizon"
    and elected: "\<not> fresh \<or> Collect_Votes \<in> finished select i"
    and joined: "fresh \<Longrightarrow> Persist_Join ` insert c Q \<subseteq> finished select i"
  shows "h \<in> committed (core (finished select (i + 8 * delay)))"
    "Run_Local \<in> finished select (i + 8 * delay)"
    "window_slot (finished select (i + 8 * delay)) = None"
proof -
  have bound: "i + 3 * delay \<le> horizon" "(i + 3 * delay) + 5 * delay \<le> horizon"
    "(i + delay) + delay \<le> i + 3 * delay" "i + 3 * delay \<le> i + 8 * delay"
    "(i + 3 * delay) + 4 * delay \<le> i + 8 * delay" using time by linarith+
  from window_commit_work[OF service bound(1) elected joined] have
    self: "Persist_Accept c \<in> finished select ((i + delay) + delay)"
    and commit: "Collect_Receipts \<in> finished select (i + 3 * delay)" by auto
  from self completed_work_mono[OF bound(3), of jobs deps select]
  have "Persist_Accept c \<in> finished select (i + 3 * delay)" by blast
  from window_completion_work[OF service bound(2) commit this]
  have applied: "Run_Local \<in> finished select ((i + 3 * delay) + 4 * delay)"
    and release: "Release_Slot \<in> finished select ((i + 3 * delay) + 5 * delay)" by simp_all
  from commit completed_work_mono[OF bound(4), of jobs deps select]
  have "Collect_Receipts \<in> finished select (i + 8 * delay)" by blast
  then show "h \<in> committed (core (finished select (i + 8 * delay)))"
    by (simp add: window_state_def)
  from applied completed_work_mono[OF bound(5), of jobs deps select]
  show "Run_Local \<in> finished select (i + 8 * delay)" by blast
  have eq: "(i + 3 * delay) + 5 * delay = i + 8 * delay" by linarith
  have "Release_Slot \<in> finished select (i + 8 * delay)" using eq release by metis
  then show "window_slot (finished select (i + 8 * delay)) = None"
    by (simp add: window_slot_def)
qed

theorem fixed_first_publication_applied_and_slot_free:
  assumes fresh: fresh and service: "bounded_service jobs deps select delay horizon" and time: "12 * delay \<le> horizon"
  shows "h \<in> committed (core (finished select (12 * delay)))"
    "Run_Local \<in> finished select (12 * delay)"
    "window_slot (finished select (12 * delay)) = None"
proof -
  have time4: "4 * delay \<le> horizon" and time12: "4 * delay + 8 * delay \<le> horizon" using time by linarith+
  from window_election_work[OF fresh service time4] have elected:
    "\<not> fresh \<or> Collect_Votes \<in> finished select (4 * delay)"
    and joined: "fresh \<Longrightarrow> Persist_Join ` insert c Q \<subseteq> finished select (4 * delay)" by auto
  have eq: "4 * delay + 8 * delay = 12 * delay" by linarith
  from window_publication_finishes[OF service time12 elected joined]
  show "h \<in> committed (core (finished select (12 * delay)))" "Run_Local \<in> finished select (12 * delay)"
    "window_slot (finished select (12 * delay)) = None" by (simp_all add: eq)
qed

theorem fixed_incumbent_applies_and_releases_slot:
  assumes not_fresh: "\<not> fresh" and service: "bounded_service jobs deps select delay horizon"
    and time: "8 * delay \<le> horizon"
  shows "h \<in> committed (core (finished select (8 * delay)))"
    "Run_Local \<in> finished select (8 * delay)"
    "window_slot (finished select (8 * delay)) = None"
proof -
  have elected: "\<not> fresh \<or> Collect_Votes \<in> finished select 0"
    and joined: "fresh \<Longrightarrow> Persist_Join ` insert c Q \<subseteq> finished select 0" using not_fresh by auto
  have time8: "0 + 8 * delay \<le> horizon" using time by simp
  from window_publication_finishes[OF service time8 elected joined]
  show "h \<in> committed (core (finished select (8 * delay)))" "Run_Local \<in> finished select (8 * delay)"
    "window_slot (finished select (8 * delay)) = None" by simp_all
qed


section \<open>Local application projection\<close>

abbreviation key where "key \<equiv> \<lparr>rank_term = t, rank_version = v\<rparr>"
abbreviation old_key where "old_key \<equiv> \<lparr>rank_term = epoch (accepted s c), rank_version = version (accepted s c)\<rparr>"
abbreviation packet where "packet \<equiv> request c t v V V"
abbreviation apply_request where "apply_request \<equiv> Apply_Request c key"
definition window_traffic :: "nat transport_item set" where
  "window_traffic = {Registered_State packet u, Returned_Commit c key}"

definition window_applier where
  "window_applier D = (application_initial (current s c) old_key)\<lparr>
    app_term := (if Persist_Join c \<in> D then t else current s c),
    app_accepted := (if Persist_Accept c \<in> D then key else old_key),
    offered := (if Handle_Self_Commit \<in> D then Some key else None),
    self_ready := (if Handle_Self_Commit \<in> D \<and> Queue_Local \<notin> D then {apply_request} else {}),
    queued_applications := (if Queue_Local \<in> D \<and> Sample_Local \<notin> D then {apply_request} else {}),
    running_application := (if Sample_Local \<in> D \<and> Run_Local \<notin> D then Some (apply_request,key) else None),
    installed := (if Run_Local \<in> D then Some key else None),
    application_successes := (if Run_Local \<in> D then {(0,apply_request,key)} else {})\<rparr>"

lemma local_term_if_accepted:
  assumes ord: "ordered_work jobs deps D" and accepted: "Persist_Accept c \<in> D"
  shows "app_term (window_applier D) = t"
  using acceptance_term[of c] window_orderD(2)[OF ord accepted]
  by (cases fresh) (auto simp: window_applier_def)

lemma window_applier_step:
  assumes ord: "ordered_work jobs deps D" and ready_op: "work_ready jobs deps D a"
  shows "window_applier (insert a D) = window_applier D \<or>
    application_step c window_traffic (window_applier D) (window_applier (insert a D))"
proof (cases a)
  case (Persist_Join n)
  show ?thesis
  proof (cases "n = c")
    case False
    with Persist_Join show ?thesis by (simp add: window_applier_def)
  next
    case True
    with window_readyD[OF ready_op] Persist_Join have fresh: fresh and absent: "Persist_Join c \<notin> D"
      by (auto simp: window_jobs_def split: if_splits)
    from clean_term[OF fresh, of c] absent have term_fact: "app_term (window_applier D) < t"
      by (simp add: window_applier_def)
    have result: "window_applier (insert a D) = (window_applier D)\<lparr>app_term := t\<rparr>"
      by (rule application_state.equality) (use Persist_Join True in \<open>simp_all add: window_applier_def\<close>)
    show ?thesis unfolding result by (intro disjI2 application_step.advance_term[OF term_fact])
  qed
next
  case (Persist_Accept n)
  show ?thesis
  proof (cases "n = c")
    case False
    with Persist_Accept show ?thesis by (simp add: window_applier_def)
  next
    case True
    from window_readyD[OF ready_op] Persist_Accept True have absent: "Persist_Accept c \<notin> D"
      and occurs: "fresh \<Longrightarrow> Persist_Join c \<in> D" by (auto split: if_splits)
    have wire: "Registered_State packet u \<in> window_traffic" by (simp add: window_traffic_def)
    have term_fact: "pub_term packet = app_term (window_applier D)"
      using acceptance_term[of c] occurs by (cases fresh) (auto simp: window_applier_def request_def)
    have freshness: "rank_term (app_accepted (window_applier D)) = pub_term packet \<longrightarrow>
        rank_version (app_accepted (window_applier D)) < pub_version packet"
      using absent newer_version by (simp add: window_applier_def request_def)
    have result: "window_applier (insert a D) = (window_applier D)\<lparr>app_accepted := request_key packet\<rparr>"
      by (rule application_state.equality) (use Persist_Accept True in \<open>simp_all add: window_applier_def request_def\<close>)
    show ?thesis unfolding result by (intro disjI2 application_step.accept[OF wire term_fact freshness])
  qed
next
  case Handle_Self_Commit
  from window_readyD[OF ready_op] Handle_Self_Commit have absent: "Handle_Self_Commit \<notin> D"
    and accepted: "Persist_Accept c \<in> D" by auto
  from window_orderD(2)[OF ord, of Queue_Local] absent have not_queued: "Queue_Local \<notin> D" by auto
  have wire: "Returned_Commit c key \<in> window_traffic" by (simp add: window_traffic_def)
  have checks: "rank_term key = app_term (window_applier D)" "key = app_accepted (window_applier D)"
    using accepted local_term_if_accepted[OF ord accepted] by (simp_all add: window_applier_def)
  have result: "window_applier (insert a D) = (window_applier D)\<lparr>offered := Some key,
    self_ready := insert apply_request (self_ready (window_applier D))\<rparr>"
    by (rule application_state.equality)
      (use Handle_Self_Commit absent not_queued in \<open>simp_all add: window_applier_def\<close>)
  show ?thesis unfolding result by (intro disjI2 application_step.handle_self[OF wire checks])
next
  case Queue_Local
  from window_readyD[OF ready_op] Queue_Local have absent: "Queue_Local \<notin> D" and reply: "Handle_Self_Commit \<in> D" by auto
  from window_orderD(2)[OF ord, of Sample_Local] absent have not_sampled: "Sample_Local \<notin> D" by auto
  have ready: "apply_request \<in> self_ready (window_applier D)"
    using absent reply by (simp add: window_applier_def)
  have result: "window_applier (insert a D) = (window_applier D)\<lparr>
    self_ready := self_ready (window_applier D) - {apply_request},
    queued_applications := insert apply_request (queued_applications (window_applier D))\<rparr>"
    by (rule application_state.equality)
      (use Queue_Local absent not_sampled in \<open>simp_all add: window_applier_def\<close>)
  show ?thesis unfolding result by (intro disjI2 application_step.queue_self[OF ready])
next
  case Sample_Local
  from window_readyD[OF ready_op] Sample_Local have absent: "Sample_Local \<notin> D" and queued: "Queue_Local \<in> D" by auto
  from window_orderD(2)[OF ord queued] have reply: "Handle_Self_Commit \<in> D" by auto
  from window_orderD(2)[OF ord, of Run_Local] absent have not_applied: "Run_Local \<notin> D" by auto
  have checks: "apply_request \<in> queued_applications (window_applier D)"
    "running_application (window_applier D) = None" "offered (window_applier D) = Some key"
    using absent queued reply by (simp_all add: window_applier_def)
  have result: "window_applier (insert a D) = (window_applier D)\<lparr>
    queued_applications := queued_applications (window_applier D) - {apply_request},
    running_application := Some (apply_request,key)\<rparr>"
    by (rule application_state.equality)
      (use Sample_Local absent not_applied in \<open>simp_all add: window_applier_def\<close>)
  show ?thesis unfolding result by (intro disjI2 application_step.read_supplier[OF checks])
next
  case Run_Local
  from window_readyD[OF ready_op] Run_Local have absent: "Run_Local \<notin> D" and sampled: "Sample_Local \<in> D" by auto
  have running: "running_application (window_applier D) = Some (apply_request,key)"
    using absent sampled by (simp add: window_applier_def)
  have result: "window_applier (insert a D) = (window_applier D)\<lparr>
    running_application := None, installed := Some key,
    application_successes := insert (incarnation (window_applier D),apply_request,key)
      (application_successes (window_applier D))\<rparr>"
    by (rule application_state.equality)
      (use Run_Local absent in \<open>simp_all add: window_applier_def application_initial_def\<close>)
  show ?thesis unfolding result by (intro disjI2 application_step.apply_success[OF running])
qed (simp_all add: window_applier_def)

lemma window_has_application_trace:
  "application_reachable c window_traffic (current s c) old_key (window_applier (finished select i))"
proof (induction i)
  case 0
  have initial_app: "window_applier {} = application_initial (current s c) old_key"
    by (simp add: window_applier_def application_initial_def)
  show ?case unfolding completed_work.simps(1) initial_app by (rule application_reachable.initial)
next
  case (Suc i)
  from completed_work_change[of jobs deps select i]
  have path: "window_applier (finished select (Suc i)) = window_applier (finished select i) \<or>
    application_step c window_traffic (window_applier (finished select i)) (window_applier (finished select (Suc i)))"
  proof (elim disjE)
    assume "finished select (Suc i) = finished select i"
    then show ?thesis by simp
  next
    assume "\<exists>a. select i = Some a \<and> work_ready jobs deps (finished select i) a \<and>
      finished select (Suc i) = insert a (finished select i)"
    then obtain a where ready: "work_ready jobs deps (finished select i) a"
      and update: "finished select (Suc i) = insert a (finished select i)" by blast
    show ?thesis unfolding update by (rule window_applier_step[OF ordered_completed_work ready])
  qed
  from path show ?case by (elim disjE) (use Suc.IH in simp, rule application_reachable.step[OF Suc.IH])
qed

corollary fixed_first_publication_local_completion:
  assumes "fresh" "bounded_service jobs deps select delay horizon" "12 * delay \<le> horizon"
  shows "h \<in> committed (core (finished select (12 * delay)))"
    "installed (window_applier (finished select (12 * delay))) = Some key"
    "window_slot (finished select (12 * delay)) = None"
    "application_reachable c window_traffic (current s c) old_key (window_applier (finished select (12 * delay)))"
proof -
  note finished = fixed_first_publication_applied_and_slot_free[OF assms]
  show "h \<in> committed (core (finished select (12 * delay)))" by (rule finished(1))
  show "installed (window_applier (finished select (12 * delay))) = Some key"
    using finished(2) by (simp add: window_applier_def)
  show "window_slot (finished select (12 * delay)) = None" by (rule finished(3))
  show "application_reachable c window_traffic (current s c) old_key (window_applier (finished select (12 * delay)))"
    by (rule window_has_application_trace)
qed

corollary fixed_incumbent_local_completion:
  assumes "\<not> fresh" "bounded_service jobs deps select delay horizon" "8 * delay \<le> horizon"
  shows "h \<in> committed (core (finished select (8 * delay)))"
    "installed (window_applier (finished select (8 * delay))) = Some key"
    "window_slot (finished select (8 * delay)) = None"
    "application_reachable c window_traffic (current s c) old_key (window_applier (finished select (8 * delay)))"
proof -
  note finished = fixed_incumbent_applies_and_releases_slot[OF assms]
  show "h \<in> committed (core (finished select (8 * delay)))" by (rule finished(1))
  show "installed (window_applier (finished select (8 * delay))) = Some key"
    using finished(2) by (simp add: window_applier_def)
  show "window_slot (finished select (8 * delay)) = None" by (rule finished(3))
  show "application_reachable c window_traffic (current s c) old_key (window_applier (finished select (8 * delay)))"
    by (rule window_has_application_trace)
qed

lemma fixed_window_handoff:
  assumes local_run: "Run_Local \<in> finished select i"
  shows "reachable V (core (finished select i))"
    "c \<in> active (core (finished select i))" "leader (core (finished select i)) t = Some c"
    "tip (core (finished select i)) t = h"
    "n \<in> insert c Q \<Longrightarrow> current (core (finished select i)) n = t"
    "n \<in> insert c Q \<Longrightarrow> accepted (core (finished select i)) n = h"
proof -
  let ?D = "finished select i"
  note ordered = ordered_completed_work[of jobs deps select i]
  note previous = window_orderD(2)[OF ordered]
  have sampled: "Sample_Local \<in> ?D" using previous[OF local_run] by simp
  have queued: "Queue_Local \<in> ?D" using previous[OF sampled] by simp
  have self: "Handle_Self_Commit \<in> ?D" using previous[OF queued] by simp
  have committed: "Collect_Receipts \<in> ?D" using previous[OF self] by simp
  have accepted: "Persist_Accept n \<in> ?D" if "n \<in> insert c Q" for n
    using previous[OF self] previous[OF committed] that by auto
  have own: "Persist_Accept c \<in> ?D" by (rule accepted) simp
  have registered: "Register \<in> ?D" using previous[OF own] by (cases fresh) auto
  have election: "\<not> fresh \<or> Collect_Votes \<in> ?D"
    using previous[OF registered] by (cases fresh) auto
  show "reachable V (core ?D)" by (rule window_core_reachable)
  from election_snapshot[OF ordered election]
  show "c \<in> active (core ?D)" "leader (core ?D) t = Some c" by simp_all
  show "tip (core ?D) t = h" using registered by (simp add: window_state_def)
  assume n: "n \<in> insert c Q"
  show "current (core ?D) n = t"
  proof (cases fresh)
    case True
    with previous[OF accepted[OF n]]
    show ?thesis by (simp add: window_state_def)
  next
    case False
    have "Persist_Join n \<notin> ?D" using window_orderD(1)[OF ordered, of "Persist_Join n"] False
      by (auto simp: window_jobs_def split: if_splits)
    with acceptance_term[OF False n] show ?thesis by (simp add: window_state_def)
  qed
  show "accepted (core ?D) n = h" using accepted[OF n] by (simp add: window_state_def)
qed

end

end
