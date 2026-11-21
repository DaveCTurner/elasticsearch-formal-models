theory Coordination_State_Example
  imports Coordination_State_Refinement
begin

text \<open>
  The class can start a second publication after locally accepting the first.
  If the first changes configuration, a late self-commit can install the
  new configuration while the second publication carries the old one.
  All inputs in this trace are authentic, and only the last call violates
  the caller's publication-completion condition.
\<close>

fun successful_prefix ::
  "node set \<Rightarrow> node set \<Rightarrow> 'v set \<Rightarrow> config \<Rightarrow> 'v \<Rightarrow>
    'v java_state \<Rightarrow> 'v java_action list \<Rightarrow> bool" where
  "successful_prefix N E V C initial_value j [] = True"
| "successful_prefix N E V C initial_value j (a # as) =
    (java_checks j a \<and> caller_contract N E V C initial_value j a \<and>
      successful_prefix N E V C initial_value (java_call N E j a) as)"

lemma reachable_after_prefix:
  assumes "successful_prefix N E V C initial_value j actions"
    "java_reachable N E V C initial_value versions j"
  shows "java_reachable N E V C initial_value versions (foldl (java_call N E) j actions)"
  using assms
proof (induction actions arbitrary: j)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  then have "java_reachable N E V C initial_value versions (java_call N E j a)"
    by (auto intro: java_reachable.advance)
  with Cons show ?case by simp
qed

definition pending_publication :: "unit java_action list" where
  "pending_publication = [
    Java_Bootstrap 0 rank_zero () {0} {0},
    Java_Start_Join 0 0 1,
    Java_Start_Join 1 0 1,
    Java_Join 0 0 1 rank_zero,
    Java_Join 1 0 1 rank_zero,
    Java_Client 0 1 1 () {1} {0},
    Java_Publish 0 (request 0 1 1 {1} {0}) (),
    Java_Publish 1 (request 0 1 1 {1} {0}) (),
    Java_Response 0 0 \<lparr>rank_term = 1, rank_version = 1\<rparr>,
    Java_Response 1 0 \<lparr>rank_term = 1, rank_version = 1\<rparr>,
    Java_Client 0 1 2 () {1} {0}]"

abbreviation example_nodes :: "node set" where
  "example_nodes \<equiv> {0,1}"

definition pending_state :: "unit java_state" where
  "pending_state = foldl (java_call example_nodes example_nodes)
    (java_initial () (\<lambda>_. 0)) pending_publication"

lemmas call_simps = java_call_def java_put_def java_reset_def
  Let_def add_vote_def java_election_def java_publication_def java_has_quorum_def signed_int_def request_def

lemmas replay_simps = pending_publication_def java_initial_def call_simps

text \<open>
  Replaying the eleven actions is the expensive part of the proofs below, so it is done once.
  The schematic goal is closed by the simplifier, which instantiates the right-hand side with the
  state that it computes.
\<close>

schematic_goal pending_state_eq: "pending_state = ?state"
  by (simp add: pending_state_def replay_simps)

lemma pending_state_reachable:
  "java_reachable example_nodes example_nodes {()} {0} () (\<lambda>_. 0) pending_state"
proof -
  have prefix: "successful_prefix example_nodes example_nodes {()} {0} ()
    (java_initial () (\<lambda>_. 0)) pending_publication"
    by (simp add: replay_simps)
  have init: "java_reachable example_nodes example_nodes {()} {0} () (\<lambda>_. 0) (java_initial () (\<lambda>_. 0))"
    by (rule java_reachable.init) simp_all
  show ?thesis unfolding pending_state_def by (rule reachable_after_prefix[OF prefix init])
qed

theorem authenticated_late_commit_counterexample:
  "\<exists>s :: unit tla_state.
    tla_reachable {0,1} {()} {0} () (\<lambda>_. 0) s \<and>
    java_reachable {0,1} {0,1} {()} {0} () (\<lambda>_. 0) (project_java {0,1} s) \<and>
    Commit_Msg 0 0 \<lparr>rank_term = 1, rank_version = 1\<rparr> \<in> messages s \<and>
    java_checks (project_java {0,1} s) (Java_Commit 0 0 \<lparr>rank_term = 1, rank_version = 1\<rparr>) \<and>
    \<not> (\<exists>s'. (s' = s \<or> tla_next {0,1} {()} {0} () s s') \<and>
      java_call {0,1} {0,1} (project_java {0,1} s) (Java_Commit 0 0 \<lparr>rank_term = 1, rank_version = 1\<rparr>) = project_java {0,1} s')"
proof -
  obtain s where s: "tla_reachable example_nodes {()} {0} () (\<lambda>_. 0) s"
    "pending_state = project_java example_nodes s"
    using coordination_state_refines_tla[OF pending_state_reachable] by blast
  have concrete: "election_won (java_nodes pending_state 0)" "published_version (java_nodes pending_state 0) = 2"
    "accepted_key (java_nodes pending_state 0) = \<lparr>rank_term = 1, rank_version = 1\<rparr>" "current_term (java_nodes pending_state 0) = 1"
    "local_committed (java_nodes pending_state 0) = {0}" "accepted_config (java_nodes pending_state 0) = {1}"
    "Commit_Msg 0 0 \<lparr>rank_term = 1, rank_version = 1\<rparr> \<in> java_journal pending_state"
    by (simp_all add: pending_state_eq)
  have conditions: "election_won (nodes_at s 0)" "rank_version \<lparr>rank_term = 1, rank_version = 1\<rparr> \<noteq> published_version (nodes_at s 0)"
    "accepted_key (nodes_at s 0) = \<lparr>rank_term = 1, rank_version = 1\<rparr>" "rank_term (\<lparr>rank_term = 1, rank_version = 1\<rparr>) = current_term (nodes_at s 0)"
    "local_committed (nodes_at s 0) \<noteq> accepted_config (nodes_at s 0)" "accepted_config (nodes_at s 0) \<noteq> {}"
    using concrete unfolding s(2) by (simp_all add: mask_votes_def)
  have unmatched: "\<not> (\<exists>s'. (s' = s \<or> tla_next example_nodes {()} {0} () s s') \<and>
      java_call example_nodes example_nodes (project_java example_nodes s) (Java_Commit 0 0 \<lparr>rank_term = 1, rank_version = 1\<rparr>) = project_java example_nodes s')"
    by (rule late_commit_has_no_matching_step[OF conditions])
  have projected: "java_reachable example_nodes example_nodes {()} {0} () (\<lambda>_. 0) (project_java example_nodes s)"
    using pending_state_reachable unfolding s(2) .
  have msg: "Commit_Msg 0 0 \<lparr>rank_term = 1, rank_version = 1\<rparr> \<in> messages s" using concrete(7) unfolding s(2) by simp
  have checks: "java_checks (project_java example_nodes s) (Java_Commit 0 0 \<lparr>rank_term = 1, rank_version = 1\<rparr>)"
    using conditions(3) conditions(4)[symmetric] by (simp add: Let_def mask_votes_def)
  show ?thesis
    apply (rule exI[of _ s])
    apply (intro conjI)
    by (rule s(1) projected msg checks unmatched)+
qed

theorem late_commit_breaks_carried_quorum:
  defines "p \<equiv> request 0 1 2 {1} {0}"
  shows "\<exists>j :: unit java_state.
    java_reachable {0,1} {0,1} {()} {0} () (\<lambda>_. 0) j \<and>
    (let apply = Java_Commit 0 0 \<lparr>rank_term = 1, rank_version = 1\<rparr>;
         accept = Java_Publish 1 p ();
         respond = Java_Response 1 0 \<lparr>rank_term = 1, rank_version = 2\<rparr>;
         j1 = java_call {0,1} {0,1} j apply;
         j2 = java_call {0,1} {0,1} j1 accept;
         j3 = java_call {0,1} {0,1} j2 respond
     in java_checks j apply \<and> Commit_Msg 0 0 \<lparr>rank_term = 1, rank_version = 1\<rparr> \<in> java_journal j \<and>
        java_checks j1 accept \<and> Publish_Msg 1 p () \<in> java_journal j1 \<and>
        java_checks j2 respond \<and> Response_Msg 1 0 \<lparr>rank_term = 1, rank_version = 2\<rparr> \<in> java_journal j2 \<and>
        Commit_Msg 0 0 \<lparr>rank_term = 1, rank_version = 2\<rparr> \<in> java_journal j3 \<and>
        \<not> quorum (pub_previous p) {n. \<exists>c. Response_Msg n c \<lparr>rank_term = 1, rank_version = 2\<rparr> \<in> java_journal j3})"
proof -
  let ?apply = "Java_Commit 0 0 \<lparr>rank_term = 1, rank_version = 1\<rparr>"
  let ?accept = "Java_Publish 1 p ()"
  let ?response = "Java_Response 1 0 \<lparr>rank_term = 1, rank_version = 2\<rparr>"
  let ?j1 = "java_call example_nodes example_nodes pending_state ?apply"
  let ?j2 = "java_call example_nodes example_nodes ?j1 ?accept"
  let ?j3 = "java_call example_nodes example_nodes ?j2 ?response"
  have checks: "java_checks pending_state ?apply" "Commit_Msg 0 0 \<lparr>rank_term = 1, rank_version = 1\<rparr> \<in> java_journal pending_state"
    "java_checks ?j1 ?accept" "Publish_Msg 1 p () \<in> java_journal ?j1"
    "java_checks ?j2 ?response" "Response_Msg 1 0 \<lparr>rank_term = 1, rank_version = 2\<rparr> \<in> java_journal ?j2"
    "Commit_Msg 0 0 \<lparr>rank_term = 1, rank_version = 2\<rparr> \<in> java_journal ?j3"
    by (simp_all add: pending_state_eq call_simps p_def)
  have no_response: "Response_Msg 0 c \<lparr>rank_term = 1, rank_version = 2\<rparr> \<notin> java_journal ?j3" for c
    by (simp add: pending_state_eq call_simps p_def)
  have "\<not> (\<exists>c. Response_Msg 0 c \<lparr>rank_term = 1, rank_version = 2\<rparr> \<in> java_journal ?j3)" using no_response by blast
  then have "pub_previous p \<inter> {n. \<exists>c. Response_Msg n c \<lparr>rank_term = 1, rank_version = 2\<rparr> \<in> java_journal ?j3} = {}"
    by (simp add: p_def request_def)
  then have lacks: "\<not> quorum (pub_previous p) {n. \<exists>c. Response_Msg n c \<lparr>rank_term = 1, rank_version = 2\<rparr> \<in> java_journal ?j3}"
    unfolding quorum_def majority_def by simp
  show ?thesis unfolding Let_def
    apply (rule exI[of _ pending_state])
    apply (intro conjI)
    by (rule pending_state_reachable checks lacks)+
qed

end
