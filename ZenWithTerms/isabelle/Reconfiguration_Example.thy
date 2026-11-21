theory Reconfiguration_Example
  imports Dynamic_Configuration
begin

lemma transition_into:
  "transition C s u \<Longrightarrow> u = v \<Longrightarrow> transition C s v"
  by simp

text \<open>
  Node 0 wins with a quorum of the bootstrap configuration. It gathers node 1's
  join to propose the disjoint configuration {1}. Both nodes acknowledge the
  change, and node 1 applies the commit. After node 0 restarts, node 1 elects
  and commits a descendant using only the new configuration.
\<close>

theorem disjoint_configuration_failover:
  "\<exists>s a b. dynamic_reachable {0} s \<and>
    a \<in> quorum_commits s \<and> b \<in> quorum_commits s \<and>
    term_of a = 1 \<and> term_of b = 2 \<and> prefix a b \<and>
    carried {0} a = {0} \<and> config_of {0} a = {1} \<and>
    carried {0} b = {1} \<and> config_of {0} b = {1}"
proof -
  let ?C = "{0} :: config"
  let ?D = "{1} :: config"
  let ?s0 = "bootstrapped ?C"
  let ?j0 = "(0,0,1,rank_zero) :: node \<times> node \<times> nat \<times> rank"
  let ?j1 = "(1,0,1,rank_zero) :: node \<times> node \<times> nat \<times> rank"
  let ?j2 = "(1,1,2,\<lparr>rank_term = 1, rank_version = 1\<rparr>) :: node \<times> node \<times> nat \<times> rank"
  let ?a = "[\<lparr>pub_term = 1, pub_version = 1, pub_payload = 10,
    pub_owner = 0, pub_config = ?D, pub_previous = ?C\<rparr>]"
  let ?b = "?a @ [\<lparr>pub_term = 2, pub_version = 2, pub_payload = 20,
    pub_owner = 1, pub_config = ?D, pub_previous = ?D\<rparr>]"
  let ?e0 = "\<lparr>elected_from = [], elected_committed = ?C, elected_votes = {0}\<rparr>"
  let ?e1 = "\<lparr>elected_from = ?a, elected_committed = ?D, elected_votes = {1}\<rparr>"

  define s1 where "s1 = ?s0\<lparr>node_term := (\<lambda>_. 0)(0 := 1),
    sent_joins := {?j0}, joined_since_restart := {0}\<rparr>"
  have t1: "transition ?C ?s0 s1"
    unfolding s1_def
    by (rule transition_into, rule transition.start_join[where n=0 and c=0 and t=1])
      (simp_all add: bootstrapped_def)
  define s2 where "s2 = s1\<lparr>certificate := (\<lambda>_. None)((0,1) := Some ?e0)\<rparr>"
  have t2: "transition ?C s1 s2"
    unfolding s2_def
    by (rule transition_into, rule transition.win[where c=0 and Q="{0}"])
      (auto simp: s1_def bootstrapped_def quorum_def majority_def fresh_votes_def)
  define both_terms where "both_terms = (\<lambda>_ :: node. (0 :: nat))(0 := 1, 1 := 1)"
  define s3 where "s3 = s2\<lparr>node_term := both_terms,
    sent_joins := {?j0,?j1}, joined_since_restart := {0,1}\<rparr>"
  have t3: "transition ?C s2 s3"
    unfolding s3_def
    by (rule transition_into, rule transition.start_join[where n=1 and c=0 and t=1])
      (auto simp: s2_def s1_def bootstrapped_def both_terms_def rank_less_iff rank_le_iff)
  define s4 where "s4 = s3\<lparr>publication_tip := (\<lambda>_. [])((0,1) := ?a),
    publications := {?a}\<rparr>"
  have t4: "transition ?C s3 s4"
    unfolding s4_def
    by (rule transition_into, rule transition.publish[where c=0 and D="{1}" and Q="{1}" and v=1 and payload=10 and h="?a"])
      (auto simp: s3_def s2_def s1_def bootstrapped_def both_terms_def rank_less_iff rank_le_iff active_leader_def
        fresh_votes_def quorum_def majority_def)
  define s5 where "s5 = s4\<lparr>durable_history := (\<lambda>_. [])(0 := ?a), acknowledgements := {(0,?a)}\<rparr>"
  have t5: "transition ?C s4 s5"
    unfolding s5_def
    by (rule transition_into, rule transition.receive[where n=0 and h="?a"])
      (auto simp: s4_def s3_def s2_def s1_def bootstrapped_def both_terms_def rank_less_iff rank_le_iff)
  define s6 where "s6 = s5\<lparr>durable_history := (\<lambda>_. [])(0 := ?a, 1 := ?a),
    acknowledgements := {(0,?a),(1,?a)}\<rparr>"
  have t6: "transition ?C s5 s6"
    unfolding s6_def
    by (rule transition_into, rule transition.receive[where n=1 and h="?a"])
      (auto simp: s5_def s4_def s3_def s2_def s1_def bootstrapped_def both_terms_def rank_less_iff rank_le_iff)
  define s7 where "s7 = s6\<lparr>quorum_commits := {?a}\<rparr>"
  have t7: "transition ?C s6 s7"
    unfolding s7_def
  proof (rule transition_into, rule transition.certify[where c=0 and h="?a"])
    show "joint_receipts ?C s6 ?a"
      unfolding joint_receipts_def
      by (rule exI[where x="{0,1}"])
        (simp add: s6_def quorum_def majority_def)
  qed (auto simp: s6_def s5_def s4_def s3_def s2_def s1_def bootstrapped_def both_terms_def rank_less_iff rank_le_iff active_leader_def)
  define s8 where "s8 = s7\<lparr>committed_config := (\<lambda>_. ?C)(1 := ?D)\<rparr>"
  have t8: "transition ?C s7 s8"
    unfolding s8_def
    by (rule transition_into, rule transition.apply_commit[where n=1])
      (auto simp: s7_def s6_def s5_def s4_def s3_def s2_def s1_def bootstrapped_def both_terms_def rank_less_iff rank_le_iff active_leader_def)
  define s9 where "s9 = s8\<lparr>joined_since_restart := {1}\<rparr>"
  have t9: "transition ?C s8 s9"
    unfolding s9_def
    by (rule transition_into, rule transition.reboot[where n=0])
      (auto simp: s8_def s7_def s6_def s5_def s4_def s3_def)
  note first_term = s9_def s8_def s7_def s6_def s5_def s4_def s3_def s2_def s1_def bootstrapped_def both_terms_def
  define s10 where "s10 = s9\<lparr>node_term := both_terms(1 := 2), sent_joins := {?j0,?j1,?j2}\<rparr>"
  have t10: "transition ?C s9 s10"
    unfolding s10_def
    by (rule transition_into, rule transition.start_join[where n=1 and c=1 and t=2])
      (auto simp: first_term)
  define s11 where "s11 = s10\<lparr>certificate := (\<lambda>_. None)((0,1) := Some ?e0, (1,2) := Some ?e1),
    publication_tip := (\<lambda>_. [])((0,1) := ?a, (1,2) := ?a)\<rparr>"
  have t11: "transition ?C s10 s11"
    unfolding s11_def
    by (rule transition_into, rule transition.win[where c=1 and Q="{1}"])
      (auto simp: s10_def first_term quorum_def majority_def fresh_votes_def)
  define s12 where "s12 = s11\<lparr>publication_tip := (\<lambda>_. [])((0,1) := ?a, (1,2) := ?b),
    publications := {?a,?b}\<rparr>"
  have t12: "transition ?C s11 s12"
    unfolding s12_def
    by (rule transition_into, rule transition.publish[where c=1 and D="{1}" and Q="{1}" and v=2 and payload=20 and h="?b"])
      (auto simp: s11_def s10_def first_term active_leader_def fresh_votes_def quorum_def majority_def)
  define s13 where "s13 = s12\<lparr>durable_history := (\<lambda>_. [])(0 := ?a, 1 := ?b),
    acknowledgements := {(0,?a),(1,?a),(1,?b)}\<rparr>"
  have t13: "transition ?C s12 s13"
    unfolding s13_def
    by (rule transition_into, rule transition.receive[where n=1 and h="?b"])
      (auto simp: s12_def s11_def s10_def first_term rank_less_iff rank_le_iff)
  define s14 where "s14 = s13\<lparr>quorum_commits := {?a,?b}\<rparr>"
  have t14: "transition ?C s13 s14"
    unfolding s14_def
  proof (rule transition_into, rule transition.certify[where c=1 and h="?b"])
    show "joint_receipts ?C s13 ?b"
      unfolding joint_receipts_def
      by (rule exI[where x="{1}"]) (simp add: s13_def quorum_def majority_def)
  qed (auto simp: s13_def s12_def s11_def s10_def first_term active_leader_def)
  have "dynamic_reachable ?C s14"
    by (rule dynamic_reachable.advance[OF _ t14],
        rule dynamic_reachable.advance[OF _ t13],
        rule dynamic_reachable.advance[OF _ t12],
        rule dynamic_reachable.advance[OF _ t11],
        rule dynamic_reachable.advance[OF _ t10],
        rule dynamic_reachable.advance[OF _ t9],
        rule dynamic_reachable.advance[OF _ t8],
        rule dynamic_reachable.advance[OF _ t7],
        rule dynamic_reachable.advance[OF _ t6],
        rule dynamic_reachable.advance[OF _ t5],
        rule dynamic_reachable.advance[OF _ t4],
        rule dynamic_reachable.advance[OF _ t3],
        rule dynamic_reachable.advance[OF _ t2],
        rule dynamic_reachable.advance[OF _ t1], rule dynamic_reachable.boot) simp_all
  then show ?thesis
    by (intro exI[where x=s14] exI[where x="?a"] exI[where x="?b"]) (simp add: s14_def)
qed

end
