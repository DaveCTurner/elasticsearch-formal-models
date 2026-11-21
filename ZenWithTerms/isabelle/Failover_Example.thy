theory Failover_Example
  imports Fixed_Configuration
begin

text \<open>Two different majorities commit successive publications with a leader restart between them.

  Each intermediate state is a constant, defined by a single update of its predecessor. Its fields
  are then given in normal form, so that proving a step only inspects the fields of its predecessor.\<close>

abbreviation example_nodes :: "node set" where "example_nodes \<equiv> {0,1,2}"
abbreviation first_history :: history where "first_history \<equiv> [(1,1,10)]"
abbreviation second_history :: history where "second_history \<equiv> [(1,1,10),(2,2,20)]"

lemma majority_01: "majority example_nodes {0,1}" and majority_12: "majority example_nodes {1,2}"
  by (simp_all add: majority_def)

lemma initial_fields [simp]:
  "current initial = (\<lambda>_. 0) \<and>
    accepted initial = (\<lambda>_. []) \<and>
    joins initial = {} \<and>
    leader initial = (\<lambda>_. None) \<and>
    electors initial = (\<lambda>_. {}) \<and>
    started initial = {} \<and>
    active initial = {} \<and>
    tip initial = (\<lambda>_. []) \<and>
    published initial = {} \<and>
    receipts initial = {} \<and>
    committed initial = {}"
  by (auto simp: initial_def)

definition join_zero :: coordination where
  "join_zero = initial\<lparr>current := (current initial)(0 := 1),
    joins := insert (0,0,1,accepted initial 0) (joins initial),
    started := insert 0 (started initial), active := active initial - {0}\<rparr>"

lemma join_zero_fields [simp]:
  "current join_zero = (\<lambda>_. 0)(0 := 1) \<and>
    accepted join_zero = (\<lambda>_. []) \<and>
    joins join_zero = {(0,0,1,[])} \<and>
    leader join_zero = (\<lambda>_. None) \<and>
    electors join_zero = (\<lambda>_. {}) \<and>
    started join_zero = {0} \<and>
    active join_zero = {} \<and>
    tip join_zero = (\<lambda>_. []) \<and>
    published join_zero = {} \<and>
    receipts join_zero = {} \<and>
    committed join_zero = {}"
  by (auto simp: join_zero_def)

definition join_one :: coordination where
  "join_one = join_zero\<lparr>current := (current join_zero)(1 := 1),
    joins := insert (1,0,1,accepted join_zero 1) (joins join_zero),
    started := insert 1 (started join_zero), active := active join_zero - {1}\<rparr>"

lemma join_one_fields [simp]:
  "current join_one = (\<lambda>_. 0)(0 := 1, 1 := 1) \<and>
    accepted join_one = (\<lambda>_. []) \<and>
    joins join_one = {(1,0,1,[]),(0,0,1,[])} \<and>
    leader join_one = (\<lambda>_. None) \<and>
    electors join_one = (\<lambda>_. {}) \<and>
    started join_one = {1,0} \<and>
    active join_one = {} \<and>
    tip join_one = (\<lambda>_. []) \<and>
    published join_one = {} \<and>
    receipts join_one = {} \<and>
    committed join_one = {}"
  by (auto simp: join_one_def)

definition elect_zero :: coordination where
  "elect_zero = join_one\<lparr>leader := (leader join_one)(1 := Some 0), electors := (electors join_one)(1 := {0,1}),
    tip := (tip join_one)(1 := accepted join_one 0), active := insert 0 (active join_one)\<rparr>"

lemma elect_zero_fields [simp]:
  "current elect_zero = (\<lambda>_. 0)(0 := 1, 1 := 1) \<and>
    accepted elect_zero = (\<lambda>_. []) \<and>
    joins elect_zero = {(1,0,1,[]),(0,0,1,[])} \<and>
    leader elect_zero = (\<lambda>_. None)(1 := Some 0) \<and>
    electors elect_zero = (\<lambda>_. {})(1 := {0,1}) \<and>
    started elect_zero = {1,0} \<and>
    active elect_zero = {0} \<and>
    tip elect_zero = (\<lambda>_. [])(1 := []) \<and>
    published elect_zero = {} \<and>
    receipts elect_zero = {} \<and>
    committed elect_zero = {}"
  by (auto simp: elect_zero_def)

definition publish_first :: coordination where
  "publish_first = elect_zero\<lparr>tip := (tip elect_zero)(1 := first_history), published := insert first_history (published elect_zero)\<rparr>"

lemma publish_first_fields [simp]:
  "current publish_first = (\<lambda>_. 0)(0 := 1, 1 := 1) \<and>
    accepted publish_first = (\<lambda>_. []) \<and>
    joins publish_first = {(1,0,1,[]),(0,0,1,[])} \<and>
    leader publish_first = (\<lambda>_. None)(1 := Some 0) \<and>
    electors publish_first = (\<lambda>_. {})(1 := {0,1}) \<and>
    started publish_first = {1,0} \<and>
    active publish_first = {0} \<and>
    tip publish_first = (\<lambda>_. [])(1 := [(1,1,10)]) \<and>
    published publish_first = {[(1,1,10)]} \<and>
    receipts publish_first = {} \<and>
    committed publish_first = {}"
  by (auto simp: publish_first_def)

definition accept_zero :: coordination where
  "accept_zero = publish_first\<lparr>accepted := (accepted publish_first)(0 := first_history), receipts := insert (0,first_history) (receipts publish_first)\<rparr>"

lemma accept_zero_fields [simp]:
  "current accept_zero = (\<lambda>_. 0)(0 := 1, 1 := 1) \<and>
    accepted accept_zero = (\<lambda>_. [])(0 := [(1,1,10)]) \<and>
    joins accept_zero = {(1,0,1,[]),(0,0,1,[])} \<and>
    leader accept_zero = (\<lambda>_. None)(1 := Some 0) \<and>
    electors accept_zero = (\<lambda>_. {})(1 := {0,1}) \<and>
    started accept_zero = {1,0} \<and>
    active accept_zero = {0} \<and>
    tip accept_zero = (\<lambda>_. [])(1 := [(1,1,10)]) \<and>
    published accept_zero = {[(1,1,10)]} \<and>
    receipts accept_zero = {(0,[(1,1,10)])} \<and>
    committed accept_zero = {}"
  by (auto simp: accept_zero_def)

definition accept_one :: coordination where
  "accept_one = accept_zero\<lparr>accepted := (accepted accept_zero)(1 := first_history), receipts := insert (1,first_history) (receipts accept_zero)\<rparr>"

lemma accept_one_fields [simp]:
  "current accept_one = (\<lambda>_. 0)(0 := 1, 1 := 1) \<and>
    accepted accept_one = (\<lambda>_. [])(0 := [(1,1,10)], 1 := [(1,1,10)]) \<and>
    joins accept_one = {(1,0,1,[]),(0,0,1,[])} \<and>
    leader accept_one = (\<lambda>_. None)(1 := Some 0) \<and>
    electors accept_one = (\<lambda>_. {})(1 := {0,1}) \<and>
    started accept_one = {1,0} \<and>
    active accept_one = {0} \<and>
    tip accept_one = (\<lambda>_. [])(1 := [(1,1,10)]) \<and>
    published accept_one = {[(1,1,10)]} \<and>
    receipts accept_one = {(1,[(1,1,10)]),(0,[(1,1,10)])} \<and>
    committed accept_one = {}"
  by (auto simp: accept_one_def)

definition commit_first :: coordination where
  "commit_first = accept_one\<lparr>committed := insert (tip accept_one 1) (committed accept_one)\<rparr>"

lemma commit_first_fields [simp]:
  "current commit_first = (\<lambda>_. 0)(0 := 1, 1 := 1) \<and>
    accepted commit_first = (\<lambda>_. [])(0 := [(1,1,10)], 1 := [(1,1,10)]) \<and>
    joins commit_first = {(1,0,1,[]),(0,0,1,[])} \<and>
    leader commit_first = (\<lambda>_. None)(1 := Some 0) \<and>
    electors commit_first = (\<lambda>_. {})(1 := {0,1}) \<and>
    started commit_first = {1,0} \<and>
    active commit_first = {0} \<and>
    tip commit_first = (\<lambda>_. [])(1 := [(1,1,10)]) \<and>
    published commit_first = {[(1,1,10)]} \<and>
    receipts commit_first = {(1,[(1,1,10)]),(0,[(1,1,10)])} \<and>
    committed commit_first = {[(1,1,10)]}"
  by (auto simp: commit_first_def)

definition restart_zero :: coordination where
  "restart_zero = commit_first\<lparr>started := started commit_first - {0}, active := active commit_first - {0}\<rparr>"

lemma restart_zero_fields [simp]:
  "current restart_zero = (\<lambda>_. 0)(0 := 1, 1 := 1) \<and>
    accepted restart_zero = (\<lambda>_. [])(0 := [(1,1,10)], 1 := [(1,1,10)]) \<and>
    joins restart_zero = {(1,0,1,[]),(0,0,1,[])} \<and>
    leader restart_zero = (\<lambda>_. None)(1 := Some 0) \<and>
    electors restart_zero = (\<lambda>_. {})(1 := {0,1}) \<and>
    started restart_zero = {1} \<and>
    active restart_zero = {} \<and>
    tip restart_zero = (\<lambda>_. [])(1 := [(1,1,10)]) \<and>
    published restart_zero = {[(1,1,10)]} \<and>
    receipts restart_zero = {(1,[(1,1,10)]),(0,[(1,1,10)])} \<and>
    committed restart_zero = {[(1,1,10)]}"
  by (auto simp: restart_zero_def)

definition rejoin_one :: coordination where
  "rejoin_one = restart_zero\<lparr>current := (current restart_zero)(1 := 2),
    joins := insert (1,1,2,accepted restart_zero 1) (joins restart_zero),
    started := insert 1 (started restart_zero), active := active restart_zero - {1}\<rparr>"

lemma rejoin_one_fields [simp]:
  "current rejoin_one = (\<lambda>_. 0)(0 := 1, 1 := 2) \<and>
    accepted rejoin_one = (\<lambda>_. [])(0 := [(1,1,10)], 1 := [(1,1,10)]) \<and>
    joins rejoin_one = {(1,1,2,[(1,1,10)]),(1,0,1,[]),(0,0,1,[])} \<and>
    leader rejoin_one = (\<lambda>_. None)(1 := Some 0) \<and>
    electors rejoin_one = (\<lambda>_. {})(1 := {0,1}) \<and>
    started rejoin_one = {1} \<and>
    active rejoin_one = {} \<and>
    tip rejoin_one = (\<lambda>_. [])(1 := [(1,1,10)]) \<and>
    published rejoin_one = {[(1,1,10)]} \<and>
    receipts rejoin_one = {(1,[(1,1,10)]),(0,[(1,1,10)])} \<and>
    committed rejoin_one = {[(1,1,10)]}"
  by (auto simp: rejoin_one_def)

definition join_two :: coordination where
  "join_two = rejoin_one\<lparr>current := (current rejoin_one)(2 := 2),
    joins := insert (2,1,2,accepted rejoin_one 2) (joins rejoin_one),
    started := insert 2 (started rejoin_one), active := active rejoin_one - {2}\<rparr>"

lemma join_two_fields [simp]:
  "current join_two = (\<lambda>_. 0)(0 := 1, 1 := 2, 2 := 2) \<and>
    accepted join_two = (\<lambda>_. [])(0 := [(1,1,10)], 1 := [(1,1,10)]) \<and>
    joins join_two = {(2,1,2,[]),(1,1,2,[(1,1,10)]),(1,0,1,[]),(0,0,1,[])} \<and>
    leader join_two = (\<lambda>_. None)(1 := Some 0) \<and>
    electors join_two = (\<lambda>_. {})(1 := {0,1}) \<and>
    started join_two = {2,1} \<and>
    active join_two = {} \<and>
    tip join_two = (\<lambda>_. [])(1 := [(1,1,10)]) \<and>
    published join_two = {[(1,1,10)]} \<and>
    receipts join_two = {(1,[(1,1,10)]),(0,[(1,1,10)])} \<and>
    committed join_two = {[(1,1,10)]}"
  by (auto simp: join_two_def)

definition elect_one :: coordination where
  "elect_one = join_two\<lparr>leader := (leader join_two)(2 := Some 1), electors := (electors join_two)(2 := {1,2}),
    tip := (tip join_two)(2 := accepted join_two 1), active := insert 1 (active join_two)\<rparr>"

lemma elect_one_fields [simp]:
  "current elect_one = (\<lambda>_. 0)(0 := 1, 1 := 2, 2 := 2) \<and>
    accepted elect_one = (\<lambda>_. [])(0 := [(1,1,10)], 1 := [(1,1,10)]) \<and>
    joins elect_one = {(2,1,2,[]),(1,1,2,[(1,1,10)]),(1,0,1,[]),(0,0,1,[])} \<and>
    leader elect_one = (\<lambda>_. None)(1 := Some 0, 2 := Some 1) \<and>
    electors elect_one = (\<lambda>_. {})(1 := {0,1}, 2 := {1,2}) \<and>
    started elect_one = {2,1} \<and>
    active elect_one = {1} \<and>
    tip elect_one = (\<lambda>_. [])(1 := [(1,1,10)], 2 := [(1,1,10)]) \<and>
    published elect_one = {[(1,1,10)]} \<and>
    receipts elect_one = {(1,[(1,1,10)]),(0,[(1,1,10)])} \<and>
    committed elect_one = {[(1,1,10)]}"
  by (auto simp: elect_one_def)

definition publish_second :: coordination where
  "publish_second = elect_one\<lparr>tip := (tip elect_one)(2 := second_history), published := insert second_history (published elect_one)\<rparr>"

lemma publish_second_fields [simp]:
  "current publish_second = (\<lambda>_. 0)(0 := 1, 1 := 2, 2 := 2) \<and>
    accepted publish_second = (\<lambda>_. [])(0 := [(1,1,10)], 1 := [(1,1,10)]) \<and>
    joins publish_second = {(2,1,2,[]),(1,1,2,[(1,1,10)]),(1,0,1,[]),(0,0,1,[])} \<and>
    leader publish_second = (\<lambda>_. None)(1 := Some 0, 2 := Some 1) \<and>
    electors publish_second = (\<lambda>_. {})(1 := {0,1}, 2 := {1,2}) \<and>
    started publish_second = {2,1} \<and>
    active publish_second = {1} \<and>
    tip publish_second = (\<lambda>_. [])(1 := [(1,1,10)], 2 := [(1,1,10),(2,2,20)]) \<and>
    published publish_second = {[(1,1,10),(2,2,20)],[(1,1,10)]} \<and>
    receipts publish_second = {(1,[(1,1,10)]),(0,[(1,1,10)])} \<and>
    committed publish_second = {[(1,1,10)]}"
  by (auto simp: publish_second_def)

definition accept_one_again :: coordination where
  "accept_one_again = publish_second\<lparr>accepted := (accepted publish_second)(1 := second_history), receipts := insert (1,second_history) (receipts publish_second)\<rparr>"

lemma accept_one_again_fields [simp]:
  "current accept_one_again = (\<lambda>_. 0)(0 := 1, 1 := 2, 2 := 2) \<and>
    accepted accept_one_again = (\<lambda>_. [])(0 := [(1,1,10)], 1 := [(1,1,10),(2,2,20)]) \<and>
    joins accept_one_again = {(2,1,2,[]),(1,1,2,[(1,1,10)]),(1,0,1,[]),(0,0,1,[])} \<and>
    leader accept_one_again = (\<lambda>_. None)(1 := Some 0, 2 := Some 1) \<and>
    electors accept_one_again = (\<lambda>_. {})(1 := {0,1}, 2 := {1,2}) \<and>
    started accept_one_again = {2,1} \<and>
    active accept_one_again = {1} \<and>
    tip accept_one_again = (\<lambda>_. [])(1 := [(1,1,10)], 2 := [(1,1,10),(2,2,20)]) \<and>
    published accept_one_again = {[(1,1,10),(2,2,20)],[(1,1,10)]} \<and>
    receipts accept_one_again = {(1,[(1,1,10),(2,2,20)]),(1,[(1,1,10)]),(0,[(1,1,10)])} \<and>
    committed accept_one_again = {[(1,1,10)]}"
  by (auto simp: accept_one_again_def)

definition accept_two :: coordination where
  "accept_two = accept_one_again\<lparr>accepted := (accepted accept_one_again)(2 := second_history), receipts := insert (2,second_history) (receipts accept_one_again)\<rparr>"

lemma accept_two_fields [simp]:
  "current accept_two = (\<lambda>_. 0)(0 := 1, 1 := 2, 2 := 2) \<and>
    accepted accept_two = (\<lambda>_. [])(0 := [(1,1,10)], 1 := [(1,1,10),(2,2,20)], 2 := [(1,1,10),(2,2,20)]) \<and>
    joins accept_two = {(2,1,2,[]),(1,1,2,[(1,1,10)]),(1,0,1,[]),(0,0,1,[])} \<and>
    leader accept_two = (\<lambda>_. None)(1 := Some 0, 2 := Some 1) \<and>
    electors accept_two = (\<lambda>_. {})(1 := {0,1}, 2 := {1,2}) \<and>
    started accept_two = {2,1} \<and>
    active accept_two = {1} \<and>
    tip accept_two = (\<lambda>_. [])(1 := [(1,1,10)], 2 := [(1,1,10),(2,2,20)]) \<and>
    published accept_two = {[(1,1,10),(2,2,20)],[(1,1,10)]} \<and>
    receipts accept_two = {(2,[(1,1,10),(2,2,20)]),(1,[(1,1,10),(2,2,20)]),(1,[(1,1,10)]),(0,[(1,1,10)])} \<and>
    committed accept_two = {[(1,1,10)]}"
  by (auto simp: accept_two_def)

definition commit_second :: coordination where
  "commit_second = accept_two\<lparr>committed := insert (tip accept_two 2) (committed accept_two)\<rparr>"

lemma commit_second_fields [simp]:
  "current commit_second = (\<lambda>_. 0)(0 := 1, 1 := 2, 2 := 2) \<and>
    accepted commit_second = (\<lambda>_. [])(0 := [(1,1,10)], 1 := [(1,1,10),(2,2,20)], 2 := [(1,1,10),(2,2,20)]) \<and>
    joins commit_second = {(2,1,2,[]),(1,1,2,[(1,1,10)]),(1,0,1,[]),(0,0,1,[])} \<and>
    leader commit_second = (\<lambda>_. None)(1 := Some 0, 2 := Some 1) \<and>
    electors commit_second = (\<lambda>_. {})(1 := {0,1}, 2 := {1,2}) \<and>
    started commit_second = {2,1} \<and>
    active commit_second = {1} \<and>
    tip commit_second = (\<lambda>_. [])(1 := [(1,1,10)], 2 := [(1,1,10),(2,2,20)]) \<and>
    published commit_second = {[(1,1,10),(2,2,20)],[(1,1,10)]} \<and>
    receipts commit_second = {(2,[(1,1,10),(2,2,20)]),(1,[(1,1,10),(2,2,20)]),(1,[(1,1,10)]),(0,[(1,1,10)])} \<and>
    committed commit_second = {[(1,1,10),(2,2,20)],[(1,1,10)]}"
  by (auto simp: commit_second_def)

text \<open>Node 0 joins term 1.\<close>
lemma join_zero_step: "step example_nodes initial join_zero"
  unfolding join_zero_def
  by (rule step.join[where n=0 and c=0 and t=1])
    (simp_all add: majority_def fresher_eq_def version_def epoch_def)

text \<open>Node 1 joins term 1, voting for candidate 0.\<close>
lemma join_one_step: "step example_nodes join_zero join_one"
  unfolding join_one_def
  by (rule step.join[where n=1 and c=0 and t=1])
    (simp_all add: majority_def fresher_eq_def version_def epoch_def)

text \<open>Node 0 wins the election for term 1 with votes from 0 and 1.\<close>
lemma elect_zero_step: "step example_nodes join_one elect_zero"
proof -
  have started: "0 \<in> started join_one" by simp
  have at_term: "1 = current join_one 0" by simp
  have unled: "leader join_one 1 = None" by simp
  have voted: "\<forall>n\<in>{0,1}. \<exists>h. (n,0,1,h) \<in> joins join_one \<and> h \<preceq> accepted join_one 0"
    by (intro ballI exI conjI) (auto simp: fresher_eq_def epoch_def)
  have joined: "\<exists>c' h. (0,c',1,h) \<in> joins join_one" by auto
  show ?thesis
    unfolding elect_zero_def
    by (rule step.elect[where c=0 and t=1 and Q="{0,1}", OF started at_term unled majority_01 voted joined])
qed

text \<open>Node 0 proposes [(1,1,10)].\<close>
lemma publish_first_step: "step example_nodes elect_zero publish_first"
  unfolding publish_first_def
  by (rule step.propose[where c=0 and t=1 and v=1 and payload=10])
    (simp_all add: majority_def fresher_eq_def version_def epoch_def)

text \<open>Node 0 accepts it.\<close>
lemma accept_zero_step: "step example_nodes publish_first accept_zero"
  unfolding accept_zero_def
  by (rule step.accept[where n=0 and h="first_history"])
    (simp_all add: majority_def fresher_eq_def version_def epoch_def)

text \<open>Node 1 accepts it.\<close>
lemma accept_one_step: "step example_nodes accept_zero accept_one"
  unfolding accept_one_def
  by (rule step.accept[where n=1 and h="first_history"])
    (simp_all add: majority_def fresher_eq_def version_def epoch_def)

text \<open>Nodes 0 and 1 form a majority that commits it.\<close>
lemma commit_first_step: "step example_nodes accept_one commit_first"
  unfolding commit_first_def
  by (rule step.commit[where c=0 and t=1 and Q="{0,1}"])
    (simp_all add: majority_def fresher_eq_def version_def epoch_def)

text \<open>Node 0 restarts.\<close>
lemma restart_zero_step: "step example_nodes commit_first restart_zero"
  unfolding restart_zero_def
  by (rule step.restart[where n=0])

text \<open>Node 1 joins term 2 for candidate 1, reporting [(1,1,10)].\<close>
lemma rejoin_one_step: "step example_nodes restart_zero rejoin_one"
  unfolding rejoin_one_def
  by (rule step.join[where n=1 and c=1 and t=2])
    (simp_all add: majority_def fresher_eq_def version_def epoch_def)

text \<open>Node 2 joins term 2, reporting the empty history.\<close>
lemma join_two_step: "step example_nodes rejoin_one join_two"
  unfolding join_two_def
  by (rule step.join[where n=2 and c=1 and t=2])
    (simp_all add: majority_def fresher_eq_def version_def epoch_def)

text \<open>Node 1 wins the election for term 2 with votes from 1 and 2.\<close>
lemma elect_one_step: "step example_nodes join_two elect_one"
proof -
  have started: "1 \<in> started join_two" by simp
  have at_term: "2 = current join_two 1" by simp
  have unled: "leader join_two 2 = None" by simp
  have voted: "\<forall>n\<in>{1,2}. \<exists>h. (n,1,2,h) \<in> joins join_two \<and> h \<preceq> accepted join_two 1"
  proof
    fix n :: node
    assume "n \<in> {1,2}"
    then consider "n = 1" | "n = 2" by auto
    then show "\<exists>h. (n,1,2,h) \<in> joins join_two \<and> h \<preceq> accepted join_two 1"
    proof cases
      case 1
      then show ?thesis by (intro exI[of _ first_history]) simp
    next
      case 2
      then show ?thesis by (intro exI[of _ "[]"]) (simp add: fresher_eq_def epoch_def)
    qed
  qed
  have joined: "\<exists>c' h. (1,c',2,h) \<in> joins join_two" by auto
  show ?thesis
    unfolding elect_one_def
    by (rule step.elect[where c=1 and t=2 and Q="{1,2}", OF started at_term unled majority_12 voted joined])
qed

text \<open>Node 1 proposes [(1,1,10),(2,2,20)].\<close>
lemma publish_second_step: "step example_nodes elect_one publish_second"
  unfolding publish_second_def
  by (rule step.propose[where c=1 and t=2 and v=2 and payload=20])
    (simp_all add: majority_def fresher_eq_def version_def epoch_def)

text \<open>Node 1 accepts it.\<close>
lemma accept_one_again_step: "step example_nodes publish_second accept_one_again"
  unfolding accept_one_again_def
  by (rule step.accept[where n=1 and h="second_history"])
    (simp_all add: majority_def fresher_eq_def version_def epoch_def)

text \<open>Node 2 accepts it.\<close>
lemma accept_two_step: "step example_nodes accept_one_again accept_two"
  unfolding accept_two_def
  by (rule step.accept[where n=2 and h="second_history"])
    (simp_all add: majority_def fresher_eq_def version_def epoch_def)

text \<open>Nodes 1 and 2 form a majority that commits it.\<close>
lemma commit_second_step: "step example_nodes accept_two commit_second"
  unfolding commit_second_def
  by (rule step.commit[where c=1 and t=2 and Q="{1,2}"])
    (simp_all add: majority_def fresher_eq_def version_def epoch_def)

theorem two_commits_across_restart:
  "\<exists>s. reachable example_nodes s \<and>
    [(1,1,10)] \<in> committed s \<and> [(1,1,10),(2,2,20)] \<in> committed s"
proof -
  have "reachable example_nodes commit_second"
    by (rule reachable.advance[OF _ commit_second_step],
      rule reachable.advance[OF _ accept_two_step],
      rule reachable.advance[OF _ accept_one_again_step],
      rule reachable.advance[OF _ publish_second_step],
      rule reachable.advance[OF _ elect_one_step],
      rule reachable.advance[OF _ join_two_step],
      rule reachable.advance[OF _ rejoin_one_step],
      rule reachable.advance[OF _ restart_zero_step],
      rule reachable.advance[OF _ commit_first_step],
      rule reachable.advance[OF _ accept_one_step],
      rule reachable.advance[OF _ accept_zero_step],
      rule reachable.advance[OF _ publish_first_step],
      rule reachable.advance[OF _ elect_zero_step],
      rule reachable.advance[OF _ join_one_step],
      rule reachable.advance[OF _ join_zero_step],
      rule reachable.initial)
  then show ?thesis by (intro exI[of _ commit_second]) simp
qed

end
