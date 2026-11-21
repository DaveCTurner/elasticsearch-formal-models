theory Quorum_Basics
  imports Main
begin

section \<open>Nodes and majority quorums\<close>

text \<open>
  The definitions shared by the fixed and dynamic coordination models.
\<close>

type_synonym node = nat

definition majority :: "node set \<Rightarrow> node set \<Rightarrow> bool" where
  "majority V Q \<longleftrightarrow> finite V \<and> Q \<subseteq> V \<and> card V < 2 * card Q"

lemma majority_intersects:
  assumes "majority V Q" "majority V R"
  shows "\<exists>n\<in>Q. n \<in> R"
proof (rule ccontr)
  assume "\<not> (\<exists>n\<in>Q. n \<in> R)"
  then have disjoint: "Q \<inter> R = {}" by blast
  from assms have "finite Q" "finite R" "Q \<union> R \<subseteq> V" "finite V"
    unfolding majority_def by (auto intro: finite_subset)
  then have "card Q + card R \<le> card V"
    using card_Un_disjoint[OF \<open>finite Q\<close> \<open>finite R\<close> disjoint]
    by (metis card_mono)
  with assms show False unfolding majority_def by linarith
qed

end
