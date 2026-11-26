theory Quorum_Basics
  imports Main
begin

section \<open>Nodes and majority quorums\<close>

text \<open>
  Node IDs and the strict-majority relation that underlies every quorum in these theories.
\<close>

typedecl node

text \<open>
  Every value of type \<open>node\<close> is a legal node ID, and there is no bound on their number. A
  configuration whose voting nodes are infinite is never satisfied by any finite set of votes, so
  no election or commit can use one.
\<close>

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

datatype configuration_element
  = ConfigNode node
  | StaleConfigurationMarker

type_synonym config = "configuration_element set"

text \<open>
  A configuration is the set of nodes whose votes count. A set of votes is a quorum of a
  configuration if it contains a majority of the configuration's nodes.
\<close>

definition voting_nodes_of :: "config \<Rightarrow> node set" where
  "voting_nodes_of config \<equiv> {n. ConfigNode n \<in> config}"

definition quorum :: "config \<Rightarrow> node set \<Rightarrow> bool" where
  "quorum configuration votes \<longleftrightarrow> majority (voting_nodes_of configuration) ((voting_nodes_of configuration) \<inter> votes)"

lemma quorum_intersects:
  assumes "quorum C Q" "quorum C R"
  obtains n where "n \<in> Q" "n \<in> R"
  using majority_intersects assms unfolding quorum_def by blast

end
