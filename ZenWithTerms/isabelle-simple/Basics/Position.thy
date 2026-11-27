theory Position
  imports Quorum "HOL-Library.Product_Lexorder"
begin

section \<open>Positions\<close>

text \<open>
  A position is a term together with a version. It orders published states by how recent they are,
  and in any execution of the protocol it identifies a published state: no two publications have
  the same position (\<open>dynamic_unique_publication\<close>).
\<close>

record position =
  position_term :: nat
  position_version :: nat

abbreviation position_zero :: position where
  "position_zero \<equiv> \<lparr>position_term = 0, position_version = 0\<rparr>"

text \<open>
  Positions are ordered lexicographically, by term and then by version. A record cannot
  inherit the order of a pair, so the order is defined on every record extension and
  is the lexicographic order on the two fields followed by the extension.
\<close>

instantiation position_ext :: (linorder) linorder
begin

definition less_eq_position_ext :: "'a position_ext \<Rightarrow> 'a position_ext \<Rightarrow> bool" where
  "a \<le> b \<longleftrightarrow> (position_term a, position_version a, position.more a) \<le> (position_term b, position_version b, position.more b)"

definition less_position_ext :: "'a position_ext \<Rightarrow> 'a position_ext \<Rightarrow> bool" where
  "a < b \<longleftrightarrow> (position_term a, position_version a, position.more a) < (position_term b, position_version b, position.more b)"

instance
proof
  fix a b c :: "'a position_ext"
  show "a < b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a"
    unfolding less_eq_position_ext_def less_position_ext_def by (simp add: less_le_not_le)
  show "a \<le> a" unfolding less_eq_position_ext_def by simp
  show "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c"
    unfolding less_eq_position_ext_def by (rule order_trans)
  show "a \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a = b"
  proof -
    assume "a \<le> b" "b \<le> a"
    then have "(position_term a, position_version a, position.more a) = (position_term b, position_version b, position.more b)"
      unfolding less_eq_position_ext_def by (rule antisym)
    then show "a = b" by (simp add: position.equality)
  qed
  show "a \<le> b \<or> b \<le> a"
    unfolding less_eq_position_ext_def by (rule linear)
qed

end

lemma position_eta[simp]: "\<lparr>
  position_term    = position_term (k :: position),
  position_version = position_version k
\<rparr> = k"
  by (cases k) simp

lemma position_le_iff:
  fixes a b :: position
  shows "a \<le> b \<longleftrightarrow> position_term a < position_term b
                 \<or> position_term a = position_term b \<and> position_version a \<le> position_version b"
  unfolding less_eq_position_ext_def by (auto simp: less_eq_prod_def less_prod_def order_le_less)

lemma position_less_iff:
  fixes a b :: position
  shows "a < b \<longleftrightarrow> position_term a < position_term b
                 \<or> position_term a = position_term b \<and> position_version a < position_version b"
  unfolding less_position_ext_def by (auto simp: less_prod_def order_le_less)

lemma position_term_mono: "(p :: position) \<le> q \<Longrightarrow> position_term p \<le> position_term q"
  by (auto simp: position_le_iff)

lemma position_maximum:
  fixes f :: "'a \<Rightarrow> 'b::linorder"
  assumes "finite A" "A \<noteq> {}"
  obtains x where "x \<in> A" "\<And>y. y \<in> A \<Longrightarrow> f y \<le> f x"
proof -
  have fin: "finite (image f A)" using assms by simp
  have "Max (image f A) \<in> image f A" using Max_in[OF fin] assms by simp
  then obtain x where x: "x \<in> A" and eq: "Max (image f A) = f x" by blast
  show thesis
  proof (rule that[OF x])
    fix y
    assume "y \<in> A"
    then have "f y \<le> Max (image f A)" by (intro Max_ge[OF fin]) simp
    then show "f y \<le> f x" by (simp only: eq)
  qed
qed

lemma position_minimum:
  fixes f :: "'a \<Rightarrow> 'b::linorder"
  assumes "finite A" "A \<noteq> {}"
  obtains x where "x \<in> A" "\<And>y. y \<in> A \<Longrightarrow> f x \<le> f y"
proof -
  have fin: "finite (image f A)" using assms by simp
  have "Min (image f A) \<in> image f A" using Min_in[OF fin] assms by simp
  then obtain x where x: "x \<in> A" and eq: "Min (image f A) = f x" by blast
  show thesis
  proof (rule that[OF x])
    fix y
    assume "y \<in> A"
    then have "Min (image f A) \<le> f y" by (intro Min_le[OF fin]) simp
    then show "f x \<le> f y" by (simp only: eq)
  qed
qed

end
