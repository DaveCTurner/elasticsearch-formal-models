theory Preliminaries
  imports "../../common/isabelle/TLA-Utils"
begin

lemma card_insert_le_general: "card A \<le> card (insert x A)"
proof (cases "finite A")
  case True thus ?thesis by (intro card_insert_le)
qed simp

typedecl Value
typedecl Node

definition ValidConfigs :: "Node set set"
  where "ValidConfigs \<equiv> {vs. finite vs \<and> vs \<noteq> {}}"

definition modifyAt :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"
  where "modifyAt f a0 mb a \<equiv> if a = a0 then mb (f a) else f a"

lemma modifyAt_eq_simp[simp]: "modifyAt f a mb a = mb (f a)" by (simp add: modifyAt_def)
lemma modifyAt_ne_simp[simp]: "a \<noteq> a0 \<Longrightarrow> modifyAt f a0 mb a = f a" by (simp add: modifyAt_def)

definition modified :: "('a \<Rightarrow> 'b) stfun \<Rightarrow> 'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> action"
  where "modified f a mb st \<equiv> f (snd st) = modifyAt (f (fst st)) a mb"

definition updated :: "('a \<Rightarrow> 'b) stfun \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> action"
  where "updated f a b = modified f a (\<lambda>_. b)"

definition unspecified :: "('a \<Rightarrow> 'b) stfun \<Rightarrow> 'a \<Rightarrow> action"
  where "unspecified f a st = (\<forall> a'. a' \<noteq> a \<longrightarrow> f (fst st) a' = f (snd st) a')"

record DescendentsEntry =
  prevT :: nat
  prevI :: nat
  nextT :: nat
  nextI :: nat

record JoinPayload =
  jp_laTerm     :: nat
  jp_laVersion  :: nat

record PublishRequestPayload =
  prq_version  :: nat
  prq_value    :: Value
  prq_config   :: "Node set"
  prq_commConf :: "Node set"

record PublishResponsePayload =
  prs_version  :: nat

record CommitPayload =
  c_version  :: nat

datatype Payload
  = Join            JoinPayload
  | PublishRequest  PublishRequestPayload
  | PublishResponse PublishResponsePayload
  | Commit          CommitPayload

record Message =
  source  :: Node
  dest    :: Node
  "term"  :: nat (* quoting needed because 'term' is a reserved word *)
  payload :: Payload

definition laTerm    :: "Message \<Rightarrow> nat" where "laTerm     m \<equiv> case payload m of Join jp \<Rightarrow> jp_laTerm     jp"
definition laVersion :: "Message \<Rightarrow> nat" where "laVersion  m \<equiv> case payload m of Join jp \<Rightarrow> jp_laVersion  jp"
definition version   :: "Message \<Rightarrow> nat" where "version  m \<equiv> case payload m of
    PublishRequest  prq \<Rightarrow> prq_version  prq
  | PublishResponse prs \<Rightarrow> prs_version  prs
  | Commit          c   \<Rightarrow> c_version    c"
definition "value"   :: "Message \<Rightarrow> Value" where "value m \<equiv> case payload m of
    PublishRequest  prq \<Rightarrow> prq_value prq"
definition config    :: "Message \<Rightarrow> Node set" where "config m \<equiv> case payload m of
    PublishRequest  prq \<Rightarrow> prq_config prq"
definition commConf  :: "Message \<Rightarrow> Node set" where "commConf m \<equiv> case payload m of
    PublishRequest  prq \<Rightarrow> prq_commConf prq"

datatype TermVersion  = TermVersion nat (* term *) nat (* version *)

instantiation TermVersion :: linorder
begin
fun less_TermVersion :: "TermVersion \<Rightarrow> TermVersion \<Rightarrow> bool" where
  "less_TermVersion (TermVersion t1 i1) (TermVersion t2 i2) = (t1 < t2 \<or> (t1 = t2 \<and> i1 < i2))"
definition less_eq_TermVersion :: "TermVersion \<Rightarrow> TermVersion \<Rightarrow> bool" where
  "less_eq_TermVersion ti1 ti2 = (ti1 = ti2 \<or> ti1 < ti2)"
instance proof
  fix x y z :: TermVersion
  obtain tx ix where x: "x = TermVersion tx ix" by (cases x, auto)
  obtain ty iy where y: "y = TermVersion ty iy" by (cases y, auto)
  obtain tz iz where z: "z = TermVersion tz iz" by (cases z, auto)

  from x y z
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" "x \<le> x" "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" "x \<le> y \<or> y \<le> x" by (auto simp add: less_eq_TermVersion_def)
qed
end

end
