theory Publication_Basics
  imports Position_Basics
begin

section \<open>Publications and publication histories\<close>

text \<open>
  A publication is the metadata of a published state, and a publication history is the chain of publications
  that led to a state, oldest first.
\<close>

record publication =
  publication_position :: position
  publication_owner :: node
  publication_config :: config
  publication_previous_config :: config

type_synonym publication_history = "publication list"

fun at_tip :: "'a \<Rightarrow> (publication \<Rightarrow> 'a) \<Rightarrow> publication_history \<Rightarrow> 'a" where
  "at_tip empty_value project [] = empty_value"
| "at_tip empty_value project (request # requests) =
    (if requests = [] then project request else at_tip empty_value project requests)"

lemma at_tip_snoc[simp]: "at_tip empty_value project (publication_history @ [request]) = project request"
  by (induction publication_history) auto

abbreviation position_of_tip_of :: "publication_history \<Rightarrow> position" where
  "position_of_tip_of \<equiv> at_tip position_zero
    publication_position"

abbreviation term_of_tip_of :: "publication_history \<Rightarrow> nat" where
  "term_of_tip_of publication_history \<equiv> position_term (position_of_tip_of publication_history)"

abbreviation config_of_tip_of :: "config \<Rightarrow> publication_history \<Rightarrow> config" where
  "config_of_tip_of initial_configuration \<equiv> at_tip initial_configuration publication_config"

abbreviation previous_config_of_tip_of :: "config \<Rightarrow> publication_history \<Rightarrow> config" where
  "previous_config_of_tip_of initial_configuration \<equiv> at_tip initial_configuration publication_previous_config"

abbreviation owner_of_tip_of :: "publication_history \<Rightarrow> node" where
  "owner_of_tip_of \<equiv> at_tip (SOME n. True) publication_owner"

text \<open>
  The publication that \<open>handleClientValue\<close> returns, for a state with the given position (term and
  version), last accepted configuration and last committed configuration. It is built by a record
  construction at each call site, rather than by a constructor function.
\<close>

end
