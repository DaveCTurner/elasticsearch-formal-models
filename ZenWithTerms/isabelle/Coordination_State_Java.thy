theory Coordination_State_Java
  imports Zen_With_Terms_Refinement
begin

section \<open>Method-boundary model of CoordinationState.java\<close>

text \<open>
  This transcription represents Java state at serialized call boundaries.
  The node record projects PersistedState and the transient fields of
  CoordinationState. A vote collection is represented by the keys of its map.
  The extra stored Join objects and boolean addVote result do not affect
  protocol state. The journal records results available for delivery. A returned
  publication or commit is made available to every destination, as in Next.
\<close>

record 'v java_state =
  java_nodes :: "node \<Rightarrow> 'v local_node"
  java_journal :: "'v message set"

datatype 'v java_action =
    Java_Bootstrap node rank 'v config config
  | Java_Start_Join node node nat
  | Java_Join node node nat rank
  | Java_Client node nat nat 'v config config
  | Java_Publish node publication 'v
  | Java_Response node node rank
  | Java_Commit node node rank
  | Java_Restart node

definition signed_int :: "int \<Rightarrow> int" where
  "signed_int x = (x + 2147483648) mod 4294967296 - 2147483648"

definition java_has_quorum :: "config \<Rightarrow> node set \<Rightarrow> bool" where
  "java_has_quorum D Q \<longleftrightarrow> signed_int (int (card D)) < signed_int (2 * int (card (D \<inter> Q)))"

definition add_vote :: "node set \<Rightarrow> node \<Rightarrow> node set \<Rightarrow> node set" where
  "add_vote E n Q = (if n \<in> E then insert n Q else Q)"

definition java_election :: "'v local_node \<Rightarrow> node set \<Rightarrow> bool" where
  "java_election x Q \<longleftrightarrow> java_has_quorum (local_committed x) Q \<and> java_has_quorum (accepted_config x) Q"

definition java_publication :: "'v local_node \<Rightarrow> node set \<Rightarrow> bool" where
  "java_publication x Q \<longleftrightarrow> java_has_quorum (local_committed x) Q \<and> java_has_quorum (published_config x) Q"

definition java_reset :: "'v local_node \<Rightarrow> 'v local_node" where
  "java_reset x = x\<lparr>join_votes := {}, started_join := False, election_won := False,
    published_version := 0, published_config := accepted_config x, publish_votes := {}\<rparr>"

definition java_put :: "'v java_state \<Rightarrow> node \<Rightarrow> 'v local_node \<Rightarrow> 'v java_state" where
  "java_put j n x = j\<lparr>java_nodes := (java_nodes j)(n := x)\<rparr>"

definition java_initial :: "'v \<Rightarrow> (node \<Rightarrow> nat) \<Rightarrow> 'v java_state" where
  "java_initial value versions = \<lparr>java_nodes = (\<lambda>n. \<lparr>current_term = 0, accepted_key = \<lparr>rank_term = 0, rank_version = versions n\<rparr>,
    accepted_value = value, accepted_config = {}, local_committed = {}, join_votes = {},
    started_join = False, election_won = False, published_version = 0,
    published_config = {}, publish_votes = {}\<rparr>), java_journal = {}\<rparr>"

text \<open>
  These are the runtime protocol checks, excluding Java assertions. A failed
  check leaves the projected state unchanged. Persistence failures, external
  calls and scheduling are governed by the method-boundary contract below.
\<close>

fun java_checks :: "'v java_state \<Rightarrow> 'v java_action \<Rightarrow> bool" where
  "java_checks j (Java_Bootstrap n k value D F) = (accepted_config (java_nodes j n) = {})"
| "java_checks j (Java_Start_Join n c t) = (current_term (java_nodes j n) < t)"
| "java_checks j (Java_Join n c t k) =
    (let x = java_nodes j c in t = current_term x \<and> started_join x \<and>
      k \<le> accepted_key x \<and> accepted_config x \<noteq> {})"
| "java_checks j (Java_Client n t v value D F) =
    (let x = java_nodes j n in election_won x \<and> published_version x = rank_version (accepted_key x) \<and>
      t = current_term x \<and> published_version x < v \<and>
      \<not> (D \<noteq> accepted_config x \<and> local_committed x \<noteq> accepted_config x) \<and>
      java_has_quorum D (join_votes x))"
| "java_checks j (Java_Publish n p value) =
    (let x = java_nodes j n in pub_term p = current_term x \<and>
      \<not> (pub_term p = rank_term (accepted_key x) \<and> pub_version p \<le> rank_version (accepted_key x)))"
| "java_checks j (Java_Response n c k) =
    (let x = java_nodes j c in election_won x \<and> k = published_key x)"
| "java_checks j (Java_Commit n c k) =
    (let x = java_nodes j n in rank_term k = current_term x \<and> k = accepted_key x)"
| "java_checks j (Java_Restart n) = True"

fun java_execute ::
  "node set \<Rightarrow> node set \<Rightarrow> 'v java_state \<Rightarrow> 'v java_action \<Rightarrow> 'v java_state" where
  "java_execute N E j (Java_Bootstrap n k value D F) =
    java_put j n ((java_nodes j n)\<lparr>accepted_key := k, accepted_value := value,
      accepted_config := D, local_committed := F\<rparr>)"
| "java_execute N E j (Java_Start_Join n c t) =
    (let x = java_nodes j n in
     (java_put j n ((java_reset x)\<lparr>current_term := t, started_join := True\<rparr>))
       \<lparr>java_journal := insert (Join_Msg n c t (accepted_key x)) (java_journal j)\<rparr>)"
| "java_execute N E j (Java_Join n c t k) =
    (let x = java_nodes j c; Q = add_vote E n (join_votes x); won = java_election x Q
     in java_put j c (x\<lparr>join_votes := Q, election_won := won,
       published_version := (if won \<and> \<not> election_won x then rank_version (accepted_key x) else published_version x)\<rparr>))"
| "java_execute N E j (Java_Client n t v value D F) =
    (let x = java_nodes j n; p = request n t v D F
     in (java_put j n (x\<lparr>published_version := v, published_config := D, publish_votes := {}\<rparr>))
       \<lparr>java_journal := java_journal j \<union> {Publish_Msg d p value | d. d \<in> N}\<rparr>)"
| "java_execute N E j (Java_Publish n p value) =
    (java_put j n ((java_nodes j n)\<lparr>accepted_key := request_key p, accepted_value := value,
       accepted_config := pub_config p, local_committed := pub_previous p\<rparr>))
       \<lparr>java_journal := insert (Response_Msg n (pub_owner p) (request_key p)) (java_journal j)\<rparr>"
| "java_execute N E j (Java_Response n c k) =
    (let x = java_nodes j c; Q = add_vote E n (publish_votes x)
     in (java_put j c (x\<lparr>publish_votes := Q\<rparr>))
       \<lparr>java_journal := (if java_publication x Q then java_journal j \<union> {Commit_Msg c d k | d. d \<in> N}
         else java_journal j)\<rparr>)"
| "java_execute N E j (Java_Commit n c k) =
    java_put j n ((java_nodes j n)\<lparr>local_committed := accepted_config (java_nodes j n)\<rparr>)"
| "java_execute N E j (Java_Restart n) = java_put j n (java_reset (java_nodes j n))"

definition java_call ::
  "node set \<Rightarrow> node set \<Rightarrow> 'v java_state \<Rightarrow> 'v java_action \<Rightarrow> 'v java_state" where
  "java_call N E j a = (if java_checks j a then java_execute N E j a else j)"

section \<open>Caller contract\<close>

text \<open>
  The universe includes every node ID that can participate and every
  configuration ID, including inert bootstrap placeholders. E is the fixed
  set of master-eligible IDs and inert voting IDs. Only eligible voters are
  inserted into the Java maps. The TLA+ maps may retain votes outside E.
  No required voting configuration contains such a voter.

  The contract below fixes shared bootstrap data, specifies assertions on
  bootstrap and supplied publication metadata, and requires authentic
  routed inputs. A late commit on a leader can be ignored by the abstraction
  if the accepted configuration is already installed. Otherwise the caller
  must deliver the leader's commit before starting another publication.
\<close>

fun caller_contract ::
  "node set \<Rightarrow> node set \<Rightarrow> 'v set \<Rightarrow> config \<Rightarrow> 'v \<Rightarrow> 'v java_state \<Rightarrow> 'v java_action \<Rightarrow> bool" where
  "caller_contract N E V C initial_value j (Java_Bootstrap n k value D F) =
    (let x = java_nodes j n in n \<in> N \<and> k = accepted_key x \<and> rank_term k = 0 \<and>
      D = C \<and> F = C \<and> value = initial_value \<and> local_committed x = {} \<and>
      published_version x = 0 \<and> published_config x = {} \<and> \<not> election_won x \<and>
      join_votes x = {} \<and> publish_votes x = {})"
| "caller_contract N E V C initial_value j (Java_Start_Join n c t) = (n \<in> N \<and> c \<in> N)"
| "caller_contract N E V C initial_value j (Java_Join n c t k) =
    (Join_Msg n c t k \<in> java_journal j)"
| "caller_contract N E V C initial_value j (Java_Client n t v value D F) =
    (n \<in> N \<and> value \<in> V \<and> D \<subseteq> E \<and> F = local_committed (java_nodes j n))"
| "caller_contract N E V C initial_value j (Java_Publish n p value) =
    (Publish_Msg n p value \<in> java_journal j \<and> pub_config p \<subseteq> E \<and> pub_previous p \<subseteq> E)"
| "caller_contract N E V C initial_value j (Java_Response n c k) =
    (Response_Msg n c k \<in> java_journal j)"
| "caller_contract N E V C initial_value j (Java_Commit n c k) =
    (let x = java_nodes j n in Commit_Msg c n k \<in> java_journal j \<and>
      (election_won x \<and> rank_version k \<noteq> published_version x \<longrightarrow> local_committed x = accepted_config x))"
| "caller_contract N E V C initial_value j (Java_Restart n) = (n \<in> N)"

fun abstract_action :: "'v java_action \<Rightarrow> 'v tla_action" where
  "abstract_action (Java_Bootstrap n k value D F) = Bootstrap n"
| "abstract_action (Java_Start_Join n c t) = Start_Join n c t"
| "abstract_action (Java_Join n c t k) = Handle_Join n c t k"
| "abstract_action (Java_Client n t v value D F) = Client_Value n t v value D"
| "abstract_action (Java_Publish n p value) = Handle_Publish n p value"
| "abstract_action (Java_Response n c k) = Handle_Response n c k"
| "abstract_action (Java_Commit n c k) = Handle_Commit c n k"
| "abstract_action (Java_Restart n) = Restart n"

inductive java_reachable ::
  "node set \<Rightarrow> node set \<Rightarrow> 'v set \<Rightarrow> config \<Rightarrow> 'v \<Rightarrow>
    (node \<Rightarrow> nat) \<Rightarrow> 'v java_state \<Rightarrow> bool"
  for N E V C initial_value versions where
  init: "finite N \<Longrightarrow> E \<subseteq> N \<Longrightarrow> card N < 1073741824 \<Longrightarrow>
    C \<subseteq> E \<Longrightarrow> C \<noteq> {} \<Longrightarrow> initial_value \<in> V \<Longrightarrow>
    java_reachable N E V C initial_value versions (java_initial initial_value versions)"
| advance: "java_reachable N E V C initial_value versions j \<Longrightarrow>
    (java_checks j a \<longrightarrow> caller_contract N E V C initial_value j a) \<Longrightarrow>
    java_reachable N E V C initial_value versions (java_call N E j a)"

end
