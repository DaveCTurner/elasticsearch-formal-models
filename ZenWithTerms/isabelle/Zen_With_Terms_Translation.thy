theory Zen_With_Terms_Translation
  imports Dynamic_Configuration
begin

section \<open>The Init and Next actions of ZenWithTerms.tla\<close>

text \<open>
  A local record groups the entries for one node in the TLA+ function variables.
  Configuration and value constants are parameters. The four message tags are
  distinct constructors. Natural node IDs represent a finite set of Nodes.
  The opaque TLA+ values have an arbitrary Isabelle type. The publication
  metadata reuses the abstract record with a dummy payload; the wire value is
  a separate field and is never changed by message delivery.
\<close>

datatype 'v message =
    Join_Msg node node nat rank
  | Publish_Msg node publication 'v
  | Response_Msg node node rank
  | Commit_Msg node node rank

record 'v local_node =
  current_term :: nat
  accepted_key :: rank
  accepted_value :: 'v
  accepted_config :: config
  local_committed :: config
  join_votes :: "node set"
  started_join :: bool
  election_won :: bool
  published_version :: nat
  published_config :: config
  publish_votes :: "node set"

record 'v tla_state =
  nodes_at :: "node \<Rightarrow> 'v local_node"
  messages :: "'v message set"
  descendant :: "(rank \<times> rank) set"

datatype 'v tla_action =
    Bootstrap node
  | Start_Join node node nat
  | Handle_Join node node nat rank
  | Client_Value node nat nat 'v config
  | Handle_Publish node publication 'v
  | Handle_Response node node rank
  | Handle_Commit node node rank
  | Restart node

definition tla_initial :: "'v \<Rightarrow> (node \<Rightarrow> nat) \<Rightarrow> 'v tla_state" where
  "tla_initial value versions = \<lparr>
    nodes_at = (\<lambda>n. \<lparr>current_term = 0, accepted_key = \<lparr>rank_term = 0, rank_version = versions n\<rparr>, accepted_value = value,
      accepted_config = {}, local_committed = {}, join_votes = {}, started_join = False,
      election_won = False, published_version = 0, published_config = {}, publish_votes = {}\<rparr>),
    messages = {}, descendant = {}\<rparr>"

definition put_node :: "'v tla_state \<Rightarrow> node \<Rightarrow> 'v local_node \<Rightarrow> 'v tla_state" where
  "put_node s n x = s\<lparr>nodes_at := (nodes_at s)(n := x)\<rparr>"

definition reset_transient :: "'v local_node \<Rightarrow> 'v local_node" where
  "reset_transient x = x\<lparr>join_votes := {}, started_join := False, election_won := False,
    published_version := 0, published_config := accepted_config x, publish_votes := {}\<rparr>"

definition election_quorum :: "'v local_node \<Rightarrow> node set \<Rightarrow> bool" where
  "election_quorum x Q \<longleftrightarrow> quorum (local_committed x) Q \<and> quorum (accepted_config x) Q"

definition response_quorum :: "'v local_node \<Rightarrow> node set \<Rightarrow> bool" where
  "response_quorum x Q \<longleftrightarrow> quorum (local_committed x) Q \<and> quorum (published_config x) Q"

abbreviation published_key :: "'v local_node \<Rightarrow> rank" where
  "published_key x \<equiv> \<lparr>rank_term = current_term x, rank_version = published_version x\<rparr>"

abbreviation request_key :: "publication \<Rightarrow> rank" where
  "request_key p \<equiv> \<lparr>rank_term = pub_term p, rank_version = pub_version p\<rparr>"

definition request :: "node \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> config \<Rightarrow> config \<Rightarrow> publication" where
  "request n t v D E = \<lparr>pub_term = t, pub_version = v, pub_payload = 0,
    pub_owner = n, pub_config = D, pub_previous = E\<rparr>"

definition extend_descendant :: "(rank \<times> rank) set \<Rightarrow> rank \<Rightarrow> rank \<Rightarrow> (rank \<times> rank) set" where
  "extend_descendant G p h = G \<union> {(p,h)} \<union> {(a,h) | a. (a,p) \<in> G}"

fun enabled :: "node set \<Rightarrow> 'v set \<Rightarrow> 'v tla_state \<Rightarrow> 'v tla_action \<Rightarrow> bool" where
  "enabled N V s (Bootstrap n) =
    (let x = nodes_at s n in n \<in> N \<and> accepted_config x = {} \<and> rank_term (accepted_key x) = 0 \<and>
      local_committed x = {} \<and> published_version x = 0 \<and> published_config x = {} \<and>
      \<not> election_won x \<and> join_votes x = {} \<and> publish_votes x = {})"
| "enabled N V s (Start_Join n c t) = (n \<in> N \<and> c \<in> N \<and> current_term (nodes_at s n) < t)"
| "enabled N V s (Handle_Join n c t r) =
    (let x = nodes_at s c in Join_Msg n c t r \<in> messages s \<and> t = current_term x \<and>
      started_join x \<and> r \<le> accepted_key x \<and> accepted_config x \<noteq> {})"
| "enabled N V s (Client_Value n t v value D) =
    (let x = nodes_at s n in n \<in> N \<and> value \<in> V \<and> D \<subseteq> N \<and> D \<noteq> {} \<and>
      election_won x \<and> published_version x = rank_version (accepted_key x) \<and> t = current_term x \<and>
      published_version x < v \<and>
      (D \<noteq> accepted_config x \<longrightarrow> local_committed x = accepted_config x) \<and> quorum D (join_votes x))"
| "enabled N V s (Handle_Publish n p value) =
    (let x = nodes_at s n in Publish_Msg n p value \<in> messages s \<and> pub_term p = current_term x \<and>
      (pub_term p = rank_term (accepted_key x) \<longrightarrow> rank_version (accepted_key x) < pub_version p))"
| "enabled N V s (Handle_Response n c k) =
    (let x = nodes_at s c in Response_Msg n c k \<in> messages s \<and> election_won x \<and> k = published_key x)"
| "enabled N V s (Handle_Commit c n k) =
    (let x = nodes_at s n in Commit_Msg c n k \<in> messages s \<and>
      rank_term k = current_term x \<and> k = accepted_key x \<and>
      (election_won x \<longrightarrow> rank_version k = published_version x))"
| "enabled N V s (Restart n) = (n \<in> N)"

fun execute :: "node set \<Rightarrow> config \<Rightarrow> 'v \<Rightarrow> 'v tla_state \<Rightarrow> 'v tla_action \<Rightarrow> 'v tla_state" where
  "execute N C initial_value s (Bootstrap n) =
    put_node s n ((nodes_at s n)\<lparr>accepted_config := C, local_committed := C, accepted_value := initial_value\<rparr>)"
| "execute N C initial_value s (Start_Join n c t) =
    (let x = nodes_at s n in
     (put_node s n ((reset_transient x)\<lparr>current_term := t, started_join := True\<rparr>))
       \<lparr>messages := insert (Join_Msg n c t (accepted_key x)) (messages s)\<rparr>)"
| "execute N C initial_value s (Handle_Join n c t r) =
    (let x = nodes_at s c; Q = insert n (join_votes x); won = election_quorum x Q
     in put_node s c (x\<lparr>join_votes := Q, election_won := won,
       published_version := (if \<not> election_won x \<and> won then rank_version (accepted_key x) else published_version x)\<rparr>))"
| "execute N C initial_value s (Client_Value n t v value D) =
    (let x = nodes_at s n; p = request n t v D (local_committed x)
     in (put_node s n (x\<lparr>published_version := v, published_config := D, publish_votes := {}\<rparr>))
       \<lparr>messages := messages s \<union> {Publish_Msg d p value | d. d \<in> N},
         descendant := extend_descendant (descendant s) (accepted_key x) \<lparr>rank_term = t, rank_version = v\<rparr>\<rparr>)"
| "execute N C initial_value s (Handle_Publish n p value) =
    (put_node s n ((nodes_at s n)\<lparr>accepted_key := request_key p, accepted_value := value,
       accepted_config := pub_config p, local_committed := pub_previous p\<rparr>))
       \<lparr>messages := insert (Response_Msg n (pub_owner p) (request_key p)) (messages s)\<rparr>"
| "execute N C initial_value s (Handle_Response n c k) =
    (let x = nodes_at s c; Q = insert n (publish_votes x)
     in (put_node s c (x\<lparr>publish_votes := Q\<rparr>))
       \<lparr>messages := (if response_quorum x Q then messages s \<union> {Commit_Msg c d k | d. d \<in> N}
         else messages s)\<rparr>)"
| "execute N C initial_value s (Handle_Commit c n k) =
    (let x = nodes_at s n in put_node s n (x\<lparr>local_committed := accepted_config x\<rparr>))"
| "execute N C initial_value s (Restart n) = put_node s n (reset_transient (nodes_at s n))"

inductive tla_reachable ::
  "node set \<Rightarrow> 'v set \<Rightarrow> config \<Rightarrow> 'v \<Rightarrow> (node \<Rightarrow> nat) \<Rightarrow> 'v tla_state \<Rightarrow> bool"
  for N V C initial_value versions where
  init: "finite N \<Longrightarrow> C \<subseteq> N \<Longrightarrow> C \<noteq> {} \<Longrightarrow> initial_value \<in> V \<Longrightarrow>
    tla_reachable N V C initial_value versions (tla_initial initial_value versions)"
| advance: "tla_reachable N V C initial_value versions s \<Longrightarrow> enabled N V s a \<Longrightarrow>
    tla_reachable N V C initial_value versions (execute N C initial_value s a)"

end
