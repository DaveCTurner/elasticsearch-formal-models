theory Coordination_Transport
  imports Coordinator_Lifecycle
begin

section \<open>Publication wire projection\<close>

datatype 'v publication_wire =
    Full_State
  | Local_State
  | Diff_State bool 'v publication 'v

definition publication_identity where
  "publication_identity p = (request_key p, pub_owner p, pub_config p, pub_payload p)"

text \<open>
  A diff carries a base UUID and a target UUID. The receiver may have the
  target already. In that case ClusterStateDiff returns the cached state,
  and the transport wrapper still restores the transmitted committed configuration.
  On a matching base, an empty DiscoveryNodes diff keeps the cached master.
  A replacement carries the target master even when the sender's base was
  a masterless view of an accepted state.
\<close>

fun decode_publication where
  "decode_publication p u Full_State = Some p"
| "decode_publication p u Local_State = Some p"
| "decode_publication p u (Diff_State keep_master b cached d) =
    (if d = u then Some (cached\<lparr>pub_previous := pub_previous p\<rparr>)
     else if d = b then Some (p\<lparr>pub_owner :=
       (if keep_master then pub_owner cached else pub_owner p)\<rparr>)
     else None)"

fun compatible_publication where
  "compatible_publication p u Full_State = True"
| "compatible_publication p u Local_State = True"
| "compatible_publication p u (Diff_State keep_master b cached d) =
    ((d = u \<longrightarrow> publication_identity cached = publication_identity p) \<and>
     (d = b \<and> keep_master \<longrightarrow> pub_owner cached = pub_owner p))"

lemma restore_committed_projection:
  "publication_identity cached = publication_identity p \<Longrightarrow>
    cached\<lparr>pub_previous := pub_previous p\<rparr> = p"
  by (cases cached; cases p) (simp add: publication_identity_def)

lemma decode_publication_correct:
  assumes "compatible_publication p u wire" "decode_publication p u wire = Some decoded"
  shows "decoded = p"
  using assms
proof (cases wire)
  case (Diff_State keep_master b cached d)
  show ?thesis
  proof (cases "d = u")
    case True
    with Diff_State assms show ?thesis by (simp add: restore_committed_projection)
  next
    case False
    with Diff_State assms show ?thesis
      by (auto simp: publication_identity_def split: if_splits)
  qed
qed auto

section \<open>Transport paths at coordination call boundaries\<close>

datatype routed_vote = Vote node node nat rank

fun vote_message :: "routed_vote \<Rightarrow> 'v message" where
  "vote_message (Vote n c t k) = Join_Msg n c t k"

fun vote_matches where
  "vote_matches n c t (Vote voter candidate term key) = (voter = n \<and> candidate = c \<and> term = t)"

fun vote_candidate where
  "vote_candidate (Vote n c t k) = c"

datatype 'v transport_item =
    Returned_Vote routed_vote
  | Sent_Vote node routed_vote
  | Registered_State publication 'v
  | Publish_RPC node nat node publication 'v
  | Publish_Reply node nat node rank "routed_vote option"
  | Routed_Response node node rank
  | Retired_RPC node nat
  | Returned_Commit node rank
  | Sent_Commit node node rank

abbreviation journal where "journal s \<equiv> java_journal (coordination s)"
abbreviation registered where
  "registered s c k \<equiv> k \<in> registered_publications (lifecycle_at s c)"

fun local_event where
  "local_event (Dispatch (Java_Bootstrap n k v D F) enter) = True"
| "local_event (Dispatch (Java_Restart n) enter) = True"
| "local_event (Dispatch a enter) = False"
| "local_event (Begin_Publication n t w v D F install) = (\<not> install)"
| "local_event _ = True"

definition response_quorum where
  "response_quorum E s n c \<longleftrightarrow>
    (let x = java_nodes (coordination s) c in java_publication x (add_vote E n (publish_votes x)))"

fun enqueue_vote where
  "enqueue_vote c None H = H"
| "enqueue_vote c (Some q) H = insert (Sent_Vote c q) H"

text \<open>
  Traffic is a history. Failed decoding, dropped messages and calls rejected
  before a successful method boundary can leave the state unchanged. Publish
  replies carry a ghost actual responder and no wire voter ID. A callback
  looks up its destination using the issuer and logical request ID. Logical
  IDs name individual registrations. A wire ID may be recycled after old
  replies can no longer reach the lookup. The retired marker models removal
  of that handler, including timeout and disconnection.
\<close>

inductive transport_step for N E V C v where
  control:
    "local_event a \<Longrightarrow> coordinator_enabled N E V C v s a \<Longrightarrow>
     transport_step N E V C v s H (coordinator_execute N E s a) H"
| start_join:
    "coordinator_enabled N E V C v s (Dispatch (Java_Start_Join n c t) False) \<Longrightarrow>
     transport_step N E V C v s H (coordinator_execute N E s (Dispatch (Java_Start_Join n c t) False))
       (insert (Returned_Vote (Vote n c t (accepted_key (java_nodes (coordination s) n)))) H)"
| send_vote:
    "Returned_Vote q \<in> H \<Longrightarrow> vote_matches n c t q \<Longrightarrow>
     transport_step N E V C v s H s (insert (Sent_Vote c q) H)"
| receive_vote:
    "Sent_Vote d (Vote n c t k) \<in> H \<Longrightarrow> java_checks (coordination s) (Java_Join n d t k) \<Longrightarrow>
     (enter \<Longrightarrow> leader_entry N E (coordination s) (Java_Join n d t k)) \<Longrightarrow>
     transport_step N E V C v s H (coordinator_execute N E s (Dispatch (Java_Join n d t k) enter)) H"
| begin_publication:
    "coordinator_enabled N E V C v s (Begin_Publication c t w u D F True) \<Longrightarrow>
     transport_step N E V C v s H (coordinator_execute N E s (Begin_Publication c t w u D F True))
       (insert (Registered_State (request c t w D F) u) H)"
| send_publish:
    "Registered_State p u \<in> H \<Longrightarrow> n \<in> N \<Longrightarrow>
     (\<And>d q x. Publish_RPC (pub_owner p) i d q x \<notin> H) \<Longrightarrow>
     transport_step N E V C v s H s (insert (Publish_RPC (pub_owner p) i n p u) H)"
| receive_publish:
    "Publish_RPC c i n p u \<in> H \<Longrightarrow>
     (wire = Local_State \<Longrightarrow> n = c) \<Longrightarrow>
     compatible_publication p u wire \<Longrightarrow> decode_publication p u wire = Some decoded \<Longrightarrow>
     java_checks (coordination s) (Java_Publish n decoded u) \<Longrightarrow>
     (\<And>q. opt = Some q \<Longrightarrow> Returned_Vote q \<in> H \<and> vote_matches n (pub_owner decoded) (pub_term decoded) q) \<Longrightarrow>
     transport_step N E V C v s H (coordinator_execute N E s (Dispatch (Java_Publish n decoded u) False))
       (insert (Publish_Reply c i n (request_key decoded) opt) H)"
| publish_callback:
    "Publish_RPC c i n p u \<in> H \<Longrightarrow> Publish_Reply c i actual k opt \<in> H \<Longrightarrow> Retired_RPC c i \<notin> H \<Longrightarrow>
     transport_step N E V C v s H s
       (insert (Retired_RPC c i) (insert (Routed_Response n c k) (enqueue_vote c opt H)))"
| retire:
    "Publish_RPC c i n p u \<in> H \<Longrightarrow>
     transport_step N E V C v s H s (insert (Retired_RPC c i) H)"
| count_response:
    "Routed_Response n c k \<in> H \<Longrightarrow> java_checks (coordination s) (Java_Response n c k) \<Longrightarrow>
     transport_step N E V C v s H (coordinator_execute N E s (Dispatch (Java_Response n c k) False))
       (if response_quorum E s n c then insert (Returned_Commit c k) H else H)"
| send_commit:
    "Returned_Commit c k \<in> H \<Longrightarrow> n \<in> N \<Longrightarrow>
     transport_step N E V C v s H s (insert (Sent_Commit c n k) H)"
| receive_commit:
    "Sent_Commit c n k \<in> H \<Longrightarrow> java_checks (coordination s) (Java_Commit n c k) \<Longrightarrow>
     transport_step N E V C v s H (coordinator_execute N E s (Dispatch (Java_Commit n c k) False)) H"

section \<open>Provenance and routing invariants\<close>

definition publish_from where
  "publish_from E s c p \<longleftrightarrow> c = pub_owner p \<and> registered s c (request_key p) \<and>
    pub_config p \<subseteq> E \<and> pub_previous p \<subseteq> E"

fun supported where
  "supported N E s (Returned_Vote q) = (vote_message q \<in> journal s)"
| "supported N E s (Sent_Vote d q) = (d = vote_candidate q \<and> vote_message q \<in> journal s)"
| "supported N E s (Registered_State p u) =
    (publish_from E s (pub_owner p) p \<and> (\<forall>d\<in>N. Publish_Msg d p u \<in> journal s))"
| "supported N E s (Publish_RPC c i n p u) =
    (publish_from E s c p \<and> Publish_Msg n p u \<in> journal s)"
| "supported N E s (Publish_Reply c i n k opt) =
    (Response_Msg n c k \<in> journal s \<and> registered s c k \<and>
      (\<forall>q\<in>set_option opt. vote_message q \<in> journal s \<and> vote_matches n c (rank_term k) q))"
| "supported N E s (Routed_Response n c k) = (Response_Msg n c k \<in> journal s \<and> registered s c k)"
| "supported N E s (Retired_RPC c i) = True"
| "supported N E s (Returned_Commit c k) = (registered s c k \<and> (\<forall>d\<in>N. Commit_Msg c d k \<in> journal s))"
| "supported N E s (Sent_Commit c n k) = (registered s c k \<and> Commit_Msg c n k \<in> journal s)"

definition routing_ok where
  "routing_ok H \<longleftrightarrow>
    (\<forall>c i n p u d q x. Publish_RPC c i n p u \<in> H \<longrightarrow>
      Publish_RPC c i d q x \<in> H \<longrightarrow> n = d \<and> p = q \<and> u = x) \<and>
    (\<forall>c i n k opt. Publish_Reply c i n k opt \<in> H \<longrightarrow>
      (\<exists>p u. Publish_RPC c i n p u \<in> H \<and> k = request_key p))"

lemma reply_origin:
  assumes "routing_ok H" "Publish_Reply c i n k opt \<in> H"
  obtains p u where "Publish_RPC c i n p u \<in> H" "k = request_key p"
  using assms unfolding routing_ok_def by metis

lemma routed_reply:
  assumes "routing_ok H" "Publish_RPC c i n p u \<in> H" "Publish_Reply c i actual k opt \<in> H"
  shows "actual = n" "k = request_key p"
proof -
  obtain q x where "Publish_RPC c i actual q x \<in> H" and k: "k = request_key q"
    by (rule reply_origin[OF assms(1,3)])
  with assms(1,2) have "actual = n \<and> q = p" unfolding routing_ok_def by metis
  then show "actual = n" "k = request_key p" using k by simp_all
qed

lemma add_rpc:
  assumes ok: "routing_ok H" and fresh: "\<And>d q x. Publish_RPC c i d q x \<notin> H"
  shows "routing_ok (insert (Publish_RPC c i n p u) H)"
  unfolding routing_ok_def
proof (rule conjI; intro allI impI)
  fix a j d q x e r y
  assume "Publish_RPC a j d q x \<in> insert (Publish_RPC c i n p u) H"
    "Publish_RPC a j e r y \<in> insert (Publish_RPC c i n p u) H"
  with ok fresh show "d = e \<and> q = r \<and> x = y"
    unfolding routing_ok_def by auto
next
  fix a j d k opt
  assume "Publish_Reply a j d k opt \<in> insert (Publish_RPC c i n p u) H"
  then have "Publish_Reply a j d k opt \<in> H" by simp
  then obtain q x where "Publish_RPC a j d q x \<in> H" "k = request_key q"
    by (rule reply_origin[OF ok])
  then show "\<exists>q x. Publish_RPC a j d q x \<in> insert (Publish_RPC c i n p u) H \<and> k = request_key q"
    by (intro exI[of _ q] exI[of _ x]) simp
qed

lemma add_reply:
  assumes ok: "routing_ok H" and sent: "Publish_RPC c i n p u \<in> H"
  shows "routing_ok (insert (Publish_Reply c i n (request_key p) opt) H)"
  unfolding routing_ok_def
proof (rule conjI; intro allI impI)
  fix a j d q x e r y
  assume "Publish_RPC a j d q x \<in> insert (Publish_Reply c i n (request_key p) opt) H"
    "Publish_RPC a j e r y \<in> insert (Publish_Reply c i n (request_key p) opt) H"
  with ok show "d = e \<and> q = r \<and> x = y" unfolding routing_ok_def by auto
next
  fix a j d k reply_vote
  assume "Publish_Reply a j d k reply_vote \<in> insert (Publish_Reply c i n (request_key p) opt) H"
  then consider "a = c" "j = i" "d = n" "k = request_key p" |
    "Publish_Reply a j d k reply_vote \<in> H" by auto
  then show "\<exists>q x. Publish_RPC a j d q x \<in> insert (Publish_Reply c i n (request_key p) opt) H \<and> k = request_key q"
  proof cases
    case 1
    with sent show ?thesis by (intro exI[of _ p] exI[of _ u]) simp
  next
    case 2
    then obtain q x where "Publish_RPC a j d q x \<in> H" "k = request_key q"
      by (rule reply_origin[OF ok])
    then show ?thesis by (intro exI[of _ q] exI[of _ x]) simp
  qed
qed

lemma journal_grows:
  "journal s \<subseteq> journal (coordinator_execute N E s a)"
proof (cases a)
  case (Dispatch action enter)
  then show ?thesis by (cases action) (auto simp: put_lifecycle_def Let_def java_put_def)
qed (auto simp: put_lifecycle_def Let_def java_put_def)

lemma registration_grows:
  assumes "registered s c k"
  shows "registered (coordinator_execute N E s a) c k"
proof (cases a)
  case (Dispatch action enter)
  then show ?thesis using assms
    by (cases action) (auto simp: put_lifecycle_def split: if_splits)
qed (use assms in \<open>auto simp: put_lifecycle_def Let_def split: if_splits\<close>)

lemma supported_later:
  assumes "supported N E s msg"
  shows "supported N E (coordinator_execute N E s a) msg"
  using assms journal_grows[of s N E a]
  by (cases msg) (auto simp: publish_from_def intro: registration_grows)

lemma past_configs:
  assumes "coordinator_reachable N E V C v versions s"
  shows "local_committed (java_nodes (coordination s) c) \<subseteq> E"
proof -
  obtain t where "configurations_ok E t" "coordination s = project_java E t"
    using coordinator_refines_tla[OF assms] by blast
  then show ?thesis by (simp add: configurations_okD(2) mask_votes_def)
qed

lemma advance_transport:
  assumes enabled: "coordinator_enabled N E V C v s a"
    and past: "\<And>msg. msg \<in> H \<Longrightarrow> supported N E s msg"
    and added: "\<And>msg. msg \<in> H' \<Longrightarrow> msg \<notin> H \<Longrightarrow>
      supported N E (coordinator_execute N E s a) msg"
    and routing: "routing_ok H'"
  shows "(coordinator_execute N E s a = s \<or> (\<exists>b. coordinator_enabled N E V C v s b \<and>
      coordinator_execute N E s a = coordinator_execute N E s b)) \<and>
    (\<forall>msg\<in>H'. supported N E (coordinator_execute N E s a) msg) \<and> routing_ok H'"
  using enabled routing supported_later[OF past] added by blast

lemma transport_step_refines:
  assumes step: "transport_step N E V C v s H s' H'"
    and reach: "coordinator_reachable N E V C v versions s"
    and history: "\<And>msg. msg \<in> H \<Longrightarrow> supported N E s msg"
    and routing: "routing_ok H"
  shows "(s' = s \<or> (\<exists>a. coordinator_enabled N E V C v s a \<and> s' = coordinator_execute N E s a)) \<and>
    (\<forall>msg\<in>H'. supported N E s' msg) \<and> routing_ok H'"
  using step
proof cases
  case control
  show ?thesis unfolding control(1,2)
    by (rule advance_transport[OF control(4) history]) (use routing in auto)
next
  case (start_join n c t)
  show ?thesis unfolding start_join(1,2)
    by (rule advance_transport[OF start_join(3) history])
      (use routing in \<open>auto simp: routing_ok_def put_lifecycle_def Let_def\<close>)
next
  case (send_vote q n c t)
  then show ?thesis using history routing by (cases q) (auto simp: routing_ok_def dest: history)
next
  case (receive_vote d n c t k enter)
  have enabled: "coordinator_enabled N E V C v s (Dispatch (Java_Join n d t k) enter)"
    using receive_vote by (auto dest: history)
  show ?thesis unfolding receive_vote(1,2)
    by (rule advance_transport[OF enabled history]) (use routing in auto)
next
  case (begin_publication c t w u D F)
  then have previous: "F \<subseteq> E" using past_configs[OF reach, of c] by auto
  show ?thesis unfolding begin_publication(1,2)
    by (rule advance_transport[OF begin_publication(3) history])
      (use begin_publication(3) routing previous in
        \<open>auto simp: routing_ok_def put_lifecycle_def Let_def publish_from_def request_def\<close>)
next
  case (send_publish p u n i)
  then show ?thesis using history add_rpc[OF routing send_publish(5)]
    by (auto dest!: history)
next
  case (receive_publish c i n p u wire decoded opt)
  then have decoded: "decoded = p" by (blast intro: decode_publication_correct)
  have src: "supported N E s (Publish_RPC c i n p u)"
    by (rule history[OF receive_publish(3)])
  have src': "supported N E (coordinator_execute N E s (Dispatch (Java_Publish n decoded u) False))
      (Publish_RPC c i n p u)" by (rule supported_later[OF src])
  have opt: "vote_message q \<in> journal (coordinator_execute N E s (Dispatch (Java_Publish n decoded u) False)) \<and>
        vote_matches n (pub_owner p) (pub_term p) q" if "q \<in> set_option opt" for q
  proof -
    from that have "opt = Some q" by (cases opt) auto
    with receive_publish have "Returned_Vote q \<in> H \<and> vote_matches n (pub_owner p) (pub_term p) q"
      using decoded by blast
    then have returned: "Returned_Vote q \<in> H"
      and matches: "vote_matches n (pub_owner p) (pub_term p) q" by auto
    have "supported N E (coordinator_execute N E s (Dispatch (Java_Publish n decoded u) False)) (Returned_Vote q)"
      by (rule supported_later[OF history[OF returned]])
    with matches show ?thesis by (simp only: supported.simps)
  qed
  have enabled: "coordinator_enabled N E V C v s (Dispatch (Java_Publish n decoded u) False)"
    using receive_publish decoded src by (auto simp: publish_from_def)
  show ?thesis unfolding receive_publish(1,2)
    by (rule advance_transport[OF enabled history])
      (use decoded src' opt add_reply[OF routing receive_publish(3)] in
        \<open>auto simp: publish_from_def put_lifecycle_def simp del: split_paired_All\<close>)
next
  case (publish_callback c i n p u actual k opt)
  then have "actual = n" by (blast intro: routed_reply(1)[OF routing])
  moreover have "vote_candidate q = c" if "vote_matches n c (rank_term k) q" for q
    using that by (cases q) simp
  ultimately show ?thesis using publish_callback history routing
    by (cases opt) (auto simp: routing_ok_def simp del: split_paired_All dest!: history)
next
  case retire
  then show ?thesis using routing history by (auto simp: routing_ok_def)
next
  case (count_response n c k)
  then have prev: "supported N E s (Routed_Response n c k)" by (blast intro: history)
  then have enabled: "coordinator_enabled N E V C v s (Dispatch (Java_Response n c k) False)"
    using count_response by simp
  have later: "supported N E (coordinator_execute N E s (Dispatch (Java_Response n c k) False))
    (Routed_Response n c k)" by (rule supported_later[OF prev])
  show ?thesis unfolding count_response(1,2)
    by (rule advance_transport[OF enabled history])
      (use later routing in
        \<open>auto simp: routing_ok_def response_quorum_def put_lifecycle_def Let_def split: if_splits\<close>)
next
  case (send_commit c k n)
  then show ?thesis using routing history by (auto simp: routing_ok_def dest!: history)
next
  case (receive_commit c n k)
  have enabled: "coordinator_enabled N E V C v s (Dispatch (Java_Commit n c k) False)"
    using receive_commit by (auto dest: history)
  show ?thesis unfolding receive_commit(1,2)
    by (rule advance_transport[OF enabled history]) (use routing in auto)
qed

inductive transport_reachable for N E V C v versions where
  init: "default_strategy N E C \<Longrightarrow> v \<in> V \<Longrightarrow>
    transport_reachable N E V C v versions (coordinator_initial v versions) {}"
| step: "transport_reachable N E V C v versions s H \<Longrightarrow> transport_step N E V C v s H s' H' \<Longrightarrow>
    transport_reachable N E V C v versions s' H'"

theorem transport_invariants:
  assumes "transport_reachable N E V C v versions s H"
  shows "coordinator_reachable N E V C v versions s \<and>
    (\<forall>msg\<in>H. supported N E s msg) \<and> routing_ok H"
  using assms
proof induction
  case init
  then show ?case by (auto simp: routing_ok_def intro: coordinator_reachable.init)
next
  case (step s H s' H')
  with transport_step_refines[OF step.hyps(2), of versions]
  show ?case by (blast intro: coordinator_reachable.advance)
qed

theorem transport_reply_matches_request:
  assumes "transport_reachable N E V C v versions s H"
    "Publish_RPC c i n p u \<in> H" "Publish_Reply c i actual k opt \<in> H"
  shows "actual = n" "k = request_key p"
proof -
  have "routing_ok H" using transport_invariants[OF assms(1)] by blast
  from routed_reply[OF this assms(2,3)] show "actual = n" "k = request_key p" by simp_all
qed

theorem transport_inputs_discharge_caller_contract:
  assumes run: "transport_reachable N E V C v versions s H"
  shows "Sent_Vote d (Vote n c t k) \<in> H \<Longrightarrow>
      d = c \<and> caller_contract N E V C v (coordination s) (Java_Join n d t k)"
    "Publish_RPC c i n p u \<in> H \<Longrightarrow> compatible_publication p u wire \<Longrightarrow>
      decode_publication p u wire = Some decoded \<Longrightarrow>
      caller_contract N E V C v (coordination s) (Java_Publish n decoded u)"
    "Routed_Response n c k \<in> H \<Longrightarrow>
      caller_contract N E V C v (coordination s) (Java_Response n c k)"
    "Sent_Commit c n k \<in> H \<Longrightarrow> java_checks (coordination s) (Java_Commit n c k) \<Longrightarrow>
      caller_contract N E V C v (coordination s) (Java_Commit n c k)"
proof -
  have reach: "coordinator_reachable N E V C v versions s"
    and supported: "msg \<in> H \<Longrightarrow> supported N E s msg" for msg
    using transport_invariants[OF run] by blast+
  show "Sent_Vote d (Vote n c t k) \<in> H \<Longrightarrow>
      d = c \<and> caller_contract N E V C v (coordination s) (Java_Join n d t k)"
    by (drule supported) auto
  show "Publish_RPC c i n p u \<in> H \<Longrightarrow> compatible_publication p u wire \<Longrightarrow>
      decode_publication p u wire = Some decoded \<Longrightarrow>
      caller_contract N E V C v (coordination s) (Java_Publish n decoded u)"
    by (drule supported) (auto simp: publish_from_def dest: decode_publication_correct)
  show "Routed_Response n c k \<in> H \<Longrightarrow>
      caller_contract N E V C v (coordination s) (Java_Response n c k)"
    by (drule supported) simp
  assume "Sent_Commit c n k \<in> H" and "java_checks (coordination s) (Java_Commit n c k)"
  with supported[OF \<open>Sent_Commit c n k \<in> H\<close>]
  have "coordinator_enabled N E V C v s (Dispatch (Java_Commit n c k) False)" by simp
  from coordinator_commit_ordering[OF reach this]
  show "caller_contract N E V C v (coordination s) (Java_Commit n c k)" .
qed

theorem transport_refines_tla:
  assumes "transport_reachable N E V C v versions s H"
  shows "\<exists>t. tla_reachable N V C v versions t \<and> configurations_ok E t \<and> coordination s = project_java E t"
  using transport_invariants[OF assms] by (blast intro: coordinator_refines_tla)

end
