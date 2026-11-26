theory Abstract_Model
  imports Publication_Basics "HOL-Library.Sublist"
begin

section \<open>Dynamic quorum certificates and publication ancestry\<close>

text \<open>
  An abstract, history-based model of the coordination protocol, from which the
  safety properties are proved. It is not a transcription of any Java class: it
  is the target that the TLA+ translation refines. Its state corresponds to the
  concrete protocol as follows.

  Conventions used throughout this theory:
  \<^item> \<open>node\<close>: a node ID. Where a field is indexed by a node, it is that node's own state (for
    example \<open>current_term_of n\<close> is the term of \<open>n\<close>). In a tuple, the position of the node
    says whether it is the sender or the receiver, as described for each field below.
  \<^item> \<open>term\<close> (a \<open>nat\<close>): an election term. It is the term of a node's current state, of a join,
    of an election, or of a publication.
  \<^item> \<open>version\<close> (a \<open>nat\<close>): the version of a publication within its term, chosen by the leader in
    \<open>publish\<close>. A \<open>position\<close> is a term and a version, ordered by term and then by version.
  \<^item> \<open>publication_history\<close>: a chain of publications, oldest first. Its tip is its last publication,
    so \<open>position_of_tip_of\<close>, \<open>term_of_tip_of\<close> and \<open>owner_of_tip_of\<close> describe the tip, and the owner is the
    leader that published it.

  The fields of \<open>abstract_state\<close>:
  \<^item> \<open>current_term_of n\<close>: the current term of node \<open>n\<close> (\<open>CoordinationState.getCurrentTerm\<close>).
  \<^item> \<open>started_join_since_reboot\<close>: the nodes that have started a join since their last reboot, so they
    may become candidates (\<open>startedJoinSinceLastReboot\<close>).
  \<^item> \<open>joins_sent (voter, candidate, term, position)\<close>: \<open>voter\<close> sent a \<open>Join\<close> to \<open>candidate\<close> for \<open>term\<close>,
    carrying \<open>voter\<close>'s last accepted position (the tip of its accepted history).
  \<^item> \<open>elections_won (candidate, term)\<close>: the election that \<open>candidate\<close> won in \<open>term\<close>, if any. Its
    \<open>election_votes\<close> are the voters whose joins formed the quorum, \<open>election_last_accepted_history\<close> is
    the history \<open>candidate\<close> had accepted when it won, and \<open>election_committed_configuration\<close> is its last
    committed configuration then.
  \<^item> \<open>publications_sent\<close>: every publication history that has been published, by its owner.
  \<^item> \<open>publications_accepted n\<close>: the publication history that node \<open>n\<close> has accepted
    (\<open>durable_history\<close>).
  \<^item> \<open>last_committed_configuration_of n\<close>: the last configuration committed by node \<open>n\<close>.
  \<^item> \<open>publish_responses_sent (n, h)\<close>: node \<open>n\<close> sent a \<open>PublishResponse\<close> acknowledging history \<open>h\<close>.
  \<^item> \<open>publications_committed\<close>: the histories with a quorum of acknowledgements, for which a commit may be
    sent (\<open>ApplyCommitRequest\<close>).

  The history that a leader is extending in a term is not a field of the state; it is computed by
  \<open>last_published_history_of\<close>, defined below.

  The actions of \<open>transition\<close>, with the node that performs each one:
  \<^item> \<open>start_join\<close>: \<open>voter\<close> raises its term to \<open>new_term\<close> and sends a join to \<open>candidate\<close>.
  \<^item> \<open>win_election\<close>: \<open>candidate\<close> wins its current term with a quorum of \<open>voters\<close>.
  \<^item> \<open>publish\<close>: \<open>leader\<close> publishes a new history at its current term and \<open>version\<close>, with configuration
    \<open>new_config\<close>. The cluster state that is published is not modelled, only its voting configuration. A
    \<^emph>\<open>configuration change\<close> is a publication whose \<open>new_config\<close> differs from the configuration at the tip
    of the leader's accepted history. It is allowed only if that configuration has been committed, so
    there is never more than one uncommitted configuration change in a history. A publication that keeps
    the configuration of the tip is not a configuration change, however much of the cluster state it
    alters, and is allowed even while an earlier configuration change is still being committed.
  \<^item> \<open>receive\<close>: \<open>node\<close> accepts \<open>publication_history\<close> and sends a publish response for it.
  \<^item> \<open>commit\<close>: \<open>leader\<close> commits \<open>publication_history\<close> once a joint quorum has acknowledged it.
  \<^item> \<open>apply_commit\<close>: \<open>node\<close> applies a commit of its accepted history.
  \<^item> \<open>reboot\<close>: \<open>node\<close> restarts, so it is no longer marked as having started a join.
\<close>

record election =
  election_votes :: "node set"
  election_last_accepted_history :: publication_history
  election_committed_configuration :: config

record abstract_state =
  current_term_of :: "node \<Rightarrow> nat"
  (* TODO started_join_since_reboot matches the Java impl but abstractly it'd be nicer to track the current leaders :: "node set"  *)
  started_join_since_reboot :: "node set"
  joins_sent :: "(node \<times> node \<times> nat \<times> position) set"
  elections_won :: "(node \<times> nat) \<Rightarrow> election option"
  publications_sent :: "publication_history set"
  publications_accepted :: "node \<Rightarrow> publication_history"
  last_committed_configuration_of :: "node \<Rightarrow> config"
  publish_responses_sent :: "(node \<times> publication_history) set"
  publications_committed :: "publication_history set"


locale abstract_model =
  fixes initial_configuration :: config
begin

abbreviation config_of_tip_of :: "publication_history \<Rightarrow> config" where
  "config_of_tip_of \<equiv> at_tip initial_configuration publication_config"

abbreviation previous_config_of_tip_of :: "publication_history \<Rightarrow> config" where
  "previous_config_of_tip_of \<equiv> at_tip initial_configuration publication_previous_config"


definition bootstrapped :: "abstract_state" where
  "bootstrapped = \<lparr>
    current_term_of                 = (\<lambda>_. 0),
    started_join_since_reboot       = {},
    joins_sent                      = {},
    elections_won                   = (\<lambda>_. None),
    publications_sent               = {},
    publications_accepted           = (\<lambda>_. []),
    last_committed_configuration_of = (\<lambda>_. initial_configuration),
    publish_responses_sent          = {},
    publications_committed          = {}
  \<rparr>"

text \<open>
  \<open>published_by s leader term\<close> is the set of histories in \<open>publications_sent\<close> whose tip was published by
  \<open>leader\<close> in \<open>term\<close>.

  \<open>last_published_history_of s (leader, term)\<close> is the history that \<open>leader\<close> is extending in \<open>term\<close>,
  computed from \<open>elections_won\<close> and \<open>publications_sent\<close>. It is the greatest history that \<open>leader\<close> has
  published in \<open>term\<close> (greatest under \<open>prefix\<close>: \<open>leadership_ok\<close> ensures these histories form a chain), or,
  if it has published none, the accepted history recorded in the election that \<open>leader\<close> won in \<open>term\<close>.
  If \<open>leader\<close> did not win \<open>term\<close> the value is unspecified (\<open>undefined\<close>); nothing relies on it.
  A new \<open>publish\<close> extends this history by one publication, so it becomes the new greatest.

  The equations are not used by \<open>simp\<close> (see below): unfold them only where the value is needed.
\<close>

definition published_by :: "abstract_state \<Rightarrow> node \<Rightarrow> nat \<Rightarrow> publication_history set" where
  "published_by abstract_state leader vote_term =
    {publication_history\<in>publications_sent abstract_state. owner_of_tip_of publication_history = leader
     \<and> term_of_tip_of publication_history = vote_term}"

fun last_published_history_of :: "abstract_state \<Rightarrow> node \<times> nat \<Rightarrow> publication_history" where
  "last_published_history_of abstract_state (leader, vote_term) =
    (case elections_won abstract_state (leader, vote_term) of
      None \<Rightarrow> undefined
    | Some election \<Rightarrow>
        if published_by abstract_state leader vote_term = {}
        then election_last_accepted_history election
        else THE greatest. greatest \<in> published_by abstract_state leader vote_term
             \<and> (\<forall>publication_history\<in>published_by abstract_state leader vote_term. prefix publication_history greatest))"

lemma last_published_history_cong_key:
  assumes "elections_won other_state key = elections_won abstract_state key"
  assumes "published_by other_state (fst key) (snd key)
           = published_by abstract_state (fst key) (snd key)"
  shows "last_published_history_of other_state key = last_published_history_of abstract_state key"
proof (cases key)
  case (Pair leader vote_term)
  from assms have won: "elections_won other_state (leader, vote_term) = elections_won abstract_state (leader, vote_term)"
    and sent: "published_by other_state leader vote_term
               = published_by abstract_state leader vote_term"
    by (simp_all add: Pair)
  show ?thesis unfolding Pair last_published_history_of.simps won sent by (rule refl)
qed

lemma last_published_history_cong:
  assumes "elections_won other_state = elections_won abstract_state"
  assumes "publications_sent other_state = publications_sent abstract_state"
  shows "last_published_history_of other_state key = last_published_history_of abstract_state key"
proof (cases key)
  case (Pair leader vote_term)
  have same: "published_by other_state leader vote_term
              = published_by abstract_state leader vote_term"
    unfolding published_by_def using assms(2) by simp
  show ?thesis unfolding Pair last_published_history_of.simps same assms(1) by (rule refl)
qed

lemma last_published_history_win_other:
  assumes "key \<noteq> (candidate, vote_term)"
  shows "last_published_history_of (abstract_state\<lparr>elections_won := (elections_won abstract_state)((candidate, vote_term) := new_election)\<rparr>) key
       = last_published_history_of abstract_state key"
proof (rule last_published_history_cong_key)
  show "elections_won (abstract_state\<lparr>elections_won := (elections_won abstract_state)((candidate, vote_term) := new_election)\<rparr>) key = elections_won abstract_state key"
    using assms by auto
  show "published_by
            (abstract_state\<lparr>elections_won := (elections_won abstract_state)((candidate, vote_term) := new_election)\<rparr>)
            (fst key)
            (snd key)
        =
         published_by abstract_state (fst key) (snd key)"
    unfolding published_by_def by simp
qed

lemma last_published_history_win_new:
  assumes "published_by abstract_state candidate vote_term = {}"
  shows "last_published_history_of (abstract_state\<lparr>elections_won := (elections_won abstract_state)((candidate, vote_term) := Some election)\<rparr>) (candidate, vote_term)
       = election_last_accepted_history election"
  using assms by (simp add: published_by_def)

text \<open>
  The computed value is only unfolded on purpose. Updates to any other field leave it unchanged.
\<close>

declare last_published_history_of.simps [simp del]

lemma last_published_history_of_update_current_term_of[simp]:
  "last_published_history_of (abstract_state\<lparr>current_term_of := x\<rparr>) key = last_published_history_of abstract_state key"
  by (rule last_published_history_cong) simp_all

lemma last_published_history_of_update_joins_sent[simp]:
  "last_published_history_of (abstract_state\<lparr>joins_sent := x\<rparr>) key = last_published_history_of abstract_state key"
  by (rule last_published_history_cong) simp_all

lemma last_published_history_of_update_started_join_since_reboot[simp]:
  "last_published_history_of (abstract_state\<lparr>started_join_since_reboot := x\<rparr>) key = last_published_history_of abstract_state key"
  by (rule last_published_history_cong) simp_all

lemma last_published_history_of_update_publications_accepted[simp]:
  "last_published_history_of (abstract_state\<lparr>publications_accepted := x\<rparr>) key = last_published_history_of abstract_state key"
  by (rule last_published_history_cong) simp_all

lemma last_published_history_of_update_last_committed_configuration_of[simp]:
  "last_published_history_of (abstract_state\<lparr>last_committed_configuration_of := x\<rparr>) key = last_published_history_of abstract_state key"
  by (rule last_published_history_cong) simp_all

lemma last_published_history_of_update_publish_responses_sent[simp]:
  "last_published_history_of (abstract_state\<lparr>publish_responses_sent := x\<rparr>) key = last_published_history_of abstract_state key"
  by (rule last_published_history_cong) simp_all

lemma last_published_history_of_update_publications_committed[simp]:
  "last_published_history_of (abstract_state\<lparr>publications_committed := x\<rparr>) key = last_published_history_of abstract_state key"
  by (rule last_published_history_cong) simp_all

text \<open>
  \<open>voted s candidate term voters\<close>: every node in \<open>voters\<close> has sent \<open>candidate\<close> a join for \<open>term\<close>, so each
  has promised not to accept publications from earlier terms.

  \<open>fresh_votes s candidate term h voters\<close> is the stronger condition that each of those joins carried a
  position no later than the tip of \<open>h\<close>. A voter's join position is the tip of what it had accepted when
  it voted (see \<open>messages_ok\<close>), so \<open>h\<close> is at least as recent as anything those voters had accepted. This is
  what lets a leader at \<open>term\<close> base its history on \<open>h\<close> without losing anything committed by a quorum
  that intersects \<open>voters\<close>. It is required of the election's accepted history (\<open>win_election\<close>) and of the history
  each \<open>publish\<close> extends.
\<close>

definition voted :: "abstract_state \<Rightarrow> node \<Rightarrow> nat \<Rightarrow> node set \<Rightarrow> bool" where
  "voted abstract_state candidate term voters \<longleftrightarrow>
    (\<forall>voter\<in>voters. \<exists>position. (voter, candidate, term, position) \<in> joins_sent abstract_state)"

definition fresh_votes ::
  "abstract_state \<Rightarrow> node \<Rightarrow> nat \<Rightarrow> publication_history \<Rightarrow> node set \<Rightarrow> bool" where
  "fresh_votes abstract_state candidate term publication_history voters \<longleftrightarrow>
    (\<forall>voter\<in>voters. \<exists>position\<le>position_of_tip_of publication_history. (voter, candidate, term, position) \<in> joins_sent abstract_state)"

lemma fresh_votes_voted:
  assumes  "fresh_votes abstract_state candidate term publication_history voters"
  shows "voted abstract_state candidate term voters"
  using assms unfolding voted_def fresh_votes_def by blast

definition active_leader :: "abstract_state \<Rightarrow> node \<Rightarrow> bool" where
  "active_leader abstract_state node \<longleftrightarrow>
    node \<in> started_join_since_reboot abstract_state
    \<and> elections_won abstract_state (node, current_term_of abstract_state node) \<noteq> None"

text \<open>
  \<open>acknowledged_by_joint_quorum s h\<close>: a single set of nodes that is a quorum of both the configuration
  that \<open>h\<close>'s tip was published against (\<open>previous_config_of_tip_of\<close>) and the configuration it proposes
  (\<open>config_of_tip_of\<close>) has sent a publish response for \<open>h\<close>. This is what must hold for \<open>h\<close> to be
  committed.
\<close>

definition acknowledged_by_joint_quorum :: "abstract_state \<Rightarrow> publication_history \<Rightarrow> bool" where
  "acknowledged_by_joint_quorum abstract_state publication_history \<longleftrightarrow>
    (\<exists>voters. quorum (previous_config_of_tip_of publication_history) voters
              \<and> quorum (config_of_tip_of publication_history) voters
              \<and> (\<forall>voter\<in>voters. (voter, publication_history) \<in> publish_responses_sent abstract_state))"

text \<open>
  The guard of \<open>publish\<close> that mentions the last committed configuration only restricts configuration
  changes (a \<open>new_config\<close> that differs from the configuration at the tip of the accepted history); a
  publication that keeps the same configuration is not restricted by it.

  The carried configuration is the committed configuration in the publish request.
  A first quorum commit uses that configuration and the publication's new configuration.
  Once a commit is recorded, subsequent commit notifications can replay it.
  Elections and quorum commits are recorded atomically. The join certificate used for
  a proposal may include further votes since election.
\<close>

inductive transition :: "abstract_state \<Rightarrow> abstract_state \<Rightarrow> bool" where
  start_join: "\<lbrakk>
      current_term_of abstract_state voter < new_term
    \<rbrakk> \<Longrightarrow>
    transition 
        abstract_state
        (abstract_state\<lparr>
          current_term_of           := (current_term_of abstract_state)(voter := new_term),
          joins_sent                := insert (voter, candidate, new_term, position_of_tip_of (publications_accepted abstract_state voter))
                           (joins_sent abstract_state),
          started_join_since_reboot := insert voter (started_join_since_reboot abstract_state)
        \<rparr>)"
| win_election: "\<lbrakk>
      candidate \<in> started_join_since_reboot abstract_state;
      elections_won abstract_state (candidate, current_term_of abstract_state candidate) = None;
      quorum (last_committed_configuration_of abstract_state candidate) voters;
      quorum (config_of_tip_of (publications_accepted abstract_state candidate)) voters;
      fresh_votes
          abstract_state
          candidate
          (current_term_of abstract_state candidate)
          (publications_accepted abstract_state candidate)
          voters
    \<rbrakk> \<Longrightarrow>
    transition abstract_state (abstract_state\<lparr>
      elections_won     := (elections_won abstract_state)((candidate, current_term_of abstract_state candidate) :=
        Some \<lparr>
          election_votes                   = voters,
          election_last_accepted_history   = publications_accepted abstract_state candidate,
          election_committed_configuration = last_committed_configuration_of abstract_state candidate
        \<rparr>)
    \<rparr>)"
| publish: "\<lbrakk>
      active_leader abstract_state leader;
      last_published_history_of abstract_state (leader, current_term_of abstract_state leader) = publications_accepted abstract_state leader;
      position_version (position_of_tip_of (publications_accepted abstract_state leader)) < version;
      new_config \<noteq> config_of_tip_of (publications_accepted abstract_state leader) \<longrightarrow>
        last_committed_configuration_of abstract_state leader = config_of_tip_of (publications_accepted abstract_state leader);
      quorum new_config voters;
      fresh_votes
          abstract_state
          leader
          (current_term_of abstract_state leader)
          (publications_accepted abstract_state leader)
          voters;
      new_publication_history = publications_accepted abstract_state leader @
        [\<lparr>
          publication_position        = \<lparr>
            position_term    = current_term_of abstract_state leader,
            position_version = version
          \<rparr>,
          publication_owner           = leader,
          publication_config          = new_config,
          publication_previous_config = last_committed_configuration_of abstract_state leader
        \<rparr>]
    \<rbrakk> \<Longrightarrow>
    transition 
        abstract_state
        (abstract_state\<lparr>
          publications_sent := insert new_publication_history (publications_sent abstract_state)
        \<rparr>)"
| receive: "\<lbrakk>
      publication_history \<in> publications_sent abstract_state;
      term_of_tip_of publication_history = current_term_of abstract_state node;
      position_of_tip_of (publications_accepted abstract_state node) < position_of_tip_of publication_history
    \<rbrakk> \<Longrightarrow>
    transition 
        abstract_state
        (abstract_state\<lparr>
          publications_accepted           := (publications_accepted abstract_state)(node := publication_history),
          last_committed_configuration_of := (last_committed_configuration_of abstract_state)(node := previous_config_of_tip_of publication_history),
          publish_responses_sent          := insert (node, publication_history) (publish_responses_sent abstract_state)
        \<rparr>)"
| commit: "\<lbrakk>
      active_leader abstract_state leader;
      publication_history = last_published_history_of abstract_state (leader, current_term_of abstract_state leader);
      publication_history \<in> publications_sent abstract_state;
      term_of_tip_of publication_history = current_term_of abstract_state leader;
      owner_of_tip_of publication_history = leader;
      acknowledged_by_joint_quorum abstract_state publication_history
    \<rbrakk> \<Longrightarrow>
    transition 
        abstract_state
        (abstract_state\<lparr>publications_committed := insert publication_history (publications_committed abstract_state)\<rparr>)"
| apply_commit: "\<lbrakk>
      publications_accepted abstract_state node \<in> publications_committed abstract_state;
      term_of_tip_of (publications_accepted abstract_state node) = current_term_of abstract_state node;
      active_leader abstract_state node \<longrightarrow>
        publications_accepted abstract_state node = last_published_history_of abstract_state (node, current_term_of abstract_state node)
    \<rbrakk> \<Longrightarrow>
    transition 
      abstract_state
      (abstract_state\<lparr>last_committed_configuration_of := (last_committed_configuration_of abstract_state)
        (node := config_of_tip_of (publications_accepted abstract_state node))\<rparr>)"
| reboot: "transition 
               abstract_state
               (abstract_state\<lparr>started_join_since_reboot := started_join_since_reboot abstract_state - {node}\<rparr>)"

inductive dynamic_reachable :: "abstract_state \<Rightarrow> bool" where
  boot: "initial_configuration \<noteq> {} \<Longrightarrow> dynamic_reachable bootstrapped"
| advance: "dynamic_reachable abstract_state \<Longrightarrow> transition 
                                                                         abstract_state
                                                                         next_abstract \<Longrightarrow>
    dynamic_reachable next_abstract"

lemma dynamic_reachable_nonempty: "dynamic_reachable abstract_state \<Longrightarrow> initial_configuration \<noteq> {}"
  by (induction rule: dynamic_reachable.induct) auto

text \<open>
  \<open>effective_config commits h c\<close>: \<open>c\<close> is a possible value for the last committed configuration of a node
  whose accepted history is \<open>h\<close>, where \<open>commits\<close> is the set of committed histories.

  When the tip of \<open>h\<close> was published it recorded the configuration that was committed at the time, its
  previous configuration (\<open>previous_config_of_tip_of h\<close>). That stays the last committed configuration
  until \<open>h\<close> itself is committed, at which point the configuration that \<open>h\<close> proposed
  (\<open>config_of_tip_of h\<close>) takes effect. So there are two cases: \<open>c\<close> is the previous configuration, or \<open>h\<close>
  is committed and \<open>c\<close> is its own. For the empty history both are the initial configuration.

  It is used wherever a configuration is paired with a history: for a node's accepted history and its last
  committed configuration (\<open>messages_ok\<close>), for an election's accepted history and committed configuration
  (\<open>leadership_ok\<close>), and for the parent of a publication and the previous configuration recorded in it
  (\<open>valid_edge\<close>). Committing more histories only adds to the second case, so it preserves the relation
  (\<open>effective_config_insert\<close>).
\<close>

definition effective_config :: "publication_history set \<Rightarrow> publication_history \<Rightarrow> config \<Rightarrow> bool" where
  "effective_config commits publication_history configuration \<longleftrightarrow>
    configuration = previous_config_of_tip_of publication_history
    \<or> publication_history \<in> commits
      \<and> configuration = config_of_tip_of publication_history"

lemma effective_config_insert:
  "effective_config commits publication_history configuration \<Longrightarrow>
    effective_config (insert commit commits) publication_history configuration"
  by (simp only: effective_config_def insert_iff) blast

definition valid_edge :: "publication_history set \<Rightarrow> publication_history \<Rightarrow> publication \<Rightarrow> bool" where
  "valid_edge commits parent request \<longleftrightarrow>
    term_of_tip_of parent \<le> position_term (publication_position request)
    \<and> 0 < position_term (publication_position request)
    \<and> position_version (position_of_tip_of parent) < position_version (publication_position request)
    \<and> effective_config commits parent (publication_previous_config request)
    \<and> (publication_config request \<noteq> config_of_tip_of parent \<longrightarrow> publication_previous_config request = config_of_tip_of parent)"

lemma valid_edge_insert:
  "valid_edge commits parent request \<Longrightarrow> valid_edge (insert commit commits) parent request"
  unfolding valid_edge_def by (blast intro: effective_config_insert)

definition prefix_closed :: "publication_history set \<Rightarrow> bool" where
  "prefix_closed histories \<longleftrightarrow>
    (\<forall>parent request. parent @ [request] \<in> histories \<longrightarrow> parent \<in> insert [] histories)"

definition messages_ok :: "abstract_state \<Rightarrow> bool" where
  "messages_ok abstract_state \<longleftrightarrow>
    (\<forall>node. publications_accepted abstract_state node \<in> insert [] (publications_sent abstract_state)
            \<and> term_of_tip_of (publications_accepted abstract_state node) \<le> current_term_of abstract_state node
            \<and> effective_config
                  (publications_committed abstract_state)
                  (publications_accepted abstract_state node)
                  (last_committed_configuration_of abstract_state node))
    \<and> (\<forall>node publication_history. (node, publication_history) \<in> publish_responses_sent abstract_state \<longrightarrow>
        position_of_tip_of publication_history \<le> position_of_tip_of (publications_accepted abstract_state node))
    \<and> (\<forall>voter candidate term position. (voter, candidate, term, position) \<in> joins_sent abstract_state \<longrightarrow>
        term \<le> current_term_of abstract_state voter
        \<and> (\<forall>publication_history. (voter, publication_history) \<in> publish_responses_sent abstract_state
                                 \<and> term_of_tip_of publication_history < term \<longrightarrow>
            position_of_tip_of publication_history \<le> position))
    \<and> (\<forall>voter candidate candidate' term position position'.
        (voter, candidate, term, position) \<in> joins_sent abstract_state
        \<and> (voter, candidate', term, position') \<in> joins_sent abstract_state \<longrightarrow> candidate = candidate')
    \<and> (\<forall>node\<in>started_join_since_reboot abstract_state. 0 < current_term_of abstract_state node)"

definition publications_ok :: "abstract_state \<Rightarrow> bool" where
  "publications_ok abstract_state \<longleftrightarrow>
    finite (publications_sent abstract_state)
    \<and> [] \<notin> publications_sent abstract_state
    \<and> prefix_closed (publications_sent abstract_state)
    \<and> (\<forall>parent request. parent @ [request] \<in> publications_sent abstract_state \<longrightarrow>
        valid_edge (publications_committed abstract_state) parent request)
    \<and> (\<forall>publication_history\<in>publications_committed abstract_state.
        publication_history \<in> publications_sent abstract_state
        \<and> acknowledged_by_joint_quorum abstract_state publication_history)"

definition leadership_ok :: "abstract_state \<Rightarrow> bool" where
  "leadership_ok abstract_state \<longleftrightarrow>
    (\<forall>candidate term election. elections_won abstract_state (candidate, term) = Some election \<longrightarrow>
      election_last_accepted_history election \<in> insert [] (publications_sent abstract_state)
      \<and> term_of_tip_of (election_last_accepted_history election) < term
      \<and> effective_config
            (publications_committed abstract_state)
            (election_last_accepted_history election)
            (election_committed_configuration election)
      \<and> quorum (election_committed_configuration election) (election_votes election)
      \<and> quorum (config_of_tip_of (election_last_accepted_history election)) (election_votes election)
      \<and> fresh_votes
            abstract_state
            candidate
            term
            (election_last_accepted_history election)
            (election_votes election))
    \<and> finite (publications_sent abstract_state)
    \<and> (\<forall>publication_history\<in>publications_sent abstract_state.
        (\<exists>election. elections_won abstract_state (owner_of_tip_of publication_history, term_of_tip_of publication_history) = Some election
                    \<and> prefix (election_last_accepted_history election) publication_history)
        \<and> (\<exists>voters. quorum (config_of_tip_of publication_history) voters
                    \<and> voted
                          abstract_state
                          (owner_of_tip_of publication_history)
                          (term_of_tip_of publication_history)
                          voters))
    \<and> (\<forall>first_history\<in>publications_sent abstract_state. \<forall>second_history\<in>publications_sent abstract_state.
        owner_of_tip_of first_history = owner_of_tip_of second_history
        \<and> term_of_tip_of first_history = term_of_tip_of second_history \<longrightarrow>
        prefix first_history second_history \<or> prefix second_history first_history)"

text \<open>
  Publications by one leader in one term form a chain, so there is a greatest one.
  This is what makes the computed \<open>last_published_history_of\<close> well defined.
\<close>

lemma chain_greatest:
  assumes "finite histories" "histories \<noteq> {}"
  assumes "\<forall>first_history\<in>histories. \<forall>second_history\<in>histories.
    prefix first_history second_history \<or> prefix second_history first_history"
  shows "\<exists>greatest\<in>histories. \<forall>publication_history\<in>histories. prefix publication_history greatest"
  using assms
proof (induction rule: finite_ne_induct)
  case (singleton history)
  then show ?case by simp
next
  case (insert history histories)
  then obtain greatest where g: "greatest \<in> histories" "\<forall>publication_history\<in>histories. prefix publication_history greatest" by auto
  from insert.prems g(1) have "prefix history greatest \<or> prefix greatest history" by simp
  then show ?case
  proof
    assume "prefix history greatest"
    then show ?thesis using g by (intro bexI[of _ greatest]) auto
  next
    assume "prefix greatest history"
    then show ?thesis using g by (intro bexI[of _ history]) (auto elim: prefix_order.order_trans)
  qed
qed

lemma published_by_self:
  assumes "publication_history \<in> publications_sent abstract_state"
  shows "publication_history \<in> published_by
                                   abstract_state
                                   (owner_of_tip_of publication_history)
                                   (term_of_tip_of publication_history)"
  using assms unfolding published_by_def by simp

lemma last_published_history_publication:
  assumes ok: "leadership_ok abstract_state"
  assumes pub: "publication_history \<in> published_by abstract_state leader vote_term"
  shows "last_published_history_of abstract_state (leader, vote_term) \<in> published_by
                                                                            abstract_state
                                                                            leader
                                                                            vote_term"
    "prefix publication_history (last_published_history_of abstract_state (leader, vote_term))"
proof -
  let ?set = "published_by abstract_state leader vote_term"
  have fin: "finite ?set" using ok unfolding leadership_ok_def published_by_def by auto
  have chain: "\<forall>first_history\<in>?set. \<forall>second_history\<in>?set. prefix first_history second_history
                                                          \<or> prefix second_history first_history"
    using ok unfolding leadership_ok_def published_by_def by (auto simp del: split_paired_All)
  obtain greatest where g: "greatest \<in> ?set" "\<forall>history\<in>?set. prefix history greatest"
    using chain_greatest[OF fin _ chain] pub by auto
  have unique: "\<exists>!greatest. greatest \<in> ?set \<and> (\<forall>history\<in>?set. prefix history greatest)"
  proof (rule ex1I[of _ greatest])
    show "greatest \<in> ?set \<and> (\<forall>history\<in>?set. prefix history greatest)" using g by simp
    fix other assume "other \<in> ?set \<and> (\<forall>history\<in>?set. prefix history other)"
    then show "other = greatest" using g by (blast intro: prefix_order.antisym)
  qed
  obtain election where "elections_won abstract_state (leader, vote_term) = Some election"
    using ok pub unfolding leadership_ok_def published_by_def by fastforce
  then have "last_published_history_of abstract_state (leader, vote_term) =
      (THE greatest. greatest \<in> ?set \<and> (\<forall>history\<in>?set. prefix history greatest))"
    using pub by (auto simp: last_published_history_of.simps)
  from theI'[OF unique] this
  show "last_published_history_of abstract_state (leader, vote_term) \<in> ?set"
    "prefix publication_history (last_published_history_of abstract_state (leader, vote_term))"
    using pub by auto
qed

lemma last_published_history_election:
  assumes ok: "leadership_ok abstract_state"
  assumes won: "elections_won abstract_state (leader, vote_term) = Some election"
  shows "prefix (election_last_accepted_history election) (last_published_history_of abstract_state (leader, vote_term))"
proof (cases "published_by abstract_state leader vote_term = {}")
  case True
  then show ?thesis using won by (simp add: last_published_history_of.simps)
next
  case False
  then obtain publication_history where pub: "publication_history \<in> published_by
                                                                        abstract_state
                                                                        leader
                                                                        vote_term" by blast
  then obtain other where "elections_won abstract_state (leader, vote_term) = Some other"
    "prefix (election_last_accepted_history other) publication_history"
    using ok unfolding leadership_ok_def published_by_def by fastforce
  with won have "prefix (election_last_accepted_history election) publication_history" by simp
  with last_published_history_publication(2)[OF ok pub]
  show ?thesis by (blast intro: prefix_order.order_trans)
qed

lemma last_published_history_eq:
  assumes ok: "leadership_ok abstract_state"
  assumes pub: "greatest \<in> published_by abstract_state leader vote_term"
  assumes max: "\<forall>publication_history\<in>published_by abstract_state leader vote_term. prefix publication_history greatest"
  shows "last_published_history_of abstract_state (leader, vote_term) = greatest"
  using last_published_history_publication[OF ok pub] max pub
  by (blast intro: prefix_order.antisym)

lemma last_published_history_publish_other:
  assumes "owner_of_tip_of publication_history = candidate" "term_of_tip_of publication_history = vote_term"
  assumes "key \<noteq> (candidate, vote_term)"
  shows "last_published_history_of (abstract_state\<lparr>publications_sent := insert publication_history (publications_sent abstract_state)\<rparr>) key
       = last_published_history_of abstract_state key"
proof (rule last_published_history_cong_key)
  show "elections_won (abstract_state\<lparr>publications_sent := insert publication_history (publications_sent abstract_state)\<rparr>) key = elections_won abstract_state key"
    by simp
  show "published_by
            (abstract_state\<lparr>publications_sent := insert publication_history (publications_sent abstract_state)\<rparr>)
            (fst key)
            (snd key)
        =
         published_by abstract_state (fst key) (snd key)"
    using assms unfolding published_by_def by (cases key) auto
qed

lemma last_published_history_publish_new:
  assumes ok: "leadership_ok abstract_state"
  assumes next_ok: "leadership_ok (abstract_state\<lparr>publications_sent := insert publication_history (publications_sent abstract_state)\<rparr>)"
  assumes meta: "owner_of_tip_of publication_history = candidate" "term_of_tip_of publication_history = vote_term"
  assumes new: "publication_history = parent @ [publication]"
  assumes tip: "last_published_history_of abstract_state (candidate, vote_term) = parent"
  shows "last_published_history_of (abstract_state\<lparr>publications_sent := insert publication_history (publications_sent abstract_state)\<rparr>) (candidate, vote_term)
       = publication_history"
proof -
  let ?next = "abstract_state\<lparr>publications_sent := insert publication_history (publications_sent abstract_state)\<rparr>"
  have new_in: "publication_history \<in> published_by ?next candidate vote_term" using meta unfolding published_by_def by simp
  have greatest: "\<forall>other\<in>published_by ?next candidate vote_term. prefix other publication_history"
  proof (intro ballI)
    fix other assume o: "other \<in> published_by ?next candidate vote_term"
    show "prefix other publication_history"
    proof (cases "other = publication_history")
      case True
      then show ?thesis by simp
    next
      case False
      then have "other \<in> published_by abstract_state candidate vote_term" using o unfolding published_by_def by auto
      from last_published_history_publication(2)[OF ok this] tip
      obtain zs where "parent = other @ zs" unfolding prefix_def by auto
      with new show ?thesis unfolding prefix_def by auto
    qed
  qed
  show ?thesis by (rule last_published_history_eq[OF next_ok new_in greatest])
qed

lemma messagesD:
  assumes "messages_ok abstract_state"
  shows
    "publications_accepted abstract_state node \<in> insert [] (publications_sent abstract_state)"
    "term_of_tip_of (publications_accepted abstract_state node) \<le> current_term_of abstract_state node"
    "effective_config
         (publications_committed abstract_state)
         (publications_accepted abstract_state node)
         (last_committed_configuration_of abstract_state node)"
    "(node,publication_history) \<in> publish_responses_sent abstract_state \<Longrightarrow> position_of_tip_of publication_history \<le> position_of_tip_of (publications_accepted abstract_state node)"
    "(node,candidate,vote_term,join_position) \<in> joins_sent abstract_state \<Longrightarrow> vote_term \<le> current_term_of abstract_state node"
    "(node,candidate,vote_term,join_position) \<in> joins_sent abstract_state \<Longrightarrow> (node,publication_history) \<in> publish_responses_sent abstract_state \<Longrightarrow>
      term_of_tip_of publication_history < vote_term \<Longrightarrow> position_of_tip_of publication_history \<le> join_position"
    "(node,candidate,vote_term,join_position) \<in> joins_sent abstract_state \<Longrightarrow> (node,other_candidate,vote_term,other_join_position) \<in> joins_sent abstract_state \<Longrightarrow> candidate = other_candidate"
    "node \<in> started_join_since_reboot abstract_state \<Longrightarrow> 0 < current_term_of abstract_state node"
  using assms unfolding messages_ok_def
  apply (auto simp del: split_paired_All split_paired_Ex)
  by blast

lemma publicationsD:
  assumes "publications_ok abstract_state"
  shows
    "finite (publications_sent abstract_state)"
    "[] \<notin> publications_sent abstract_state"
    "prefix_closed (publications_sent abstract_state)"
    "publication_history @ [publication] \<in> publications_sent abstract_state \<Longrightarrow> valid_edge
                                                                                  (publications_committed abstract_state)
                                                                                  publication_history
                                                                                  publication"
    "publication_history \<in> publications_committed abstract_state \<Longrightarrow> publication_history \<in> publications_sent abstract_state"
    "publication_history \<in> publications_committed abstract_state \<Longrightarrow> acknowledged_by_joint_quorum abstract_state publication_history"
  using assms unfolding publications_ok_def by auto

lemma leadershipD:
  assumes ok: "leadership_ok abstract_state"
  shows
    "elections_won abstract_state (candidate,vote_term) = Some election \<Longrightarrow> election_last_accepted_history election \<in> insert [] (publications_sent abstract_state)"
    "elections_won abstract_state (candidate,vote_term) = Some election \<Longrightarrow> term_of_tip_of (election_last_accepted_history election) < vote_term"
    "elections_won abstract_state (candidate,vote_term) = Some election \<Longrightarrow>
      effective_config
          (publications_committed abstract_state)
          (election_last_accepted_history election)
          (election_committed_configuration election)"
    "elections_won abstract_state (candidate,vote_term) = Some election \<Longrightarrow> quorum (election_committed_configuration election) (election_votes election)"
    "elections_won abstract_state (candidate,vote_term) = Some election \<Longrightarrow> quorum (config_of_tip_of (election_last_accepted_history election)) (election_votes election)"
    "elections_won abstract_state (candidate,vote_term) = Some election \<Longrightarrow> fresh_votes
                                                                              abstract_state
                                                                              candidate
                                                                              vote_term
                                                                              (election_last_accepted_history election)
                                                                              (election_votes election)"
    "elections_won abstract_state (candidate,vote_term) = Some election \<Longrightarrow> prefix (election_last_accepted_history election) (last_published_history_of abstract_state (candidate,vote_term))"
    "publication_history \<in> publications_sent abstract_state \<Longrightarrow> \<exists>election. elections_won abstract_state (owner_of_tip_of publication_history,term_of_tip_of publication_history) = Some election
                                                                         \<and> prefix (election_last_accepted_history election) publication_history"
    "publication_history \<in> publications_sent abstract_state \<Longrightarrow> prefix publication_history (last_published_history_of abstract_state (owner_of_tip_of publication_history,term_of_tip_of publication_history))"
    "publication_history \<in> publications_sent abstract_state \<Longrightarrow> \<exists>voters. quorum (config_of_tip_of publication_history) voters
                                                                       \<and> voted
                                                                             abstract_state
                                                                             (owner_of_tip_of publication_history)
                                                                             (term_of_tip_of publication_history)
                                                                             voters"
proof -
  note unfolded = ok[unfolded leadership_ok_def]
  note won = unfolded[THEN conjunct1, rule_format]
  note sent = unfolded[THEN conjunct2, THEN conjunct2, THEN conjunct1, rule_format]
  show "elections_won abstract_state (candidate,vote_term) = Some election \<Longrightarrow> election_last_accepted_history election \<in> insert [] (publications_sent abstract_state)"
    by (rule won[THEN conjunct1])
  show "elections_won abstract_state (candidate,vote_term) = Some election \<Longrightarrow> term_of_tip_of (election_last_accepted_history election) < vote_term"
    by (rule won[THEN conjunct2, THEN conjunct1])
  show "elections_won abstract_state (candidate,vote_term) = Some election \<Longrightarrow>
      effective_config
          (publications_committed abstract_state)
          (election_last_accepted_history election)
          (election_committed_configuration election)"
    by (rule won[THEN conjunct2, THEN conjunct2, THEN conjunct1])
  show "elections_won abstract_state (candidate,vote_term) = Some election \<Longrightarrow> quorum (election_committed_configuration election) (election_votes election)"
    by (rule won[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1])
  show "elections_won abstract_state (candidate,vote_term) = Some election \<Longrightarrow> quorum (config_of_tip_of (election_last_accepted_history election)) (election_votes election)"
    by (rule won[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1])
  show "elections_won abstract_state (candidate,vote_term) = Some election \<Longrightarrow> fresh_votes
                                                                                 abstract_state
                                                                                 candidate
                                                                                 vote_term
                                                                                 (election_last_accepted_history election)
                                                                                 (election_votes election)"
    by (rule won[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2])
  show "elections_won abstract_state (candidate,vote_term) = Some election \<Longrightarrow> prefix (election_last_accepted_history election) (last_published_history_of abstract_state (candidate,vote_term))"
    by (rule last_published_history_election[OF ok])
  show "publication_history \<in> publications_sent abstract_state \<Longrightarrow> \<exists>election. elections_won abstract_state (owner_of_tip_of publication_history,term_of_tip_of publication_history) = Some election
                                                                            \<and> prefix (election_last_accepted_history election) publication_history"
    by (rule sent[THEN conjunct1])
  show "publication_history \<in> publications_sent abstract_state \<Longrightarrow> prefix publication_history (last_published_history_of abstract_state (owner_of_tip_of publication_history,term_of_tip_of publication_history))"
    by (rule last_published_history_publication(2)[OF ok published_by_self])
  show "publication_history \<in> publications_sent abstract_state \<Longrightarrow> \<exists>voters. quorum (config_of_tip_of publication_history) voters
                                                                          \<and> voted
                                                                                abstract_state
                                                                                (owner_of_tip_of publication_history)
                                                                                (term_of_tip_of publication_history)
                                                                                voters"
    by (rule sent[THEN conjunct2])
qed

lemma same_config_vote:
  assumes ok: "messages_ok abstract_state"
  assumes quorum_fact: "quorum new_configuration voters" "quorum new_configuration other_voters"
  assumes votes: "voted abstract_state candidate vote_term voters" "voted
                                                                        abstract_state
                                                                        other_candidate
                                                                        vote_term
                                                                        other_voters"
  shows "candidate = other_candidate"
proof -
  obtain node where "node \<in> voters" "node \<in> other_voters" using quorum_intersects[OF quorum_fact] by blast
  with votes obtain join_position other_join_position where "(node,candidate,vote_term,join_position) \<in> joins_sent abstract_state" "(node,other_candidate,vote_term,other_join_position) \<in> joins_sent abstract_state"
    unfolding voted_def by blast
  then show ?thesis by (rule messagesD(7)[OF ok])
qed

lemma new_election_base:
  assumes messages: "messages_ok abstract_state"
  assumes leaders: "leadership_ok abstract_state"
  assumes none: "elections_won abstract_state (candidate,current_term_of abstract_state candidate) = None"
  assumes vote_term_fact: "0 < current_term_of abstract_state candidate"
  assumes quorum_fact: "quorum (config_of_tip_of (publications_accepted abstract_state candidate)) voters"
  assumes fresh: "fresh_votes
                      abstract_state
                      candidate
                      (current_term_of abstract_state candidate)
                      (publications_accepted abstract_state candidate)
                      voters"
  shows "term_of_tip_of (publications_accepted abstract_state candidate) < current_term_of abstract_state candidate"
proof (rule ccontr)
  let ?publication_history = "publications_accepted abstract_state candidate"
  let ?vote_term = "current_term_of abstract_state candidate"
  assume "\<not> term_of_tip_of ?publication_history < ?vote_term"
  then have eq: "term_of_tip_of ?publication_history = ?vote_term" using messagesD(2)[OF messages, of candidate] by simp
  have pub: "?publication_history \<in> publications_sent abstract_state" using messagesD(1)[OF messages, of candidate] vote_term_fact eq by auto
  obtain other_voters where "quorum (config_of_tip_of ?publication_history) other_voters" "voted abstract_state (owner_of_tip_of ?publication_history) ?vote_term other_voters"
    using leadershipD(10)[OF leaders pub] eq by auto
  then have "candidate = owner_of_tip_of ?publication_history" by (rule same_config_vote[OF messages quorum_fact _ fresh_votes_voted[OF fresh]])
  with leadershipD(8)[OF leaders pub] eq none show False by auto
qed

lemma messages_start_join:
  assumes ok: "messages_ok abstract_state"
  assumes newer: "current_term_of abstract_state node < vote_term"
  shows "messages_ok (abstract_state\<lparr>
    current_term_of           := (current_term_of abstract_state)(node := vote_term),
    joins_sent                := insert (node,candidate,vote_term,position_of_tip_of (publications_accepted abstract_state node)) (joins_sent abstract_state),
    started_join_since_reboot := insert node (started_join_since_reboot abstract_state)
  \<rparr>)"
proof -
  have mono: "current_term_of abstract_state other_node \<le> ((current_term_of abstract_state)(node := vote_term)) other_node" for other_node using newer by auto
  have accepted_bound: "term_of_tip_of (publications_accepted abstract_state other_node) \<le> ((current_term_of abstract_state)(node := vote_term)) other_node" for other_node
    by (rule order_trans[OF messagesD(2)[OF ok] mono])
  have join_bound: "(other_node,other_candidate,other_join_position,join_position) \<in> joins_sent abstract_state \<Longrightarrow> other_join_position \<le> ((current_term_of abstract_state)(node := vote_term)) other_node" for other_node other_candidate other_join_position join_position
    by (rule order_trans[OF messagesD(5)[OF ok, of other_node other_candidate other_join_position join_position] mono])
  have no_prior_vote: "(node,other_candidate,vote_term,join_position) \<notin> joins_sent abstract_state" for other_candidate join_position
    using newer messagesD(5)[OF ok, of node other_candidate vote_term join_position] by auto
  have positive: "0 < ((current_term_of abstract_state)(node := vote_term)) other_node" if "other_node \<in> started_join_since_reboot abstract_state" for other_node
    using messagesD(8)[OF ok that] mono[of other_node] by linarith
  show ?thesis
    using ok newer accepted_bound join_bound no_prior_vote positive messagesD(4,7)[OF ok]
    unfolding messages_ok_def
    by (auto simp add: fun_upd_same simp del: fun_upd_apply)
qed

lemma messages_receive:
  assumes ok: "messages_ok abstract_state"
  assumes pub: "publication_history \<in> publications_sent abstract_state"
  assumes cur: "term_of_tip_of publication_history = current_term_of abstract_state node"
  assumes position: "position_of_tip_of (publications_accepted abstract_state node) < position_of_tip_of publication_history"
  shows "messages_ok (abstract_state\<lparr>
    publications_accepted           := (publications_accepted abstract_state)(node := publication_history),
    last_committed_configuration_of := (last_committed_configuration_of abstract_state)(node := previous_config_of_tip_of publication_history),
    publish_responses_sent          := insert (node,publication_history) (publish_responses_sent abstract_state)
  \<rparr>)"
proof -
  have receipt: "position_of_tip_of earlier_history \<le> position_of_tip_of publication_history" if "(node,earlier_history) \<in> publish_responses_sent abstract_state" for earlier_history
    using position messagesD(4)[OF ok that] by order
  have "\<not> term_of_tip_of publication_history < vote_term" if "(node,candidate,vote_term,join_position) \<in> joins_sent abstract_state" for candidate vote_term join_position
    using cur messagesD(5)[OF ok that] by simp
  then show ?thesis using ok pub cur receipt unfolding messages_ok_def effective_config_def by auto
qed

lemma messages_certify:
  assumes "messages_ok abstract_state"
  shows "messages_ok (abstract_state\<lparr>publications_committed := insert publication_history (publications_committed abstract_state)\<rparr>)"
  using assms unfolding messages_ok_def effective_config_def by auto

lemma messages_apply:
  assumes "messages_ok abstract_state" "publications_accepted abstract_state node \<in> publications_committed abstract_state"
  shows "messages_ok (abstract_state\<lparr>last_committed_configuration_of := (last_committed_configuration_of abstract_state)(node := config_of_tip_of (publications_accepted abstract_state node))\<rparr>)"
  using assms unfolding messages_ok_def effective_config_def by auto

lemma publications_publish:
  assumes ok: "publications_ok abstract_state"
  assumes messages_ok_fact: "messages_ok abstract_state"
  assumes active: "active_leader abstract_state candidate"
  assumes inc: "position_version (position_of_tip_of (publications_accepted abstract_state candidate)) < version"
  assumes guard: "new_configuration \<noteq> config_of_tip_of (publications_accepted abstract_state candidate) \<longrightarrow>
      last_committed_configuration_of abstract_state candidate = config_of_tip_of (publications_accepted abstract_state candidate)"
  assumes new: "publication_history = publications_accepted abstract_state candidate @ [\<lparr>
    publication_position        = \<lparr>
      position_term    = current_term_of abstract_state candidate,
      position_version = version
    \<rparr>,
    publication_owner           = candidate,
    publication_config          = new_configuration,
    publication_previous_config = last_committed_configuration_of abstract_state candidate
  \<rparr>]"
  shows "publications_ok (abstract_state\<lparr>
    publications_sent := insert publication_history (publications_sent abstract_state)
  \<rparr>)"
proof -
  let ?publication = "\<lparr>
    publication_position        = \<lparr>
      position_term    = current_term_of abstract_state candidate,
      position_version = version
    \<rparr>,
    publication_owner           = candidate,
    publication_config          = new_configuration,
    publication_previous_config = last_committed_configuration_of abstract_state candidate
  \<rparr>"
  have "candidate \<in> started_join_since_reboot abstract_state" using active unfolding active_leader_def by simp
  have "valid_edge (publications_committed abstract_state) (publications_accepted abstract_state candidate) ?publication"
    using messagesD(2,3)[OF messages_ok_fact, of candidate] messagesD(8)[OF messages_ok_fact \<open>candidate \<in> started_join_since_reboot abstract_state\<close>] inc guard
    unfolding valid_edge_def by simp
  from this messagesD(1)[OF messages_ok_fact, of candidate] ok
  show ?thesis
    unfolding publications_ok_def prefix_closed_def acknowledged_by_joint_quorum_def new by auto
qed

lemma publications_receive:
  assumes ok: "publications_ok abstract_state"
  shows "publications_ok (abstract_state\<lparr>
    publications_accepted           := (publications_accepted abstract_state)(node := publication_history),
    last_committed_configuration_of := (last_committed_configuration_of abstract_state)(node := previous_config_of_tip_of publication_history),
    publish_responses_sent          := insert (node,publication_history) (publish_responses_sent abstract_state)
  \<rparr>)"
proof -
  let ?next_abstract_state = "abstract_state\<lparr>
    publications_accepted           := (publications_accepted abstract_state)(node := publication_history),
    last_committed_configuration_of := (last_committed_configuration_of abstract_state)(node := previous_config_of_tip_of publication_history),
    publish_responses_sent          := insert (node,publication_history) (publish_responses_sent abstract_state)
  \<rparr>"
  have "acknowledged_by_joint_quorum ?next_abstract_state earlier_history" if "earlier_history \<in> publications_committed abstract_state" for earlier_history
    using publicationsD(6)[OF ok that] unfolding acknowledged_by_joint_quorum_def by auto
  then show ?thesis using ok unfolding publications_ok_def by auto
qed

lemma publications_certify:
  assumes "publications_ok abstract_state" "publication_history \<in> publications_sent abstract_state" "acknowledged_by_joint_quorum 
                                                                              abstract_state
                                                                              publication_history"
  shows "publications_ok (abstract_state\<lparr>publications_committed := insert publication_history (publications_committed abstract_state)\<rparr>)"
  using assms unfolding publications_ok_def acknowledged_by_joint_quorum_def by (auto intro: valid_edge_insert)

lemma leadership_start_join:
  assumes ok: "leadership_ok abstract_state"
  shows "leadership_ok (abstract_state\<lparr>
    current_term_of           := (current_term_of abstract_state)(node := vote_term),
    joins_sent                := insert (node,candidate,vote_term,position_of_tip_of (publications_accepted abstract_state node)) (joins_sent abstract_state),
    started_join_since_reboot := insert node (started_join_since_reboot abstract_state)
  \<rparr>)"
proof -
  let ?next_abstract_state = "abstract_state\<lparr>
    current_term_of           := (current_term_of abstract_state)(node := vote_term),
    joins_sent                := insert (node,candidate,vote_term,position_of_tip_of (publications_accepted abstract_state node)) (joins_sent abstract_state),
    started_join_since_reboot := insert node (started_join_since_reboot abstract_state)
  \<rparr>"
  have fresh: "fresh_votes
                   abstract_state
                   other_candidate
                   other_join_position
                   publication_history
                   voters \<Longrightarrow> fresh_votes ?next_abstract_state other_candidate
                                                                 other_join_position
                                                                 publication_history
                                                                 voters" for other_candidate other_join_position publication_history voters
    unfolding fresh_votes_def by force
  have votes: "\<exists>voters. quorum (config_of_tip_of publication_history) voters
                        \<and> voted ?next_abstract_state (owner_of_tip_of publication_history) (term_of_tip_of publication_history) voters"
    if "publication_history \<in> publications_sent abstract_state" for publication_history
    using leadershipD(10)[OF ok that] unfolding voted_def by force
  show ?thesis using ok fresh votes unfolding leadership_ok_def by auto
qed

lemma leadership_win:
  assumes messages: "messages_ok abstract_state"
  assumes ok: "leadership_ok abstract_state"
  assumes started: "candidate \<in> started_join_since_reboot abstract_state"
  assumes none: "elections_won abstract_state (candidate,current_term_of abstract_state candidate) = None"
  assumes quorum: "quorum (last_committed_configuration_of abstract_state candidate) voters" "quorum (config_of_tip_of (publications_accepted abstract_state candidate)) voters"
  assumes vote: "fresh_votes
                     abstract_state
                     candidate
                     (current_term_of abstract_state candidate)
                     (publications_accepted abstract_state candidate)
                     voters"
  shows "leadership_ok (abstract_state\<lparr>
           elections_won     := (elections_won abstract_state)((candidate,current_term_of abstract_state candidate) :=
        Some \<lparr>
          election_votes                   = voters,
          election_last_accepted_history   = publications_accepted abstract_state candidate,
          election_committed_configuration = last_committed_configuration_of abstract_state candidate
        \<rparr>)
         \<rparr>)"
proof -
  have base: "term_of_tip_of (publications_accepted abstract_state candidate) < current_term_of abstract_state candidate"
    by (rule new_election_base[OF messages ok none messagesD(8)[OF messages started] quorum(2) vote])
  have other: "publication_history \<in> publications_sent abstract_state \<Longrightarrow> (owner_of_tip_of publication_history,term_of_tip_of publication_history) \<noteq> (candidate,current_term_of abstract_state candidate)" for publication_history
    using leadershipD(8)[OF ok, of publication_history] none by auto
  show ?thesis
    using ok none base quorum vote other messagesD(1,3)[OF messages, of candidate]
    unfolding leadership_ok_def fresh_votes_def voted_def by auto
qed

lemma leadership_publish:
  assumes ok: "leadership_ok abstract_state"
  assumes active: "active_leader abstract_state candidate"
  assumes tip: "last_published_history_of abstract_state (candidate,current_term_of abstract_state candidate) = publications_accepted abstract_state candidate"
  assumes quorum: "quorum new_configuration voters"
  assumes vote: "fresh_votes
                     abstract_state
                     candidate
                     (current_term_of abstract_state candidate)
                     (publications_accepted abstract_state candidate)
                     voters"
  assumes new: "publication_history = publications_accepted abstract_state candidate @ [\<lparr>
    publication_position        = \<lparr>
      position_term    = current_term_of abstract_state candidate,
      position_version = version
    \<rparr>,
    publication_owner           = candidate,
    publication_config          = new_configuration,
    publication_previous_config = last_committed_configuration_of abstract_state candidate
  \<rparr>]"
  shows "leadership_ok (abstract_state\<lparr>
    publications_sent := insert publication_history (publications_sent abstract_state)
  \<rparr>)"
proof -
  have meta: "owner_of_tip_of publication_history = candidate" "term_of_tip_of publication_history = current_term_of abstract_state candidate" "config_of_tip_of publication_history = new_configuration" using new by auto
  have extends: "prefix earlier_history (last_published_history_of abstract_state (candidate,current_term_of abstract_state candidate)) \<Longrightarrow> prefix earlier_history publication_history" for earlier_history
    using tip new by simp
  have chain: "\<forall>other\<in>publications_sent abstract_state.
      owner_of_tip_of other = owner_of_tip_of publication_history
      \<and> term_of_tip_of other = term_of_tip_of publication_history \<longrightarrow>
      prefix other publication_history"
  proof (intro ballI impI)
    fix other assume o: "other \<in> publications_sent abstract_state" and "owner_of_tip_of other = owner_of_tip_of publication_history
                                                                        \<and> term_of_tip_of other = term_of_tip_of publication_history"
    then have "other \<in> published_by
                           abstract_state
                           candidate
                           (current_term_of abstract_state candidate)" using meta unfolding published_by_def by simp
    from extends[OF last_published_history_publication(2)[OF ok this]]
    show "prefix other publication_history" using tip by simp
  qed
  obtain election where election_fact: "elections_won abstract_state (candidate,current_term_of abstract_state candidate) = Some election"
    using active unfolding active_leader_def by auto
  have base: "prefix (election_last_accepted_history election) publication_history"
    by (rule extends[OF leadershipD(7)[OF ok election_fact]])
  have new_votes: "\<exists>other_voters. quorum (config_of_tip_of publication_history) other_voters
                                  \<and> voted
                                        abstract_state
                                        (owner_of_tip_of publication_history)
                                        (term_of_tip_of publication_history)
                                        other_voters"
    by (rule exI[of _ voters]) (simp add: meta quorum fresh_votes_voted[OF vote])
  show ?thesis using ok election_fact base new_votes meta chain
    unfolding leadership_ok_def fresh_votes_def voted_def by (auto simp del: split_paired_All)
qed

lemma leadership_certify:
  assumes "leadership_ok abstract_state"
  shows "leadership_ok (abstract_state\<lparr>publications_committed := insert publication_history (publications_committed abstract_state)\<rparr>)"
  using assms unfolding leadership_ok_def fresh_votes_def voted_def by (auto intro: effective_config_insert)

lemma dynamic_invariants:
  assumes "dynamic_reachable abstract_state"
  shows "messages_ok abstract_state
         \<and> publications_ok abstract_state
         \<and> leadership_ok abstract_state"
  using assms
proof (induction rule: dynamic_reachable.induct)
  case boot
  show ?case by (simp add: bootstrapped_def messages_ok_def effective_config_def
      publications_ok_def prefix_closed_def leadership_ok_def)
next
  case (advance abstract_state next_abstract_state)
  then have messages_ok_fact: "messages_ok abstract_state" and publications_ok_fact: "publications_ok abstract_state" and leadership_ok_fact: "leadership_ok abstract_state" by auto
  from advance.hyps(2) show ?case
  proof (cases rule: transition.cases)
    case start_join
    with messages_ok_fact publications_ok_fact leadership_ok_fact
    show ?thesis
      by (simp add: messages_start_join leadership_start_join publications_ok_def acknowledged_by_joint_quorum_def)
  next
    case win_election
    with messages_ok_fact publications_ok_fact leadership_ok_fact
    show ?thesis
      by (simp add: leadership_win messages_ok_def publications_ok_def acknowledged_by_joint_quorum_def)
  next
    case publish
    then show ?thesis
    proof (intro conjI)
      show "messages_ok next_abstract_state" using publish messages_ok_fact unfolding messages_ok_def by auto
      show "publications_ok next_abstract_state" using publish publications_ok_fact messages_ok_fact by (blast intro: publications_publish)
      show "leadership_ok next_abstract_state" using publish leadership_ok_fact by (blast intro: leadership_publish)
    qed
  next
    case receive
    with messages_ok_fact publications_ok_fact leadership_ok_fact
    show ?thesis by (simp add: messages_receive publications_receive leadership_ok_def
        fresh_votes_def voted_def)
  next
    case commit
    with messages_ok_fact publications_ok_fact leadership_ok_fact
    show ?thesis by (simp add: messages_certify publications_certify leadership_certify)
  next
    case apply_commit
    with messages_ok_fact publications_ok_fact leadership_ok_fact
    show ?thesis by (simp add: messages_apply publications_ok_def acknowledged_by_joint_quorum_def
        leadership_ok_def fresh_votes_def voted_def)
  next
    case reboot
    with messages_ok_fact publications_ok_fact leadership_ok_fact
    show ?thesis by (auto simp: messages_ok_def publications_ok_def acknowledged_by_joint_quorum_def
        leadership_ok_def fresh_votes_def voted_def)
  qed
qed

section \<open>Quorums between committed configurations\<close>

text \<open>
  The lemmas below take \<open>earlier_history\<close>, a prefix of a publication history \<open>h\<close>: an earlier state on the same
  chain, usually one that has been committed or that an election started from. They ask which configurations
  \<open>h\<close> may require quorums of.

  The \<open>gap\<close> hypothesis says that no committed history lies strictly between \<open>earlier_history\<close> and \<open>h\<close> (by
  position). Without such a commit the configuration cannot move on twice: by \<open>valid_edge\<close> a publication
  may only change the configuration if the one before it has taken effect, which happens by being committed.
  So with a gap, the configuration at \<open>earlier_history\<close> is still one of the two that \<open>h\<close> relies on
  (\<open>earlier_config\<close>), and quorums of it can be intersected with those of \<open>h\<close>
  (\<open>earlier_election_quorum\<close>, \<open>earlier_commit_quorum\<close>).
\<close>

lemma prefix_of_sent:
  assumes ok: "publications_ok abstract_state"
  assumes ran: "publication_history \<in> insert [] (publications_sent abstract_state)"
  assumes pref: "prefix earlier_history publication_history"
  shows "earlier_history \<in> insert [] (publications_sent abstract_state)
         \<and> (earlier_history = publication_history
            \<or> position_of_tip_of earlier_history < position_of_tip_of publication_history)"
  using ran pref
proof (induction publication_history rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc publication publication_history)
  then have pub: "publication_history @ [publication] \<in> publications_sent abstract_state" by simp
  then have parent: "publication_history \<in> insert [] (publications_sent abstract_state)"
    using publicationsD(3)[OF ok] unfolding prefix_closed_def by blast
  have inc: "position_of_tip_of publication_history < position_of_tip_of (publication_history @ [publication])"
    using publicationsD(4)[OF ok pub] by (auto simp: valid_edge_def position_less_iff)
  show ?case
  proof (cases "earlier_history = publication_history @ [publication]")
    case True
    with pub show ?thesis by simp
  next
    case False
    then have "prefix earlier_history publication_history" using snoc.prems by simp
    from snoc.IH[OF parent this] inc show ?thesis by (auto intro: less_trans)
  qed
qed

text \<open>
  Starting at an earlier history, either the old or the new configuration remains the
  that history's configuration until an intervening publication is committed.
  A change to both would require applying such a commit before proposing again.
\<close>

lemma earlier_config:
  assumes ok: "publications_ok abstract_state"
  assumes mem: "publication_history \<in> insert [] (publications_sent abstract_state)"
  assumes publications_ok_fact: "prefix earlier_history publication_history"
  assumes gap: "\<forall>commit\<in>publications_committed abstract_state. \<not> (position_of_tip_of earlier_history < position_of_tip_of commit
                                                                  \<and> position_of_tip_of commit < position_of_tip_of publication_history)"
  shows "config_of_tip_of earlier_history = previous_config_of_tip_of publication_history
         \<or> config_of_tip_of earlier_history = config_of_tip_of publication_history"
  using mem publications_ok_fact gap
proof (induction publication_history rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc publication publication_history)
  show ?case
  proof (cases "earlier_history = publication_history @ [publication]")
    case True
    then show ?thesis by simp
  next
    case False
    have pub: "publication_history @ [publication] \<in> publications_sent abstract_state" using snoc.prems(1) by simp
    have parent: "publication_history \<in> insert [] (publications_sent abstract_state)"
      using prefix_of_sent[OF ok snoc.prems(1), of publication_history] by simp
    have pref: "prefix earlier_history publication_history" using snoc.prems(2) False by simp
    have inc: "position_of_tip_of publication_history < position_of_tip_of (publication_history @ [publication])"
      using prefix_of_sent[OF ok snoc.prems(1), of publication_history] by simp
    have no_commit: "publication_history \<in> publications_committed abstract_state \<Longrightarrow> earlier_history = publication_history"
      using prefix_of_sent[OF ok parent pref] snoc.prems(3) inc by blast
    have earlier_gap: "\<forall>commit\<in>publications_committed abstract_state. \<not> (position_of_tip_of earlier_history < position_of_tip_of commit
                                                                         \<and> position_of_tip_of commit < position_of_tip_of publication_history)"
      using snoc.prems(3) inc by (meson less_trans)
    have ih: "config_of_tip_of earlier_history = previous_config_of_tip_of publication_history
              \<or> config_of_tip_of earlier_history = config_of_tip_of publication_history"
      by (rule snoc.IH[OF parent pref earlier_gap])
    have edge: "valid_edge (publications_committed abstract_state) publication_history publication" by (rule publicationsD(4)[OF ok pub])
    from ih edge no_commit show ?thesis
      unfolding valid_edge_def effective_config_def by auto
  qed
qed

lemma earlier_election_quorum:
  assumes ok: "publications_ok abstract_state" "leadership_ok abstract_state"
  assumes cert: "elections_won abstract_state (candidate,vote_term) = Some election"
  assumes pref: "prefix earlier_history (election_last_accepted_history election)"
  assumes gap: "\<forall>publication_history\<in>publications_committed abstract_state. \<not> (position_of_tip_of earlier_history < position_of_tip_of publication_history
                                                                               \<and> position_of_tip_of publication_history < position_of_tip_of (election_last_accepted_history election))"
  assumes applied: "election_last_accepted_history election \<in> publications_committed abstract_state \<Longrightarrow> earlier_history = election_last_accepted_history election"
  shows "quorum (config_of_tip_of earlier_history) (election_votes election)"
  using earlier_config[OF ok(1) leadershipD(1)[OF ok(2) cert] pref gap]
    leadershipD(3,4,5)[OF ok(2) cert] applied
  unfolding effective_config_def by auto

lemma earlier_commit_quorum:
  assumes ok: "publications_ok abstract_state"
  assumes committed: "publication_history \<in> publications_committed abstract_state"
  assumes pref: "prefix earlier_history publication_history"
  assumes gap: "\<forall>commit\<in>publications_committed abstract_state. \<not> (position_of_tip_of earlier_history < position_of_tip_of commit
                                                                  \<and> position_of_tip_of commit < position_of_tip_of publication_history)"
  obtains voters where "quorum (config_of_tip_of earlier_history) voters" "\<forall>node\<in>voters. (node,publication_history) \<in> publish_responses_sent abstract_state"
proof -
  have "publication_history \<in> insert [] (publications_sent abstract_state)" using publicationsD(5)[OF ok committed] by simp
  from earlier_config[OF ok this pref gap] have cfg: "config_of_tip_of earlier_history = previous_config_of_tip_of publication_history
                                                      \<or> config_of_tip_of earlier_history = config_of_tip_of publication_history" .
  obtain voters where "quorum (previous_config_of_tip_of publication_history) voters" "quorum (config_of_tip_of publication_history) voters"
    and receipts: "\<forall>node\<in>voters. (node,publication_history) \<in> publish_responses_sent abstract_state"
    using publicationsD(6)[OF ok committed] unfolding acknowledged_by_joint_quorum_def by blast
  with cfg have "quorum (config_of_tip_of earlier_history) voters" by auto
  from this receipts show thesis by (rule that)
qed

text \<open>
  \<open>unique_leader s term\<close>: at most one node has won an election in \<open>term\<close>. Elections need a quorum of
  joins and a node only joins one candidate per term (\<open>messages_ok\<close>), so two winners in one term would need
  an overlapping voter to have joined both; this is proved from that (\<open>reachable_term_safe\<close>).

  \<open>safe_term s term\<close>: \<open>term\<close> cannot lose anything that has been committed in an earlier term. It has a
  unique leader, and every history published in \<open>term\<close> extends every history committed in an earlier term.
  This is the property that the main safety argument establishes for every term by strong induction on
  the term (\<open>reachable_term_safe\<close>), and it is what \<open>earlier_prefix\<close> assumes for all lower terms.
\<close>

definition unique_leader :: "abstract_state \<Rightarrow> nat \<Rightarrow> bool" where
  "unique_leader abstract_state term \<longleftrightarrow>
    (\<forall>candidate candidate' election election'.
      elections_won abstract_state (candidate, term) = Some election \<longrightarrow>
      elections_won abstract_state (candidate', term) = Some election' \<longrightarrow> candidate = candidate')"

definition safe_term :: "abstract_state \<Rightarrow> nat \<Rightarrow> bool" where
  "safe_term abstract_state term \<longleftrightarrow> unique_leader abstract_state term
                                   \<and> (\<forall>committed\<in>publications_committed abstract_state. \<forall>published\<in>publications_sent abstract_state.
                                       (term_of_tip_of committed < term
                                        \<and> term_of_tip_of published = term)
                                           \<longrightarrow> prefix committed published)"

lemma same_term_prefix:
  assumes ok: "leadership_ok abstract_state"
  assumes unique: "unique_leader abstract_state (term_of_tip_of first_history)"
  assumes pub: "first_history \<in> publications_sent abstract_state" "second_history \<in> publications_sent abstract_state"
  assumes same: "term_of_tip_of first_history = term_of_tip_of second_history"
  shows "prefix first_history second_history \<or> prefix second_history first_history"
proof -
  have "owner_of_tip_of first_history = owner_of_tip_of second_history"
    using leadershipD(8)[OF ok pub(1)] leadershipD(8)[OF ok pub(2)] unique same
    unfolding unique_leader_def by fastforce
  with leadershipD(9)[OF ok pub(1)] leadershipD(9)[OF ok pub(2)] same
  show ?thesis by (metis prefix_same_cases)
qed

lemma earlier_prefix:
  assumes pub_ok: "publications_ok abstract_state"
  assumes leaders: "leadership_ok abstract_state"
  assumes lower: "\<And>other_join_position. other_join_position < vote_term \<Longrightarrow> safe_term abstract_state other_join_position"
  assumes first_history_fact: "first_history \<in> insert [] (publications_committed abstract_state)"
  assumes second_history_fact: "second_history \<in> insert [] (publications_sent abstract_state)"
  assumes bt: "term_of_tip_of second_history < vote_term"
  assumes position: "position_of_tip_of first_history \<le> position_of_tip_of second_history"
  shows "prefix first_history second_history"
proof (cases "first_history = []")
  case True
  then show ?thesis by simp
next
  case False
  then have commit: "first_history \<in> publications_committed abstract_state" using first_history_fact by simp
  have a_pub: "first_history \<in> publications_sent abstract_state" by (rule publicationsD(5)[OF pub_ok commit])
  have b_pub: "second_history \<in> publications_sent abstract_state"
  proof (rule ccontr)
    assume "second_history \<notin> publications_sent abstract_state"
    with second_history_fact have "second_history = []" by simp
    moreover have "position_of_tip_of [] < position_of_tip_of first_history"
      using prefix_of_sent[OF pub_ok, of first_history "[]"] a_pub False by simp
    ultimately show False using position by simp
  qed
  have safe: "safe_term abstract_state (term_of_tip_of second_history)" by (rule lower[OF bt])
  show ?thesis
  proof (cases "term_of_tip_of first_history = term_of_tip_of second_history")
    case True
    have "unique_leader abstract_state (term_of_tip_of first_history)" using safe True unfolding safe_term_def by simp
    from same_term_prefix[OF leaders this a_pub b_pub True]
    show ?thesis using prefix_of_sent[OF pub_ok, of first_history second_history] a_pub position by auto
  next
    case False
    then have "term_of_tip_of first_history < term_of_tip_of second_history" using position_term_mono[OF position] by simp
    with safe commit b_pub show ?thesis unfolding safe_term_def by blast
  qed
qed

lemma older_commit_bound:
  assumes messages_ok_fact: "messages_ok abstract_state"
  assumes publications_ok_fact: "publications_ok abstract_state"
  assumes leadership_ok_fact: "leadership_ok abstract_state"
  assumes lower: "\<And>other_join_position. other_join_position < vote_term \<Longrightarrow> safe_term abstract_state other_join_position"
  assumes cert: "elections_won abstract_state (candidate,vote_term) = Some election"
  assumes committed: "first_history \<in> publications_committed abstract_state"
  assumes older: "term_of_tip_of first_history < vote_term"
  shows "position_of_tip_of first_history \<le> position_of_tip_of (election_last_accepted_history election)"
proof (rule ccontr)
  let ?second_history = "election_last_accepted_history election"
  let ?commit_set = "publications_committed abstract_state"
  let ?small = "insert [] {publication_history \<in> ?commit_set. position_of_tip_of publication_history \<le> position_of_tip_of ?second_history}"
  let ?large = "{publication_history \<in> ?commit_set. term_of_tip_of publication_history < vote_term
                 \<and> position_of_tip_of ?second_history < position_of_tip_of publication_history}"
  assume not_le: "\<not> position_of_tip_of first_history \<le> position_of_tip_of ?second_history"
  have fin: "finite ?commit_set" using publicationsD(1,5)[OF publications_ok_fact] by (meson finite_subset subsetI)
  obtain commit where kin: "commit \<in> ?small" and kmax: "\<And>publication_history. publication_history \<in> ?small \<Longrightarrow> position_of_tip_of publication_history \<le> position_of_tip_of commit"
    by (rule position_maximum[of ?small position_of_tip_of]) (use fin in auto)
  obtain publication where xin: "publication \<in> ?large" and xmin: "\<And>publication_history. publication_history \<in> ?large \<Longrightarrow> position_of_tip_of publication \<le> position_of_tip_of publication_history"
    by (rule position_minimum[of ?large position_of_tip_of]) (use fin committed older not_le in auto)
  from kin have kcomm: "commit \<in> insert [] ?commit_set" and kb: "position_of_tip_of commit \<le> position_of_tip_of ?second_history"
    by (auto simp: position_le_iff split: list.splits)
  from xin have xc: "publication \<in> ?commit_set" and xt: "term_of_tip_of publication < vote_term" and bx: "position_of_tip_of ?second_history < position_of_tip_of publication" by auto
  have kp: "prefix commit ?second_history"
    by (rule earlier_prefix[OF publications_ok_fact leadership_ok_fact lower kcomm leadershipD(1,2)[OF leadership_ok_fact cert] kb])
  have x_pub: "publication \<in> insert [] (publications_sent abstract_state)" using publicationsD(5)[OF publications_ok_fact xc] by simp
  have kx: "prefix commit publication"
    by (rule earlier_prefix[OF publications_ok_fact leadership_ok_fact lower kcomm x_pub xt less_imp_le[OF le_less_trans[OF kb bx]]])
  have b_gap: "publication_history \<in> ?commit_set \<Longrightarrow> position_of_tip_of commit < position_of_tip_of publication_history \<Longrightarrow>
    position_of_tip_of publication_history \<le> position_of_tip_of ?second_history \<Longrightarrow> False" for publication_history
    using kmax[of publication_history] by auto
  have x_gap: "publication_history \<in> ?commit_set \<Longrightarrow> position_of_tip_of commit < position_of_tip_of publication_history \<Longrightarrow>
    position_of_tip_of publication_history < position_of_tip_of publication \<Longrightarrow> False" for publication_history
  proof -
    assume hc: "publication_history \<in> ?commit_set" and kh: "position_of_tip_of commit < position_of_tip_of publication_history" and hx: "position_of_tip_of publication_history < position_of_tip_of publication"
    have "position_of_tip_of ?second_history < position_of_tip_of publication_history" by (rule not_le_imp_less) (rule notI, erule b_gap[OF hc kh])
    moreover have "term_of_tip_of publication_history < vote_term" using position_term_mono[OF less_imp_le[OF hx]] xt by simp
    ultimately have "publication_history \<in> ?large" using hc by simp
    from xmin[OF this] hx show False by simp
  qed
  have applied: "commit = ?second_history" if "?second_history \<in> ?commit_set"
  proof (rule ccontr)
    assume "commit \<noteq> ?second_history"
    from prefix_of_sent[OF publications_ok_fact leadershipD(1)[OF leadership_ok_fact cert] kp] this
    have "position_of_tip_of commit < position_of_tip_of ?second_history" by blast
    from b_gap[OF that this order_refl] show False .
  qed
  have bg: "\<forall>publication_history\<in>?commit_set. \<not> (position_of_tip_of commit < position_of_tip_of publication_history
                                                 \<and> position_of_tip_of publication_history < position_of_tip_of ?second_history)"
    using b_gap by (meson less_imp_le)
  have xg: "\<forall>publication_history\<in>?commit_set. \<not> (position_of_tip_of commit < position_of_tip_of publication_history
                                                 \<and> position_of_tip_of publication_history < position_of_tip_of publication)"
    using x_gap by blast
  have eq: "quorum (config_of_tip_of commit) (election_votes election)"
    by (rule earlier_election_quorum[OF publications_ok_fact leadership_ok_fact cert kp bg applied])
  obtain voters where quorum_fact: "quorum (config_of_tip_of commit) voters" and receipts: "\<forall>node\<in>voters. (node,publication) \<in> publish_responses_sent abstract_state"
    by (rule earlier_commit_quorum[OF publications_ok_fact xc kx xg])
  obtain node where node_fact: "node \<in> election_votes election" "node \<in> voters" using quorum_intersects[OF eq quorum_fact] by blast
  obtain join_position where join_position_fact: "join_position \<le> position_of_tip_of ?second_history" "(node,candidate,vote_term,join_position) \<in> joins_sent abstract_state"
    using leadershipD(6)[OF leadership_ok_fact cert] node_fact(1) unfolding fresh_votes_def by blast
  have "(node,publication) \<in> publish_responses_sent abstract_state" using receipts node_fact(2) by blast
  from messagesD(6)[OF messages_ok_fact join_position_fact(2) this xt] join_position_fact(1) bx
  show False by order
qed

theorem every_term_safe:
  assumes messages_ok_fact: "messages_ok abstract_state"
  assumes publications_ok_fact: "publications_ok abstract_state"
  assumes leadership_ok_fact: "leadership_ok abstract_state"
  shows "safe_term abstract_state vote_term"
proof (induction vote_term rule: less_induct)
  case (less vote_term)
  have older: "position_of_tip_of first_history \<le> position_of_tip_of (election_last_accepted_history election)"
    if "elections_won abstract_state (candidate,vote_term) = Some election" "first_history \<in> publications_committed abstract_state" "term_of_tip_of first_history < vote_term" for first_history candidate election
    by (rule older_commit_bound[OF messages_ok_fact publications_ok_fact leadership_ok_fact less.IH that])
  have unique: "unique_leader abstract_state vote_term"
  proof (unfold unique_leader_def, intro allI impI)
    fix candidate other_candidate election other_election
    assume cert: "elections_won abstract_state (candidate,vote_term) = Some election" "elections_won abstract_state (other_candidate,vote_term) = Some other_election"
    let ?commit_set = "publications_committed abstract_state"
    let ?older = "insert [] {publication_history \<in> ?commit_set. term_of_tip_of publication_history < vote_term}"
    have fin: "finite ?commit_set" using publicationsD(1,5)[OF publications_ok_fact] by (meson finite_subset subsetI)
    obtain commit where commit_fact: "commit \<in> ?older" and max: "\<And>publication_history. publication_history \<in> ?older \<Longrightarrow> position_of_tip_of publication_history \<le> position_of_tip_of commit"
      by (rule position_maximum[of ?older position_of_tip_of]) (use fin in auto)
    have kcomm: "commit \<in> insert [] ?commit_set" using commit_fact by auto
    have votes: "quorum (config_of_tip_of commit) (election_votes certified_election)" if certg: "elections_won abstract_state (node,vote_term) = Some certified_election" for node certified_election
    proof -
      let ?second_history = "election_last_accepted_history certified_election"
      have old: "term_of_tip_of ?second_history < vote_term" by (rule leadershipD(2)[OF leadership_ok_fact certg])
      have kb: "position_of_tip_of commit \<le> position_of_tip_of ?second_history" using commit_fact older[OF certg, of commit]
        by (auto simp: position_le_iff split: list.splits)
      have mem: "?second_history \<in> insert [] (publications_sent abstract_state)" by (rule leadershipD(1)[OF leadership_ok_fact certg])
      have pref: "prefix commit ?second_history" by (rule earlier_prefix[OF publications_ok_fact leadership_ok_fact less.IH kcomm mem old kb])
      have cutoff: "publication_history \<in> ?commit_set \<Longrightarrow> position_of_tip_of publication_history \<le> position_of_tip_of ?second_history \<Longrightarrow> position_of_tip_of publication_history \<le> position_of_tip_of commit" for publication_history
        using old max[of publication_history] position_term_mono[of "position_of_tip_of publication_history" "position_of_tip_of ?second_history"] by auto
      have gap: "\<forall>publication_history\<in>?commit_set. \<not> (position_of_tip_of commit < position_of_tip_of publication_history
                                                      \<and> position_of_tip_of publication_history < position_of_tip_of ?second_history)"
      proof (intro ballI notI, elim conjE)
        fix publication_history
        assume hc: "publication_history \<in> ?commit_set" and kh: "position_of_tip_of commit < position_of_tip_of publication_history" and hb: "position_of_tip_of publication_history < position_of_tip_of ?second_history"
        from cutoff[OF hc less_imp_le[OF hb]] kh show False by order
      qed
      have applied: "?second_history \<in> ?commit_set \<Longrightarrow> commit = ?second_history"
        using cutoff[of ?second_history] prefix_of_sent[OF publications_ok_fact mem pref] by auto
      show ?thesis by (rule earlier_election_quorum[OF publications_ok_fact leadership_ok_fact certg pref gap applied])
    qed
    show "candidate = other_candidate" by (rule same_config_vote[OF messages_ok_fact votes[OF cert(1)] votes[OF cert(2)]
          fresh_votes_voted[OF leadershipD(6)[OF leadership_ok_fact cert(1)]]
          fresh_votes_voted[OF leadershipD(6)[OF leadership_ok_fact cert(2)]]])
  qed
  have "prefix first_history second_history" if ac: "first_history \<in> publications_committed abstract_state" and bp: "second_history \<in> publications_sent abstract_state"
    and at: "term_of_tip_of first_history < vote_term" and bt: "term_of_tip_of second_history = vote_term" for first_history second_history
  proof -
    obtain election where cert: "elections_won abstract_state (owner_of_tip_of second_history,vote_term) = Some election" and base: "prefix (election_last_accepted_history election) second_history"
      using leadershipD(8)[OF leadership_ok_fact bp] bt by blast
    have "first_history \<in> insert [] (publications_committed abstract_state)" using ac by simp
    from earlier_prefix[OF publications_ok_fact leadership_ok_fact less.IH this leadershipD(1,2)[OF leadership_ok_fact cert] older[OF cert ac at]] base
    show ?thesis by (rule prefix_order.trans)
  qed
  with unique show ?case unfolding safe_term_def by blast
qed

section \<open>Safety for reachable executions\<close>

lemma reachable_term_safe:
  assumes "dynamic_reachable abstract_state"
  shows "safe_term abstract_state vote_term"
  using dynamic_invariants[OF assms] by (blast intro: every_term_safe)

theorem dynamic_one_election_candidate_per_term:
  assumes "dynamic_reachable abstract_state"
    "elections_won abstract_state (candidate,vote_term) = Some election" "elections_won abstract_state (other_candidate,vote_term) = Some other_election"
  shows "candidate = other_candidate"
  using reachable_term_safe[OF assms(1), of vote_term] assms(2,3)
  unfolding safe_term_def unique_leader_def by blast

theorem dynamic_unique_publication:
  assumes reach: "dynamic_reachable abstract_state"
  assumes pub: "first_history \<in> publications_sent abstract_state" "second_history \<in> publications_sent abstract_state"
  assumes position: "position_of_tip_of first_history = position_of_tip_of second_history"
  shows "first_history = second_history"
proof -
  from dynamic_invariants[OF reach] have publications_ok_fact: "publications_ok abstract_state" and leadership_ok_fact: "leadership_ok abstract_state" by auto
  have unique: "unique_leader abstract_state (term_of_tip_of first_history)" using reachable_term_safe[OF reach, of "term_of_tip_of first_history"]
    unfolding safe_term_def by simp
  from same_term_prefix[OF leadership_ok_fact unique pub] position
  have "prefix first_history second_history \<or> prefix second_history first_history" by simp
  with prefix_of_sent[OF publications_ok_fact, of first_history second_history] prefix_of_sent[OF publications_ok_fact, of second_history first_history] pub position
  show ?thesis by auto
qed

theorem dynamic_committed_states_form_chain:
  assumes reach: "dynamic_reachable abstract_state"
  assumes commits: "first_history \<in> publications_committed abstract_state" "second_history \<in> publications_committed abstract_state"
  shows "prefix first_history second_history \<or> prefix second_history first_history"
proof -
  from dynamic_invariants[OF reach] have publications_ok_fact: "publications_ok abstract_state" and leadership_ok_fact: "leadership_ok abstract_state" by auto
  have pub: "first_history \<in> publications_sent abstract_state" "second_history \<in> publications_sent abstract_state"
    using publicationsD(5)[OF publications_ok_fact commits(1)] publicationsD(5)[OF publications_ok_fact commits(2)] by auto
  consider (earlier) "term_of_tip_of first_history < term_of_tip_of second_history" | (same) "term_of_tip_of first_history = term_of_tip_of second_history" | (later) "term_of_tip_of second_history < term_of_tip_of first_history" by linarith
  then show ?thesis
  proof cases
    case earlier
    then show ?thesis using reachable_term_safe[OF reach, of "term_of_tip_of second_history"] commits(1) pub(2)
      unfolding safe_term_def by blast
  next
    case same
    have "unique_leader abstract_state (term_of_tip_of first_history)" using reachable_term_safe[OF reach, of "term_of_tip_of first_history"]
      unfolding safe_term_def by simp
    then show ?thesis by (rule same_term_prefix[OF leadership_ok_fact _ pub same])
  next
    case later
    then show ?thesis using reachable_term_safe[OF reach, of "term_of_tip_of first_history"] commits(2) pub(1)
      unfolding safe_term_def by blast
  qed
qed

section \<open>The quorum for a first commit\<close>

abbreviation current_published_history :: "abstract_state \<Rightarrow> node \<Rightarrow> publication_history" where
  "current_published_history abstract_state node \<equiv> last_published_history_of abstract_state (node, current_term_of abstract_state node)"

definition current_published_history_ok :: "abstract_state \<Rightarrow> bool" where
  "current_published_history_ok abstract_state \<longleftrightarrow>
    (\<forall>node term. elections_won abstract_state (node, term) \<noteq> None \<longrightarrow> term \<le> current_term_of abstract_state node)
    \<and> (\<forall>node. active_leader abstract_state node
              \<and> term_of_tip_of (current_published_history abstract_state node) = current_term_of abstract_state node \<longrightarrow>
        current_published_history abstract_state node \<in> publications_sent abstract_state
        \<and> (publications_accepted abstract_state node = current_published_history abstract_state node
           \<or> publications_accepted abstract_state node = butlast (current_published_history abstract_state node))
        \<and> effective_config
              (publications_committed abstract_state)
              (current_published_history abstract_state node)
              (last_committed_configuration_of abstract_state node))"

lemma current_published_history_start_join:
  assumes ok: "current_published_history_ok abstract_state"
  assumes inc: "current_term_of abstract_state node < vote_term"
  shows "current_published_history_ok (abstract_state\<lparr>
    current_term_of           := (current_term_of abstract_state)(node := vote_term),
    joins_sent                := insert (node,candidate,vote_term,position_of_tip_of (publications_accepted abstract_state node)) (joins_sent abstract_state),
    started_join_since_reboot := insert node (started_join_since_reboot abstract_state)
  \<rparr>)"
proof -
  have old_term: "other_join_position \<le> current_term_of abstract_state other_node" if "elections_won abstract_state (other_node,other_join_position) \<noteq> None" for other_node other_join_position
    using ok that unfolding current_published_history_ok_def by blast
  have none: "elections_won abstract_state (node,vote_term) = None"
  proof (rule ccontr)
    assume "elections_won abstract_state (node,vote_term) \<noteq> None"
    from old_term[OF this] inc show False by simp
  qed
  have bound: "other_join_position \<le> vote_term" if "elections_won abstract_state (node,other_join_position) \<noteq> None" for other_join_position
    using old_term[OF that] inc by linarith
  show ?thesis using ok none bound unfolding current_published_history_ok_def active_leader_def by auto
qed

lemma current_published_history_win:
  assumes ok: "current_published_history_ok abstract_state"
  assumes leaders: "leadership_ok abstract_state"
  assumes none: "elections_won abstract_state (candidate,current_term_of abstract_state candidate) = None"
  assumes base: "term_of_tip_of (publications_accepted abstract_state candidate) < current_term_of abstract_state candidate"
  assumes hist: "election_last_accepted_history election = publications_accepted abstract_state candidate"
  shows "current_published_history_ok (abstract_state\<lparr>
    elections_won := (elections_won abstract_state)((candidate,current_term_of abstract_state candidate) := Some election)
  \<rparr>)"
proof -
  let ?next = "abstract_state\<lparr>
    elections_won := (elections_won abstract_state)((candidate,current_term_of abstract_state candidate) := Some election)
  \<rparr>"
  have empty: "published_by abstract_state candidate (current_term_of abstract_state candidate) = {}"
    using leadershipD(8)[OF leaders] none unfolding published_by_def by fastforce
  have same: "last_published_history_of ?next (candidate,current_term_of abstract_state candidate) = election_last_accepted_history election"
    using empty by (simp add: published_by_def last_published_history_of.simps)
  have other: "last_published_history_of ?next (node,vote_term) = last_published_history_of abstract_state (node,vote_term)"
    if "(node,vote_term) \<noteq> (candidate,current_term_of abstract_state candidate)" for node vote_term
  proof (rule last_published_history_cong_key)
    show "elections_won ?next (node,vote_term) = elections_won abstract_state (node,vote_term)" using that by auto
    show "published_by ?next (fst (node,vote_term)) (snd (node,vote_term))
          = published_by abstract_state (fst (node,vote_term)) (snd (node,vote_term))"
      unfolding published_by_def by simp
  qed
  show ?thesis
    unfolding current_published_history_ok_def
  proof (rule conjI; intro allI impI)
    fix node vote_term
    assume "elections_won ?next (node,vote_term) \<noteq> None"
    then show "vote_term \<le> current_term_of ?next node" using ok unfolding current_published_history_ok_def by (cases "(node,vote_term) = (candidate,current_term_of abstract_state candidate)") auto
  next
    fix node
    assume act: "active_leader ?next node
                 \<and> term_of_tip_of (current_published_history ?next node) = current_term_of ?next node"
    show "current_published_history ?next node \<in> publications_sent ?next
          \<and> (publications_accepted ?next node = current_published_history ?next node
             \<or> publications_accepted ?next node = butlast (current_published_history ?next node))
          \<and> effective_config
                (publications_committed ?next)
                (current_published_history ?next node)
                (last_committed_configuration_of ?next node)"
    proof (cases "node = candidate")
      case True
      with act same base hist have False by simp
      then show ?thesis by simp
    next
      case False
      then have "current_published_history ?next node = current_published_history abstract_state node" using other by simp
      then show ?thesis using act False ok unfolding current_published_history_ok_def active_leader_def by auto
    qed
  qed
qed

lemma current_published_history_publish:
  assumes ok: "current_published_history_ok abstract_state"
  assumes leaders: "leadership_ok abstract_state"
  assumes next_leaders: "leadership_ok (abstract_state\<lparr>publications_sent := insert publication_history (publications_sent abstract_state)\<rparr>)"
  assumes active: "active_leader abstract_state candidate"
  assumes tip: "current_published_history abstract_state candidate = publications_accepted abstract_state candidate"
  assumes new: "publication_history = publications_accepted abstract_state candidate @ [\<lparr>
    publication_position        = \<lparr>
      position_term    = current_term_of abstract_state candidate,
      position_version = version
    \<rparr>,
    publication_owner           = candidate,
    publication_config          = new_configuration,
    publication_previous_config = last_committed_configuration_of abstract_state candidate
  \<rparr>]"
  shows "current_published_history_ok (abstract_state\<lparr>
    publications_sent := insert publication_history (publications_sent abstract_state)
  \<rparr>)"
proof -
  let ?next = "abstract_state\<lparr>publications_sent := insert publication_history (publications_sent abstract_state)\<rparr>"
  let ?term = "current_term_of abstract_state candidate"
  have meta: "owner_of_tip_of publication_history = candidate" "term_of_tip_of publication_history = ?term" using new by auto
  have new_in: "publication_history \<in> published_by ?next candidate ?term" using meta unfolding published_by_def by simp
  have greatest: "prefix other publication_history" if "other \<in> published_by ?next candidate ?term" for other
  proof (cases "other = publication_history")
    case True
    then show ?thesis by simp
  next
    case False
    then have "other \<in> published_by abstract_state candidate ?term" using that unfolding published_by_def by auto
    from last_published_history_publication(2)[OF leaders this] tip new
    show ?thesis by simp
  qed
  have same: "current_published_history ?next candidate = publication_history"
    using last_published_history_eq[OF next_leaders new_in ballI[OF greatest]] by simp
  have other: "last_published_history_of ?next (node,vote_term) = last_published_history_of abstract_state (node,vote_term)"
    if "(node,vote_term) \<noteq> (candidate,?term)" for node vote_term
  proof -
    have same: "published_by ?next node vote_term = published_by abstract_state node vote_term"
      using that meta unfolding published_by_def by auto
    show ?thesis by (rule last_published_history_cong_key) (simp_all add: same)
  qed
  have good: "effective_config
                  (publications_committed abstract_state)
                  publication_history
                  (last_committed_configuration_of abstract_state candidate)"
    by (simp add: new effective_config_def)
  have parent: "butlast publication_history = publications_accepted abstract_state candidate" by (simp add: new)
  show ?thesis
    unfolding current_published_history_ok_def
  proof (rule conjI; intro allI impI)
    fix node vote_term
    assume "elections_won ?next (node,vote_term) \<noteq> None"
    then show "vote_term \<le> current_term_of ?next node" using ok unfolding current_published_history_ok_def by auto
  next
    fix node
    assume act: "active_leader ?next node
                 \<and> term_of_tip_of (current_published_history ?next node) = current_term_of ?next node"
    show "current_published_history ?next node \<in> publications_sent ?next
          \<and> (publications_accepted ?next node = current_published_history ?next node
             \<or> publications_accepted ?next node = butlast (current_published_history ?next node))
          \<and> effective_config
                (publications_committed ?next)
                (current_published_history ?next node)
                (last_committed_configuration_of ?next node)"
    proof (cases "node = candidate")
      case True
      then show ?thesis using same good parent by (simp add: effective_config_def)
    next
      case False
      then have "current_published_history ?next node = current_published_history abstract_state node" using other by simp
      then show ?thesis using act False ok unfolding current_published_history_ok_def active_leader_def by (auto simp: effective_config_def)
    qed
  qed
qed

lemma receive_at_current_published_history:
  assumes reach: "dynamic_reachable abstract_state"
  assumes local: "current_published_history_ok abstract_state"
  assumes active: "active_leader abstract_state node"
  assumes current: "term_of_tip_of (current_published_history abstract_state node) = current_term_of abstract_state node"
  assumes pub: "publication_history \<in> publications_sent abstract_state"
  assumes same: "term_of_tip_of publication_history = current_term_of abstract_state node"
  assumes inc: "position_of_tip_of (publications_accepted abstract_state node) < position_of_tip_of publication_history"
  shows "publication_history = current_published_history abstract_state node"
proof -
  let ?vote_term = "current_term_of abstract_state node"
  let ?tip = "current_published_history abstract_state node"
  let ?first_history = "publications_accepted abstract_state node"
  from dynamic_invariants[OF reach]
  have messages_ok_fact: "messages_ok abstract_state" and publications_ok_fact: "publications_ok abstract_state" and leadership_ok_fact: "leadership_ok abstract_state" by auto
  obtain election other_election where certs: "elections_won abstract_state (node,?vote_term) = Some election" "elections_won abstract_state (owner_of_tip_of publication_history,?vote_term) = Some other_election"
    using active leadershipD(8)[OF leadership_ok_fact pub] same unfolding active_leader_def by auto
  have node_fact: "node = owner_of_tip_of publication_history" by (rule dynamic_one_election_candidate_per_term[OF reach certs])
  have pref: "prefix publication_history ?tip" using leadershipD(9)[OF leadership_ok_fact pub] node_fact same by simp
  have accepted: "?first_history = ?tip \<or> ?first_history = butlast ?tip"
    using local active current unfolding current_published_history_ok_def by blast
  show ?thesis
  proof (rule ccontr)
    assume ne: "publication_history \<noteq> ?tip"
    have "prefix publication_history (butlast ?tip)"
      using pref ne by (cases ?tip rule: rev_cases) auto
    with pref accepted have "prefix publication_history ?first_history" by auto
    from prefix_of_sent[OF publications_ok_fact messagesD(1)[OF messages_ok_fact] this] inc
    show False by auto
  qed
qed

lemma current_published_history_receive:
  assumes reach: "dynamic_reachable abstract_state"
  assumes ok: "current_published_history_ok abstract_state"
  assumes pub: "publication_history \<in> publications_sent abstract_state"
  assumes vote_term_fact: "term_of_tip_of publication_history = current_term_of abstract_state node"
  assumes position: "position_of_tip_of (publications_accepted abstract_state node) < position_of_tip_of publication_history"
  shows "current_published_history_ok (abstract_state\<lparr>
    publications_accepted           := (publications_accepted abstract_state)(node := publication_history),
    last_committed_configuration_of := (last_committed_configuration_of abstract_state)(node := previous_config_of_tip_of publication_history),
    publish_responses_sent          := insert (node,publication_history) (publish_responses_sent abstract_state)
  \<rparr>)"
proof -
  have eq: "active_leader abstract_state node \<Longrightarrow> term_of_tip_of (current_published_history abstract_state node) = current_term_of abstract_state node \<Longrightarrow> publication_history = current_published_history abstract_state node"
    by (rule receive_at_current_published_history[OF reach ok _ _ pub vote_term_fact position])
  have cfg: "effective_config
                 (publications_committed abstract_state)
                 publication_history
                 (previous_config_of_tip_of publication_history)" by (simp add: effective_config_def)
  show ?thesis using ok eq pub cfg
    unfolding current_published_history_ok_def active_leader_def by auto
qed

lemma reachable_current_published_history_ok:
  assumes "dynamic_reachable abstract_state"
  shows "current_published_history_ok abstract_state"
  using assms
proof (induction rule: dynamic_reachable.induct)
  case boot
  show ?case by (simp add: current_published_history_ok_def active_leader_def bootstrapped_def)
next
  case (advance abstract_state next_abstract_state)
  from dynamic_invariants[OF advance.hyps(1)] have messages_ok_fact: "messages_ok abstract_state" and leadership_ok_fact: "leadership_ok abstract_state" by auto
  from advance.hyps(2) show ?case
  proof (cases rule: transition.cases)
    case start_join
    with advance.IH show ?thesis by (simp add: current_published_history_start_join)
  next
    case (win_election candidate voters)
    have base: "term_of_tip_of (publications_accepted abstract_state candidate) < current_term_of abstract_state candidate"
      by (rule new_election_base[OF messages_ok_fact leadership_ok_fact win_election(3) messagesD(8)[OF messages_ok_fact win_election(2)] win_election(5) win_election(6)])
    show ?thesis using win_election(1) current_published_history_win[OF advance.IH leadership_ok_fact win_election(3) base] by simp
  next
    case publish
    with advance.IH leadership_ok_fact dynamic_invariants[OF dynamic_reachable.advance[OF advance.hyps(1,2)]]
    show ?thesis by (blast intro: current_published_history_publish)
  next
    case receive
    with advance.IH advance.hyps(1) show ?thesis by (simp add: current_published_history_receive)
  next
    case commit
    with advance.IH show ?thesis
      by (auto simp: current_published_history_ok_def active_leader_def intro: effective_config_insert)
  next
    case apply_commit
    with advance.IH show ?thesis
      by (auto simp: current_published_history_ok_def active_leader_def effective_config_def)
  next
    case reboot
    with advance.IH show ?thesis by (auto simp: current_published_history_ok_def active_leader_def)
  qed
qed

theorem first_commit_quorums_agree:
  assumes reach: "dynamic_reachable abstract_state"
  assumes active: "active_leader abstract_state candidate"
  assumes tip: "publication_history = current_published_history abstract_state candidate"
  assumes current: "term_of_tip_of publication_history = current_term_of abstract_state candidate"
  assumes uncommitted: "publication_history \<notin> publications_committed abstract_state"
  shows "acknowledged_by_joint_quorum abstract_state publication_history \<longleftrightarrow>
    (\<exists>voters. quorum (last_committed_configuration_of abstract_state candidate) voters
              \<and> quorum (config_of_tip_of publication_history) voters
              \<and> (\<forall>node\<in>voters. (node,publication_history) \<in> publish_responses_sent abstract_state))"
proof -
  have "effective_config
            (publications_committed abstract_state)
            publication_history
            (last_committed_configuration_of abstract_state candidate)"
    using reachable_current_published_history_ok[OF reach] active tip current unfolding current_published_history_ok_def by blast
  then have "last_committed_configuration_of abstract_state candidate = previous_config_of_tip_of publication_history"
    using uncommitted unfolding effective_config_def by simp
  then show ?thesis unfolding acknowledged_by_joint_quorum_def by simp
qed

end

declare abstract_model.last_published_history_of_update_current_term_of [simp]
declare abstract_model.last_published_history_of_update_joins_sent [simp]
declare abstract_model.last_published_history_of_update_started_join_since_reboot [simp]
declare abstract_model.last_published_history_of_update_publications_accepted [simp]
declare abstract_model.last_published_history_of_update_last_committed_configuration_of [simp]
declare abstract_model.last_published_history_of_update_publish_responses_sent [simp]
declare abstract_model.last_published_history_of_update_publications_committed [simp]

end
