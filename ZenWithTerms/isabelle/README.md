# Cluster coordination in Isabelle/HOL

## Verification

Run this command from the repository root with Isabelle2025-2.

```sh
isabelle build -D ZenWithTerms/isabelle -o quick_and_dirty=false
```

This document covers safety. Liveness is described separately in
[LIVENESS.md](LIVENESS.md).

The `Zen_With_Terms` session checks the fixed and dynamic models with no admitted
lemmas. The fixed-configuration theory includes the following results.

- `committed_states_form_chain` proves that any two committed histories in an execution
  are prefix-comparable. The committed set retains all earlier quorum commits.
- `unique_publication` proves that two publications in an execution with the same
  term and version have the same entire history, including the opaque state identity.
- `one_election_candidate_per_term` proves that two majorities of votes for the same
  term must name the same candidate. This also covers certificates whose votes
  have yet to be delivered or checked for freshness by a candidate.
- `two_commits_across_restart` constructs an execution in which node 0 commits
  `[(1,1,10)]` with voters 0 and 1, node 0 restarts, then node 1 commits
  `[(1,1,10),(2,2,20)]` with voters 1 and 2.

The model is based on the formal-models checkout at `ca26d5c` and was compared with
Elasticsearch at `07f5f43e6bf3`. The production class is
`server/src/main/java/org/elasticsearch/cluster/coordination/CoordinationState.java`.
It links to `ZenWithTerms/tla/ZenWithTerms.tla`. The older `cluster/isabelle` model
uses per-slot consensus and explicit catch-up messages. Its proof supplied the
quorum-intersection and invariant-preservation approach.

## Fixed configuration

This Isabelle/HOL session models the default, fixed-voting-configuration fragment of
[ZenWithTerms](../tla/ZenWithTerms.tla). It starts with a common bootstrapped state and version
zero. Nodes can restart, and the network can delay, drop, or replay authentic messages.
The same finite voting set supplies majorities for elections and publications.
The election and commit rules express their quorum premises as bounded universals,
and the commit rule refers directly to the publication tip. These formulations are
equivalent to the draft premises and permit Isabelle to derive the induction rule.

The model records a publication as a list of updates from the bootstrap state. Each update
contains a term, version, and opaque state identity. The list is proof-only history. Each
proposal appends to the elected leader's current publication tip, which the leader must
have accepted locally. This represents the caller's obligation to compute the new cluster
state from the previous one. The publication ancestry section below checks the
stability of the Java caller's input during this computation.

| Model step | Java boundary |
| --- | --- |
| `join` | `CoordinationState.handleStartJoin` advances the durable term and returns a vote with the accepted term and version. |
| `elect` | Successful `handleJoin` with a majority of distinct eligible votes whose accepted states are no fresher than the candidate's state. The model checks the certificate as one step. |
| `propose` | `handleClientValue` starts publication from the previous state. |
| `accept` | `handlePublishRequest` persists the accepted state before returning an acknowledgement. |
| `commit` | `handlePublishResponse` reaches a quorum for the current publication and emits an `ApplyCommitRequest`. The model checks the certificate as one step. |
| `restart` | Clears transient election state while preserving durable terms and acceptances. Sent votes, receipts, and historical publication data remain available to the model. |

The model records a commit when the leader obtains a publication quorum. It abstracts
away delivery of the commit request because `handleCommit` preserves the fixed
voting configuration.

The central invariant uses an upper bound on which older publications can still
get a majority.
A voter that has moved to a higher term counts toward that majority only if it already
acknowledged the publication. Intersecting this potential majority with the new leader's
election majority gives a voter whose join certified an accepted state at least as fresh
as the older publication. By induction, that publication is in the new leader's ancestry.
The same intersection rules out a quorum for a fresh proposal in an old term once
a higher-term leader has published.

## Dynamic reconfiguration

The [dynamic model](Dynamic_Configuration.thy) keeps the committed configuration
at each node and records both the proposed and the carried committed configuration
in each publication. A quorum is a majority of the intersection of votes with the
specified configuration. Configurations can be disjoint.

| Model step | ZenWithTerms action |
| --- | --- |
| `start_join` | `HandleStartJoin` durably increases a node's term and emits a join containing the rank of its accepted state. |
| `win` | `HandleJoin` reaches majorities in both the candidate's committed and accepted configurations. The historical certificate records both the election base and its quorum witness. |
| `publish` | `HandleClientValue` extends the leader's accepted publication tip. A configuration change requires the accepted and committed configurations to agree. Every proposed configuration needs a majority of join votes, which can include votes delivered after the election. |
| `receive` | `HandlePublishRequest` records a fresh acceptance, installs the carried committed configuration and emits an acknowledgement. |
| `certify` | `HandlePublishResponse` records first quorum commit using majorities in the carried and proposed configurations. |
| `apply_commit` | `HandleCommit` installs the accepted configuration as locally committed after a matching quorum commit. An active leader can apply only the current publication tip. |
| `reboot` | `RestartNode` disables election and publication activity until a new join. Durable state and historical evidence survive. |

The proof inducts on term in the final state of an arbitrary reachable execution.
This lets it compare a higher-term election against lower-term commits whose quorum
may have completed after the election. Between a committed checkpoint and the next
commit, its configuration remains one of the two configurations in each descendant
publication's quorum. If an election base omits an older commit, take the earliest
such commit by rank and the latest checkpoint at or before the election base.
The election votes and the omitted commit's acknowledgements intersect in the
checkpoint configuration. The intersecting voter's join must report an accepted
state at least as fresh as the omitted commit. This contradicts the candidate's
freshness check. The latest lower-term commit then provides a common quorum
configuration for any two election certificates in the same term.

- `dynamic_committed_states_form_chain` establishes ancestry for all quorum commits,
  including configuration changes.
- `dynamic_unique_publication` establishes equality of histories and their
  configurations and payloads when their `(term, version)` agrees.
- `dynamic_one_election_candidate_per_term` compares recorded successful
  election certificates, including those of leaders that later stepped down or restarted.
- `disjoint_configuration_failover` checks a transition from `{0}` to `{1}`,
  followed by a restart of node 0 and a descendant commit by node 1.

The common version-zero bootstrap and the atomic certificate abstraction carry
over from the fixed model. The dynamic model retains authentic joins and receipts
and abstracts vote collection and message delivery. The history attached to each
publication is ghost ancestry. `first_commit_quorums_agree` proves that for a
first commit the active leader's local committed configuration equals the carried
configuration, so the two quorum checks match `HandlePublishResponse`.
Subsequent commit notifications for that publication preserve the quorum commit set.

## Refinement from ZenWithTerms.tla

[Zen_With_Terms_Translation.thy](Zen_With_Terms_Translation.thy) transcribes `Init`
and the eight `Next` actions. It groups the per-node functions into records, models
the four distinct message tags as constructors, and keeps the TLA+ message set and
descendant relation. `Nodes` is finite, and values have an arbitrary Isabelle type.
The TLC `StateConstraint` is irrelevant to reachability in these proofs.

[Zen_With_Terms_Refinement.thy](Zen_With_Terms_Refinement.thy) proves that each
enabled translated action takes a related dynamic state through one transition
or leaves it unchanged. Relatedness records the provenance of joins, publish
requests, responses, and commits. It also relates the accepted state and active
publication tip, and maps proper publication prefixes to concrete descendant edges.
Bootstrap stutters because the dynamic model already has the initial configuration.
Term-zero version numbers are normalized only on the abstract side. The translated
actions retain each node's original version for freshness checks and descendant
edges. Wire values remain opaque and are tracked by publication key.

The refinement transfers `LogMatching`, `OneMasterPerTerm`, and
`CommittedValuesDescendantsFromCommittedValues` to the translation. It also
rules out election wins by different candidates in the same term at different
points of an execution, including across restarts. The correspondence of the
translation to the TLA+ text is by inspection. Isabelle checks the simulation
and the safety transfer.

## Refinement of CoordinationState.java method calls

[Coordination_State_Java.thy](Coordination_State_Java.thy) transcribes the protocol
checks and updates at serialized method boundaries in `CoordinationState.java` at
Elasticsearch revision `07f5f43e6bf3`. It also models the constructor's transient
reset, the default strategy's quorum and reconfiguration checks, and the voter-ID
map in `VoteCollection`. The TLA+ side retains all delivered votes. The projection
keeps the master-eligible IDs in those vote sets, which gives the same quorum
answers when the required configurations contain only eligible IDs. The proof
checks Java's signed `int` quorum arithmetic under a bound of fewer than
\(2^{30}\) modeled IDs.

[Coordination_State_Refinement.thy](Coordination_State_Refinement.thy) proves that
every successful call satisfying `caller_contract` maps to a translated action
or stutters. Calls rejected by a runtime protocol check stutter. The reachability
theorem composes with the TLA+ refinement above.

The following conditions define the method-boundary contract and its production
proof obligations.

- **Inputs and outputs.** Transport must preserve message provenance and routing,
  including join destinations and response sources. The journal treats returned
  requests as available for delivery and permits callers to leave them undelivered.
  Bootstrap data must agree within the modeled cluster, and supplied publication
  metadata must preserve the current committed configuration.
- **State representation.** The projection uses stable IDs with a fixed
  eligibility classification. Inert voting IDs can represent bootstrap placeholders.
  It represents nonnegative Java term and version values as naturals. The opaque
  value projection must ignore recipient-local information and the commit-only
  metadata updates that leave publication identity unchanged.
- **Execution.** Calls run serially with the `PersistedState` effects described by
  its interface. Recovery must preserve the projected durable state. Failures
  during persistence and assertions about projected-away metadata require their
  own justification.
- **Self-commit ordering.** Java's `handleCommit` checks current term and the
  accepted key. The TLA+ action also checks the published version when an election
  is won. If the keys differ, the caller must ensure that the commit leaves the
  projected committed configuration unchanged. The proof then treats the call as
  a stutter.

[Coordination_State_Example.thy](Coordination_State_Example.thy) demonstrates why
the last condition matters. A leader can accept and obtain a commit for a change
from `{0}` to `{1}`, start another publication carrying the old configuration,
and then apply the authentic first commit. The class accepts that call, and no
matching TLA+ step or stutter exists from the related state. This trace exercises
the class boundary without the caller's publication-completion condition.

## Coordinator publication lifecycle

[Coordinator_Lifecycle.thy](Coordinator_Lifecycle.thy) discharges the
self-commit ordering condition using a transcription of the production lifecycle
at mutex boundaries. The proof tracks calls to the coordination core alongside
the leader mode, publication slot, and historical local commit applications.

| Production path | Lifecycle event |
| --- | --- |
| `Coordinator.publish` checks leader mode and an empty `currentPublication` before starting the core publication. | `Begin_Publication` records the slot and publication key when installation succeeds. An exception before installation can advance the core's published version without registering a deliverable commit. |
| `CoordinatorPublication.onCompletion` waits for `localNodeAckEvent`. A successful local acknowledgement follows `Publication.ApplyCommitResponseHandler.onResponse`, after `Coordinator.handleApplyCommit` has applied that commit. | `Finish_Success` clears the matching slot after local commit application. |
| `removePublicationAndPossiblyBecomeCandidate` clears the slot and steps down if it is still leading that publication's term. Cancellation can leave a publication pending until a callback arrives. | `Finish_Failure` clears the slot and disables leader mode for that term. An old-term callback may clear its slot while the node leads a newer term. |
| `processJoinRequest` enters leader mode on a new election win. A future-term join first runs `joinLeaderInTerm` and advances the term. | Leader entry is associated with the false-to-true win within that mutex region. A repeated join preserves an existing win. A restart clears the transient join flag, so it takes a new term to win again. |

An unapplied publication in the current term occupies the slot whenever its
publisher is still in leader mode. Thus, when a leader starts a newer publication
in that term, any earlier registered publication has already been locally applied.
Durable acceptance cannot go back to an earlier key, and applying the same commit
again preserves the projected configuration. `late_self_commit_is_replay` proves
this directly. `coordinator_commit_ordering` also covers authentic commit
deliveries in general by using election uniqueness to identify the source when
the recipient has won that term.

The correspondence between the lifecycle events and the Java control paths was
checked by inspection. The proof uses the method-boundary contracts for transport
provenance, matching acknowledgements to successful calls, state projection, and
persistence. The transport model below establishes provenance for the modeled
send paths. Relating opaque publication ancestry to cluster-state computation
still requires the caller's previous-state consistency argument.

## Coordination transport provenance

[Coordination_Transport.thy](Coordination_Transport.thy) adds a transport history
beside the Coordinator state. The receive rules use send and callback records
plus the core runtime checks. Isabelle derives the corresponding journal entries
and publication registrations from earlier successful calls. The history permits
delays, dropped traffic, duplicate deliveries that pass the runtime checks, and
delivery to the local node. A retired publish response handler cannot route
another reply for the same request.

| Production path | Modeled routing |
| --- | --- |
| `CoordinationState.handleStartJoin`, `Coordinator.joinLeaderInTerm`, `JoinHelper.sendJoinRequest`, and `Coordinator.joinWithDestination` | The returned vote carries the voter, candidate, term and accepted key. The immediate path sends it to the returned vote's candidate. The discovery and publish-reply paths filter the cached vote by candidate and term. The minimum term on the outer JoinRequest can affect scheduling while the optional vote's fields stay intact. |
| `CoordinatorPublication.sendPublishRequest` and `PublicationTransportHandler.PublicationContext` | The installed publication supplies the state and the publication target supplies the receiver. The local fast path uses that state directly. The full and diff paths preserve the same projected request and destination, including when an incompatible diff triggers a full-state retry. |
| `ClusterState.ClusterStateDiff.apply` and `PublicationTransportHandler.deserializeAndApplyDiff` | A compatible diff takes target version and coordination metadata from the diff and can inherit an unchanged master from the base. A cached target UUID can bypass diff application. The transport suffix restores the transmitted committed configuration in both cases. `decode_publication_correct` checks that any successful branch reconstructs the sent projection. |
| `Coordinator.handlePublishRequest`, `PublicationTarget.PublishResponseHandler`, and `TransportService` | Acceptance produces the response term and version. The destination captured by the outstanding request supplies the voter ID when the reply is dispatched. A piggybacked join retains the responder, candidate and publication term from the sender-side filter. |
| `CoordinationState.handlePublishResponse`, `PublicationTarget.sendApplyCommit`, and `Coordinator.handleApplyCommit` | The quorum-producing response call supplies the commit request. All targets receive that request's issuer and key unchanged. The proof traces each commit to an installed publication, so the lifecycle theorem can discharge the self-commit ordering condition. |

`transport_reply_matches_request` identifies the actual responder and publication
key for a reply matched to a request registration.
`transport_inputs_discharge_caller_contract` covers the four inbound core calls.
`transport_refines_tla` composes transport reachability with the Coordinator and
Java refinements and hence carries over the safety results of the TLA+ translation.

The mapping from source to the transport transitions was checked by inspection at
the Java revision above. It uses honest participants, faithful successful codecs,
and replies from the original request endpoint, correlated by an ID that has not
been reused while an earlier reply could still arrive. The TCP response channel
uses the incoming request ID. Ordinary response lookup in `InboundHandler`
uses that ID alone. The join and commit codecs also accept identities from the
message body. The guarantee therefore applies to the production send paths under
those transport premises. Arbitrary inbound frames and Byzantine peers are
outside the model. For a cached target UUID, the cache must agree on the
publication projection apart from the commit-only fields. For a matching base
UUID and an empty nodes diff, the cache must supply the target master. A diff
that replaces the nodes carries the target master directly, including after an
election when the sender's previous state can be a masterless view. State UUIDs
serve as opaque values independent of recipient-local state.

The proof also uses the existing local input and persistence contracts.
The state supplied for publication must advertise the publishing Coordinator as
master. In production, `NodeJoinExecutor` sets the local master on election and
`MasterService.executeTasks` requires an update from an established master to
keep the local node as master. The proof starts from the supplied publication and
leaves the cluster-state computation and previous-state consistency argument
outside the transport model.

## PersistedState and restart recovery

[Coordination_Persistence.thy](Coordination_Persistence.thy) checks the durability
contract for the built-in synchronous Lucene backend used by master-eligible
nodes at the Java revision above. It models the part of each on-disk commit used
by coordination. The current term and accepted version come from Lucene commit
user data. The accepted term and both voting configurations come from the
global metadata document.

| Production path | Durability argument |
| --- | --- |
| `CoordinationState.handleStartJoin`, `setInitialState`, `handlePublishRequest`, and `handleCommit` | These are the core methods that can change the disk projection. The term setter updates the current term independently of the accepted state. The state setter updates the accepted key and both configurations. The commit marker preserves the accepted key and copies the accepted configuration into the committed configuration. A join vote or publish response is returned after its setter succeeds. |
| `GatewayMetaState.LucenePersistedState` and `PersistedClusterStateService.Writer` | The setters finish writing to disk before updating their in-memory fields. Full writes cover the initial state, a new accepted term, and retry after a failed write that may have left uncommitted changes. Term-only writes preserve accepted metadata. Incremental state writes rewrite the global document when coordination metadata changes. The projected result of each writer branch equals the corresponding setter update. |
| `Writer.prepareCommit`, `Writer.completeCommit`, and `loadBestOnDiskState` | The writer prepares all paths and completes each commit before reporting success. Commit-time I/O failure raises a fatal `IOError`. A process crash during completion can leave old and new copies. The loader selects by accepted term, accepted version, then current term. It rejects a selection with a current term below any other copy's. |
| `GatewayMetaState.createOnDiskPersistedState` and `Coordinator.doStart` | Startup reconstructs the accepted version and coordination metadata. Metadata upgrades modify projects and initial state preparation changes local nodes, settings, and blocks. These operations preserve the disk projection. The backend rewrites the recovered image before coordination starts. The `CoordinationState` constructor clears transient votes, election state, and publication state and seeds the published configuration from the recovered accepted configuration. |

`restart_after_acknowledged_write` shows that any retained configured path
recovers the acknowledged projection. `restart_during_write` shows that a
successful recovery from an interrupted write can be linearized before or after
that call. The after branch can keep ghost messages from the call in the abstract
history. The concrete transport can leave those messages undelivered.
`durable_execution_refines_tla` composes these synchronous persistence steps
with the transport model and the existing Java and TLA+ refinements.

The accepted value in the Java model is a ghost publication identity. Startup
constructs a new `ClusterState`, whose state UUID can differ from the original
publication UUID. `recovered_value_from_journal` proves that the recovered key
identifies the same abstract value in the proof history, using log matching.
The journal is ghost state. Production neither persists it nor uses it during
startup. Wire UUIDs still identify transport cache entries within the transport
model's codec and identity conditions.

The source-to-model mapping was checked by inspection. The proof depends on
faithful disk codecs, Lucene's per-path atomic commit semantics and durability
after a successful commit, and the storage retaining at least one configured
copy for recovery of an existing node. It models fail-stop interruption at the
serialized method boundary. A failed prepare has no committed effect, while
a fatal completion failure can leave either committed image on each path.
The fixed path set in the composed execution excludes restoring backups and
attaching divergent historical copies. The recovery lemmas separately cover
strictly older copies when an up-to-date copy survives and no copy has a greater
current term. A same-rank stale copy can differ in committed configuration and
tie the loader's ordering, as `same_rank_config_divergence` shows.

The literal Java restart contract does not hold for every built-in backend.
With `AsyncPersistedState` on a data node without the master role, a setter can
return before the background write, and background state writes replace both
voting configurations with `STALE_STATE_CONFIG`. A coordinating-only node's
`InMemoryPersistedState` starts over at term zero with empty configurations.
The composed theorem above covers synchronous nodes. The mixed-role projection
below accounts for the weaker backends. Plugin-supplied persistence
implementations have separate contracts.

## Mixed-role deployments

[Mixed_Role_Durability.thy](Mixed_Role_Durability.thy) composes the synchronous
voting nodes with two kinds of non-master observer. An observer can receive and
apply publications, join a master, and respond to a publication. Its local term,
accepted state, and configurations can change on recovery without changing any
voting node's durable state.

| Production path | Mixed-role model |
| --- | --- |
| `GatewayMetaState.AsyncPersistedState` | The setters update live state and queue flags before returning. A single worker captures a batch, writes the captured term first when present, and writes the captured accepted key with both configurations set to the stale-state marker. Calls arriving during a batch can queue the next one. An aborted batch can lose unwritten updates. On restart, the loader can see the old or new image from an interrupted path commit, and the new runtime state has an empty queue and worker. |
| `GatewayMetaState.createInMemoryPersistedState` | Restart creates a new coordination state at term and version zero with empty configurations. Previously sent packets can still be in flight. |
| `Coordinator.startElectionScheduler`, the join paths, and `VoteCollection.addVote` | The scheduler only runs on master-eligible nodes. Joins are directed to master-eligible candidates. A non-master sender can trigger the receiver's term handling and affect cluster membership, but supplies no vote. An increase prompted by an observer is represented by the ordinary synchronous term-advance step. |
| `CoordinationState.handleJoin` and `handlePublishResponse` | The core can re-evaluate an unchanged vote set. If an observer message has a voting-state effect, an existing join or response from a counted voter can be replayed with the same effect. This covers leader entry and commit output without assuming that every observer message stutters. |

`mixed_role_durability` proves that projecting a mixed execution onto its voting
nodes yields an execution of the synchronous durability model.
`mixed_role_refines_tla` transfers the existing coordination safety results to
that projection. In particular, an observer's restart can roll its local state
back without rolling back an election vote or quorum acceptance. The theorem
does not claim monotone local acceptance or application on observers.

The projection assumes fixed master eligibility for each node ID, including
across restart. Voting configurations contain eligible IDs and may contain
inert bootstrap placeholders. The built-in backends, default election strategy,
transport premises, and storage assumptions above apply. Role changes that
promote previously asynchronous or in-memory nodes, plugin backends, application
state recovery, and liveness stay outside this model. The correspondence to the
Java control paths was checked by inspection.

## Master eligibility changes across restarts

This model deliberately does not cover role changes that keep the same
persistent node ID, such as a node restarting as coordinating-only and later
restarting as master-eligible. The decision is to treat such changes across
publications as out of scope, and `mixed_role_refines_tla` carries the
fixed-eligibility assumption stated above.

The reason is a known, low-risk gap in the Java code.
`GatewayMetaState.createInMemoryPersistedState` overwrites the on-disk state
with an empty image at term and version zero while keeping the node ID. If that
node later restarts as master-eligible while its ID is still in the voting
configuration, it has forgotten its earlier votes and acceptances. It can vote
again in a term it already voted in, so two leaders can be elected in the same
term and commit different states with the same key. We did not find a guard
against this in the startup role check, and the correspondence was checked by
inspection only.

An earlier draft theory, `Role_Change_Durability.thy`, formalised a
counterexample trace and a term-retention result for the async backend. Its proofs were
not complete (one `simp` step did not terminate), and the decision above made
it unnecessary, so it was removed. It remains in the git history (branch `2026/11/21/chatgpt-zen2-proof`,
commit `7a252e7` and earlier).

## Bootstrap agreement

[Bootstrap_Agreement.thy](Bootstrap_Agreement.thy) models configured
bootstrap in `ClusterBootstrapService.checkRequirements` and
`startBootstrap`. The local view must match a strict majority of the
requirements, including the local node. An unmatched requirement
contributes an inert placeholder. `Coordinator.setInitialConfiguration`
checks that the current peer view has a quorum of the proposed configuration
before installing it.

**Deployment assumptions for configured bootstrap**

- Node names are unambiguous. A bootstrap requirement always resolves to
  the same persistent node ID across discovery views, and two requirements
  in the roster identify distinct IDs. The same rule applies to any
  address-based requirements.
- Wherever bootstrap settings are supplied for this cluster, they specify
  the same requirements. The end-to-end refinement assumes that initial
  voting configurations agree wherever they have been installed.

With the same requirement set and a consistent injective binding from
requirements to persistent node IDs, two successful views install the same
configuration exactly when they discover the same bound IDs.
`configured_quorums_intersect` proves that their initial quorums still
intersect when those views install different placeholders. Together with
one vote per persistent ID in a term, this yields uniqueness for elections
using the initial configurations. The theory also checks examples that
separate configuration equality from quorum intersection.

The Java method checks ambiguity within each discovery view. The binding
condition is global. The initial-quorum result leaves the general case of
dynamic reconfiguration from different initial configurations open.
Agreement of the installed configurations supplies the common
configuration premise of the existing refinement. The best-effort
unconfigured bootstrap path has no shared roster from this model.

## Publication ancestry

[Publication_Ancestry.thy](Publication_Ancestry.thy) models the interval
between a `MasterService` batch reading its input and
`Coordinator.publish` admitting its output. The batch starts after the
local election win, with an empty publication slot. The serial master
service keeps the next local batch from starting until the current batch
finishes. The model excludes a local restart during a running batch.

`admitted_batch_keeps_its_accepted_base` proves that the runtime
term and leader checks keep the batch's accepted base valid at admission
when the result term is at most the term captured by the batch.
If a term advance could invalidate the snapshot, the old batch cannot
pass admission. In the retained term, election uniqueness and the
publication lifecycle exclude a newer local acceptance in the empty slot.
An authentic delayed commit preserves the projected accepted base.

`admitted_batch_refines_begin` lifts a batch to the Coordinator model
when the task extends its supplied snapshot, names the local master,
and preserves the snapshot's committed configuration.
`admitted_batch_uses_captured_parent_in_tla` obtains the TLA+ descendant
edge from the captured accepted key to the new publication. The first
post-election batch can receive a masterless view of the same accepted
state. The built-in persistence backends return no alternate state from
`getLatestStoredState`. The scheduling, view, and built-in election
task correspondence were checked by inspection of `MasterService`,
`Coordinator`, `JoinHelper`, and `NodeJoinExecutor`.

An executor's semantic use of its input and its output metadata remain
producer obligations at the generic executor interface.
`runtime_admission_cannot_imply_begin` exhibits the missing
committed-configuration check without relying on Java assertions.
The stock executor proof below discharges this obligation for the
modeled state construction paths.

## MasterService executor state construction

[Master_Service_Executors.thy](Master_Service_Executors.thy) models the
builder input and the fields used by coordination. A result extends its
input when the builder is seeded from that input and applies the task's
edits to it. The proof tracks this parent through task accumulation,
election completion, and the final version update. Application metadata,
routing, blocks, and other content are opaque in the proof.

| Source path | Modeled effect |
| --- | --- |
| `ClusterState.Builder(ClusterState)`, `Metadata.Builder(Metadata)`, and `CoordinationMetadata.Builder(CoordinationMetadata)` | The copies retain the committed voting configuration. Editing a project, settings, routing, customs, blocks, or voting exclusions preserves it. The parent comes from the copied input. |
| `MasterService.UnbatchedExecutor`, `SimpleBatchedExecutor`, `SimpleBatchedAckListenerTaskExecutor`, and `LocalMasterServiceTask` | The supplied state seeds the update. A successful batched update supplies the next input, and the post-batch hook receives the final state. A local read-only task returns its input. |
| `Coordinator.improveConfiguration` and the voting-exclusion tasks | These use the copied coordination metadata and change the accepted configuration or exclusions independently of the committed configuration. |
| `NodeJoinExecutor.becomeMasterAndTrimConflictingNodes` | The first publication sets the term and names the local master. The stock persistence backends supply no alternate `JoinTask.initialState`, and the default post-election reconfigurator returns its input. The join, node-removal, and allocation edits operate on this base. |
| `RestoreService` and `GatewayService.RecoverStateUpdateTask` | Restore seeds the publication metadata builder from the live task input and copies selected settings, customs, and project data from the snapshot. Gateway recovery edits the routing table and recovery block on its input. |
| `MasterService.patchVersions` | The version update copies the returned state, increments its version, and increments the metadata version if the metadata changed. It preserves both voting configurations. |

`builtin_executor_preserves_base` establishes the parent and committed
configuration for the modeled executor results. For an admitted result,
`admitted_builtin_executor_refines_publication` discharges the producer
premises of the batch ancestry proof, and
`admitted_builtin_executor_has_tla_parent` derives the corresponding
TLA+ descendant edge.

The ordinary task path starts from the established local master's view.
The production `runOnlyOnMaster` overrides are `LocalMasterServiceTask`,
which returns its input, and `NodeJoinExecutor`, which can complete an
election on a masterless view. For an ordinary join on an established
master, the batch snapshot's term equals the captured current term.
The runtime lower bound on the join task's term and its earlier enqueue
then give equality independently of the Java assertion.

The mapping of the Java source to these edit categories was checked by
inspection at Elasticsearch revision `99986f8b4832`. Isabelle checks
the state construction and its composition with the Coordinator proof.
The scope is the default strategy and stock state construction paths.
The generic executor interface can return an arbitrary state, and
plugin callbacks, custom persistence and reconfiguration, and
task-specific payload semantics require separate refinement arguments.
For example, the stateless persistence implementation can supply a fresher
election base from storage. It copies the local committed configuration into
the replacement, but its parent differs from the original batch input.
The proof of the stock election path uses the absence of such a replacement.

## Commit application and acknowledgements

[Commit_Application.thy](Commit_Application.thy) distinguishes the
leader's internal self-commit transport response from its external node
acknowledgement. The latter waits for a separate applier task. A follower's
commit response likewise follows its applier callback.

Both tasks supply `Coordinator.applierState` when the applier runs. A
successful callback witnesses the sampled publication key. It is safe
to acknowledge a later quorum-committed descendant of the state in the
request. For example, cancellation after quorum can let the leader finish
while an older follower apply task is still queued. The task can also
succeed when it finds the same state already installed. Success records
what the process incarnation that ran the task applied. A later async or
in-memory restart can lose the locally applied state while an earlier
acknowledgement is still in flight.

`mixed_node_acknowledges_committed_prefix` relates the requested and
sampled keys to authenticated quorum commits in the mixed-role proof.
The requested history is a prefix of the sampled history.
`coupled_node_acknowledges_committed_prefix` establishes this result for
the execution that interleaves observer coordination and application work,
including both observer restart paths. The guarantee
concerns the publication key and its ancestry. The production view can
hide unrecovered metadata, and listener exceptions handled by the
applier do not undo an installed state. The model uses the per-node
callback, separate from the task-level acknowledgement aggregation in
`MasterService`.

## Stateless persistence and election recovery

[Stateless_Persistence.thy](Stateless_Persistence.thy) gives the stateless
plugin its own refinement to an append-only committed history. Stateless
coordination elects using a self vote and a shared lease grant, and
publishes using the new configuration, which is the leader's singleton.
This gives it a different proof from the default strategy's joint quorums.

| Source path | Modeled effect |
| --- | --- |
| `StatelessElectionStrategy.onNewElection` and `beforeCommit` | A successful register CAS reserves a strictly larger term. A success callback confirms the reservation for its nominated incarnation. A failed invocation can leave a reservation without an election grant. Activation and approval are separate. The approval model uses the largest successful term at the start of the lease read as a lower bound, which accommodates a read overlapping an unfinished CAS. |
| `StatelessPersistedState.writeClusterStateToDisk` and `BlobStoreSyncDirectory` | Startup and term changes skip local durability. Only the named leader writes the accepted image. A visible segments manifest follows upload of its referenced data. Upload can finish after a new grant. A commit approval needs the publication's already-written image and an admissible lease read. |
| `getLatestStoredClusterStateMetadataForTerm` and `getLatestStoredState` | Recovery probes from the previous term down through missing directories. It can retain the local image when it dominates the observed key. A successful download can return a later version from the same probed term. If the image disappears before download, production fails that election attempt. |
| `NodeJoinExecutor`, `SingleNodeReconfigurator`, and `MasterService.patchVersions` | The election task chooses the greater accepted key, uses its content as the parent, carries the local committed configuration, installs the candidate's singleton as accepted, and increments the selected base's version. The stateless voting-exclusion APIs reject changes, so the join task's exclusion rewrite cannot replace this singleton in a stock stateless run. |
| `StatelessClusterStateCleanupService` | Cleanup follows application in a committed term and deletes only earlier term directories. An outstanding old writer can recreate an older directory. Recovery still protects the latest approved term from deletion. |

`stateless_refines_committed_log` proves that each modeled execution
projects to an append-only approved history. `stateless_commits_form_chain`
then gives ancestry for delivered commit notifications.
`stateless_unique_publication` gives unique identities by term and version,
and `stateless_one_grantee_across_execution` gives grant uniqueness across
the execution. For a new term, `chosen_parent_extends_prior_commits`
shows that the selected base covers the earlier commits even when it is
downloaded after local state has been lost.
`stateless_executor_uses_selected_base` checks the version and configuration
updates on that alternate path, and `downloaded_executor_refines_election_base`
connects the Java key comparison to the abstract choice. A storage image can
include a publication whose lease check never succeeded. The recovery proof
uses the retained approved frontier to establish ancestry in that case.
`first_election_snapshot_preserves_committed` checks that the local committed
configuration used by the adapter stays fixed while the term is current
and its first publication is still being prepared.

Approval is the fence check that authorizes an apply-commit notification.
The earlier publication bookkeeping event named `onCommit` can happen while
the fence-check future is still pending. The theorem covers the notification
history. To start another publication in the same term, the Coordinator must
first clear the slot. Successful completion waits for the leader's own
apply-commit response through that future. Failure fences the same-term
leader. This supplies the previous-publication premise of the stateless
transition.

The Java mapping was checked by inspection at Elasticsearch revision
`99986f8b4832`. The refinement is at lease, storage, and publication
boundaries. It uses one shared lease and blob namespace for the cluster,
monotonic register CAS, the read-after-success floor of the register API,
faithful visibility and decoding of complete Lucene manifests, and a
successful per-term writer that advances its image monotonically. It also
uses authenticated transport with grants and publication work confined to
the nominated process incarnation, and serialized publication lifecycles.
Local accepted state can be lost on restart. A fresh incarnation uses a
new grant, and its first publication can recover from the shared store.
Storage errors, missing payloads after a probe, and rejected lease checks
can halt an attempt.

### Production stateless storage

[Stateless_Storage.thy](Stateless_Storage.thy) checks the Java storage
boundary against the stateless safety model. The checked Java revision is
`99986f8b4832`. The model treats provider requests as operations on complete
objects and traces their effects separately from the Java callbacks. It
uses a single local metadata writer per term and these source bindings:

| Source path | Isabelle correspondence |
| --- | --- |
| `ObjectStoreService`, `StatelessElectionStrategy`, `StatelessLease` | All coordination paths in a cluster use the same configured cluster repository. The lease key is `cluster_state/lease`, while manifests and files are keyed by the decimal term under `cluster_state/`. The empty lease represents term zero. Election writes compare the encoded lease and advance its term to `max(proposed, observed + 1)`. Updates to the node-left and project-deletion generations leave the term unchanged. The proofs use the range in which Java's signed counters do not wrap. |
| `S3BlobContainer`, `GoogleCloudStorageBlobStore`, `AzureBlobStore` | The stateless S3 repository leaves conditional writes enabled. Its CAS uses GET plus conditional PUT against the observed ETag, or an absent-object condition. GCS pins the witness and update to the same live object generation, using generation zero for creation. Azure pins an existing-object read and update to one valid exclusive lease and uses conditional creation for a missing object. Its register implementation requires the primary endpoint. |
| `BlobContainer.compareAndSetRegister` and `StatelessElectionStrategy.beforeCommit` | A failed or missing witness cannot produce a grant. An exceptionally completed CAS can still change the object. A successful grant callback belongs to its own write and can arrive out of order. A successful fence read must cover the effects that already returned success when the read started. The proof derives the abstract fence from the journal of object revisions, even if another write is in flight. |
| `Coordinator`, `CoordinationState`, `GatewayMetaState.LucenePersistedState` | The self-publication handler holds the coordinator mutex and validates the publication term and accepted version before persisting it. The current term stays fixed across the blocking write, so its directory and the commit's term agree. The response follows persistence. Within a term, strictly newer publications advance the accepted version. Rewriting its committed flags can leave the publication key and lineage unchanged. |
| `PersistedClusterStateService.Writer` and `BlobStoreSyncDirectory` | A full write on term change replaces the index contents. Within a term Lucene may reuse files of its previous commit. `sync` waits for newly referenced files to finish uploading before the manifest rename writes the atomic segments blob. File pruning keeps the latest manifest and the files it references. A failed manifest finalization can leave a visible complete manifest even though the writer reports failure. |
| `StatelessPersistedState.TermBlobDirectory` and `StatelessClusterStateCleanupService` | Recovery lists the term's segments objects, reads the highest generation, and downloads the referenced files into staging. The decoder checks the committed image when opening the staged Lucene directory. Cleanup of earlier terms follows committed local application. Partial deletion can remove the newest manifest and leave an older one, or cause download failure. |

The live-directory proof shows that a completed header remains available
at its key or at a later key until a later committed term makes that
directory obsolete. The stateless model now permits cleanup of a subset of
earlier terms and partial-cleanup observations below the approved frontier.
A search for a term that can still approve a publication cannot use those
observations to roll back its base. The ancestry, publication uniqueness,
and grant uniqueness statements are unchanged.

The cloud mapping uses the provider's documented atomic whole-object
updates, conditional-write guards, and read/list visibility on the
configured endpoint. On S3 this includes the binding between the ETag
and the bytes read from the lease object. The model uses authentic
successful reads, Lucene's decoding, immutable segment names, and
increasing manifest generations. All nodes must use the same dedicated
bucket or container and base path. The namespace excludes external writes
and deletes, restores, and lifecycle expiry. The model also uses
one live writer per term as supplied by the coordination refinement. The
proof checks the storage transition model and the consequences of those
contracts. The Elasticsearch repository adapters and Java/Lucene source
correspondence are reviewed by inspection.

### Paginated recovery

[Stateless_Paginated_Recovery.thy](Stateless_Paginated_Recovery.thy) allows
each page to observe a different set of manifests. A new manifest can
sort before the cursor and go unseen. A manifest whose name stays present
throughout a successful ordered traversal must be returned. The empty
first page of a completed traversal indicates that the directory had no
manifests when that page was read. [GCS listing and page tokens](https://docs.cloud.google.com/storage/docs/json_api/v1/objects/list)

#### Provider cursor contracts

[Stateless_Listing_Providers.thy](Stateless_Listing_Providers.thy)
checks the page-to-cursor correspondence separately from retention.
The GCS source review includes `StorageImpl.BlobPageFetcher` in SDK
2.71.0, which keeps the list options and replaces the page token, and
`PageImpl.PageIterator`, which follows a continuation after an empty page.
Azure SDK 12.27.1 forwards `NextMarker` to the next hierarchical listing
request without interpreting it.

| Provider | Production path and proof boundary |
| --- | --- |
| GCS | `GoogleCloudStorageBlobStore.listBlobsByPrefix` consumes the JSON listing through `iterateAll()`, with the same prefix and delimiter on each page. GCS says the token records the last returned name and generation and the next request returns keys after it. Immutable manifest names let the proof project that token to the name. `gcs_listing_refines_cursor` accepts a different view on every request and permits a continuation whose next page is empty. [GCS Objects list](https://docs.cloud.google.com/storage/docs/json_api/v1/objects/list) · [GCS pagination](https://docs.cloud.google.com/storage/docs/paginate-results) |
| S3 | General-purpose buckets document strong LIST consistency and identify a complete result with `IsTruncated=false`. The ordinary `S3BlobContainer.executeListing` path uses an opaque continuation token. The documentation leaves its resumption rule under deletion open. [S3 ListObjectsV2](https://docs.aws.amazon.com/AmazonS3/latest/API/API_ListObjectsV2.html) · [S3 consistency](https://docs.aws.amazon.com/AmazonS3/latest/userguide/Welcome.html#ConsistencyModel) |
| Azure | `AzureBlobStore.listBlobsByPrefix` uses the SDK's hierarchical listing at the primary endpoint. An empty `NextMarker` indicates a complete response. The ordinary iterator forwards an opaque marker whose resumption after deletion remains unspecified. [Azure List Blobs](https://learn.microsoft.com/en-us/rest/api/storageservices/list-blobs) · [Azure SDK pagination](https://learn.microsoft.com/en-us/azure/developer/java/sdk/pagination) |

The checked countermodel for the opaque continuation paths starts
with ordered keys `a, b, anchor, z`. The first page returns `a` and
records `b` as the next key. Cleanup removes `a` and `b`. A continuation
that falls back to the saved offset can then return `z` and miss
`anchor`, even though both pages reflect fresh views and the overall
output is ordered. In an unchanged view the countermodel resumes at its
recorded next key. This establishes a limit of the documented premises.
It does not identify either provider's token implementation or establish
a production safety failure.

#### Single-response recovery on S3 and Azure

[Stateless_Single_Page_Recovery.thy](Stateless_Single_Page_Recovery.thy)
checks stateless recovery with the accompanying guards in
`S3BlobContainer.listBlobsByPrefix` and
`AzureBlobStore.listBlobsByPrefix`. The guards run for
`OperationPurpose.CLUSTER_STATE`, on both the metadata probe and the
payload download. S3 requires an explicit `IsTruncated=false` and an
absent continuation token. Azure reads the first SDK response and
requires an empty or absent marker.

A response requiring continuation fails with `IOException`.
`StatelessPersistedState` treats this as a failed read, and
`Coordinator.getLatestStoredStateAfterWinningAnElection` abandons the
election attempt. A complete response with zero manifests still means
the term directory is empty. A term with more manifests than fit in a
single response can therefore prevent recovery until the listing fits.

**Deployment assumption.** Across all stateless storage backends, the
items matching each recovery listing, including the cleanup backlog,
fit in one complete provider response. This is a bound on the actual
response, including the absence of a continuation token or marker. A
count below the provider's nominal page limit alone does not establish
completeness. The S3 and Azure guards still reject incomplete responses
if the deployment exceeds this bound.

The provider boundary is strong consistency of a complete, uncontinued
LIST response for the manifest prefix. Each accepted response gives
one directory view. The header and download can observe different
views, and a file that disappears before it is read can fail recovery.
`checked_live_term_listing` establishes that a successful response in
the frontier term is nonempty and selects an image at or above the
approved frontier. `checked_download_preserves_commits` transfers that
bound to the selected election base. These proofs use no continuation
semantics for S3 or Azure.

In the term of the last approved publication, recovery has two cases.
If that publication was the first in its term, every manifest in the
term contains its history or an extension. The directory stays nonempty.
If it was a subsequent publication, its manifest stays present across
the scan. The earlier leader can still finalize a successor upload after
the new grant, but the successor cannot start a successful lease check
in the earlier term. The publication lifecycle requires the successor's
successful local completion before another publication can write.

The retention bound uses the order of calls in Lucene 10.5.2.
`BlobStoreSyncDirectory.rename` uploads the new manifest and captures its
delete queue before returning. Lucene's `IndexWriter.finishCommit` then
checkpoints, marking the preceding manifest obsolete. Elasticsearch
can submit that deletion only after another manifest rename. Async
deletes and retries may keep older files around. They cannot remove
either of the two most recent manifest keys. Marking the first
publication committed can write another manifest for the same history.
After that, the committed UUID and the leader's singleton configuration
already match, so marking subsequent publications is a no-op.
[Lucene IndexWriter 10.5.2](https://github.com/apache/lucene/blob/releases/lucene/10.5.2/lucene/core/src/java/org/apache/lucene/index/IndexWriter.java#L4004-L4037)

[Stateless_Manifest_Retention.thy](Stateless_Manifest_Retention.thy)
models remote rename effects separately from local completion. A
failure before the manifest takes effect leaves no new key. An ambiguous
PUT can leave a new key without a deletion batch. A failure after the
batch is captured can leave both. The model permits every old batch to
take effect later and to remove any subset of its keys repeatedly.
`asynchronous_deletes_preserve_latest_two` proves that the two latest
manifest generations are live and absent from all captured batches.
This relies on a fresh name for each effective rename in a term and on
closing the same-term writer after a finalization failure.
Each batch captures its destination term container. For a reused local
writer, filenames carried over from an earlier term are older than the
new term's manifest generations. The model tracks deletions of manifest
keys belonging to the captured term.
`PersistedClusterStateService.Writer.completeCommit` closes the writer
and raises `IOError` on I/O failure; a new incarnation cannot acquire
the old lease again. Whole-directory cleanup still uses the separately
checked rule that deletes terms earlier than an applied commit.

An election that can still commit cannot skip the term of the approved
frontier. A successful paginated download from that term may return a
version below the earlier header and still cover the frontier. A
download from a later term covers the frontier by the ancestry
invariant. A missing manifest or missing referenced file during the
read can fail the attempt. The abstract header and download rules now
use the approved frontier as the minimum for its term. The committed
ancestry, publication uniqueness, and grant uniqueness statements are
unchanged.

The verified deployment requires exactly one `path.data` per node and
forbids multiple data paths. With the deprecated multiple-data-path
layout, `PersistedClusterStateService` creates a separate Lucene writer
for each path and
`StatelessPersistedClusterStateService` routes all of them to the same
remote term prefix. The proof requires that a file name still denotes the
bytes referenced by a retained manifest. Distinct writers updating the
same key need a separate argument for this property.

- [Amazon S3 consistency](https://docs.aws.amazon.com/AmazonS3/latest/userguide/Welcome.html#ConsistencyModel) and [conditional writes](https://docs.aws.amazon.com/AmazonS3/latest/userguide/conditional-writes.html)
- [Google Cloud Storage consistency](https://docs.cloud.google.com/storage/docs/consistency) and [generation preconditions](https://docs.cloud.google.com/storage/docs/request-preconditions)
- [Azure Blob Storage consistency and leases](https://learn.microsoft.com/en-us/azure/storage/blobs/concurrency-manage)

The backend scope is production S3 with conditional writes, GCS, and
primary Azure Blob Storage. The `fs` repository is used here for testing
and is explicitly outside the proof's scope. Its in-place lease writes
and partial-write behavior are outside the cloud whole-object contract.

## Composed coordination and task acknowledgements

[Stateless_Execution.thy](Stateless_Execution.thy) combines the stateless lease
and recovery model with authenticated publication delivery and application.
A first publication takes its base from the accepted state or shared recovery.
A subsequent publication extends the latest approved state in its term.
Publication registration names a live grant holder. Delivery requires a packet
for the receiving incarnation. Restart clears the local working state and
increments that incarnation. Historical evidence of earlier successful
applications survives as ghost state.

`stateless_node_acknowledges_committed_prefix` proves that both the requested
publication and the state actually applied were approved and had a commit
notification. The requested history is a prefix of the applied history. The
state sampled from the live applier supplier can be later than the request.

[Stock_Coordination_Execution.thy](Stock_Coordination_Execution.thy) captures
the mixed-role voting state at the start of a stock MasterService batch.
Every newly registered publication comes from a captured batch. The runtime
admission checks and the batch trace imply that this result extends the
accepted state still present at admission. The executor also preserves the
committed voting configuration from its input. The stock reachability theorem
projects to the Isabelle translation of ZenWithTerms. The registration theorem
identifies the captured parent per registration, and the existing
`admitted_builtin_executor_has_tla_parent` gives a translated descendant edge
for a single admitted batch.

[Task_Acknowledgements.thy](Task_Acknowledgements.thy) checks one countdown
slot for each required publication target and one for `onCommit`. The
publisher always has a target slot. Success requires a successful callback
from every required target. Failure requires the commit slot and all target
slots to have been counted, with at least one failed target. Timeout wins
only while a slot remains. The model checks the atomic winner and abstracts
the subsequent delivery of the client callback.

In stateless coordination, `Publication.handlePublishResponse` invokes
`onCommit` once quorum returns a future, which can still be waiting for
`StatelessElectionStrategy.beforeCommit`. The apply-commit send waits for that
future to succeed. An early countdown can contribute to timeout. Task success
also requires the publisher's successful application callback, which needs
the fenced commit request. `coupled_stateless_task_success` checks this
implication in an interleaved task and coordination execution.
`stock_task_success` identifies one reachable dynamic execution containing
the requested quorum commit and a committed descendant for each required
target's acknowledgement.

#### Default-strategy application paths

[Default_Application.thy](Default_Application.thy) projects the voting
and observer paths to per-node applier traces. A successful publish or
apply-commit handler uses the authenticated traffic for that recipient.
The voting-node projection also follows successful term changes and
synchronous recovery. An interrupted write resets the restarting
process to the selected durable image and discards its pending local
applications. Async and in-memory observers follow their own recovery
rules.

`Coordinator.handleApplyCommit` offers the accepted key before
responding or scheduling work. A remote node queues its application in
that handler. On the publisher, the self reply completes
`localNodeAckEvent`, and `CoordinatorPublication.onCompletion` uses
that event to queue the publisher's application. Only success of that
application can produce the publisher's task acknowledgement.
`ClusterApplierService.runTask` samples the live supplier on its single
worker. The proof allows success on the same state reference as well as
installation of a newer committed state. A reply records the request
and its sampled key in the sending incarnation. Delivery may be later.

`stock_applier_projection` derives every per-node applier trace from
these handler, restart, and worker transitions.
`production_stock_task_success` uses those derived traces to discharge
the premises of `stock_task_success`. The listener is bound to its
registered publication and can consume only evidence available at
each callback. The Java correspondence is at the production call
boundaries and was checked by source inspection.

### Assumption review

| Top-level result | Scope and remaining interface |
| --- | --- |
| Fixed and dynamic ancestry, publication uniqueness, and election uniqueness | The reachability definitions include a common bootstrap, majority quorums, and the protocol's message and restart rules. The dynamic results use majorities of both configurations where the protocol requires them and allow disjoint configurations. The configured bootstrap mapping requires unambiguous node names and consistent bootstrap configurations wherever present. |
| Stock execution and publication parent | The explicit role-separation premise keeps asynchronous and in-memory observers outside the voting participant set. Roles are fixed across restart. The transitions require the stock executor family, one batch per publishing node, an admitted publisher and payload, and valid configuration domains. They inherit synchronous durability for voting nodes, the authenticated transport and codec boundary, and the Coordinator publication lifecycle. The common projection gives a reachable translated state. The per-registration result gives the actual captured parent separately. |
| Stateless node and task acknowledgement | The execution relation encapsulates storage and grant provenance. The provider projection assumes a common namespace, a monotonic whole-object lease register with the successful-callback floor, and faithful visibility and decoding of complete manifests. Recovery uses a single data path, a serialized writer for the term, fresh manifest names, and the documented one-response backlog bound. Term and version counters stay within their production ranges. The cloud scope is conditional-write S3, GCS, and primary Azure. The test `fs` repository is excluded. A successful recovery read is conditional on its storage premises and can fail. Authenticated send and recipient-incarnation routing are transition conditions. |
| Task countdown and stock task success | The source correspondence assumes distinct publication targets, stable `mustAck` decisions, a publisher in the target set, at most one callback per slot, and a count within Java's signed integer range. The production theorem derives each required applier trace from the combined execution. It inherits authenticated transport, request-handler correlation, fixed roles, and serialized applier work. |

The top-level theorems quantify over Isabelle execution relations. The
correspondence with the production call sites was checked by source inspection.
The proofs in this document concern safety. They leave progress, callback
delivery, and the identity of the exception forwarded on task failure outside
the guarantee. [LIVENESS.md](LIVENESS.md) describes the liveness statement, the
proof plan, and the liveness theories checked so far, which are still a work
in progress.
