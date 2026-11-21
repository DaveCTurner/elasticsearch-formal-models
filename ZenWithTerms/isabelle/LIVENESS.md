# Liveness of cluster coordination

These notes propose a liveness statement and a proof plan for the default
election strategy and stateless coordination. The existing Isabelle theorems
establish safety for reachable executions. Liveness will also need assumptions
about which actions eventually run, which operations complete, and how much
time an attempt has to finish.

## Proposed statement

Consider a cluster starting from configured startup or recovering after a
failure, with publication work pending. Suppose it eventually has a stable
set of healthy processes that can discover one another, exchange the needed
messages, persist state, and run their coordination and applier work. For the
default strategy, the healthy set must supply the majorities needed by the
configurations used in bootstrap, election, and publication. For stateless
coordination, a healthy eligible candidate must be able to reach the shared
lease register and recover, write, and read back the cluster state it needs.
Other nodes may crash, remain silent, or leave RPCs and writes pending
indefinitely, including writes that take effect without reporting completion.

An existing leader can take the steady-state path if it stays in office,
retains the required quorum, and its publication and applier work receives
fair service. While valid publication work remains pending and the healthy
participants can still make progress, show that eventually either an update
commits or an eligible node starts or resumes discovery and gets far enough
to attempt an election. This obligation must hold again after each failed
attempt if publication remains stalled. It also applies when a leader
continues sending heartbeats but cannot publish.

Given these retry opportunities, assume there is eventually a quiet window
in which one eligible candidate starts an election. A quiet window has the
following properties.

- The candidate can discover a quorum whose accepted states are no fresher
  than its own in the default strategy. Any leader observations that would
  cause those participants to refuse pre-votes have expired.
- The required RPCs, storage operations, and local callbacks get enough
  service to finish within the window and their deadlines.
- No competing action supersedes the attempt before the first publication
  can finish. This covers late higher-term messages, competing lease claims,
  and local retries that could cancel the attempt. Ordinary traffic may
  continue.
- Progress-critical resources are available to the healthy path, including
  when operations started before the window are still pending.

Under these conditions, derive progress from startup through bootstrap
when needed. Then show that a healthy leader completes a pending update or
the candidate wins, commits its election-completion publication, and applies
it locally. If the leader and the required participants stay healthy, valid
updates that reach the head of the publication queue eventually commit and
are applied locally. A task acknowledgement can additionally depend on
targets outside the publication quorum and can time out while the update
still commits.

The deterministic statement is conditional on a usable quiet window. A
separate scheduling result would show when such windows eventually occur with
probability one. This is where the proposed result goes beyond fully
asynchronous scheduling in [Fischer, Lynch, and Paterson](https://groups.csail.mit.edu/tds/papers/Lynch/jacm85.pdf).

## Failure detection and failover policy

Use the same election and publication proof for both policies. Let a policy
report a suspected failure, schedule a follower removal, cancel a publication,
or permit discovery and pre-voting for a replacement. Model the effect on
Coordinator separately from the evidence that led to it. In particular,
suspecting a leader, freeing a publication slot, and enabling a replacement
election are distinct events. Follower removal still goes through the normal
publication and voting-configuration rules.

The shared liveness argument needs two properties at this interface.

- **Recovery opportunities.** Under each policy's stated health, timing, and
  resource assumptions, a continuing stall leads either to a commit or to an
  eligible candidate that can reach an election attempt. Failed attempts
  leave another opportunity while the stall persists. Starting discovery
  alone is insufficient if the needed voters still refuse pre-votes because
  they recognise the incumbent.
- **Time to finish.** The scheduling argument needs opportunities in which
  policy actions and delayed callbacks leave a healthy attempt enough time
  to complete its first publication. This includes cancellations, candidate
  transitions, term advances, and membership changes that affect its quorum.
  The shared proof can make this a condition of a quiet window. Each policy
  must account for it when deriving that such windows occur.

Check those properties for each policy:

- **Current implementation.** Follow `LeaderChecker` into the candidate
  transition, `FollowersChecker` and `LagDetector` into follower removal,
  and `cluster.publish.timeout` into publication cancellation and whatever
  then frees the slot or changes leadership. Determine which paths still run
  while a leader is answering heartbeats but has stalled in publication.
  Determine when slow healthy work can be cancelled, including a slow first
  publication. A timeout scheduled on an executor or behind a mutex held by
  stuck work needs its own progress argument.
- **Quorum-backed failover.** Study a policy inspired by
  [issue #80400](https://github.com/elastic/elasticsearch/issues/80400),
  which discusses moving the publication timeout to start at commit and
  cases where another leader could serve a faster reachable quorum. For
  this variant, define the evidence by which an alternative healthy quorum
  agrees that failover is appropriate. Specify which configurations count,
  how evidence is tied to the incumbent and term, and when old evidence
  expires. Show that the evidence can be collected and acted on while the
  incumbent still sends heartbeats or has an indefinitely stalled write.
  In particular, check whether incumbent pre-vote suppression, a blocked
  resource, or a dependency on a publication by the incumbent can prevent
  collecting or using the evidence. The failover agreement authorises an
  attempt. The candidate still needs the ordinary election and publication
  quorums or the stateless lease and storage conditions.

If one policy fails to provide either property for some execution, record
that execution and the narrower conditions under which that policy supplies
the interface. The shared quiet-window argument can still apply to the
other policy.

## Proof plan

Each milestone has its own stopping point. The fixed-configuration milestones
start from an already bootstrapped cluster. A later milestone supplies that
starting condition from startup.

### One attempt in a fixed configuration

1. **Specify the starting state and progress conditions.** Use an arbitrary
   fixed voting configuration and one pending update. Specify the events
   that count as progress and the deadlines and resources needed in the
   window. The progress theorems should cover every execution satisfying the
   stated window and service conditions.

2. **An eligible candidate wins.** Start with a candidate that has discovered
   a quorum. Given timely service and an accepted state fresh enough for
   that quorum, derive the pre-votes, term selection, durable joins, and
   election. Stop at the election win. Failure detection and randomized
   retries supply starting conditions in later milestones.

3. **The winner commits its first publication.** Start at the election win
   and follow registration, quorum acceptance, and the commit notification.
   Stop at quorum commit. State the publication deadline and which writes
   and replies must complete.

4. **The publisher applies the commit and frees its slot.** Follow the
   leader's local apply-commit and application callback. Check whether a wait
   on a non-quorum target can delay slot release after the commit. Then show
   that an established leader with a free slot can service the next admitted
   update under the same health and scheduling conditions. Task
   acknowledgement has a separate stopping point if it waits for additional
   targets.

### Recovery and retry

5. **Trace individual failure signals and stalls.** For the current policy,
   follow one leader check failure, one follower check failure, one lag
   report, and one publication timeout through their Coordinator effects.
   For each, record what is cancelled, which resources are released, and
   what can still arrive late. Check a stalled RPC, a hung receiver-side
   handler, and a write that takes effect without a reply. Include work
   already pending when a candidate starts. Audit the Coordinator mutex,
   publication slot, applier, executor threads, and storage resources.
   A minimal stuck execution is a useful milestone result if it identifies
   an additional completion or isolation condition.

6. **Get from a stall to another attempt.** Start with a leader that still
   answers heartbeats but cannot publish. Under the conditions found in the
   audit, show a commit or an eligible candidate reaching an election
   attempt. Then check one failed attempt and show what enables the next.
   Use those steps to establish repeated opportunities while valid work
   remains pending. For quorum-backed failover, first specify the evidence
   and its term and configuration boundaries, then check the same recovery
   obligation. The quorum-backed policy can be studied independently after
   the shared interface is specified.

7. **Establish that one usable window is possible.** For the production
   timers, capped backoff, and pre-vote rounds, account for existing retry
   phases and earlier work. Find conditions under which one candidate can
   finish the path above before any competing action can supersede it.
   This establishes what the scheduler has to provide in a single
   opportunity.

8. **Turn repeated opportunities into eventual quiet.** Check that chances
   of success do not become too small after earlier failures. A uniform
   positive lower bound conditional on the past would suffice. If production
   timing gives a weaker bound, determine whether it still makes the
   probability of remaining stalled tend to zero. Use the recovered retry
   opportunities and the resource conditions from the stall audit.

### Broader starting states and strategies

9. **Reach the election starting condition from configured startup.** Split
   this into discovery of a healthy configured majority, eligibility to
   bootstrap, durable installation, and entry to pre-voting. Check delayed
   peers and bootstrap retries. [Bootstrap_Agreement.thy](Bootstrap_Agreement.thy)
   establishes initial quorum intersection under its roster and identity
   assumptions, including when views produce different placeholders.
   Identify the extra condition needed for equal installed configurations
   in the current dynamic refinement, or the refinement change needed to
   support differing views. Examine unconfigured bootstrap separately.

10. **Extend the single-window argument one strategy at a time.** For dynamic
    reconfiguration, identify the committed, accepted, and proposed
    configurations used at each stage and the healthy majority each
    requires. For stateless coordination, check lease acquisition and
    recovery-base selection first, then the manifest write and commit fence.
    Include incomplete listings, unreadable images, and contending storage
    operations whose effects outlive their callers. Reuse the retry argument
    once the corresponding window and failure-policy obligations have been
    established.

### Follow-up milestones

11. **Close the stateless publication slot after local application.** Extend
    the stateless projection with Coordinator's current publication identity
    and completion callbacks. Follow the fenced apply-commit request through
    the self reply, target completion or cancellation, and the local applier.
    Prove that a serviced successful application callback clears the matching
    slot. Include the work before the mutex acquisition in that callback.
    Check fence and application failures separately, and show that a delayed
    callback from an older attempt cannot clear a newer slot.

12. **Publish the next stateless update.** Use slot release as the handoff to
    the next admitted update in the same term. Derive manifest installation,
    fence approval, local application, and another slot release from the
    existing approved history and continued lease ownership. Check when a
    newer lease or failed completion turns this into the recovery path.

13. **Connect production work to the service bounds.** For the fixed,
    dynamic, and stateless windows, identify the actual RPC, durable write,
    executor task, or callback that supplies each scheduled operation.
    Derive that enabled work is eventually dispatched and completed under
    explicit resource and timing assumptions. Include work queued before
    the window, shutdown or rejection where relevant, and stale callbacks.
    Use this correspondence to transfer progress from the projected
    schedule to every production execution satisfying those conditions.

14. **Derive retries from the failure-handling paths.** Replace the recurring
    recovery-episode premise wherever the current detector and Coordinator
    paths can supply it. Start with one serviced failure notification and
    show which eligible voters resume pre-voting and what enables a further
    attempt. For the proposed quorum-backed alternative, specify how the
    reports are obtained and how they permit pre-voting while the incumbent
    still answers checks. Identify what can be serviced independently of a
    hung incumbent, and retain the stalled-write counterexample for paths
    that depend on its resources.

15. **Check timer phases before assigning probabilities.** Starting from
    the timers and callbacks already armed after a failed attempt, identify
    when production can reach a point where the remaining draws can open a
    usable window. Include the candidate's own next retry and deadlines
    already running. Then state a stochastic execution model and derive a
    conditional chance of success at those points, or state which timer,
    scheduling, or service assumptions are needed for that bound. The Java
    jitter range supplies possible delays. A probability claim also needs
    a model of which delays and service outcomes occur after earlier failures.

16. **Weaken the configured bootstrap handoff.** Start with a live majority
    and a common installed configuration that can still contain inert
    placeholders. Carry it into the first election without counting
    placeholders as voters. Then check what progress is possible when
    captured configurations differ or when an earlier captured quorum
    loses members. Treat unconfigured best-effort startup separately,
    including whether separate initial clusters can converge.

17. **Allow stateless recovery across changing storage views.** Replace the
    stable-view premise with conditions on each complete listing and the
    subsequent file reads. Reuse the retention and ancestry results for
    safety, then identify what guarantees a successful read or another
    usable opportunity after an abort. Include cleanup between reads and
    lease effects that complete after their callers time out.

18. **State task acknowledgement progress separately.** For a committed
    publication, derive task success when the commit bookkeeping and all
    required successful application acknowledgements are serviced before
    any acknowledgement deadline. Check when failure or timeout wins if
    some targets fail or never respond. Include delivery of the terminal
    callback and distinguish the acknowledgement deadline from the
    publication deadline.

### End-to-end progress milestones

19. **Compose stateless recovery with the next publication.** Carry the
    publication identity, process incarnation, and lease term through one
    trace from changing-view recovery to the fenced commit, local
    application, slot release, and admission of the next update. Check the
    handoff at the point where Coordinator finishes processing any deferred
    term change. A fresh grant or a failed callback should lead back into
    recovery with the right state. This would connect the existing results
    at their actual handoff states.

20. **Derive callback identity from the publication object's lifetime.**
    Model the Java rules for creating a publication, choosing a single
    completion, finishing the self-response future, and clearing the slot.
    Show that every callback that can reach a slot clear still owns that
    slot. Include cancellation, step-down, and a callback queued before
    retirement. This discharges the projected stale-input guard using the
    production lifetime rules, including when Java assertions are disabled.

21. **Give a progress guarantee for a submitted MasterService task.** Start
    before admission, with a task in its queue. Show what makes the task
    reach a batch and what happens if leadership changes before it can
    publish. Distinguish successful completion, rejection with a delivered
    result, and retry by a caller that supports it. Check starvation under
    sustained higher-priority work, and state any fairness or load premise
    needed to guarantee service of the original task.

22. **Derive reachable timer cuts from a bounded production schedule.**
    Start from post-failure timer and callback states that the Java
    lifecycle can actually reach. Use executor capacity, mutex ownership,
    timer cancellation, and service bounds to show when a usable cut
    recurs. In particular, distinguish a queued callback that can still
    be suppressed from one that has already entered and must drain. If
    legal scheduling can defeat recurrence even under the proposed bounds,
    give a small counterexecution and identify the extra condition or
    scheduler change that would rule it out. Apply the existing probability
    result once this recurrence condition is available.

23. **Carry differing configured bootstrap views through the first commit.**
    Use the shared roster and real-voter intersection to identify which
    mismatched placeholder configurations can support an election and
    accept the winning publication. Check when the first committed state
    gives the participants a common configuration that the ordinary
    dynamic proof can take over. If crossing that boundary requires a new
    safety invariant, prove it before claiming progress for those views.

24. **Check a concrete quorum-backed failover protocol.** Specify how current
    participants measure lack of publication progress, exchange evidence,
    expire it, and permit pre-voting. Prove that evidence collection and the
    replacement attempt can run without the incumbent's mutex or a
    publication by the incumbent. Check stale evidence and changes to the
    voting configuration while reports are outstanding. Show that the new
    authorization only opens an attempt and preserves the existing election,
    storage, and publication safety checks.

### Remaining production and composition milestones

25. **Close the two exceptional callback paths.** Extend the lifetime proof
    to cover failures during construction and after the applier has reported
    success. Check the Java exception and executor rules for both paths. Where
    those rules allow an unsafe trace, specify a fix and verify it with Java
    assertions disabled.

    - `CoordinatorPublication` schedules its cancellation timeout before its
      informational timeout. If the second schedule throws, the first
      callback may still run for an object that was never installed. Check
      rejection, shutdown, and callbacks already queued or waiting for the
      mutex. Prove that such a callback cannot complete the publication,
      clear another object's slot, or drive a mode change. Test cancellation
      after partial construction and an ownership check under the mutex.
    - The changed-state branch in `ClusterApplierService` can run timing and
      logging after `onResponse` within the same `try` that calls `onFailure`
      on an exception. Check which calls can throw after success delivery. If
      needed, separate application failure from trailing bookkeeping or make
      result delivery one-shot at the callback boundary. Check that success
      followed by an exception cannot clear twice, change leadership, or
      turn an installed state into a reported failure.

26. **Check worker and listener handoff under shutdown and leadership loss.**
    Connect Coordinator slot release and publication-listener delivery to the
    next MasterService queue round. Check the two shutdown paths that can
    release the worker without a task result. Decide what result callers can
    rely on while the process stays up, and verify either terminal delivery
    or an explicit lifecycle exclusion. Keep caller retries distinct from
    the original task and state the load and service conditions for each.

27. **Isolate stalled operations from the healthy path.** Trace the mutex,
    executor slots, transport handlers, and storage clients used by discovery,
    failover reports, lease acquisition, and local application. For a request
    or write that never replies, check what the timeout frees, what can still
    take effect, and whether new attempts can use an independent path. Derive
    the bounded service premises where the source permits it. Record a
    blocking execution or the required implementation change where a faulty
    operation can indefinitely hold a shared resource.

28. **Supply recurring quiet windows without requiring peer-quorum flaps.**
    Check how a healthy, continuously open scheduler can desynchronise across
    failed attempts. Use the actual jitter ranges and retry generations,
    publication deadlines, and bounds on queued and entered work. Show a
    recurring usable cut and a positive conditional lower bound for success
    given prior failures, or identify the extra scheduling assumption or
    change needed. Compose this with the policy's repeated commit-or-retry
    obligation, including an incumbent that still answers heartbeats.

29. **Carry concurrent configured startup through the dynamic handoff.**
    Extend the isolated first-round result to retries, overlapping attempts,
    and states with earlier accepted but uncommitted publications. Check
    whether lagging nodes with different initial captures can catch up using
    ordinary delivery or restart paths. If some can remain offline or stale,
    prove a handoff invariant that admits them and constrains their later
    votes, or state the coverage premise that production must supply.

30. **Bind the proposed failover protocol to a concrete stateful path.**
    Specify how voters observe pending work and commit progress, how they
    authenticate reports, how the candidate measures expiry on its own clock,
    and what invalidates a generation across view changes and restarts. Check
    which executors serve the round and where authorization overrides only
    incumbent recognition in pre-vote. Compose the resulting attempt with
    ordinary freshness checks, joint quorums, and the first-publication proof.
    Check renewal after a failed round and that competing or stale rounds
    leave a healthy attempt enough time to finish.

31. **Define who can authorize a stateless replacement attempt.** The
    stateless election uses a self-vote and a shared lease register, so the
    stateful joint-majority rule gives no independent quorum here. Define an
    evidence group separate from the singleton voting configuration, including
    who is eligible, how its membership is learned and changed while
    publication is stalled, and what healthy subset can authorize a round.
    Bind authenticated evidence to the cluster, incumbent and observed lease
    term, candidate, membership view, and a fresh expiring round. Specify
    how observers distinguish an absence of new fenced commits from delayed
    local application. Decide whether evidence only opens an additional
    attempt or gates ordinary claims too. A gate also needs a progress path
    during startup, membership loss, and evidence-service outages.

32. **Verify stateless authorization through lease claim and publication.**
    Connect a fresh authorization to the existing `StatelessElectionStrategy`
    claim path. Check revalidation when the observed lease or evidence view
    changes, especially across the gap between authorization and the actual
    compare-and-set. Keep the lease register as the authority for acquiring a
    term and retain the exact-term `beforeCommit` fence. Cover competing claims,
    late successful writes after caller timeout, restart, and an incumbent
    stalled in storage while still answering heartbeats. Prove that authorized
    attempts preserve the existing storage and publication invariants, then
    derive progress through lease acquisition, manifest recovery, fenced commit,
    local application, and slot release under independent evidence and storage
    service. Include retry after a failed claim or expired round, and check that
    repeated authorization cannot keep superseding healthy attempts.

33. **Compose the top-level liveness result.** Use the policy interface to
    connect configured startup or a stalled incumbent to recurring attempts,
    then to the first commit, local installation, and resumed publication.
    Connect queue admission and task-result delivery where the theorem starts
    from a submitted task, spelling out which retries belong to the caller.
    Audit the resulting premises against production, distinguishing interface
    guarantees, deployment and workload conditions, and the timing or
    probability assumptions that remain explicit.

    The default strategy with a fixed configuration is composed in
    `Liveness_Composition`. The remaining policies, strategies and links are
    listed under Composed results.

## Checked results

### Fixed configuration

[Bounded_Service.thy](Bounded_Service.thy) models a scheduler that selects
an operation or idles at each tick. It proves that prerequisites and
bounded service of enabled work suffice to complete a finite dependency
plan. Service is a bound on selection of enabled operations in the
projection. Mapping that service bound to production requires timely
completion of the corresponding work.

[Fixed_Window_Liveness.thy](Fixed_Window_Liveness.thy) projects the
scheduled operations to the existing fixed-configuration and local
application relations. For a per-operation service bound of `B` ticks
and a quiet window of adequate length, it derives election by `4B`,
first quorum commit by `7B`, and local installation and slot release by
`12B`. The incumbent path gives quorum commit by `3B` and local
completion by `8B`. The handoff theorem exposes the accepted leader
state for the next admitted publication.

The service bounds apply to the selected quorums, eligible candidate,
compatible term and accepted state, and an isolated publication attempt.
After quorum commit, local completion still requires the publisher's
self reply and local application callback, plus terminal targets or a
post-commit cancellation that ends the target wait. The tick bounds
depend on the service premises for those operations. They give no
production deadline in milliseconds by themselves.

### Failure detection and retry opportunities

[Recovery_Liveness.thy](Recovery_Liveness.thy) separates detector
signals from serviced Coordinator callbacks. Follower and lag reports
queue removal work. A serviced current pre-commit deadline can free the
slot and move the leader to candidate. After quorum, cancellation still
depends on the local completion path to free the slot.

`stalled_write_blocks_current_replacement` exhibits a persistent stall
in the callback model. A write holds the incumbent's Coordinator mutex,
so the timeout cannot run its state change. The incumbent can still
answer direct leader checks using the last completed filesystem health
result. Voters that still recognise it can reject a replacement's
pre-votes. This rules out a progress guarantee from responsive peers and
publication timeout alone in that model.

For the proposed default-strategy alternative, the theory checks a
round-bound certificate of unexpired reports from healthy majorities in
the accepted and committed configurations, excluding the incumbent.
Collection needs independent service and affirmative reports. Such a
certificate allows an attempt even while voters still remember the
incumbent. Election freshness, votes, and publication still have their
own checks. Applying the same idea to stateless coordination would
require a separate interface to its lease and singleton voting rule.

For either policy, a permitted recovery episode with bounded service
starts an attempt within three service bounds. Repeated opportunities
follow if such episodes remain available after every stalled suffix.
The episode premise requires candidate eligibility, fresh votes,
successful callback service, and policy permission that lasts through
the episode. The callback counterexample is a case where the existing
detectors cannot ensure that premise.

### Retry timing and probability

[Scheduler_Liveness.thy](Scheduler_Liveness.thy) checks the capped retry
delay and the range of the Java jitter calculation, within the signed
arithmetic range. A sufficient opportunity has a candidate whose timer
can draw an early delay, competing fresh timers whose latest draws are
late enough, and already-armed disruptive timers whose earliest service
is past the deadline. Earlier disruptive work must have drained. An
already-armed timer can rule out such a window even if all fresh draws
are favourable.

`recovered_timer_window_completes` combines this timing condition with
a serviced recovery episode and the fixed publication model. The window
budget is three recovery service bounds plus twelve publication service
bounds. The handoff budgets for processing the pre-vote evidence already
obtained by recovery.

`retry_observation_bound_tends_to_zero` derives convergence when serviced
opportunities recur and the conditional probability of each required
observation stays bounded below after earlier failures and observations.
This covers a bounded finite list of timer draws and dispatch or service
observations. It uses no independence premise. Actual phase alignment,
service, and the required distribution of observations still need to be
established for a production deployment and its scheduler.

### Configured startup

[Bootstrap_Liveness.thy](Bootstrap_Liveness.thy) models discovery,
capture of a configured bootstrap attempt, the installer's current peer
check, the durable write, and entry to pre-voting. With bounded service
and a live quorum of the captured configuration, entry takes at most
five service bounds for a fresh capture and four for a retry of an
existing capture. A retry retains the same configuration. Replacing
one of the originally discovered peers can block it even if the new
view still contains a majority of the configured roster.

`configured_startup_to_fixed_election` supplies a sufficient handoff
from fresh startup. When the candidate and the healthy voters capture
the fully resolved common roster, the actual voters form a majority
in that configuration and the next separately serviced fixed window
elects the candidate. Startup and election each have their own service
and quiet conditions. General progress with differing installed
placeholder configurations and convergence from unconfigured
best-effort bootstrap remain outside this result.

### Dynamic reconfiguration

[Dynamic_Window_Liveness.thy](Dynamic_Window_Liveness.thy) projects
the scheduled work to the existing dynamic coordination and application
relations. It derives election by `4B`, quorum commit by `7B`, and
local installation and slot release by `12B` in an isolated window.
Separate sets of participants supply the joint election quorums, fresh
joins authorising the proposed configuration, and the joint publication
quorums. The proof allows disjoint previous and proposed configurations
when those quorums and the reconfiguration guard hold. Local completion
uses the same target-wait conditions as the fixed-configuration proof.
`recovered_dynamic_window_completes` uses the common timer and recovery
interface and ties the episode's voting configurations to the candidate's
actual accepted and committed configurations in the dynamic window.

### Stateless coordination

[Stateless_Window_Liveness.thy](Stateless_Window_Liveness.thy) checks a
single-incarnation attempt from a lease claim through a descending
manifest scan, recovery-base selection, the first publication, and
the exact lease-term fence. The lease effect and confirmation callback
are separate. The fence needs the granted term to remain current even
if a competing CAS could change it without returning success.

Starting from a valid lease effect, the theorem constructs a timed
stateless execution under bounded service of successive operations.
It reaches a fenced commit notification, local installation, and a
matching node acknowledgement within `(18 + max 1 (t - 1)) * B` ticks,
where `t` is the granted term and `B` is the service bound. The term
factor bounds the number of descending directory probes. The successful
path requires stable complete listings, readable recovery data, synced
manifest files, successful callbacks, and service of the target wait
and local applier. This execution reaches the node acknowledgement.
The Coordinator callback projection below handles publication-slot release.
`stateless_timer_window_completes` fits the same attempt inside the common
timer window, from a candidate ready to claim the lease at its wakeup.

### Follow-up results

[Stateless_Slot_Liveness.thy](Stateless_Slot_Liveness.thy) checks the
publication object through quorum bookkeeping, fencing, self reply,
target completion, and local application. A serviced successful
application callback clears the matching slot in three service bounds.
Those bounds cover reporting the local result, completing the
application hook and timing work, and acquiring the mutex for the clear.
The theory also checks failed fencing, failed application, and the
identity of a retired slot. Stale input stutters at the projected
dispatch boundary. The source correspondence relies on each publication
object's lifetime and one-shot callbacks.

[Stateless_Next_Publication.thy](Stateless_Next_Publication.thy) uses
slot release and continued leadership to start another admitted
publication from the latest accepted and approved state. With the
same live lease, healthy operation service bounded by `B`, and
completion callback service bounded by `C`, its modeled execution
fences the new commit, applies it locally, and releases the slot
within `16B + 3C` ticks. A higher live lease prevents the old exact
fence even when the higher term's claim callback has not succeeded.
A serviced current-term fence failure releases the slot and enters
candidate mode, leaving the subsequent election to the recovery proof.

[Production_Window_Service.thy](Production_Window_Service.thy) derives
the work-service bound from separate enqueue, dispatch, and successful
completion bounds. The projection matches successful callbacks by
generation and checks their causal order, including work queued before
the window. Fixed and dynamic progress transfer to every trace that
satisfies the local source-effect and service contracts. For stateless
coordination, the proof supplies an ordered path and transfers progress
to traces that project to that path. The contracts retain the effects
of the underlying source operations and their timing and resource
requirements as premises.

[Production_Recovery_Retries.thy](Production_Recovery_Retries.thy)
derives recurring attempt times from scheduler arming and rearming.
For the current policy, serviced leader failure callbacks clear the
blocking incumbent observations on the required healthy voters. For
the proposed policy, independently serviced reports provide fresh
authority even while voters still remember the incumbent. Both paths
need a visible quorum, continuing candidate eligibility, and bounded
service of the relevant callbacks. The proposed policy also needs
affirmative observations from those voters and a pre-vote override.
The stalled-write counterexample remains a case where the current
policy can fail to make these conditions hold.

[Production_Timer_Liveness.thy](Production_Timer_Liveness.thy)
checks a post-failure timer cut against still-armed callbacks,
uncancelled publication deadlines, earlier work that must drain,
and the candidate's own next retry. The capped-backoff result gives a
sufficient timing inequality, and a retained deadline can make the
window infeasible. The finite stochastic model derives a positive
conditional success probability from support for each required draw
and service observation. Recurrence of the required timer cut and
the conditional support of production draws and service remain
deployment and scheduler obligations.

[Bootstrap_Placeholder_Liveness.thy](Bootstrap_Placeholder_Liveness.thy)
extends the configured startup handoff to aligned partial views. It
preserves real node IDs, represents placeholders as distinct inert
members, and uses only real healthy voters in the election majority.
Differing installed configurations can have intersecting initial
quorums while preserving their different placeholder assignments.
An obsolete captured quorum can still block a retry. The theory also
checks that disjoint best-effort views can each produce a first commit
and that distinct persisted cluster UUIDs rule out merging them through
ordinary join, publication, and restart paths.

[Stateless_Changing_View_Liveness.thy](Stateless_Changing_View_Liveness.thy)
uses independent complete responses for descending term probes and a
separate read of the chosen recovery image. The interval between the
scan and that read can include cleanup. The proof preserves the
approved frontier and reaches a fenced commit and local acceptance
when the selected image is readable and the lease still permits the
final publication. A failed download cannot supply the election base.
A later successful CAS and callback can establish a new grant above
an intervening lease write whose caller did not observe success.
Storage availability, executor wakeup, and service of that later attempt
remain premises.

[Task_Ack_Liveness.thy](Task_Ack_Liveness.thy) proves delivery of the
task result once serviced callbacks finish the countdown or the
timeout wins. Timely successful callbacks give success, and a counted
failed target gives failure if counting completes before the timeout.
A missing target can lead to timeout once the deadline callback gets
service. If the allowance has already expired at commit bookkeeping,
that callback can trigger timeout immediately. A disabled timeout
allows a missing acknowledgement to remain pending. The task timer
uses the allowance remaining at `onCommit`, and its eligible dispatch
time and listener delivery have separate service conditions.

### End-to-end results

[Stateless_Recovery_Handoff.thy](Stateless_Recovery_Handoff.thy)
composes recovery from changing views with a fenced publication, matching
local application, release of that publication's slot, and a strictly
newer descendant publication in the same trace. The handoff includes
the deferred leadership check under the Coordinator mutex and service
of the previous publication listener. A higher observed term, a higher
live reservation, or failed completion can force a new attempt. The
retry path carries the accepted warm state into a search under a fresh
grant, using the observed term as a lower bound on the new proposal.
Reads, writes, fencing, callback service, and the successor's admission
retain their own progress premises.

[Publication_Callback_Identity.thy](Publication_Callback_Identity.thy)
derives slot ownership at a clear from the publication object's lifetime.
In the projected Coordinator instance, installation requires an empty
slot, completion chooses one outcome, and the self-response future and
applier callback are serviced once. Cancellation and step-down preserve
ownership until completion. These rules give the match required by the
slot projection even with Java assertions disabled. The source mapping
covers normal in-service construction and callback completion. It leaves
two exceptional paths open: a timeout escaping a failed publication
constructor, and applier bookkeeping throwing after reporting success.

[Master_Service_Queue_Liveness.thy](Master_Service_Queue_Liveness.thy)
starts with a submitted task. The delivery bound includes registration
of the FIFO prefix, service of preceding batches and bounded
higher-priority work, batch completion, and listener invocation. The
proof checks starvation with sustained higher-priority work, queue
timeout without dispatch, ordinary leadership-loss notification, and
retry as a fresh attempt by the caller. Two local shutdown paths can
release the worker while omitting the task result. The bounded
delivery guarantee excludes those paths.

[Production_Timer_Cut_Recurrence.thy](Production_Timer_Cut_Recurrence.thy)
derives recurring usable timer opportunities from serviced peer-quorum
loss and restore episodes. The projection tracks the single worker,
older entered work that must drain, queued old-generation work that can
be suppressed, and retained publication deadlines. A fresh scheduler
uses the initial retry range. The proof checks an overlapping schedule
with continuously open timers and immediate dispatch, so worker service
alone cannot establish a quiet cut. The probabilistic result uses
recurring bounded reset episodes, successful healthy-path service, and
conditional support for the required observations.

[Bootstrap_First_Commit.thy](Bootstrap_First_Commit.thy)
checks a first publication from differing configured views on a shared
roster. The durable vote fence and intersection of real voters rule out
two initial winners in a term. Recorded receipts from an initial quorum
also rule out a later election on the empty history. In the isolated
first round, the winner needs election and receipt quorums in both its
initial and proposed voting configurations. Its endpoint can enter the
ordinary dynamic model seeded with the winner's initial configuration
exactly when every node with a different initial view has accepted the
publication. Acceptance copies the carried configuration before commit
application. A quorum commit alone can leave nodes outside that handoff.
The Java guard checks also require compatible initial state versions and
successful Coordinator validation and delivery.

[Production_Quorum_Failover.thy](Production_Quorum_Failover.thy)
checks a proposed protocol for quorum-backed pre-vote. Voters report
continued pending work and an unchanged committed rank in the incumbent's
term. The candidate rechecks a healthy quorum in both voting configurations
at authorization and again when opening pre-vote. Reports expire and are
bound to the full view, including the round generation. Given a stable
view, fresh samples, and independent service bounded by `B` per stage,
the trace authorizes by `2 * B` and opens pre-vote by `3 * B` without
incumbent dispatch. Policy steps leave the existing protocol state
unchanged, so ordinary election and publication safety still apply. The
model leaves authenticated report exchange, observation and expiry
implementation, and the separate stateless lease path as obligations.

### Production and composition results

[Publication_Exceptional_Callbacks.thy](Publication_Exceptional_Callbacks.thy)
checks both exceptional callback paths against the hardened Java control
flow. Coordinator only runs the cancellation callback for the publication
that owns the slot under its mutex, and cancels the first timer handle if
scheduling the informational timer throws. The ownership check also covers
an escaped timer when handle cancellation loses the race. The cluster
applier now delivers success outside the application-failure catch while
retaining the applying-state cleanup. A later bookkeeping exception emits
no second result and leaves the callback projection unchanged. The proof
checks the effect of an exception if it occurs. Service of the first
callback and the effects of a failed application remain separate contracts.

[Worker_Listener_Handoff.thy](Worker_Listener_Handoff.thy) follows a matching
slot clear through deferred work, publication-listener dispatch, task-result
delivery or a classified omission, and the next queue decision within `6B`.
The bound assumes service of those callbacks and worker dispatch. Executing
the next processor requires the queue service assumptions as well. A stopped
queue after claim or an explicit publication-listener shutdown rejection can
release the worker while dropping the result. An applier that silently
declines the callback can leave both slot and worker held. Ordinary loss of
mastership can deliver a retryable result, and a retry is a separate submission.

[Stalled_Operation_Isolation.thy](Stalled_Operation_Isolation.thy) distinguishes
caller timeout from termination of the underlying operation. It checks that
a timed-out caller cannot free a mutex held by synchronous persistence, that
an abandoned lease claim can still reserve a term, and that a retained
download permit can block subsequent recovery on the same process. Local
lease dispatch can proceed without that permit. Another node's local
resources are independent, but saturation of the shared backend can still
block replacement. Bounded work service follows when causally ready jobs
have capacity and their dispatch, transport, and backend work receive
bounded service.

[Open_Scheduler_Recurrence.thy](Open_Scheduler_Recurrence.thy) finds a legal
quiet-window draw on a continuously open scheduler. A sufficiently large
jitter cap gives more separated choices than pending rival wakes can block.
The proof accounts for older entered work, the candidate's own rearm, and
early rivals' new timers. It requires bounded dispatch and drain, enough
headroom, and retained publication deadlines outside the window. Bounded
rearming gives recurring opportunities without peer-quorum flaps. The
probability bound further assumes sequential conditional support for the
required draws and service observations. The support premise is separate
from the Java random generator's range calculation.

[Concurrent_Bootstrap_Handoff.thy](Concurrent_Bootstrap_Handoff.thy) replays
interleaved initial elections, publications, and restarts into a single-seed
dynamic run when the recorded root certificates and publications agree on
that seed. The replay rewrites only unused local captures on empty histories.
The journal, certificates, and accepted histories are preserved. This
gives the dynamic safety results before all nodes have caught up. The
original state itself enters the ordinary dynamic model exactly when the
historical agreement holds and every node with a different initial view
has accepted some publication. A finite set of lagging nodes can reach that
handoff by accepting a newer committed state if none is ahead of its term.
Incompatible historical evidence remains an obstruction after catch-up.
The source still has to supply compatible historical roots and legitimate
delivery to those nodes.

[Stateful_Failover_Handoff.thy](Stateful_Failover_Handoff.thy) binds the
proposed reports to authenticated senders and a fresh challenge with a
candidate-local deadline. The authority can move an eligible follower that
still recognizes the incumbent into candidate mode. It permits a response
only past the remembered-incumbent check, while health, accepted-state
freshness, ordinary joint quorum, and the final eligibility and term checks
still apply. From entry to a serviced stable window, `StartJoin` starts
before `2B` and the first commit, local application, and slot release follow
by `12B` on the same trace. The report exchange and override are proposed
production interfaces. Causal source effects, a viable quorum, and callback
service remain explicit premises.

[Stateless_Failover_Authority.thy](Stateless_Failover_Authority.thy) defines
an additional route to a stateless attempt. A strict majority of a separately
maintained roster must report on the same cluster, incumbent and candidate
incarnations, lease term, fenced watermark, and fresh round before the
candidate deadline. The candidate and incumbent are excluded from the
reporters. A roster of three containing both cannot authorize a round, so
deployment needs enough independent observers. The normal heartbeat path
remains available. The lease bytes supply a term but no incumbent identity or
fenced watermark. Authenticated cluster and incarnation binding, trusted
fenced observations and pending-work signals, and roster management are
separate contracts. A delayed applied-state watermark alone cannot distinguish
a publication stall from a committed update awaiting application.

[Stateless_Failover_Recovery.thy](Stateless_Failover_Recovery.thy) connects
that authority to a proposed follower or candidate entry that can run
despite a recent heartbeat. At dispatch it revalidates the view and pins the
complete lease snapshot for the compare-and-set. A competing lease change
can reject the write. The attempt cannot rebase to a higher incumbent term
using its old evidence. Expiry, restart, or retirement can make a callback
unusable while a previously dispatched write can still reserve a term. A
fresh round can retry. For a successful pinned claim with bounded service,
the same slot trace reaches changing-view recovery, fenced commit, local
installation, and slot release. Honest matching-term observations can
exclude competing authorized claims during the protected interval. Ordinary
lease claims still need a quiet window, and the authentic observation path,
backend service, and proposed Java entry point remain premises.

### Composed results

[Liveness_Composition.thy](Liveness_Composition.thy) is checked in
the `Zen_With_Terms` session. It composes the stages for the
default strategy and a fixed voting configuration, then extends the chain to the
other strategies, the failover policies, the probability result and the task
queue.

`stalled_timer_window` is the step every chain shares. From any stall, the
serviced reset episode gives a post-failure cut and so a timer window whose
attempt time is after the stall and within the retry bound, the reset slack and
one dispatch delay of it.

`stalled_default_leader_completes` takes that window through a serviced recovery
episode that opens an attempt, then through the fixed window to the first quorum
commit, the publisher's local installation and the slot release. The window
budget is the recovery service bound plus twelve publication service bounds.
Three theorems restate it for other cases.

- `stalled_dynamic_leader_completes` does the same for dynamic reconfiguration.
  It also gives the committed configuration of the new state.
- `stalled_stateless_leader_completes` does the same for stateless coordination,
  up to the fenced commit notification, local installation and the node
  acknowledgement.
- `stalled_stateless_to_next_publication` carries the stateless chain further. After
  the stall's timer window, the candidate claims the lease, searches the changing
  storage view and publishes under the granted term. The slot is released after
  local application, and the same term then publishes a strictly newer descendant
  and releases its slot again. The window budget keeps every rival timer and
  pending deadline outside the whole run.
- `stalled_policy_leader_completes` takes the recovery episode as the policy
  interface, with the policy's own permission condition as a premise. Its two
  instances are `stalled_current_checks_leader_completes`, whose permission comes
  from serviced leader-failure callbacks, and `stalled_quorum_backed_leader_completes`,
  whose permission comes from independently serviced reports of a healthy quorum
  in both configurations.

`stalled_default_task_published` extends the fixed chain through the worker and
listener handoff. If the slot release is seen as the clear event within a stated
lag, the next queue round starts within six handoff service bounds and the task
is delivered as published. `stalled_default_task_delivered_in_queue` replaces
that alignment premise with two more primitive ones. The worker holds the slot,
and the clear callback is the event delivered at the release tick. It then
concludes in the queue's own task machine.

`handoff_queue_projection` proves that the queue's task machine is a projection
of the worker handoff. Prefixing the acquisition event and mapping each handoff
event to the task event it produces gives one input stream for the queue theory.
The two traces agree at every tick, provided the unexpected-exception omission
does not occur. `published_clear_avoids_unexpected_exception` shows that it
cannot after a published clear. `published_clear_delivers_to_queue_task` then
shows the queue's task machine reaching the delivered state in `Suc (i + 6 * B)`
ticks after a published clear at `i`.

`cleared_task_outcome_classified` covers every publication outcome at the clear.
The task is published, or it has a delivered retryable rejection, or its result
is dropped by one of the two lifecycle paths that release the worker without a
result. A retry after a retryable rejection is a separate attempt that only the
caller can make.

`configured_startup_first_commit` starts from configured startup. Under the
roster, capture and quorum premises of the startup handoff, the candidate reaches
pre-vote and then a first quorum commit, local installation and slot release in
the next serviced window. Startup and the election window have separate service
bounds.

`stalled_mass_tends_to_zero_from_commit` derives the probability result's
shrinking and success premises. An execution stays stalled only while no earlier
attempt has completed a first publication. A successful timer window with a
permitted and serviced recovery episode completes one, so the stalled mass tends
to zero under the conditional support premise.

What these theorems do not close:

- The dynamic and stateless chains have no probability or queue extension. The
  stateless chain carries the lease claim, the changing-view search and the
  publication recipes as premises, as the stateless theories do.
- The projection of the queue's task machine starts at the claimed task.
  Admission from the queue is the acquisition event prefixed to the stream. It is
  not derived from queue registration and load. The queue's own submission
  theorem still takes its registration and drain premises.
- The tick spaces of the publication window and the handoff trace are aligned by
  the premise that the release tick is the clear callback's tick. Nothing derives
  that a window completion produces the callback.
- Which stalls recur, the conditional support for timer draws and service, the
  source mapping of each projection, and the quorum-backed and stateless-authority
  protocols themselves remain premises. Those protocols are proposed
  interfaces, not current Java.

### Production assumptions to audit in the composed result

- **Source effects and lifecycle.** A successful operation must have the
  effect and callback generation used by the corresponding proof. The
  exceptional-callback fixes provide ownership and single-delivery guards.
  The application, publication-listener, and queue bounds still need local
  service. Shutdown omissions and silent applier shutdown are separate
  outcomes. A retryable result is terminal for its submission. A later
  attempt requires a caller that actually resubmits.
- **Deployment and workload.** The healthy participants must supply the
  election and publication quorums, or the stateless lease and manifest path.
  Configured startup needs the shared roster and identity assumptions, and
  compatible history and acceptance coverage at the dynamic handoff. Queue
  progress needs a finite overtaking bound. Healthy paths need capacity and
  independent service even if other operations hold resources indefinitely.
  The stateless storage and recovery scope is the one in the safety model.
- **Policy deployment.** The existing detector can leave an incumbent that
  responds to heartbeats unable to publish while a needed resource is held.
  The proposed policies require authenticated observations and dispatch on
  healthy paths. Stateful reports also need a fresh challenge and an actual
  pre-vote override. Stateless reports need an independently provisioned
  observer roster, trusted fenced progress, and a pinned lease-claim entry
  point. The proposals leave existing election and fencing authority in place.
- **Timing and probability.** A usable attempt needs sufficient headroom
  between timers, with pending work accounted for, and service within the
  publication deadlines. The recurrence and probability results need their
  stated arming, drain, and conditional support premises. Production needs
  separate evidence for these premises alongside the configured jitter
  range and network service assumptions.
