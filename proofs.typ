// RDMA Failover Impossibility Proofs
// Typst Document

#set document(title: [Limits of Transparent RDMA NIC Failover])
#set page(margin: 2.5cm)
#set text(font: "New Computer Modern", size: 11pt)
#set heading(numbering: "1.1")
#set math.equation(numbering: "(1)")

#let theorem(title: none, body) = {
  block(
    fill: rgb("#f0f0f0"),
    inset: 10pt,
    radius: 4pt,
    width: 100%,
    [
      #if title != none [
        *Theorem (#title):* #body
      ] else [
        *Theorem:* #body
      ]
    ]
  )
}

#let proof(body) = {
  block(
    inset: (left: 1em),
    [_Proof._ #body #h(1fr) $square$]
  )
}

#let definition(term, body) = {
  block(
    stroke: (left: 2pt + rgb("#0066cc")),
    inset: (left: 10pt, y: 5pt),
    [*Definition (#term):* #body]
  )
}

= Transparent RDMA NIC Failover: What Can and Cannot Be Supported

== The Scenario

Consider a high-availability RDMA system with a primary NIC and a backup NIC. When the primary NIC fails mid-operation, we want the backup NIC to transparently take over---completing any in-flight operations without the application noticing the failure.

#figure(
  ```
  ┌────────┐         ┌─────────────┐         ┌────────┐
  │ Sender │───op───▶│ Primary NIC │────?────│ Memory │
  └────────┘         └─────────────┘         └────────┘
       │                   ✗ FAILS                │
       │             ┌─────────────┐              │
       └────op?─────▶│ Backup NIC  │──────?───────┘
                     └─────────────┘
  ```,
  caption: [NIC failover scenario: should the backup retry the operation?]
)

The sender detects that the primary NIC has failed. The critical question: *Should the backup NIC re-execute the operation?*

- If the primary executed before failing → backup must NOT retry (double-execution)
- If the primary failed before executing → backup MUST retry (for liveness)

A *transparent failover* mechanism makes this decision without modifying the application protocol---using only the sender's observations and what the backup can read from memory.

== The Question: Which Operations Can Be Supported?

Not all RDMA operations are equal. We analyze which can be transparently failed over:

#table(
  columns: (auto, auto, auto),
  inset: 8pt,
  align: horizon,
  table.header([*Operation*], [*Idempotent?*], [*Transparent Failover?*]),
  [Send/Recv (two-sided)], [Yes], [#text(fill: rgb("#080"))[Possible]],
  [Write#footnote[Write is idempotent in isolation, but if used for memory ordering (e.g., signaling "data ready"), correctness depends on execution knowledge---which requires solving 2-consensus.]], [Yes], [#text(fill: rgb("#080"))[Possible]],
  [Read], [Yes], [#text(fill: rgb("#080"))[Possible]],
  [FADD], [No], [#text(fill: rgb("#c00"))[Impossible]],
  [CAS], [Conditional], [#text(fill: rgb("#c00"))[Impossible in general]],
)

*The fundamental issue*: Determining whether an operation was executed is a 2-consensus problem (shown in Theorem 3). Any operation whose correctness depends on knowing whether it executed cannot be transparently failed over.

For atomic operations (FADD, CAS), the problem is compounded: they are non-idempotent, so incorrect retry corrupts state regardless of ordering concerns.

#pagebreak()

== The Core Problem: What Did the Primary Do?

When the primary NIC fails, there are two possible histories:

#block(
  stroke: 1pt + rgb("#666"),
  inset: 12pt,
  radius: 4pt,
  [
    *History $H_1$: Primary Failed Before Execution*
    - Sender issued atomic operation to primary NIC
    - Primary NIC failed before executing
    - Operation was never performed
    - *Correct action*: Backup must execute the operation

    *History $H_2$: Primary Executed Then Failed*
    - Sender issued atomic operation to primary NIC
    - Primary NIC executed the operation
    - Primary NIC failed before sending completion
    - *Correct action*: Backup must NOT execute (already done)
  ]
)

The sender observes the same thing in both cases: *the primary NIC failed and no completion was received.* For idempotent operations, this ambiguity is harmless---retry produces the same result. For atomic operations, it is fatal.

== Definitions

#definition([Sender View])[
  The projection $pi_S$ extracts only what the sender can observe: operation submissions, completions, and NIC failures. The sender cannot observe whether the primary executed before failing.
]

#definition([Transparent Failover])[
  A failover mechanism where the backup's decision depends only on: (1) the sender's observations $pi_S$, and (2) reading the current memory state. No persistent metadata or protocol modifications allowed.
]

#definition([Safety and Liveness])[
  - *Safety*: Each operation executes at most once across primary and backup
  - *Liveness*: If an operation was not executed by the primary, the backup eventually executes it
]

#pagebreak()

== Theorem 1: Sender Cannot Distinguish Histories

#theorem(title: [Indistinguishability])[
  For any operation, the sender's observations are identical whether the primary executed before failing or failed before executing.
]

#proof[
  Consider any operation sent to the primary NIC.

  *History $H_1$: Failed Before Execution*
  #block(inset: (left: 1em))[
    1. Sender submits operation to primary NIC
    2. Primary NIC fails before processing
    3. Sender detects NIC failure
    4. Sender's observation: $["Submit"("op"), "NICFailure"]$
  ]

  *History $H_2$: Executed Then Failed*
  #block(inset: (left: 1em))[
    1. Sender submits operation to primary NIC
    2. Primary NIC executes operation
    3. Primary NIC fails before sending completion
    4. Sender detects NIC failure
    5. Sender's observation: $["Submit"("op"), "NICFailure"]$
  ]

  Both produce: $pi_S(H_1) = pi_S(H_2) = ["Submit"("op"), "NICFailure"]$

  Any decision rule based solely on $pi_S$ must make the same choice for both histories.
]

*For idempotent operations*: This is fine---retry is safe either way.

*For atomic operations*: This is a problem---$H_1$ requires retry, $H_2$ forbids it.

#pagebreak()

== Theorem 2: Atomic Operations Are Non-Idempotent

The indistinguishability from Theorem 1 only matters because atomic operations cannot tolerate incorrect retry.

#theorem(title: [FADD Non-Idempotency])[
  For $delta > 0$, executing FADD twice produces different state than executing once.
]

#proof[
  Let FADD add $delta$ to address $a$, starting from $m[a] = 0$.

  #table(
    columns: (auto, auto, auto),
    inset: 8pt,
    align: horizon,
    table.header([*Scenario*], [*Final State*], [*Return Value*]),
    [Execute once (correct)], [$m[a] = delta$], [$0$],
    [Execute twice (incorrect retry)], [$m[a] = 2delta$], [2nd returns $delta$],
  )

  The states differ: $delta eq.not 2delta$ for $delta > 0$. FADD is non-idempotent.
]

*Consequence*: If the backup incorrectly retries FADD after the primary already executed, the application sees $2delta$ instead of $delta$---a silent corruption.

#theorem(title: [CAS Can Succeed Twice])[
  With concurrent modification, a CAS retry can succeed even if the original succeeded.
]

#proof[
  Consider primary executing CAS$(0 arrow.r 1)$, then a concurrent process resetting the value:

  #table(
    columns: (auto, auto, auto, auto),
    inset: 6pt,
    align: horizon,
    table.header([*Step*], [*Actor*], [*Operation*], [*Memory*]),
    [1], [Primary NIC], [CAS$(0 arrow.r 1)$ succeeds], [$0 arrow.r 1$],
    [2], [Primary NIC], [Fails before completion], [---],
    [3], [Concurrent], [CAS$(1 arrow.r 0)$ succeeds], [$1 arrow.r 0$],
    [4], [Backup NIC], [CAS$(0 arrow.r 1)$ retry], [$0 arrow.r 1$ succeeds!],
  )

  The backup's retry succeeds because the value returned to $0$ (ABA problem). The application's single CAS executed twice.
]

*The Fallacy*: "CAS retry is safe because duplicates fail" assumes no concurrent modification.

#pagebreak()

== Theorem 3: Memory Inspection Cannot Help

Perhaps the backup NIC can read memory to determine if the primary executed? Theorem 3 shows this fails due to the ABA problem.

#theorem(title: [ABA Defeats Verification])[
  Reading memory cannot distinguish "primary executed then value reset" from "primary never executed."
]

#proof[
  Consider CAS$(0 arrow.r 1)$ where the initial value was $0$.

  *History $H_1$: Primary Never Executed*
  #block(inset: (left: 1em))[
    - Memory state: $m[a] = 0$ (unchanged)
    - Correct decision: Backup should execute
  ]

  *History $H_2$: Primary Executed, Then ABA Reset*
  #block(inset: (left: 1em))[
    - Primary executed: $0 arrow.r 1$
    - Concurrent process reset: $1 arrow.r 0$
    - Memory state: $m[a] = 0$ (same as $H_1$!)
    - Correct decision: Backup should NOT execute
  ]

  The backup reads $m[a] = 0$ in both cases. Any verification function $V : "Memory" -> {"Execute", "Skip"}$ must return the same answer for both, but they require opposite decisions.
]

#pagebreak()

== Why This Is Fundamentally Impossible: The Consensus Hierarchy

The ABA problem is not a bug we can fix with cleverness. It reflects a *fundamental limit* from distributed computing theory: Herlihy's Consensus Hierarchy.

=== What Is the Consensus Hierarchy?

In 1991, Maurice Herlihy proved that synchronization primitives form a strict hierarchy based on their *consensus number*---the maximum number of processes that can reach agreement using only that primitive.

#definition([Consensus Number])[
  $"CN"(X) = n$ means primitive $X$ can solve wait-free consensus among $n$ processes, but not among $n+1$ processes. $"CN"(X) = infinity$ means $X$ can solve consensus for any number of processes.
]

The hierarchy is *strict*: a primitive with $"CN" = k$ *cannot implement* any primitive with $"CN" > k$.

=== The Consensus Hierarchy

#figure(
  table(
    columns: (auto, auto, auto),
    inset: 10pt,
    align: horizon,
    stroke: 1pt,
    table.header([*Primitive*], [*CN*], [*Why*]),
    [Read/Write], [$1$], [Reads are invisible; writes return no info],
    [FADD], [$2$], [Sum is commutative: $delta_0 + delta_1 = delta_1 + delta_0$],
    [CAS], [$infinity$], [First CAS wins; all observe the winner],
  ),
  caption: [Herlihy's Consensus Hierarchy]
)

*Key Insight*: Each consensus number is *derived* from the primitive's semantics, not arbitrarily assigned:

- *Register CN = 1*: Two processes running solo see the same initial state (empty memory). They must decide differently but observe identically.

- *FADD CN = 2*: Addition is commutative. Process 2 sees $delta_0 + delta_1$ whether execution order is $[0,1,2]$ or $[1,0,2]$---same sum, different winners.

- *CAS CN = $infinity$*: The first CAS to a sentinel wins, and everyone reads the winner's value. Different winners $arrow.r$ different observations $arrow.r$ always distinguishable.

=== Failover Is 2-Process Consensus

The failover decision is *structurally equivalent* to 2-process consensus:

#figure(
  table(
    columns: (1fr, 1fr),
    inset: 10pt,
    align: horizon,
    stroke: 1pt,
    table.header([*2-Process Consensus*], [*Failover Decision*]),
    [Two processes $P_0$, $P_1$], [Two histories $H_1$, $H_2$],
    [Each proposes a value], [Each requires a decision],
    [$P_0$ proposes "execute"], [$H_1$ (not executed) requires Execute],
    [$P_1$ proposes "skip"], [$H_2$ (already executed) requires Skip],
    [Must agree on one value], [Must make correct choice],
    [Winner's value wins], [Actual history determines correctness],
  ),
  caption: [Structural isomorphism between failover and 2-consensus]
)

#theorem(title: [Reduction: Failover Solver $arrow.r.double$ 2-Consensus])[
  If a correct failover solver $F$ exists, we can solve 2-process consensus:

  #block(inset: (left: 2em))[
    1. $P_0$ and $P_1$ each write their input to `proposed[i]`
    2. Both call $F(m)$ where $m$ is the (ABA-ambiguous) memory state
    3. If $F(m) = "Execute"$: decide `proposed[0]`
    4. If $F(m) = "Skip"$: decide `proposed[1]`
  ]

  This satisfies consensus: $F$ determines a unique winner, both processes agree.
]

=== Why Read-Only Verification Fails

The backup NIC can only *read* memory to determine if the primary executed. But:

#block(
  fill: rgb("#fff0f0"),
  stroke: 2pt + rgb("#c00"),
  inset: 12pt,
  radius: 6pt,
  width: 100%,
  [
    *The Consensus Barrier*

    Failover requires solving 2-process consensus ($"CN" >= 2$).

    Read-only verification has $"CN" = 1$.

    By Herlihy's impossibility theorem: $"CN" = 1$ primitives *cannot* solve 2-consensus.

    Therefore: *transparent failover for atomics is impossible*.
  ]
)

This is not a limitation of our specific approach---it is a *mathematical impossibility*. No algorithm using only reads can solve this problem, because the consensus hierarchy is a fundamental law of distributed computing.

#theorem(title: [Main Impossibility Result])[
  Transparent failover for atomic operations is impossible because:
  1. Failover requires solving 2-process consensus (distinguishing $H_1$ from $H_2$)
  2. Transparency limits verification to read-only operations
  3. $"CN"("Read") = 1 < 2$
  4. By Herlihy's hierarchy, $"CN" = 1$ primitives cannot solve 2-consensus
]

#pagebreak()

== Summary: What Can and Cannot Be Supported

#figure(
  ```
                    ┌─────────────────────────────────┐
                    │     Primary NIC Fails           │
                    └────────────────┬────────────────┘
                                     │
              ┌──────────────────────┴──────────────────────┐
              │                                             │
     ┌────────▼────────┐                          ┌─────────▼────────┐
     │ Idempotent Ops  │                          │ Atomic Ops       │
     │ (Read, Write)   │                          │ (FADD, CAS)      │
     └────────┬────────┘                          └─────────┬────────┘
              │                                             │
              │ Retry is always safe                        │ Retry may corrupt
              │                                             │
     ┌────────▼────────┐                          ┌─────────▼────────┐
     │ ✓ SUPPORTED     │                          │ ✗ NOT SUPPORTED  │
     └─────────────────┘                          └──────────────────┘
  ```,
  caption: [Transparent failover support depends on operation idempotency]
)

#table(
  columns: (auto, 1fr),
  inset: 10pt,
  align: horizon,
  table.header([*Theorem*], [*What It Shows*]),
  [1], [Sender cannot distinguish "primary executed" from "primary failed before executing"],
  [2], [For atomic operations, incorrect retry corrupts state (non-idempotent)],
  [3], [Backup cannot determine correct action by reading memory (ABA problem)],
)

#align(center)[
  #block(
    stroke: 2pt + rgb("#c00"),
    inset: 16pt,
    radius: 8pt,
    [
      *Transparent NIC failover cannot support RDMA atomic operations.*

      FADD and CAS require knowing whether the primary executed---information that is lost when the NIC fails and cannot be recovered by reading memory.
    ]
  )
]

#pagebreak()

== Implications

*Operations That CAN Be Supported:*
- Two-sided operations (Send/Recv)---receiver participates explicitly
- RDMA Read (idempotent---reading twice is harmless)
- RDMA Write, *only if* the receiver does not depend on knowing whether the write executed (e.g., no memory ordering for synchronization)
- Any operation where correctness does not depend on execution knowledge

*Operations That CANNOT Be Supported Transparently:*
- Any operation where the receiver depends on memory ordering (requires knowing if operation executed $arrow.r$ 2-consensus)
- FADD (non-idempotent: retry corrupts state)
- CAS (ABA problem: retry can succeed twice)
- Any read-modify-write atomic

*Workarounds (Violate Transparency):*
- Receiver-side operation logs with deduplication
- Unique operation IDs tracked by receiver
- Application-level acknowledgments
- Two-phase commit protocols

The fundamental impossibility is that determining whether an operation executed requires solving 2-consensus. For truly idempotent operations where correctness does not depend on this knowledge, transparent failover works. For operations with ordering dependencies or non-idempotent semantics, it is impossible.

#pagebreak()

== Rocq Formalization

All theorems are mechanically verified in Rocq 9.0.

#table(
  columns: (auto, auto, auto),
  inset: 6pt,
  align: horizon,
  table.header([*Concept*], [*Module*], [*Key Theorems*]),
  [Sender view], [`Core/Traces.v`], [`sender_view`, `SenderObs`],
  [Transparent overlay], [`Core/Properties.v`], [`TransparentOverlay`],
  [Indistinguishability], [`Theorem1/Impossibility.v`], [`sender_views_equal`, `impossibility_safe_retransmission`],
  [FADD non-idempotent], [`Theorem2/Atomics.v`], [`fadd_non_idempotent`],
  [CAS double success], [`Theorem2/CAS.v`], [`cas_double_success`],
  [ABA problem], [`Theorem3/FailoverConsensus.v`], [`H0_H1_same_memory`],
  [CN = 1 insufficient], [`Theorem3/ConsensusNumber.v`], [`readwrite_2consensus_impossible_same_protocol`],
  [Atomic failover impossible], [`Theorem3/Hierarchy.v`], [`transparent_cas_failover_impossible`],
)

=== Key Theorems

*Theorem 1* --- Sender observations are identical for both histories:
```coq
Lemma sender_views_equal :
  sender_view T1_concrete = sender_view T2_concrete.
```

*Theorem 2* --- FADD is non-idempotent:
```coq
Theorem fadd_non_idempotent : forall a delta m,
  delta > 0 -> ~ Idempotent (OpFADD a delta) m.
```

*Theorem 3* --- No correct decision function exists for atomics:
```coq
Theorem no_correct_future_decision :
  ~ exists f : FutureObservation -> FailoverDecision,
      f scenario1_future = scenario1_correct /\
      f scenario2_future = scenario2_correct.
```

*Main Result* --- Transparent failover cannot support atomic operations:
```coq
Theorem transparent_cas_failover_impossible :
  forall tf : TransparentFailover,
    verification_via_reads tf ->
    tf.(no_metadata_writes) ->
    ~ provides_reliable_cas tf.
```
