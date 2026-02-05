// SHIFT: Exploring the Boundary of Transparent RDMA Failover
// Presentation Slides - Created with Touying for Typst

#import "@preview/touying:0.6.1": *
#import themes.simple: *

// Theme configuration
#show: simple-theme.with(
  aspect-ratio: "16-9",
  primary: rgb("#2563eb"),
  footer: [SHIFT: Exploring the Boundary of Transparent RDMA Failover],
)

// Custom styling
#let theorem-box(title, body) = {
  block(
    fill: rgb("#f0f9ff"),
    stroke: 2pt + rgb("#2563eb"),
    inset: 16pt,
    radius: 8pt,
    width: 100%,
    [
      #text(weight: "bold", fill: rgb("#1e40af"))[#title]
      #v(8pt)
      #body
    ],
  )
}

#let insight-box(body) = {
  block(
    fill: rgb("#fef3c7"),
    stroke: 2pt + rgb("#d97706"),
    inset: 12pt,
    radius: 6pt,
    width: 100%,
    body,
  )
}

#let impossible-box(body) = {
  block(
    fill: rgb("#fee2e2"),
    stroke: 2pt + rgb("#dc2626"),
    inset: 12pt,
    radius: 6pt,
    width: 100%,
    body,
  )
}

#let supported-box(body) = {
  block(
    fill: rgb("#dcfce7"),
    stroke: 2pt + rgb("#16a34a"),
    inset: 12pt,
    radius: 6pt,
    width: 100%,
    body,
  )
}

#let partial-box(body) = {
  block(
    fill: rgb("#fef9c3"),
    stroke: 2pt + rgb("#ca8a04"),
    inset: 12pt,
    radius: 6pt,
    width: 100%,
    body,
  )
}

// ============================================================
// TITLE SLIDE
// ============================================================
#title-slide[
  = Exploring the Boundary of Transparent RDMA Failover
  #v(12pt)
  *Formal Verification of SHIFT's Optimality*
  #v(24pt)
  #text(size: 18pt)[
    Three Impossibility Theorems for Cross-NIC Fault Tolerance
  ]
  #v(16pt)
  #text(size: 14pt, fill: gray)[
    SIGCOMM 2025 | Formal Proofs in Rocq 9.0
  ]
]

// ============================================================
// SECTION: Motivation - LLM Training Context
// ============================================================
= Motivation

== LLM Training at Scale

#slide(composer: (1fr, 2fr))[
  *GPU Cluster Sizes*

  - Llama 3: 16,384 H100 GPUs
  - GPT-4: Estimated 10,000+ GPUs
  - Training duration: weeks to months
  - Cost: millions of dollars per run



  *The Gang Scheduling Problem*

  Distributed training requires *all workers synchronized*.

  A single failure $arrow.r$ entire job stalls or crashes.
][
  #v(20pt)
  #figure(
    ```
    ┌─────┐ ┌─────┐ ┌─────┐ ┌─────┐
    │GPU 0│ │GPU 1│ │ ... │ │GPU N│
    └──┬──┘ └──┬──┘ └──┬──┘ └──┬──┘
       │       │       │       │
       └───────┴───────┴───────┘
              AllReduce
                 │
           ┌─────┴─────┐
           │  1 NIC    │
           │  fails    │ ← Entire job
           └───────────┘   blocked
    ```,
  )
]

== Network Failures Are Common in Production

#slide[
  #figure(
    table(
      columns: (auto, auto, 1fr),
      inset: 12pt,
      align: (left, center, left),
      stroke: 0.5pt,
      [*Operator*], [*Failure Rate*], [*Breakdown*],
      [Alibaba #footnote[Dong et al., NSDI'25]], [15.8%], [9.1% NICs + 6.7% optics],
      [Azure #footnote[Xiong et al., 2024]], [8.3%], [InfiniBand cluster failures],
      [Tencent #footnote[Meng et al., SIGCOMM'25]], [15% + 30%], [NIC errors + network anomalies],
    ),
  )



  #v(16pt)

  #insight-box[
    *Rail-Optimized Topologies* exacerbate this:

    - Optical interconnects have higher failure rates than copper
    - Multiple NICs per node $arrow.r$ multiplicative failure probability
    - Scale increases absolute frequency even with constant per-device rates
  ]
]

== Current Approaches Fall Short

#slide(composer: (1fr, 1fr))[
  *Checkpoint-Restart*

  - Save model state periodically
  - On failure: restart from last checkpoint
  - *Progress Loss*: All work since checkpoint is discarded

  #v(8pt)

  *Runtime Resilience (Bamboo, Oobleck)*

  - Dynamically reconfigure pipeline
  - Replace failed workers
  - *Limitation*: Requires app modifications, not transparent


][
  *What We Want: SHIFT*

  #supported-box[
    - *Transparent* to applications (no code changes)
    - Works with unmodified PyTorch + NCCL
    - Continue training until next checkpoint
    - Zero or minimal overhead in normal operation
  ]

  #v(12pt)

  #text(size: 14pt, style: "italic")[
    Can we achieve this? What are the fundamental limits?
  ]
]

// ============================================================
// SECTION: The Boundary Concept
// ============================================================
= The Boundary

== The Fundamental Question

#slide[
  #align(center)[
    #text(size: 24pt, weight: "bold")[
      What is the *theoretical limit* of transparent cross-NIC failover?
    ]
  ]



  #v(24pt)

  #grid(
    columns: (1fr, 1fr),
    gutter: 24pt,
    [
      *The Key Insight*

      WR-level retransmission (not packet-level) is the feasible granularity:

      - Packet-level states are hardware-managed
      - Sequence numbers, retry counters: inaccessible during failure
      - RNIC offloads reliability $arrow.r$ software cannot intercept
    ],
    [
      *SHIFT's Claim*

      We achieve the *theoretical maximum*:

      - Everything that CAN be transparently retried $arrow.r$ retried
      - Everything that CANNOT $arrow.r$ explicit error or handshake
      - Formally verified in Rocq (Coq)
    ],
  )
]

== What Does "Transparent" Mean?

#theorem-box("Definition: Transparent Overlay")[
  A failover mechanism that:

  1. Makes decisions based *only* on sender-observable events
  2. Does *not* modify application semantics
  3. Does *not* require application or receiver code changes
]

#v(12pt)

*Why is this critical?*
#insight-box[
  *One-Sided RDMA (WRITE/READ):* The receiver CPU is *silent* (bypassed).
  - We *cannot* run logic on the receiver to track state or send ACKs.
  - Failover must be handled entirely by the sender's NIC/Software.

  *(Note: For Two-Sided RDMA, the receiver CPU is active, allowing us to mitigate this via the Handshake—see Theorem 2b.)*
]



#v(12pt)

#insight-box[
  *The Constraint*: The overlay sees ONLY:

  #align(center)[`Send` $arrow.r$ `Timeout` $arrow.r$ `Completion`]

  It CANNOT see: Network events | Receiver execution | Memory state

  *Therefore*: Any retransmission decision is fundamentally a guess.
]

// ============================================================
// SECTION: Theorem 1 - Indistinguishability
// ============================================================
= Theorem 1: Indistinguishability

== The Intuition: The Sender's Dilemma

#slide(composer: (1fr, 1fr))[
  *Scenario 1: Packet Lost*
  (Liveness requires Retry)

  #text(size: 14pt)[
    ```
    Sender        Network       Receiver
      │              │              │
      │──── Op ────▶✗│              │
      │              │              │
      │  (timeout)   │              │
    ```
  ]

  *Intuition:* "Nothing happened. I must try again or the system hangs."
][
  *Scenario 2: ACK Lost*
  (Safety forbids Retry)
  #text(size: 14pt)[
    ```
    Sender        Network       Receiver
      │              │              │
      │──── Op ────────────────────▶│
      │              │          (exec)
      │◀─── ACK ───✗ │              │
      │  (timeout)   │              │
    ```]


  *Intuition:* "It finished, but I don't know it. Retrying might corrupt state."
]

== The Formalization: Indistinguishability

#slide[
  In *both* scenarios, the sender observes exactly the same:

  #align(center)[
    #text(size: 24pt)[
      `[ObsSent(op), ObsTimeout(op)]`
    ]
  ]

  #v(8pt)

  #theorem-box("Theorem 1: Indistinguishability (Verified in Rocq)")[
    For any transparent overlay, there exist traces $T_1$ (packet lost) and $T_2$ (ACK lost) such that:
    $
      "SenderView"(T_1) = "SenderView"(T_2)
    $
    Yet $T_1$ requires retry for liveness, while $T_2$ forbids it for safety.
  ]

  #impossible-box[
    *Impossibility*: A transparent decision is a function of the View. Since views are equal, the decision must be equal. It *must* be wrong for either $T_1$ or $T_2$.
  ]
]

// ============================================================
// SECTION: Theorem 2 - Non-Idempotency
// ============================================================
= Theorem 2: Non-Idempotency of Atomics

== Atomic Operations Cannot Be Transparently Retried

#slide(composer: (1fr, 1fr))[
  *FADD: State Corruption*
  #set text(20pt)

  ```
  Initial:   Memory[a] = 0

  1st FADD:  Memory[a]=0+δ=δ
             Returns: 0

  2nd FADD:  Memory[a]=δ+δ=2δ
  (retry)    Returns: δ
  ```

  Application expects counter = $delta$.

  Double execution gives $2 delta$ $arrow.r$ *Corruption*
][
  *CAS: The ABA Problem*
  #set text(20pt)

  ```
  Memory[a] = 0
  S: CAS(0→1) succeeds → a = 1
  P: CAS(1→0) succeeds → a = 0
  S: Retry CAS(0→1)    → a = 1✗
  ```

  S's single CAS executed *twice*.

  P's modification silently overwritten.

  $arrow.r$ *Linearizability violated*
]



#theorem-box("SHIFT's Response (Optimal by Theorem 2)")[
  Return `IBV_WC_RETRY_EXC_ERR` if atomic WR is in-flight during fault.

  This is the *only* correct behavior under transparency constraints.
]

== Queue Sliding: Two-Sided Operations

#slide[
  *The Hidden Non-Idempotency of SEND/RECV*

  #figure(
    table(
      columns: (auto, auto, auto),
      inset: 10pt,
      stroke: 0.5pt,
      [*Step*], [*Receive Queue*], [*Buffers*],
      [Initial], [$[R_1, R_2, R_3]$], [$B_1, B_2, B_3$ empty],
      [M₁ arrives], [$[R_2, R_3]$], [$B_1 #sym.arrow.l M_1$],
      [ACK lost, retry M₁], [$[R_3]$], [$B_2 #sym.arrow.l M_1$ (duplicate!)],
      [M₂ arrives], [$[#sym.emptyset]$], [$B_3 #sym.arrow.l M_2$ (shifted!)],
    ),
  )



  #v(12pt)

  #partial-box[
    *Queue Sliding*: Messages and buffers become permanently misaligned.

    *SHIFT's Solution*: CQ event-based 2-way handshake re-synchronizes queue indices.

    (Breaks pure transparency but hides coordination from application)
  ]
]

// ============================================================
// SECTION: Communication Library Compatibility
// ============================================================
= Communication Library Analysis

== Which NCCL Protocols Can SHIFT Support?

#slide[
  #figure(
    table(
      columns: (auto, auto, auto, 1fr),
      inset: 10pt,
      stroke: 0.5pt,
      [*Protocol*], [*Data Transfer*], [*Notification*], [*SHIFT Compatible?*],
      [Simple], [RDMA Write], [RDMA Write_Imm (flag)], [#text(fill: rgb("#16a34a"))[Fully supported]],
      [LL], [RDMA Write], [Inline flag (same WR)], [#text(fill: rgb("#dc2626"))[Vulnerable]],
      [LL128], [RDMA Write], [Inline flag (8B)], [#text(fill: rgb("#dc2626"))[Vulnerable]],
    ),
  )



  #v(16pt)

  *Why Simple Protocol Works:*

  #supported-box[
    - Receiver reads data buffer *only after* receiving flag via Write_Imm
    - Flag WR comes *after* data WR completes on sender side
    - If data WR times out $arrow.r$ flag never sent $arrow.r$ receiver never reads stale data
    - Theorem 1's T₂ scenario (memory reuse before retry) cannot occur!
  ]
]

== Extended Compatibility Analysis

#slide[
  #figure(
    table(
      columns: (auto, auto, 1fr),
      inset: 10pt,
      stroke: 0.5pt,
      [*Library*], [*Notification Method*], [*SHIFT Support*],
      [NCCL Simple], [RDMA Write_Imm], [#text(fill: rgb("#16a34a"))[Full (< 0.02% CTS overhead)]],
      [NVSHMEM], [RDMA Atomic (signal)], [#text(fill: rgb("#d97706"))[Partial (error on atomics)]],
      [MSCCL++], [RDMA Atomic (signal)], [#text(fill: rgb("#d97706"))[Partial (error on atomics)]],
      [UCX (tag matching)], [Two-sided SEND/RECV], [#text(fill: rgb("#2563eb"))[Via handshake]],
    ),
  )

  #v(12pt)

  #theorem-box("The Partition (Formal Result)")[
    All RDMA communication patterns fall into three classes:

    1. *Idempotent Writes with Ordered Notification*: Transparent retry #sym.checkmark
    2. *Atomics (FADD, CAS)*: Must return error (Theorem 2)
    3. *Two-Sided (SEND/RECV)*: Requires handshake (Queue Sliding)

    SHIFT handles all three optimally within transparency constraints.
  ]
]

// ============================================================
// SECTION: Theorem 3 - Consensus Hierarchy
// ============================================================
= Theorem 3: Consensus Hierarchy Barrier

== Why Read-Only Verification Fails

#slide[
  *Herlihy's Consensus Hierarchy*

  #figure(
    table(
      columns: (auto, auto),
      inset: 10pt,
      stroke: 0.5pt,
      [*Primitive*], [*Consensus Number*],
      [Read/Write], [$1$],
      [FADD, Queue, Stack], [$2$],
      [Compare-and-Swap], [$infinity$],
    ),
  )
]

#slide[
  #set text(20pt)
  *The Failover Problem IS 2-Consensus*

  Two "processes" must agree:

  - *P0 (Old NIC)*: "I executed the op"
  - *P1 (Backup)*: "I should take over"

  They must decide: *Commit* or *Abort*?

  But: Transparent verification = Read-only

  $"CN"("Read") = 1 < 2$

  #impossible-box[Reads alone cannot solve 2-consensus!]
]

== The ABA Attack on Any Verification

#slide[
  #set text(18pt)
  #figure[
    #table(
      columns: (1fr, 1fr),
      inset: 10pt,
      stroke: 0.5pt,
      [*History H₁: CAS Executed*], [*History H₀: CAS Not Executed*],
      [
        ```
        Memory[a] = 0
        CAS(0→1) succeeds  ← executed
        Third party: CAS(1→0)
        Final: Memory[a] = 0
        ```
      ],
      [
        ```
        Memory[a] = 0
        (packet lost, never arrived)

        Final: Memory[a] = 0
        ```
      ],
    ),
  ]

  #impossible-box[
    *Same final memory state* $arrow.r$ Any read-based verification returns identical result

    Cannot distinguish H₁ from H₀ $arrow.r$ No correct failover solver exists

    *Rocq*: `Theorem transparent_cas_failover_impossible`
  ]
]

// ============================================================
// SECTION: SHIFT Design
// ============================================================
= SHIFT Design Overview

== Architecture: SHIFTLib

#slide(composer: (3fr, 2fr))[
  #figure(
    text(size: 11pt)[
      ```
      ┌──────────────────────────────────────────────────────┐
      │                   Application                        │
      │           (PyTorch + NCCL, unmodified)               │
      ├──────────────────────────────────────────────────────┤
      │                     SHIFTLib                         │
      │  ┌─────────────────┐   ┌─────────────────────┐      │
      │  │  Wrapper Verbs  │   │  Background Thread  │      │
      │  │  (post_send,    │   │  (shadow control,   │      │
      │  │   poll_cq,...)  │   │   CQ events, probe) │      │
      │  └────────┬────────┘   └──────────┬──────────┘      │
      │           │                       │                 │
      │  ┌────────┴────────┐     ┌────────┴────────┐        │
      │  │   Default QP    │◀───▶│    Backup QP    │        │
      │  │    (RNIC 0)     │sync │    (RNIC 1)     │        │
      │  └─────────────────┘     └─────────────────┘        │
      └──────────────────────────────────────────────────────┘
      ```
    ],
  )
][
  *Key Mechanisms*

  - Shadow control verbs
  - CQ event-based handshake
  - WR execution fence
]

== SHIFT State Machine

#slide(composer: (2fr, 2fr))[
  #figure(
    text(size: 11pt)[
      ```
      ┌─────────┐  fault   ┌──────────┐  probe ok  ┌────────────┐
      │ Default │─────────▶│ Fallback │───────────▶│WaitSignaled│
      └─────────┘          └──────────┘            └─────┬──────┘
           ▲                     │                       │
           │                     │ (backup QP)           │ signaled
           │                     ▼                       ▼
           │                ┌──────────┐           ┌────────────┐
           └────────────────│  Reset   │◀──────────│WaitDrained │
               all clear    │ & Probe  │  drained  └────────────┘
                            └──────────┘
      ```
    ],
  )
][
  #set text(20pt)
  *State Transitions*

  1. *Default → Fallback*: Error WC
  2. *Fallback → WaitSignaled*: Probe
  3. *WaitSignaled → WaitDrained*: Fence
  4. *WaitDrained → Default*: Resume

  #v(8pt)

  *Latency*: ~500μs (WRITE), ~900μs (SEND)

  #insight-box[Sub-ms recovery!]
]

// ============================================================
// SECTION: Evaluation
// ============================================================
= Evaluation Highlights

== Performance: Negligible Overhead

#slide(composer: (1fr, 1fr))[
  *Baseline Latency (ib_write_lat)*

  #figure(
    table(
      columns: (auto, auto, auto),
      inset: 8pt,
      stroke: 0.5pt,
      [*Message*], [*Standard*], [*SHIFT*],
      [1 B], [2.68 μs], [2.69 μs],
      [4 B], [2.70 μs], [2.69 μs],
      [16 B], [2.69 μs], [2.68 μs],
    ),
  )

  #supported-box[
    Overhead: *< 0.4%*

    Zero-copy data path preserved
  ]
][
  #set text(20pt)
  *Memory Overhead*
  - Backup QP context: ~138 KB each
  - Backup CQ: ~33 KB each
  - 1000 backup QPs: ~171 MB total
  - *Negligible* for modern servers

  #v(12pt)

  *Control Verb Overhead*

  - Shadow verbs run in background thread
  - Total setup time: ~35ms (non-blocking)
  - Does not affect application startup
]

== Real-World Impact: PyTorch Training

#slide[
  #set text(17pt)
  *Without SHIFT:*

  #impossible-box[
    Training starts $arrow.r$ 9.5 minutes work $arrow.r$ NIC fails $arrow.r$

    Job crashes $arrow.r$ Restart from checkpoint $arrow.r$ *9.5 minutes LOST*
  ]



  #v(16pt)

  *With SHIFT:*

  #supported-box[
    Training starts $arrow.r$ 9.5 minutes work $arrow.r$ NIC fails $arrow.r$

    SHIFT failover (< 1ms) $arrow.r$ Training continues $arrow.r$ Checkpoint saves $arrow.r$

    *0 minutes lost* (progress preserved until checkpoint)
  ]



  #v(12pt)

  #align(center)[
    #text(size: 20pt, weight: "bold", fill: rgb("#059669"))[
      GPT-3 13B on 8× H100: Training continues seamlessly
    ]
  ]
]

// ============================================================
// SECTION: Conclusion
// ============================================================
= Conclusion

== SHIFT Achieves the Theoretical Maximum

#slide[
  #figure(
    table(
      columns: (auto, 1fr, auto),
      inset: 10pt,
      stroke: 0.5pt,
      [*Theorem*], [*What It Proves*], [*SHIFT's Response*],
      [1], [Packet/ACK loss indistinguishable to sender], [Retry writes (liveness)],
      [2a], [FADD/CAS are non-idempotent], [Return error on atomics],
      [2b], [Two-sided ops have queue sliding], [2-way handshake sync],
      [3], [CN=1 primitives cannot solve 2-consensus], [No read-based verification],
    ),
  )



  #v(12pt)

  #theorem-box("Optimality Claim (Verified in Rocq)")[
    Any system claiming broader transparent failover coverage MUST either:

    - *Sacrifice transparency*: Require application/receiver modifications, OR
    - *Violate correctness*: Contradict these impossibility theorems

    SHIFT operates exactly at this proven boundary.
  ]
]

== Summary: The Boundary of Transparent Failover

#slide[
  #align(center)[
    #block(
      fill: rgb("#ecfdf5"),
      stroke: 3pt + rgb("#059669"),
      inset: 24pt,
      radius: 12pt,
    )[
      #text(size: 20pt, weight: "bold")[
        SHIFT operates at the proven boundary:
      ]

      #v(12pt)

      #grid(
        columns: (1fr, 1fr),
        gutter: 16pt,
        [
          *CAN Transparently Retry:*
          - RDMA Writes (idempotent)
          - NCCL Simple protocol
          - Ordered notification patterns
        ],
        [
          *CANNOT (by theorem):*
          - FADD/CAS (non-idempotent)
          - Uncoordinated two-sided
          - Any read-based verification
        ],
      )

      #v(12pt)

      *Result*: Zero progress loss for supported workloads (NCCL Simple).

      ~2,100 lines of Rocq proofs verify this boundary.
    ]
  ]
]

// ============================================================
// FINAL SLIDE
// ============================================================
== Thank You

#slide[
  #align(center)[
    #v(20pt)

    #text(size: 28pt, weight: "bold")[
      Questions?
    ]

    #v(24pt)

    *SHIFT: Exploring the Boundary of RDMA Network Fault Tolerance*

    #v(16pt)

    #grid(
      columns: (1fr, 1fr),
      gutter: 24pt,
      [
        *Key Theorems (Rocq)*

        - `impossibility_safe_retransmission`
        - `fadd_not_idempotent`
        - `transparent_cas_failover_impossible`
      ],
      [
        *Key Files*

        - `Indistinguishability.v`
        - `FADD.v`, `CAS.v`
        - `Hierarchy.v`
      ],
    )

    #v(24pt)

    #text(size: 14pt, fill: gray)[
      Verified with Rocq 9.0 | ShiftVerification namespace
    ]
  ]
]
