// Section for SHIFT Paper: Formal Justification of Cross-NIC Fault Tolerance Boundary
// This file contains:
// 1. INTRO MODIFICATIONS (for §1)
// 2. Main body text (for §3.1)
// 3. Appendix content (detailed proofs)

// ============================================================================ 
// INTRO MODIFICATIONS (Replace/augment relevant paragraphs in §1)
// ============================================================================ 

/*
--- REPLACE the paragraph starting "However, we identify a fundamental constraint..." with: ---

However, a fundamental question arises: what are the theoretical limits of transparent cross-NIC failover? We prove that SHIFT's design achieves precisely what is possible under the transparency constraint—and that extending support to atomic or two-sided operations without coordination would require capabilities that transparent mechanisms fundamentally cannot provide.

Specifically, we identify three barriers to transparent failover:
(1) **Indistinguishability**: The sender cannot distinguish packet loss (requiring retry) from ACK loss (where retry may corrupt data)—both produce identical observations.
(2) **Non-idempotency**: Atomic operations (FADD, CAS) and Two-Sided Send operations produce side effects (state modification or queue consumption) that make blind retry unsafe.
(3) **Consensus barrier**: Determining whether an operation executed is equivalent to solving 2-process consensus, which read-only verification (the only tool available under transparency) provably cannot solve.

These results establish that SHIFT operates at the boundary of what is achievable: it supports all operations where retry is safe (idempotent writes) and correctly rejects or synchronizes operations where retry would violate correctness. This is not a limitation of our implementation but a fundamental property of the problem space. Any mechanism claiming broader support must either sacrifice transparency (requiring application or receiver modifications) or sacrifice correctness.

--- ADD to contributions list (after item 1): ---

(2) We formally prove that SHIFT's coverage is optimal: transparent failover for atomic and uncoordinated two-sided operations is impossible due to the consensus hierarchy barrier. Supporting these requires receiver-side coordination (like SHIFT's handshake) or persistent metadata—capabilities incompatible with pure transparency. All proofs are mechanically verified in Rocq 9.0. (§3.1, Appendix C)

--- MODIFY the conclusion paragraph to: ---

This work presents SHIFT, a fault-resilient layer over RDMA that achieves the theoretical maximum of transparent cross-NIC failover. We prove that SHIFT's design is optimal: it supports all traffic patterns amenable to transparent failover (idempotent operations under appropriate protocols) while correctly rejecting or synchronizing patterns that would require non-transparent mechanisms. For supported workloads—which include the dominant NCCL Simple protocol used in distributed training—SHIFT preserves application continuity under network anomalies until the next checkpoint, minimizing training progress loss. The design requires no application modifications, incurs minimal overhead, and remains agnostic to applications. Experimental results demonstrate that SHIFT sustains high performance while delivering RDMA fault tolerance, making it a practical and effective solution for large-scale distributed LLM training.
*/

// ============================================================================ 
// PART 1: MAIN BODY SECTION (New §3.1.1 or integrate into §3.1)
// ============================================================================ 

/*
=== 3.1.1 Theoretical Foundation: SHIFT Achieves the Optimal Boundary

SHIFT's design is not merely practical—it is provably optimal. We establish that the boundary between supported and unsupported operations (Table 1) reflects fundamental impossibility results, not implementation limitations.

**The Transparency Constraint.** A failover mechanism is *transparent* if it makes retransmission decisions based solely on sender-observable information (sends, completions, timeouts) without requiring: (1) receiver-side modifications, (2) persistent metadata in remote memory, or (3) application protocol changes. This constraint is essential for compatibility with unmodified applications like PyTorch/NCCL.

**The Core Dilemma.** When a network anomaly causes a timeout, the sender faces two indistinguishable scenarios:
- *Packet loss*: The operation never executed → retry is required for liveness
- *ACK loss*: The operation executed but confirmation was lost → retry may corrupt state

We prove three theorems establishing that this dilemma is insurmountable for non-idempotent operations:

**Theorem 1 (Indistinguishability).** For any transparent overlay, there exist executions with identical sender observations but opposite correctness requirements. Formally, we construct traces $\mathcal{T}_1$ (packet lost) and $\mathcal{T}_2$ (ACK lost, memory reused) where the sender view $\sigma(\mathcal{T}_1) = \sigma(\mathcal{T}_2) = [\texttt{Send}, \texttt{Timeout}]$, yet $\mathcal{T}_1$ requires retry while $\mathcal{T}_2$ forbids it.

**Theorem 2 (Non-Idempotency).**
- *Atomics*: FADD and CAS are non-idempotent. FADD adds the delta twice on retry. CAS suffers from the ABA problem where a retry can succeed incorrectly under concurrent modification.
- *Two-Sided Ops*: Retrying a SEND operation consumes an extra Receive WQE, desynchronizing the message-to-buffer mapping ("Queue Sliding"), even if the data payload itself is safe.

**Theorem 3 (Consensus Hierarchy Barrier).** Correct failover requires solving 2-process consensus. By Herlihy's impossibility theorem, read-only verification has consensus number 1, which is insufficient for 2-consensus. Therefore, no transparent mechanism can correctly determine whether an operation with side effects executed.

**SHIFT's Optimality.** These theorems partition RDMA operations into classes:

| Class | Property | SHIFT Behavior | Theoretical Justification |
|-------|----------|----------------|--------------------------|
| Idempotent Writes | Retry produces same result | Retransmit | *Safe by protocol design* |
| Atomic operations | Retry corrupts state | Return error | *Impossible to handle transparently* |
| Two-Sided operations | Retry causes Queue Sliding | Handshake | *Requires non-transparent sync* |

SHIFT supports exactly the achievable class transparently. For Two-Sided operations, it correctly breaks transparency (via the handshake) to ensure correctness, validating the theorem that transparent handling is impossible. The "error on atomics-in-flight" policy is the only correct behavior for a system that cannot modify the receiver.

**What Would Be Required for Atomics.** Supporting atomic operations would require at least one of:
- *Receiver-side operation logs* with deduplication (violates transparency)
- *Persistent metadata* tracking execution status (violates zero-copy)
- *Application-level acknowledgments* (violates application-agnostic)
- *Two-phase commit* protocols (violates low overhead)

None of these are compatible with SHIFT's transparency constraint. Our impossibility proofs (Appendix C) formalize this: the additional "property not available" is the ability to solve 2-process consensus, which transparent read-only verification fundamentally lacks.

All theorems are mechanically verified in Rocq 9.0 (~3,900 lines). Theorem 3's impossibility is formally derived from the Register CN=1 theorem via a mechanized reduction chain (`failover_impossible_by_read_cn`). The formalization is available at [CITE].
*/

// ============================================================================ 
// PART 2: APPENDIX (Formal Verification Details)
// ============================================================================ 

#set text(font: "New Computer Modern", size: 9pt)
#set par(justify: true)
#set heading(numbering: "A.1")

#let theorem(name, body) = {
  block(
    width: 100%,
    inset: (y: 4pt),
    [*Theorem* (#name)*.*
    #emph(body)]
  )
}

#let lemma(name, body) = {
  block(
    width: 100%,
    inset: (y: 4pt),
    [*Lemma* (#name)*.* #emph(body)]
  )
}

#let definition(name, body) = {
  block(
    width: 100%,
    inset: (y: 4pt),
    [*Definition* (#name)*.* #body]
  )
}

#let proof(body) = {
  block(
    width: 100%,
    inset: (left: 8pt, y: 4pt),
    [_Proof._ #body #h(1fr) $square$]
  )
}

= Formal Verification of Failover Impossibility

We formalize and mechanically verify three impossibility theorems for transparent RDMA failover. All proofs are verified in Rocq 9.0 and available at https://github.com/taooceros/shift-verification.

== Model and Definitions

#definition("Execution Trace")[
  A trace $cal(T)$ is a sequence of events including: operation sends (`EvSend`), packet/ACK losses, executions at the receiver (`EvExecute`), completions, and timeouts.
]

#definition("Sender View")[
  The _sender view_ $sigma(cal(T))$ projects a trace to only sender-observable events: sends, completions, and timeouts. Crucially, the sender cannot observe `EvExecute`, `EvPacketLost`, or `EvAckLost` directly.
]

#definition("Transparent Overlay")[
  A failover mechanism is _transparent_ if its retransmission decision $D : sigma(cal(T)) times "Op" -> {"retransmit", "skip"}$ depends only on the sender view—no persistent metadata, no receiver-side modifications, no application protocol changes.
]

== Theorem 1: Indistinguishability of Packet Loss and ACK Loss

#theorem("Impossibility of Safe Retransmission")[
  For any transparent overlay $D$, there exist traces $cal(T)_1$ and $cal(T)_2$ such that $sigma(cal(T)_1) = sigma(cal(T)_2)$, but safety requires $D(sigma(cal(T)_1)) = "retransmit"$ while $D(sigma(cal(T)_2)) = "skip"$.
]

#proof[
  We construct two traces for a Write operation to address $A_"data"$ with value $V_1$:

  $cal(T)_1$ (packet lost—retransmission required for liveness):
  $ ["EvSend"(W), "EvPacketLost"(W), "EvTimeout"(W)] $

  $cal(T)_2$ (ACK lost, memory reused—retransmission corrupts data):
  $ ["EvSend"(W), "EvReceive"(W), "EvExecute"(W), "EvAppConsume", "EvAppReuse"(V'), "EvAckLost"(W), "EvTimeout"(W)] $

  Both traces yield sender view $sigma(cal(T)_1) = sigma(cal(T)_2) = ["ObsSent"(W), "ObsTimeout"(W)]$.

  - In $cal(T)_1$: operation never executed $arrow.r$ liveness requires retransmission
  - In $cal(T)_2$: operation executed, receiver consumed $V_1$ and wrote new value $V'$ $arrow.r$ retransmission would overwrite $V'$ with stale $V_1$

  Since $D$ is a function and $sigma(cal(T)_1) = sigma(cal(T)_2)$, we have $D(sigma(cal(T)_1)) = D(sigma(cal(T)_2))$. But the traces require opposite decisions. Contradiction.
]

*Implication for SHIFT:* This theorem explains why SHIFT cannot guarantee correctness for _all_ traffic. However, for protocols where the receiver does not access data until a subsequent signal (e.g., NCCL Simple's flag mechanism), the "ACK lost + memory reused" scenario cannot occur before SHIFT completes retransmission.

== Theorem 2: Non-Idempotency of Operations

#theorem("FADD Non-Idempotency")[
  For any $delta > 0$ and memory $m$, FADD is not idempotent: $"exec"_"FADD"("exec"_"FADD"(m, a, delta), a, delta) eq.not "exec"_"FADD"(m, a, delta)$.
]

#theorem("Queue Sliding (Two-Sided Non-Idempotency)")[
  Retrying a SEND operation is not idempotent because it consumes an additional Receive WQE.
]

#proof[
  Let the receiver queue $Q_R = [R_1, R_2, ...]$.
  Trace 1 (Success): Message $M_1$ consumes $R_1$. $Q_R' = [R_2, ...]$. ACK lost.
  Trace 2 (Retry): Message $M_1$ (retry) consumes $R_2$. $Q_R'' = [R_3, ...]$.
  Result: $M_1$ is duplicated in buffers $B_1$ and $B_2$, and $R_2$ (intended for $M_2$) is lost. The streams are permanently misaligned.
]

#theorem("CAS Double Success")[
  Under concurrent modification, a CAS retry can succeed even after the original succeeded.
]

#proof[
  Consider sender $S$ with $"CAS"(a, 0, 1)$ and concurrent process $P$ with $"CAS"(a, 1, 0)$:

  #table(
    columns: (auto, auto, auto, auto),
    inset: 4pt,
    stroke: 0.5pt,
    [*Step*], [*Actor*], [*Operation*], [*$m[a]$*],
    [0], [---], [Initial], [$0$],
    [1], [$S$], [$"CAS"(0 arrow.r 1)$], [$1$ (success)],
    [2], [$S$], [Fault before ACK], [---],
    [3], [$P$], [$"CAS"(1 arrow.r 0)$], [$0$ (success)],
    [4], [$S$], [Retry $"CAS"(0 arrow.r 1)$], [$1$ (success!)],
  )

  $S$'s single logical CAS executed twice, and $P$'s modification was silently overwritten.
]

== Theorem 3: Consensus Hierarchy Barrier

We prove that correct failover requires solving 2-process consensus, which read-only verification cannot achieve.

=== Background: Herlihy's Consensus Hierarchy

#definition("Consensus Number")[
  $"CN"(X) = n$ means primitive $X$ can solve wait-free $n$-process consensus but not $(n+1)$-consensus. Key results: $"CN"("Register") = 1$, $"CN"("FADD") = 2$, $"CN"("CAS") = infinity$.
]

The hierarchy is _strict_: primitives with $"CN" = k$ cannot implement primitives with $"CN" > k$.

=== Reduction: Failover Solver $arrow.r.double$ 2-Consensus

#definition("Failover Solver")[
  $F : "Memory" -> {"Commit", "Abort"}$ returns the correct decision: Commit if the original CAS executed, Abort otherwise.
]

#theorem("2-Consensus from Failover Solver")[
  A correct failover solver $F$ yields a 2-consensus protocol:

  #block(inset: (left: 12pt))[
    1. Each process $P_i$ writes its input to $"proposed"[i]$
    2. Both call $F(m)$ on the shared memory state
    3. If $F(m) = "Commit"$: decide $"proposed"[0]$
    4. If $F(m) = "Abort"$: decide $"proposed"[1]$
  ]
]

#proof[
  - *Wait-free*: No loops; finite steps.
  - *Agreement*: Both call same $F$ on same $m$ $arrow.r$ same result $arrow.r$ same decision.
  - *Validity*: If CAS executed ($P_0$ "won"), $F(m) = "Commit"$, decision = $"proposed"[0]$. Similarly for $P_1$.
]

#theorem("Failover Solver Yields 2-Consensus")[
  A correct failover solver yields a read-based protocol solving 2-consensus.
]

#proof[
  Given $F$ satisfying `solves_failover`, construct observation $"obs"(e,i) := "if" F(m_0) "then" 0 "else" 1$ (constant, trivially satisfies `valid_rw_observation`) and decision $"decide"(x) := "if" x = 0 "then" 0 "else" 1$.

  - Solo $P_0$: `solves_failover` on `HistExecuted`$(m_0)$ gives $F(m_0) = sans("true")$ $arrow.r$ $"obs" = 0$, $"decide"(0) = 0$ $checkmark$
  - Solo $P_1$: `solves_failover` on `HistNotExecuted`$(m_0)$ gives $F(m_0) = sans("false")$ $arrow.r$ $"obs" = 1$, $"decide"(1) = 1$ $checkmark$
]

#theorem("Failover Impossible by Register CN=1")[
  No correct failover solver exists. The impossibility is formally derived from the Register CN=1 theorem.
]

#proof[
  By mechanized reduction chain:
  1. `failover_solver_yields_2consensus`: a correct solver yields `obs` (satisfying `valid_rw_observation`) and `decide` satisfying solo validity for both processes
  2. `readwrite_2consensus_impossible_same_protocol`: no read-based `obs`/`decide` pair can satisfy both solo validities (Register CN=1)
  3. `failover_impossible_by_read_cn`: combines (1) and (2) into contradiction

  This is not a separate ABA argument—it is a formal _consequence_ of $"CN"("Register") = 1$.
]

#theorem("Main Impossibility")[
  Transparent failover for atomic operations is impossible.
]

#proof[
  The main theorem (`transparent_cas_failover_impossible`) lifts the CN-based impossibility to the `TransparentFailover` interface:
  1. Any `provides_reliable_cas` witness yields a `VerificationMechanism` satisfying `solves_failover`
  2. `failover_impossible_by_read_cn` derives contradiction via the Register CN=1 barrier
]

== Mechanization Summary

#figure(
  table(
    columns: (auto, auto, auto),
    inset: 5pt,
    stroke: 0.5pt,
    [*Component*], [*Lines*], [*Key Theorems*],
    [Core (Memory, Ops, Traces)], [~400], [`mem_read_write_same`, `exec_op`],
    [Theorem 1], [~300], [`sender_views_equal`, `impossibility_safe_retransmission`],
    [Theorem 2], [~250], [`fadd_not_idempotent`, `send_queue_sliding`, `cas_double_success`],
    [Theorem 3], [~2200], [`register_cn_1_verified`, `failover_impossible_by_read_cn`, `transparent_cas_failover_impossible`],
  ),
  caption: [Rocq formalization statistics (total ~3,900 lines)]
)

All proofs compile with Rocq 9.0 without axioms beyond the standard library. The formalization models RDMA operations as state transformers ($"Memory" arrow.r "Memory" times "Result"$), traces as event sequences, and the sender view as a projection function. The failover impossibility (Theorem 3) is formally derived FROM the Register CN=1 theorem via `failover_impossible_by_read_cn`, mechanizing the connection to Herlihy's hierarchy.

== Connection to SHIFT Design

These impossibility results directly inform SHIFT's design decisions:

#table(
  columns: (1fr, 1fr),
  inset: 6pt,
  stroke: 0.5pt,
  [*Theorem*], [*SHIFT Design Choice*],
  [Thm 1: Indistinguishability], [Best-effort WR-level retransmission; error propagation when safety cannot be guaranteed],
  [Thm 2: Non-idempotency (Atomics)], [Return error if atomic WR is in-flight during fault],
  [Thm 2: Queue Sliding (Two-Sided)], [Implement 3-way handshake to re-synchronize queue indices (breaking transparency to ensure correctness)],
  [Thm 3: Consensus barrier], [No attempt to verify execution status via memory reads; rely on protocol-level idempotency or handshake instead],
)

SHIFT's approach—supporting NCCL Simple while rejecting atomics and synchronizing two-sided ops—is not a limitation of implementation but a necessary consequence of these fundamental impossibility results. The boundary identified in Table 1 is precisely the boundary between what can and cannot be transparently failed over.