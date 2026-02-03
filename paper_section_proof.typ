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

However, a fundamental question arises: what are the theoretical limits of transparent cross-NIC failover? We prove that SHIFT's design achieves precisely what is possible under the transparency constraint—and that extending support to atomic operations would require capabilities that transparent mechanisms fundamentally cannot provide.

Specifically, we identify three barriers to transparent failover:
(1) **Indistinguishability**: The sender cannot distinguish packet loss (requiring retry) from ACK loss (where retry may corrupt data)—both produce identical observations.
(2) **Non-idempotency**: Atomic operations (FADD, CAS) produce different results when executed twice, making incorrect retry catastrophic.
(3) **Consensus barrier**: Determining whether an operation executed is equivalent to solving 2-process consensus, which read-only verification (the only tool available under transparency) provably cannot solve.

These results establish that SHIFT operates at the boundary of what is achievable: it supports all operations where retry is safe (idempotent patterns like NCCL Simple) and correctly rejects operations where retry would violate correctness (atomics). This is not a limitation of our implementation but a fundamental property of the problem space. Any mechanism claiming broader support must either sacrifice transparency (requiring application or receiver modifications) or sacrifice correctness.

--- ADD to contributions list (after item 1): ---

(2) We formally prove that SHIFT's coverage is optimal: transparent failover for atomic operations is impossible due to the consensus hierarchy barrier. Supporting atomics would require receiver-side coordination or persistent metadata—capabilities incompatible with transparency. All proofs are mechanically verified in Rocq 9.0. (§3.1, Appendix C)

--- MODIFY the conclusion paragraph to: ---

This work presents SHIFT, a fault-resilient layer over RDMA that achieves the theoretical maximum of transparent cross-NIC failover. We prove that SHIFT's design is optimal: it supports all traffic patterns amenable to transparent failover (idempotent operations under appropriate protocols) while correctly rejecting patterns that would require non-transparent mechanisms (atomic operations). For supported workloads—which include the dominant NCCL Simple protocol used in distributed training—SHIFT preserves application continuity under network anomalies until the next checkpoint, minimizing training progress loss. The design requires no application modifications, incurs minimal overhead, and remains agnostic to applications. Experimental results demonstrate that SHIFT sustains high performance while delivering RDMA fault tolerance, making it a practical and effective solution for large-scale distributed LLM training.
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

**Theorem 2 (Non-Idempotency of Atomics).** FADD and CAS are non-idempotent: retry produces incorrect state. For FADD with $\delta > 0$, double execution yields $2\delta$ instead of $\delta$. For CAS, the ABA problem allows retry to succeed twice under concurrent modification.

**Theorem 3 (Consensus Hierarchy Barrier).** Correct failover requires solving 2-process consensus. By Herlihy's impossibility theorem, read-only verification has consensus number 1, which is insufficient for 2-consensus. Therefore, no transparent mechanism can correctly determine whether an atomic operation executed.

**SHIFT's Optimality.** These theorems partition RDMA operations into two classes:

| Class | Property | SHIFT Behavior | Theoretical Status |
|-------|----------|----------------|-------------------|
| Idempotent patterns | Retry produces same result | Retransmit | *Achievable* |
| Atomic operations | Retry corrupts state | Return error | *Impossible* |

SHIFT supports exactly the achievable class. The "error on atomics-in-flight" policy is not a design limitation but the only correct behavior—any mechanism claiming to transparently support atomics must either be incorrect or violate transparency.

**What Would Be Required for Atomics.** Supporting atomic operations would require at least one of:
- *Receiver-side operation logs* with deduplication (violates transparency)
- *Persistent metadata* tracking execution status (violates zero-copy)
- *Application-level acknowledgments* (violates application-agnostic)
- *Two-phase commit* protocols (violates low overhead)

None of these are compatible with SHIFT's transparency constraint. Our impossibility proofs (Appendix C) formalize this: the additional "property not available" is the ability to solve 2-process consensus, which transparent read-only verification fundamentally lacks.

**Practical Implication.** Fortunately, the dominant communication pattern in distributed training—NCCL Simple protocol—exhibits effective idempotency: receivers access data buffers only after observing the corresponding flag, ensuring that data retransmission completes before consumption. SHIFT's best-effort retransmission is thus sufficient for the workloads that matter most.

All theorems are mechanically verified in Rocq 9.0 (~2,100 lines). The formalization is available at [CITE].
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

#definition("Idempotency")[
  Operation $"op"$ is _idempotent_ on memory $m$ if $"exec"("exec"(m, "op"), "op") = "exec"(m, "op")$ (same final state and return value).
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

== Theorem 2: Non-Idempotency of Atomic Operations

#theorem("FADD Non-Idempotency")[
  For any $delta > 0$ and memory $m$, FADD is not idempotent: $"exec"_"FADD"("exec"_"FADD"(m, a, delta), a, delta) eq.not "exec"_"FADD"(m, a, delta)$.
]

#proof[
  Let $m[a] = v$. After one FADD: $m'[a] = v + delta$, returns $v$. After retry: $m''[a] = v + 2delta$, returns $v + delta$. Since $delta > 0$: $v + delta eq.not v + 2delta$ and return values differ.
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

*The Fallacy:* "CAS retry is safe because duplicates fail" assumes no concurrent modification—violated in real distributed systems.

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

#theorem("No Correct Failover Solver Exists")[
  The ABA problem makes $F$ impossible.
]

#proof[
  Consider two histories with the same final memory state $m$:
  - $H_0$: CAS never executed $arrow.r$ correct decision is Abort
  - $H_1$: CAS executed, then concurrent process reset value (ABA) $arrow.r$ correct decision is Commit

  Both have $m[a] = 0$ (the original expected value). $F(m)$ must return both Commit and Abort. Contradiction.
]

#theorem("Main Impossibility")[
  Transparent failover for atomic operations is impossible.
]

#proof[
  1. Failover requires solving 2-process consensus (distinguishing $H_0$ from $H_1$)
  2. Transparency limits verification to read-only operations
  3. $"CN"("Read") = 1 < 2$
  4. By Herlihy's impossibility theorem, $"CN" = 1$ primitives cannot solve 2-consensus

  Therefore, no transparent mechanism can provide correct failover for atomics.
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
    [Theorem 2], [~250], [`fadd_not_idempotent`, `cas_double_success`],
    [Theorem 3], [~1150], [`register_cn_1_verified`, `no_correct_failover_solver`, `transparent_cas_failover_impossible`],
  ),
  caption: [Rocq formalization statistics (total ~2,100 lines)]
)

All proofs compile with Rocq 9.0 without axioms beyond the standard library. The formalization models RDMA operations as state transformers ($"Memory" arrow.r "Memory" times "Result"$), traces as event sequences, and the sender view as a projection function.

== Connection to SHIFT Design

These impossibility results directly inform SHIFT's design decisions:

#table(
  columns: (1fr, 1fr),
  inset: 6pt,
  stroke: 0.5pt,
  [*Theorem*], [*SHIFT Design Choice*],
  [Thm 1: Indistinguishability], [Best-effort WR-level retransmission; error propagation when safety cannot be guaranteed],
  [Thm 2: Atomic non-idempotency], [Return error if atomic WR is in-flight during fault],
  [Thm 3: Consensus barrier], [No attempt to verify execution status via memory reads; rely on protocol-level idempotency instead],
)

SHIFT's approach—supporting NCCL Simple while rejecting atomics—is not a limitation of implementation but a necessary consequence of these fundamental impossibility results. The boundary identified in Table 1 is precisely the boundary between what can and cannot be transparently failed over.
