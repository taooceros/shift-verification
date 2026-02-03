// Section for SHIFT Paper: Formal Justification of Cross-NIC Fault Tolerance Boundary
// This file contains two parts:
// 1. Main body text (for §3.1.1 or integrated into §3.1)
// 2. Appendix content (detailed proofs)

// ============================================================================
// PART 1: MAIN BODY (Insert into §3.1 after "We investigated common communication libraries...")
// ============================================================================

/*
=== 3.1.1 Formal Justification

The boundary between supportable and unsupportable operations is not merely empirical—it reflects a fundamental impossibility. We formally prove three theorems that characterize the limits of transparent cross-NIC failover.

**The Core Problem.** When a network anomaly occurs, the sender observes a timeout but cannot determine whether: (a) the packet was lost before execution, requiring retransmission, or (b) the operation executed but the acknowledgment was lost, making retransmission dangerous. Both scenarios produce identical sender observations.

**Theorem 1 (Indistinguishability).** *For any RDMA operation, the sender's observations are identical whether the receiver executed the operation before the fault or the fault occurred before execution.* Formally, let $\sigma(\mathcal{T})$ denote the sender's view of trace $\mathcal{T}$. We construct traces $\mathcal{T}_1$ (packet lost) and $\mathcal{T}_2$ (ACK lost, data consumed) such that $\sigma(\mathcal{T}_1) = \sigma(\mathcal{T}_2)$, yet $\mathcal{T}_1$ requires retransmission while $\mathcal{T}_2$ forbids it.

For idempotent operations (e.g., RDMA Write to unconsumed buffers), this ambiguity is harmless—retry produces the same result. For non-idempotent operations, it is fatal.

**Theorem 2 (Non-Idempotency of Atomics).** *FADD with $\delta > 0$ is non-idempotent: executing twice yields $2\delta$ instead of $\delta$. CAS retry can succeed twice under concurrent modification (the ABA problem).*

Consider a sender S issuing CAS$(0 \rightarrow 1)$. If a concurrent process P resets the value to 0 between the original execution and the retry, both CAS operations succeed—violating at-most-once semantics.

**Theorem 3 (Consensus Hierarchy Barrier).** *Correct failover requires solving 2-process consensus. Read-only verification has consensus number 1. By Herlihy's impossibility theorem, transparent failover for atomic operations is impossible.*

The failover decision—whether the original operation executed—is structurally equivalent to 2-process consensus: two possible histories require different decisions, but the observable state (memory content) may be identical due to the ABA problem. Following Herlihy's methodology, we prove that a correct failover solver would yield a 2-consensus protocol, but read-only primitives (CN=1) cannot solve 2-consensus.

**Implications.** These theorems formally justify Table 1: NCCL Simple is resilient because the receiver accesses data only after the flag write completes (making the data write effectively idempotent from the application's perspective), while atomic-based protocols are fundamentally unsupportable. SHIFT's design—returning an error when atomic WRs are in-flight—is not a limitation but a necessary consequence of these impossibility results.

All theorems are mechanically verified in Rocq 9.0; the complete formalization is available at [CITE].
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
