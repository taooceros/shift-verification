// RDMA Failover Impossibility Proofs
// Typst Document

#set document(title: "Impossibility Results for Transparent RDMA Failover")
#set page(margin: 2.5cm)
#set text(font: "New Computer Modern", size: 11pt)
#set heading(numbering: "1.1")
#set math.equation(numbering: "(1)")

// Theorem environment
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

= Impossibility Results for Transparent RDMA Failover

== Preliminary Definitions

#definition("Silent Receiver")[
  A receiver $R$ that does not send application-level acknowledgments; the sender $S$ relies solely on transport-level signals (e.g., WQE completion status).
]

#definition("Memory Reuse")[
  After consuming data at address $A$, the application at $R$ may immediately reuse $A$ for new data without coordination with $S$.
]

#definition("Transparent Overlay")[
  A failover mechanism that operates without modifying application semantics or allocating additional persistent state in remote memory.
]

#definition("Exactly-Once Delivery")[
  A transport guarantee ensuring each message is delivered exactly once, despite failures.
]

== Theorem 1: Impossibility of Safe Retransmission for Pure-Write Protocols

#theorem(title: "Impossibility of Safe Retransmission")[
  In a system with a Silent Receiver and Memory Reuse, no transparent Sender overlay can guarantee Safety (Linearizability) during failover if the transport does not provide Exactly-Once Delivery semantics.
]

#proof[
  We prove by constructing two execution traces, $cal(T)_1$ and $cal(T)_2$, that are indistinguishable to the Sender $S$ but require mutually exclusive actions to maintain safety.

  *The Protocol (LL128 Abstracted):*

  The application requires strict ordering:
  1. $S$ sends Data: $W_D = "Write"(A_"data", V_1)$
  2. $S$ sends Flag: $W_F = "Write"(A_"flag", 1)$
  3. $R$ (App) polls $A_"flag"$. Upon seeing $1$, it consumes $V_1$ at $A_"data"$
  4. $R$ (App) resets $A_"flag" <- 0$ and may reuse $A_"data"$ for a new value $V_"new"$

  *Trace $cal(T)_1$ (Packet Loss --- Retransmission Required):*
  1. $S$ posts $W_D$
  2. Network Failure: $W_D$ is lost before reaching $R$
  3. $S$ detects timeout/error
  4. State at $R$: $A_"data"$ is untouched
  5. *Required Action:* $S$ MUST retransmit $W_D$ to ensure liveness

  *Trace $cal(T)_2$ (ACK Loss --- Retransmission Fatal):*
  1. $S$ posts $W_D$. $R$ receives $W_D$. $A_"data" <- V_1$
  2. $S$ posts $W_F$. $R$ receives $W_F$. $A_"flag" <- 1$
  3. Application Execution: $R$ (App) sees $1$, consumes $V_1$
  4. Memory Reuse: $R$ (App) modifies $A_"data"$ (e.g., $A_"data" <- V_"new"$)
  5. Network Failure: The ACK for $W_D$ (or $W_F$) is lost
  6. $S$ detects timeout/error
  7. *Observation at $S$:* $S$ sees "Uncompleted WQE" --- identical to $cal(T)_1$

  *The Dilemma:*
  - If $S$ retransmits $W_D$ (as required in $cal(T)_1$):
    - In $cal(T)_2$: $R$ receives stale data $V_1$ at $A_"data"$
    - $R$ currently holds $V_"new"$ at $A_"data"$
    - Result: *Data Corruption (Ghost Write)* --- violates safety

  - If $S$ does not retransmit:
    - In $cal(T)_1$: $R$ never receives the data
    - Result: *Deadlock* --- violates liveness

  Since $S$ cannot distinguish $cal(T)_1$ from $cal(T)_2$ using only transport-level signals, no correct action exists.
]

== Theorem 2: Violation of Linearizability for Retried Atomics

#theorem(title: "Non-Linearizability of Retried Atomics")[
  In a system with concurrent access and no receiver-side deduplication, a transparent overlay cannot guarantee Linearizability for RDMA Atomics under network failure.
]

#proof[
  We assume there exists a correct transparent failover mechanism $cal(M)$ that retransmits atomics upon timeout. We derive a contradiction.

  *Case A: Fetch-and-Add (State Corruption)*

  Let $"Op" = "FADD"("Add" = 1)$ with initial state $v = 0$.

  1. $S$ sends $"Op"$
  2. $R$ receives $"Op"$, updates $v <- v + 1$. New state: $v = 1$
  3. Failure: The ACK from $R$ to $S$ is lost
  4. $S$ observes a timeout
  5. Following $cal(M)$, $S$ retransmits $"Op"$
  6. $R$ executes $"Op"$ again: $v <- v + 1$. New state: $v = 2$

  *Violation:* The operation $"Op"$ was issued once but executed twice. The final state $v = 2$ is invalid for a single FADD. This violates at-most-once semantics.

  *Case B: Compare-and-Swap (Return Value Inconsistency)*

  Let $"Op" = "CAS"("Expect" = 0, "Swap" = 1)$ with initial state $v = 0$.

  1. $S$ sends $"Op"$
  2. $R$ checks $v = 0$, sets $v <- 1$. Returns $"Success"$ ($"OldVal" = 0$)
  3. Failure: The Success ACK is lost
  4. Concurrent modification: A third party $P_3$ executes $"CAS"("Expect" = 1, "Swap" = 0)$, resetting $v <- 0$
  5. $S$ retransmits $"Op"$
  6. $R$ checks $v = 0$, sets $v <- 1$. Returns $"Success"$ ($"OldVal" = 0$)

  *Violation:* $S$ believes its single CAS succeeded once. The actual history is:
  $ S."CAS" -> P_3."CAS" -> S."CAS" $

  The linearization point of $S$'s operation is ambiguous. More critically, $S$ has overwritten $P_3$'s modification without awareness, violating the Atomicity of the concurrent schedule.
]

== Theorem 3: Consensus Hierarchy Impossibility

#theorem(title: "Consensus Hierarchy Barrier")[
  Transparent Failover for RDMA Atomics is impossible because it requires solving Consensus using only Registers.
]

#proof[
  *Premise:* The application relies on RDMA Atomics (e.g., CAS) to solve consensus problems (leader election, lock acquisition). Thus, the RDMA operation provided by the overlay must maintain Consensus Number $infinity$.

  *Failover Coordination:* When a network fault occurs, the Client and the Backup RNIC must agree on the state of the previous operation ("Committed" or "Aborted") to preserve linearizability. This is equivalent to solving the Consensus Problem between the "Past Attempt" and the "Future Attempt."

  *Available Primitives:* Under the transparency constraint, the overlay cannot allocate new persistent state (epoch counters, transaction logs) in remote memory. It can only inspect existing application data via the Backup RNIC.

  *The Observation Limit:* Inspecting application data to infer completion is equivalent to a Read operation. In Herlihy's Hierarchy:
  - Read/Write Registers have Consensus Number $= 1$
  - CAS has Consensus Number $= infinity$

  *Contradiction:* By Herlihy's universality result, it is impossible to implement a primitive with Consensus Number $infinity$ (Reliable CAS) using only primitives with Consensus Number $1$ (Reads for verification) in a wait-free manner.

  *Conclusion:* The existence of a Backup RNIC is irrelevant because, while it can execute CAS, it lacks the shared coordination state required to decide _whether_ to execute it. Thus, transparent failover for Atomics is impossible.
]

== Summary

#table(
  columns: (auto, auto, auto),
  inset: 8pt,
  align: horizon,
  table.header(
    [*Theorem*], [*Core Argument*], [*Impossibility Type*],
  ),
  [1. Pure-Write], [Indistinguishable traces], [Safety vs. Liveness dilemma],
  [2. Atomics], [Non-idempotency], [Linearizability violation],
  [3. Consensus], [Herlihy hierarchy], [Consensus number barrier],
)
