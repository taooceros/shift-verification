# Coq Verification Plan for SHIFT

This document outlines the concrete steps to formalize the theoretical claims of the SHIFT paper in Coq.

## Phase 1: System Model & Semantics
**Goal:** Define the operational semantics of RDMA operations, focusing on side effects (Memory vs. Queue).

### 1.1 State and Operations (`coq/Core/Model.v`)
```coq
(* Abstract Addresses and Values *)
Parameter Addr : Type.
Parameter Val : Type.

(* The State of the Receiver *)
Record State := {
  mem : Addr -> Val;      (* Remote Memory *)
  rq  : list Addr;        (* Receive Queue: List of buffer addresses *)
}.

(* RDMA Operations *)
Inductive Op :=
  | Write (addr : Addr) (val : Val)
  | Send (val : Val)               (* Two-sided Send *)
  | AtomicFADD (addr : Addr) (delta : nat).

(* Execution Result *)
Inductive Result :=
  | Ok
  | OpFailed
  | RNR. (* Receiver Not Ready - No WQE *)
```

### 1.2 Operational Semantics (`coq/Core/Semantics.v`)
Define the `step` function: `Op -> State -> (State * Result)`.

- **Write:** Updates `mem`. No effect on `rq`.
- **Send:** 
  - If `rq` is empty -> Return `(state, RNR)`.
  - If `rq = b :: rest` -> Update `mem[b] = val`, set `rq = rest`, return `(new_state, Ok)`.
  (* Key Insight: Send consumes a resource even if the payload is just data *)
- **Atomic:** Updates `mem` based on previous value.

---

## Phase 2: Theorem 1 - Indistinguishability (The Sender's Dilemma)
**Goal:** Prove that a transparent sender cannot distinguish "Packet Lost" from "ACK Lost".

### 2.1 Trace Definitions (`coq/Theorem1/Trace.v`)
- Define `Event`: `Packet(op)`, `Ack`, `Timeout`.
- Define `Trace`: `list Event`.
- Define `SenderView`: A projection of the trace visible to the sender (Sends and Timeouts/Acks, but not internal Receiver states).

### 2.2 The Indistinguishability Theorem (`coq/Theorem1/Proof.v`)
**Theorem:** `exists t1 t2, (t1 <> t2) /\ (SenderView t1 = SenderView t2)`.
- **Trace 1 (Packet Loss):** `[Send(Op); Drop]` -> Sender sees Timeout. Receiver state unchanged.
- **Trace 2 (ACK Loss):** `[Send(Op); Execute(Op); Ack; Drop]` -> Sender sees Timeout. Receiver state changed.

**Implication:** A transparent sender $S$ cannot know if the state changed.

---

## Phase 3: Theorem 2 - Queue Sliding (The "Send" Impossibility)
**Goal:** Formalize the "Queue Sliding" failure mode for two-sided operations.

### 3.1 Resource Consumption Lemma (`coq/Theorem2/QueueSliding.v`)
**Lemma:** `send_consumption`.
Executing `Send` $N$ times consumes $N$ Receive Queue elements.

```coq
Lemma retry_is_destructive : forall s v,
  let (s1, _) := step (Send v) s in     (* First attempt *)
  let (s2, _) := step (Send v) s1 in    (* Retry *)
  length s2.rq < length s1.rq.
```

### 3.2 The Sliding Theorem
**Theorem:** `transparent_retry_breaks_alignment`.
- If a sender retries a `Send` due to ACK loss (Trace 2 from Thm 1):
  - The Receiver processes `Send` twice.
  - Two WQEs are consumed for one logical message.
  - **Result:** Future messages map to the wrong buffers ($M_i \to B_{i+1}$). 

This formally justifies the need for SHIFT's **3-way Handshake** to resynchronize sequence numbers and queue pointers.

---

## Phase 4: Theorem 3 - The Consensus Barrier
**Goal:** Prove that solving the ambiguity from Thm 1 requires non-transparent mechanisms.

### 4.1 Reduction (`coq/Theorem3/Consensus.v`)
- Show that reliably determining "Did Op Commit?" is equivalent to solving Consensus on the value "Commit" vs "Abort".
- Since RDMA is asynchronous and liable to faults, and pure transparency implies no receiver participation (effectively a "wait-free" requirement on the sender using only reads), we hit the FLP impossibility or Herlihy's hierarchy limits (Reads have consensus number 1).


## Plan of Action

1.  **Setup:** Initialize Coq project structure (`_CoqProject`, `Makefile`).
2.  **Core:** Implement `Model.v` and `Semantics.v`.
3.  **Thm 1:** Prove `indistinguishability`.
4.  **Thm 2:** Prove `queue_sliding` (Critical for SHIFT paper).
5.  **Thm 3:** Sketch the Consensus reduction (Lower priority, theoretical standard).
6.  **Review:** Verify that the definitions match the text in `SHIFT_structure.typ` and `theory_appendix.typ`.
