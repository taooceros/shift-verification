# Coq Verification Plan for RDMA Failover Impossibility Proofs

## Overview

This document outlines the strategy for formalizing and verifying the three impossibility theorems in Coq.

---

## Phase 1: Core Definitions and Infrastructure

### 1.1 System Model

```coq
(* Memory locations and values *)
Parameter Addr : Type.
Parameter Val : Type.

(* Memory state *)
Definition Memory := Addr -> Val.

(* Operations *)
Inductive Op :=
  | Write : Addr -> Val -> Op
  | Read : Addr -> Op
  | FADD : Addr -> nat -> Op
  | CAS : Addr -> Val -> Val -> Op.

(* Operation results *)
Inductive OpResult :=
  | WriteAck
  | ReadVal : Val -> OpResult
  | FADDVal : Val -> OpResult
  | CASResult : bool -> Val -> OpResult.
```

### 1.2 Execution Traces

```coq
(* Events in a trace *)
Inductive Event :=
  | Send : Op -> Event
  | Receive : Op -> Event
  | Execute : Op -> OpResult -> Event
  | Timeout : Event
  | AckLost : Event
  | PacketLost : Event.

Definition Trace := list Event.

(* Observation function: what the sender sees *)
Definition SenderObservation := list (Op * option OpResult).
```

### 1.3 Properties

```coq
(* Linearizability - using existing formalizations *)
(* Reference: Iris library or custom definition *)

Definition Linearizable (history : Trace) : Prop := ...

(* Safety and Liveness *)
Definition Safe (overlay : Overlay) : Prop :=
  forall trace, ValidExecution trace -> Linearizable trace.

Definition Live (overlay : Overlay) : Prop :=
  forall op, eventually_completes op.
```

---

## Phase 2: Theorem 1 - Indistinguishability Proof

### 2.1 Key Definitions

```coq
(* Silent receiver: no application-level acks *)
Definition SilentReceiver (r : Receiver) : Prop :=
  forall op, ~ sends_app_ack r op.

(* Memory reuse property *)
Definition MemoryReuse (trace : Trace) : Prop :=
  exists t1 t2 addr v1 v2,
    t1 < t2 /\
    at_time t1 (Consume addr v1) trace /\
    at_time t2 (Reuse addr v2) trace.

(* Indistinguishability *)
Definition Indistinguishable (t1 t2 : Trace) : Prop :=
  sender_observation t1 = sender_observation t2.
```

### 2.2 Proof Structure

```coq
(* Construct the two traces *)
Definition T1_packet_loss : Trace := [...].
Definition T2_ack_loss : Trace := [...].

(* Prove indistinguishability *)
Lemma traces_indistinguishable :
  Indistinguishable T1_packet_loss T2_ack_loss.

(* Prove conflicting requirements *)
Lemma T1_requires_retransmit :
  Live overlay -> must_retransmit overlay T1_packet_loss.

Lemma T2_forbids_retransmit :
  Safe overlay -> ~ must_retransmit overlay T2_ack_loss.

(* Main theorem *)
Theorem impossibility_pure_write :
  forall overlay,
    SilentReceiver R ->
    MemoryReuse ->
    ~ ExactlyOnceDelivery transport ->
    Transparent overlay ->
    ~ (Safe overlay /\ Live overlay).
Proof.
  intros.
  (* Use indistinguishability + conflicting requirements *)
  destruct (decide_retransmit overlay) as [Hretrans | Hno_retrans].
  - (* If retransmit: violates safety in T2 *)
    apply T2_forbids_retransmit in Hretrans.
    contradiction.
  - (* If no retransmit: violates liveness in T1 *)
    apply T1_requires_retransmit.
    assumption.
Qed.
```

---

## Phase 3: Theorem 2 - Non-Idempotency Proof

### 3.1 Atomic Operation Semantics

```coq
(* FADD semantics *)
Definition fadd_step (addr : Addr) (delta : nat) (m : Memory) : Memory * Val :=
  let old := m addr in
  (update m addr (old + delta), old).

(* CAS semantics *)
Definition cas_step (addr : Addr) (expected new_val : Val) (m : Memory)
  : Memory * (bool * Val) :=
  let old := m addr in
  if old =? expected
  then (update m addr new_val, (true, old))
  else (m, (false, old)).
```

### 3.2 Proof Structure

```coq
(* Non-idempotency of FADD *)
Lemma fadd_not_idempotent :
  forall addr delta m,
    delta <> 0 ->
    fadd_step addr delta (fst (fadd_step addr delta m)) <>
    fadd_step addr delta m.

(* Linearizability violation *)
Definition valid_linearization (ops : list Op) (final : Memory) : Prop := ...

Theorem fadd_retry_violates_linearizability :
  forall addr delta m,
    let (m1, _) := fadd_step addr delta m in
    let (m2, _) := fadd_step addr delta m1 in
    ~ valid_linearization [FADD addr delta] m2.

(* CAS with concurrent modification *)
Theorem cas_retry_with_interleaving :
  forall addr,
    exists trace,
      has_concurrent_cas trace /\
      retry_succeeds trace /\
      ~ Linearizable trace.
```

---

## Phase 4: Theorem 3 - Consensus Hierarchy

### 4.1 Consensus Number Definitions

```coq
(* Based on Herlihy's wait-free hierarchy *)

(* Consensus object specification *)
Record Consensus := {
  propose : Val -> Val;
  validity : forall v, propose v = v \/ exists v', propose v = v';
  agreement : forall v1 v2, propose v1 = propose v2;
}.

(* Consensus number *)
Definition ConsensusNumber (obj : Object) : nat + infinity := ...

(* Known consensus numbers *)
Axiom register_consensus_1 : ConsensusNumber Register = 1.
Axiom cas_consensus_inf : ConsensusNumber CAS = infinity.
```

### 4.2 Universality Theorem

```coq
(* Herlihy's universality result *)
Theorem herlihy_universality :
  forall obj1 obj2,
    ConsensusNumber obj1 < ConsensusNumber obj2 ->
    ~ can_implement_waitfree obj2 obj1.

(* Apply to our setting *)
Theorem cannot_implement_reliable_cas :
  forall overlay,
    Transparent overlay ->
    uses_only_reads_for_verification overlay ->
    ~ provides_consensus_inf overlay.
Proof.
  intros.
  apply herlihy_universality.
  - exact register_consensus_1.
  - exact cas_consensus_inf.
Qed.
```

---

## Phase 5: Dependencies and Libraries

### 5.1 Recommended Coq Libraries

| Library | Purpose |
|---------|---------|
| `Iris` | Concurrent separation logic, linearizability |
| `stdpp` | Standard library extensions |
| `coq-itree` | Interaction trees for traces |
| `Verdi` | Distributed systems verification |

### 5.2 Installation

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-iris coq-stdpp
```

---

## Phase 6: File Structure

```
shift_verification/
├── proofs.typ              # Typst document
├── coq/
│   ├── _CoqProject
│   ├── Makefile
│   ├── Core/
│   │   ├── Memory.v        # Memory model
│   │   ├── Operations.v    # RDMA operations
│   │   ├── Traces.v        # Execution traces
│   │   └── Properties.v    # Safety, liveness, linearizability
│   ├── Theorem1/
│   │   ├── Indistinguishability.v
│   │   └── Impossibility.v
│   ├── Theorem2/
│   │   ├── Atomics.v
│   │   ├── FADD.v
│   │   └── CAS.v
│   └── Theorem3/
│       ├── ConsensusNumber.v
│       └── Hierarchy.v
```

---

## Phase 7: Estimated Effort

| Component | Complexity | Notes |
|-----------|------------|-------|
| Core definitions | Medium | Standard distributed systems modeling |
| Theorem 1 | Medium | Trace construction + indistinguishability |
| Theorem 2 | Low-Medium | Direct operational semantics |
| Theorem 3 | High | Requires consensus number formalization |

---

## Phase 8: Alternative Approaches

### 8.1 Using TLA+ Instead

For faster prototyping, consider TLA+ model checking:
- Pros: Faster to write, automatic state exploration
- Cons: Not a full proof, bounded model checking

### 8.2 Hybrid Approach

1. Use TLA+ to validate the model and find counterexamples
2. Use Coq to formalize the core impossibility proofs
3. Reference TLA+ traces as "witnesses" in Coq proofs

---

## Next Steps

1. **Immediate**: Set up Coq project structure with `_CoqProject`
2. **Week 1**: Implement `Core/` modules
3. **Week 2**: Formalize Theorem 1 (indistinguishability)
4. **Week 3**: Formalize Theorem 2 (atomics)
5. **Week 4**: Formalize Theorem 3 (consensus hierarchy) - may require external library
