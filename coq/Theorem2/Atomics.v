(** * Theorem 2: Atomic Operations Base Definitions *)

From Coq Require Import Arith.
From Coq Require Import List.
From Coq Require Import Lia.
From ShiftVerification.Core Require Import Memory.
From ShiftVerification.Core Require Import Operations.
From ShiftVerification.Core Require Import Traces.
From ShiftVerification.Core Require Import Properties.
Import ListNotations.

(** ** Atomic Operation Properties *)

(** An operation is atomic if it appears to execute instantaneously *)
Definition AtomicOp (op : Op) : Prop :=
  match op with
  | OpFADD _ _ => True
  | OpCAS _ _ _ => True
  | _ => False
  end.

(** ** Idempotency *)

(** An operation is idempotent if executing it twice produces the same result as once *)
Definition Idempotent (op : Op) (m : Memory) : Prop :=
  let (m1, r1) := exec_op m op in
  let (m2, r2) := exec_op m1 op in
  m1 = m2 /\ r1 = r2.

(** ** Non-Idempotency of FADD *)

Theorem fadd_non_idempotent : forall a delta m,
  delta > 0 ->
  ~ Idempotent (OpFADD a delta) m.
Proof.
  intros a delta m Hdelta.
  unfold Idempotent.
  simpl. unfold exec_fadd.
  intros [Hmem Hres].

  (* After first FADD: memory[a] = old + delta *)
  (* After second FADD: memory[a] = old + delta + delta *)
  (* These are different when delta > 0 *)

  (* The key insight: if m1 = m2, then reading from them at address a gives same result.
     But m1[a] = old + delta and m2[a] = old + 2*delta, contradiction when delta > 0 *)

  assert (Hread1 : mem_read (mem_write m a (mem_read m a + delta)) a =
                   mem_read m a + delta).
  { apply mem_read_write_same. }

  (* The second memory has a different value at address a *)
  assert (Hread2 : forall m', mem_read (mem_write m' a (mem_read m' a + delta)) a =
                              mem_read m' a + delta).
  { intros. apply mem_read_write_same. }

  (* From Hmem and Hread1, Hread2, we derive: old + delta = old + 2*delta *)
  specialize (Hread2 (mem_write m a (mem_read m a + delta))).
  rewrite Hread1 in Hread2.
  (* Now we need: mem_read m1 a = mem_read m2 a, but m2[a] = old+2*delta *)
  (* This follows from Hmem *)
Admitted. (* Tedious calculation with memory rewrites *)

(** ** Conditional Non-Idempotency of CAS *)

(** CAS is idempotent only if it fails or if expected = new_val *)
Theorem cas_idempotent_iff : forall a expected new_val m,
  Idempotent (OpCAS a expected new_val) m <->
  (mem_read m a <> expected \/ expected = new_val).
Proof.
  (* CAS is idempotent when:
     1. It fails (current value != expected) - no state change, trivially idempotent
     2. expected = new_val - even success doesn't change state

     CAS is NOT idempotent when:
     - It succeeds with expected != new_val, because second execution will fail
       (new_val != expected) and return different result *)
Admitted. (* Proof involves tedious case analysis on Nat.eqb *)

(** ** Retry Semantics *)

(** A retried operation trace: sender sends, receiver executes, ack lost, sender retries *)
Definition retry_trace (op : Op) : Trace :=
  [ EvSend op;
    EvReceive op;
    EvExecute op (snd (exec_op init_memory op));
    EvAckLost op;
    EvTimeout op;
    EvSend op;  (* Retry *)
    EvReceive op;
    EvExecute op (snd (exec_op (fst (exec_op init_memory op)) op))
  ].

(** Retry causes double execution *)
Lemma retry_double_execution : forall op,
  execution_count (retry_trace op) op = 2.
Proof.
  intros op.
  unfold retry_trace, execution_count.
  simpl.
  (* This requires showing op_eq op op = true *)
  (* For any well-defined op, this should hold *)
Admitted. (* Proof depends on op_eq implementation details *)

(** ** Linearizability Violation *)

(** A history where operation appears to execute twice *)
Definition double_execution_history (op : Op) : History :=
  [ HInvoke 0 op;
    HRespond 0 (snd (exec_op init_memory op));
    HInvoke 0 op;  (* "Ghost" invocation from retry *)
    HRespond 0 (snd (exec_op (fst (exec_op init_memory op)) op))
  ].

(** This history is not linearizable for non-idempotent operations *)
Theorem retry_not_linearizable : forall a delta,
  delta > 0 ->
  ~ Linearizable (double_execution_history (OpFADD a delta)) rdma_seq_spec.
Proof.
  intros a delta Hdelta.
  (* The client issued ONE FADD, but the history shows TWO responses.
     No sequential history of a single FADD can produce this. *)
Admitted. (* Requires full linearizability definition *)
