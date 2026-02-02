(** * RDMA Operations *)

From Coq Require Import Arith.
From Coq Require Import List.
From Coq Require Import Lia.
From ShiftVerification.Core Require Import Memory.
Import ListNotations.

(** ** Operation Types *)

(** RDMA operations supported by the system *)
Inductive Op : Type :=
  | OpWrite : Addr -> Val -> Op       (* RDMA Write *)
  | OpRead : Addr -> Op               (* RDMA Read *)
  | OpFADD : Addr -> nat -> Op        (* Fetch-and-Add *)
  | OpCAS : Addr -> Val -> Val -> Op. (* Compare-and-Swap: addr, expected, new *)

(** ** Operation Results *)

Inductive OpResult : Type :=
  | ResWriteAck : OpResult                    (* Write completed *)
  | ResReadVal : Val -> OpResult              (* Read returned value *)
  | ResFADDVal : Val -> OpResult              (* FADD returned old value *)
  | ResCASResult : bool -> Val -> OpResult.   (* CAS: success flag, old value *)

(** ** Operation Semantics *)

(** Execute a write operation *)
Definition exec_write (m : Memory) (a : Addr) (v : Val) : Memory * OpResult :=
  (mem_write m a v, ResWriteAck).

(** Execute a read operation *)
Definition exec_read (m : Memory) (a : Addr) : Memory * OpResult :=
  (m, ResReadVal (mem_read m a)).

(** Execute a fetch-and-add operation *)
Definition exec_fadd (m : Memory) (a : Addr) (delta : nat) : Memory * OpResult :=
  let old_val := mem_read m a in
  let new_val := old_val + delta in
  (mem_write m a new_val, ResFADDVal old_val).

(** Execute a compare-and-swap operation *)
Definition exec_cas (m : Memory) (a : Addr) (expected new_val : Val) : Memory * OpResult :=
  let old_val := mem_read m a in
  if Nat.eqb old_val expected then
    (mem_write m a new_val, ResCASResult true old_val)
  else
    (m, ResCASResult false old_val).

(** General operation execution *)
Definition exec_op (m : Memory) (op : Op) : Memory * OpResult :=
  match op with
  | OpWrite a v => exec_write m a v
  | OpRead a => exec_read m a
  | OpFADD a delta => exec_fadd m a delta
  | OpCAS a exp new_v => exec_cas m a exp new_v
  end.

(** ** Operation Properties *)

(** Writes are idempotent: executing the same write twice yields the same memory state *)
Lemma write_idempotent : forall m a v,
  fst (exec_write (fst (exec_write m a v)) a v) = fst (exec_write m a v).
Proof.
  intros. simpl. apply mem_write_write_same.
Qed.

(** FADD is NOT idempotent *)
Lemma fadd_not_idempotent : forall m a delta,
  delta <> 0 ->
  fst (exec_fadd (fst (exec_fadd m a delta)) a delta) <> fst (exec_fadd m a delta).
Proof.
  intros m a delta Hdelta.
  unfold exec_fadd. simpl.
  intro H.
  assert (Hread1: mem_read (mem_write m a (mem_read m a + delta)) a = mem_read m a + delta).
  { apply mem_read_write_same. }
  assert (Hfinal: mem_read (mem_write (mem_write m a (mem_read m a + delta)) a
                            (mem_read (mem_write m a (mem_read m a + delta)) a + delta)) a =
                  mem_read m a + delta + delta).
  { rewrite mem_read_write_same. rewrite Hread1. reflexivity. }
  assert (Hsingle: mem_read (mem_write m a (mem_read m a + delta)) a = mem_read m a + delta).
  { apply mem_read_write_same. }
  (* If memories are equal, their reads at a must be equal *)
  assert (Heq: mem_read (mem_write (mem_write m a (mem_read m a + delta)) a
                          (mem_read (mem_write m a (mem_read m a + delta)) a + delta)) a =
               mem_read (mem_write m a (mem_read m a + delta)) a).
  { rewrite H. reflexivity. }
  rewrite Hfinal in Heq.
  rewrite Hsingle in Heq.
  lia.
Qed.

(** CAS that succeeds is NOT idempotent (state changes) *)
Lemma cas_success_changes_state : forall m a expected new_val,
  mem_read m a = expected ->
  expected <> new_val ->
  mem_read (fst (exec_cas m a expected new_val)) a <> mem_read m a.
Proof.
  intros m a expected new_val Hexpect Hdiff.
  unfold exec_cas.
  rewrite Hexpect.
  rewrite Nat.eqb_refl.
  simpl.
  rewrite mem_read_write_same.
  lia.
Qed.

(** CAS that fails is idempotent (no state change) *)
Lemma cas_fail_idempotent : forall m a expected new_val,
  mem_read m a <> expected ->
  fst (exec_cas m a expected new_val) = m.
Proof.
  intros.
  unfold exec_cas.
  destruct (Nat.eqb_spec (mem_read m a) expected).
  - contradiction.
  - reflexivity.
Qed.
