(** * Lemma 2: Non-Idempotency *)

(** This lemma proves that certain RDMA operations (Atomics) are non-idempotent,
    meaning blind retransmission violates correct RC semantics. *)

From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Classical.
From ShiftVerification.Core Require Import Memory.
From ShiftVerification.Core Require Import Operations.
From ShiftVerification.Core Require Import Traces.
From ShiftVerification.Core Require Import Properties.
Import ListNotations.

(** ** Definitions *)

(** An operation is atomic/non-idempotent if it appears to execute instantaneously but cannot be safely repeated *)
Definition NonIdempotentOp (op : Op) : Prop :=
  match op with
  | OpFADD _ _ => True
  | OpCAS _ _ _ => True
  | _ => False
  end.

(** Idempotency Definition: executing twice is same as executing once *)
Definition Idempotent (op : Op) (m : Memory) : Prop :=
  let (m1, r1) := exec_op m op in
  let (m2, r2) := exec_op m1 op in
  m1 = m2 /\ r1 = r2.

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
  simpl execution_count.
  repeat rewrite op_eq_refl.
  reflexivity.
Qed.

(** ** FADD Non-Idempotency *)

Theorem fadd_non_idempotent : forall a delta m,
  delta <> 0 ->
  ~ Idempotent (OpFADD a delta) m.
Proof.
  intros a delta m Hdelta.
  unfold Idempotent.
  simpl. unfold exec_fadd.
  intros [Hmem Hres].
  set (old := mem_read m a) in *.
  set (m1 := mem_write m a (old + delta)) in *.
  assert (Hm1_a : mem_read m1 a = old + delta) by (unfold m1; apply mem_read_write_same).
  set (m2 := mem_write m1 a (mem_read m1 a + delta)) in *.
  assert (Hm2_a : mem_read m2 a = old + delta + delta).
  { unfold m2. rewrite mem_read_write_same. rewrite Hm1_a. reflexivity. }
  assert (Heq : mem_read m1 a = mem_read m2 a) by (rewrite Hmem; reflexivity).
  rewrite Hm1_a, Hm2_a in Heq.
  lia.
Qed.

(** ** CAS Non-Idempotency (ABA Problem) *)

(** CAS is idempotent only if it fails or if expected = new_val *)
Theorem cas_idempotent_iff : forall a expected new_val m,
  Idempotent (OpCAS a expected new_val) m <->
  (mem_read m a <> expected \/ expected = new_val).
Proof.
  intros a expected new_val m.
  unfold Idempotent, exec_op, exec_cas.
  destruct (Nat.eqb (mem_read m a) expected) eqn:Hcond.
  - apply Nat.eqb_eq in Hcond.
    rewrite mem_read_write_same.
    destruct (Nat.eqb new_val expected) eqn:Hcond2.
    + apply Nat.eqb_eq in Hcond2. split; [intros _; right; symmetry; exact Hcond2 | intros _; subst new_val; rewrite mem_write_write_same; rewrite Hcond; auto].
    + apply Nat.eqb_neq in Hcond2. split; [intros [_ Hcontra]; discriminate | intros [Hcontra | Hcontra]; [exfalso; apply Hcontra; exact Hcond | exfalso; apply Hcond2; symmetry; exact Hcontra]].
  - rewrite Hcond. split; [intros _; left; apply Nat.eqb_neq; exact Hcond | intros _; split; reflexivity].
Qed.

(** ** Lemma 2: Non-Idempotency *)

Lemma non_idempotent_retry_unsafe : forall op m,
  ~ Idempotent op m ->
  let (m1, r1) := exec_op m op in
  let (m2, r2) := exec_op m1 op in
  m1 <> m2 \/ r1 <> r2.
Proof.
  intros op m Hnot_idem.
  unfold Idempotent in Hnot_idem.
  destruct (exec_op m op) as [m1 r1] eqn:E1.
  destruct (exec_op m1 op) as [m2 r2] eqn:E2.
  destruct (classic (m1 = m2)) as [Hmeq | Hmneq].
  - right. intros Hreq. apply Hnot_idem. split; assumption.
  - left. exact Hmneq.
Qed.
