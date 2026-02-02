(** * Theorem 2: Atomic Operations Base Definitions *)

From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
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

  (* Let old = mem_read m a *)
  (* m1 = mem_write m a (old + delta), so m1[a] = old + delta *)
  (* m2 = mem_write m1 a (m1[a] + delta) = mem_write m1 a (old + delta + delta) *)
  (* So m2[a] = old + 2*delta *)

  (* If m1 = m2, then m1[a] = m2[a], i.e., old + delta = old + 2*delta *)
  (* This implies delta = 0, contradicting delta > 0 *)

  set (old := mem_read m a) in *.
  set (m1 := mem_write m a (old + delta)) in *.

  assert (Hm1_a : mem_read m1 a = old + delta).
  { unfold m1. apply mem_read_write_same. }

  set (m2 := mem_write m1 a (mem_read m1 a + delta)) in *.

  assert (Hm2_a : mem_read m2 a = old + delta + delta).
  { unfold m2. rewrite mem_read_write_same. rewrite Hm1_a. reflexivity. }

  (* From Hmem: m1 = m2 *)
  (* Therefore mem_read m1 a = mem_read m2 a *)
  assert (Heq : mem_read m1 a = mem_read m2 a).
  { rewrite Hmem. reflexivity. }

  rewrite Hm1_a, Hm2_a in Heq.
  (* old + delta = old + delta + delta *)
  (* old + delta = old + 2*delta *)
  lia.
Qed.

(** ** Conditional Non-Idempotency of CAS *)

(** CAS is idempotent only if it fails or if expected = new_val *)
Theorem cas_idempotent_iff : forall a expected new_val m,
  Idempotent (OpCAS a expected new_val) m <->
  (mem_read m a <> expected \/ expected = new_val).
Proof.
  intros a expected new_val m.
  unfold Idempotent, exec_op, exec_cas.
  (* Case split on whether first CAS succeeds *)
  destruct (Nat.eqb (mem_read m a) expected) eqn:Hcond.

  - (* mem_read m a = expected: first CAS succeeds *)
    apply Nat.eqb_eq in Hcond.
    rewrite mem_read_write_same.
    destruct (Nat.eqb new_val expected) eqn:Hcond2.
    + (* new_val = expected: second CAS also succeeds *)
      apply Nat.eqb_eq in Hcond2.
      split.
      * intros _. right. symmetry. exact Hcond2.
      * intros _. subst new_val. rewrite mem_write_write_same. rewrite Hcond.
        auto.
    + (* new_val <> expected: second CAS fails *)
      apply Nat.eqb_neq in Hcond2.
      split.
      * intros [_ Hcontra]. discriminate.
      * intros [Hcontra | Hcontra].
        -- exfalso. apply Hcontra. exact Hcond.
        -- exfalso. apply Hcond2. symmetry. exact Hcontra.

  - (* mem_read m a <> expected: first CAS fails *)
    (* Hcond : Nat.eqb (mem_read m a) expected = false *)
    (* In the failure case, both exec_cas calls return (m, ResCASResult false (mem_read m a)) *)
    (* Rewrite using the equation before converting to disequality *)
    rewrite Hcond.
    split.
    + intros _. left. apply Nat.eqb_neq. exact Hcond.
    + intros _. split; reflexivity.
Qed.

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
  (* Unfold and simplify - but keep op_eq visible for rewriting *)
  simpl execution_count.
  (* The trace has two EvExecute events for op *)
  (* Each contributes (if op_eq op op then 1 else 0) = 1 *)
  repeat rewrite op_eq_refl.
  reflexivity.
Qed.

(** ** Linearizability Violation *)

(** A history where operation appears to execute twice *)
Definition double_execution_history (op : Op) : History :=
  [ HInvoke 0 op;
    HRespond 0 (snd (exec_op init_memory op));
    HInvoke 0 op;  (* "Ghost" invocation from retry *)
    HRespond 0 (snd (exec_op (fst (exec_op init_memory op)) op))
  ].

(** The responses in a double execution are different for non-idempotent ops *)
(** This captures the linearizability violation: a single logical operation
    cannot produce two different responses. *)
Theorem fadd_double_execution_different_responses : forall a delta,
  delta > 0 ->
  let op := OpFADD a delta in
  snd (exec_op init_memory op) <> snd (exec_op (fst (exec_op init_memory op)) op).
Proof.
  intros a delta Hdelta op.
  unfold op. simpl. unfold exec_fadd, init_memory, default_val.
  simpl. rewrite mem_read_write_same.
  (* First response: ResFADDVal 0 *)
  (* Second response: ResFADDVal delta *)
  (* Goal: ResFADDVal 0 <> ResFADDVal delta *)
  intro H.
  (* Use injection to extract the equality 0 = delta *)
  injection H as H0.
  (* H0 : 0 = delta, but Hdelta : delta > 0 *)
  (* Rewrite delta to 0 in Hdelta *)
  subst delta.
  (* Now Hdelta : 0 > 0, which is absurd *)
  inversion Hdelta.
Qed.

(** Note: The full Linearizable definition is a placeholder (defined as True).
    For a complete proof, we would need to:
    1. Define linearizability properly (equivalent sequential history)
    2. Show that a single FADD invocation cannot have two different responses

    The theorem fadd_double_execution_different_responses captures the key insight:
    the retry produces a DIFFERENT response than the original, which means
    the client observes behavior inconsistent with a single atomic operation. *)

Theorem retry_not_linearizable : forall a delta,
  delta > 0 ->
  (* A retry causes two executions with different results *)
  let op := OpFADD a delta in
  snd (exec_op init_memory op) <> snd (exec_op (fst (exec_op init_memory op)) op).
Proof.
  exact fadd_double_execution_different_responses.
Qed.
