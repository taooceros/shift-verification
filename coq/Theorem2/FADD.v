(** * Theorem 2 Case A: Fetch-and-Add Violations *)

From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From ShiftVerification.Core Require Import Memory.
From ShiftVerification.Core Require Import Operations.
From ShiftVerification.Core Require Import Traces.
From ShiftVerification.Core Require Import Properties.
From ShiftVerification.Theorem2 Require Import Atomics.
Import ListNotations.

(** ** FADD Retry Scenario *)

Section FADDRetry.

Variable target_addr : Addr.
Variable delta : nat.
Hypothesis delta_pos : delta > 0.

(** Initial state *)
Definition fadd_init : Memory := init_memory.
Definition fadd_op : Op := OpFADD target_addr delta.

(** State after single execution *)
Definition state_after_one : Memory :=
  fst (exec_fadd fadd_init target_addr delta).

(** State after double execution (retry) *)
Definition state_after_two : Memory :=
  fst (exec_fadd state_after_one target_addr delta).

(** ** Key Lemmas *)

Lemma single_fadd_value :
  mem_read state_after_one target_addr = delta.
Proof.
  unfold state_after_one, exec_fadd, fadd_init, init_memory, default_val.
  simpl. rewrite mem_read_write_same. lia.
Qed.

Lemma double_fadd_value :
  mem_read state_after_two target_addr = 2 * delta.
Proof.
  unfold state_after_two, state_after_one, exec_fadd, fadd_init, init_memory, default_val.
  simpl.
  rewrite mem_read_write_same.
  rewrite mem_read_write_same.
  lia.
Qed.

(** ** Violation Theorem *)

(** The application issued ONE FADD(delta).
    Expected final state: initial + delta = delta (since initial = 0).
    Actual final state after retry: initial + 2*delta = 2*delta.
    This is incorrect. *)

Theorem fadd_retry_state_corruption :
  mem_read state_after_two target_addr <> mem_read state_after_one target_addr.
Proof.
  rewrite single_fadd_value.
  rewrite double_fadd_value.
  lia.
Qed.

(** The return value is also wrong *)
Lemma fadd_first_return :
  snd (exec_fadd fadd_init target_addr delta) = ResFADDVal 0.
Proof.
  unfold exec_fadd, fadd_init, init_memory, default_val.
  simpl. reflexivity.
Qed.

Lemma fadd_second_return :
  snd (exec_fadd state_after_one target_addr delta) = ResFADDVal delta.
Proof.
  unfold exec_fadd, state_after_one.
  simpl.
  rewrite mem_read_write_same.
  reflexivity.
Qed.

(** If the sender sees only the second return value (first was lost),
    it believes the old value was delta, not 0. This is incorrect. *)
Theorem fadd_retry_return_corruption :
  snd (exec_fadd state_after_one target_addr delta) <> snd (exec_fadd fadd_init target_addr delta).
Proof.
  rewrite fadd_first_return.
  rewrite fadd_second_return.
  (* ResFADDVal delta <> ResFADDVal 0 when delta > 0 *)
  intro H. inversion H.
  (* H0 : delta = 0, but we have delta > 0 *)
  lia.
Qed.

End FADDRetry.

(** ** At-Most-Once Violation *)

Theorem fadd_retry_violates_at_most_once : forall a delta,
  delta > 0 ->
  ~ AtMostOnce (retry_trace (OpFADD a delta)).
Proof.
  intros a delta Hdelta.
  unfold AtMostOnce.
  intros H.
  specialize (H (OpFADD a delta)).
  (* retry_trace executes the operation twice *)
  assert (Hcount : execution_count (retry_trace (OpFADD a delta)) (OpFADD a delta) = 2).
  { apply retry_double_execution. }
  rewrite Hcount in H.
  lia.
Qed.

(** ** Concrete Example *)

Example fadd_example :
  let a := 0 in
  let delta := 1 in
  let m0 := init_memory in
  let (m1, r1) := exec_fadd m0 a delta in
  let (m2, r2) := exec_fadd m1 a delta in
  (* After one FADD: value = 1, return = 0 *)
  (* After two FADDs: value = 2, return = 1 *)
  mem_read m1 a = 1 /\
  mem_read m2 a = 2 /\
  r1 = ResFADDVal 0 /\
  r2 = ResFADDVal 1.
Proof.
  simpl. unfold exec_fadd, init_memory, default_val, mem_read, mem_write.
  repeat split; reflexivity.
Qed.
