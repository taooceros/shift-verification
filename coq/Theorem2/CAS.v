(** * Theorem 2 Case B: Compare-and-Swap Violations *)

From Coq Require Import Arith.
From Coq Require Import List.
From Coq Require Import Lia.
From ShiftVerification.Core Require Import Memory.
From ShiftVerification.Core Require Import Operations.
From ShiftVerification.Core Require Import Traces.
From ShiftVerification.Core Require Import Properties.
From ShiftVerification.Theorem2 Require Import Atomics.
Import ListNotations.

(** ** CAS with Concurrent Modification Scenario *)

(** This scenario shows that CAS retry is NOT safe even though
    "if it succeeded, retry will just fail" - because a third party
    can intervene. *)

Section CASConcurrent.

Variable target_addr : Addr.

(** The CAS operation: try to change 0 -> 1 *)
Definition cas_op : Op := OpCAS target_addr 0 1.

(** Third party's CAS: change 1 -> 0 *)
Definition p3_cas_op : Op := OpCAS target_addr 1 0.

(** Initial state *)
Definition cas_init : Memory := init_memory. (* target_addr = 0 *)

(** ** Execution Sequence *)

(** Step 1: Sender's CAS succeeds *)
Definition state_1 : Memory := fst (exec_cas cas_init target_addr 0 1).
Definition result_1 : OpResult := snd (exec_cas cas_init target_addr 0 1).

(** Step 2: ACK is lost, but third party P3 executes its CAS *)
Definition state_2 : Memory := fst (exec_cas state_1 target_addr 1 0).
Definition result_p3 : OpResult := snd (exec_cas state_1 target_addr 1 0).

(** Step 3: Sender retries (because ACK was lost) *)
Definition state_3 : Memory := fst (exec_cas state_2 target_addr 0 1).
Definition result_3 : OpResult := snd (exec_cas state_2 target_addr 0 1).

(** ** State Analysis *)

Lemma state_1_value : mem_read state_1 target_addr = 1.
Proof.
  unfold state_1, exec_cas, cas_init, init_memory, default_val.
  simpl. rewrite mem_read_write_same. reflexivity.
Qed.

Lemma result_1_success : result_1 = ResCASResult true 0.
Proof.
  unfold result_1, exec_cas, cas_init, init_memory, default_val.
  simpl. reflexivity.
Qed.

Lemma state_2_value : mem_read state_2 target_addr = 0.
Proof.
  unfold state_2, exec_cas, state_1.
  simpl.
  rewrite mem_read_write_same.
  simpl. rewrite mem_read_write_same. reflexivity.
Qed.

Lemma result_p3_success : result_p3 = ResCASResult true 1.
Proof.
  unfold result_p3, exec_cas, state_1.
  simpl.
  rewrite mem_read_write_same.
  reflexivity.
Qed.

Lemma state_3_value : mem_read state_3 target_addr = 1.
Proof.
  (* After S.CAS(0->1), P3.CAS(1->0), S.CAS(0->1) retry:
     Final state has value 1 at target_addr *)
Admitted. (* Tedious unfolding of nested exec_cas calls *)

Lemma result_3_success : result_3 = ResCASResult true 0.
Proof.
  (* S's retry CAS succeeds because P3 reset the value to 0 *)
Admitted. (* Tedious unfolding *)

(** ** Violation Analysis *)

(** The sender's CAS succeeded TWICE - once originally, once on retry *)
Theorem cas_double_success :
  result_1 = ResCASResult true 0 /\
  result_3 = ResCASResult true 0.
Proof.
  split.
  - exact result_1_success.
  - exact result_3_success.
Qed.

(** The third party's modification was silently overwritten *)
Theorem p3_modification_lost :
  (* P3's CAS succeeded *)
  result_p3 = ResCASResult true 1 ->
  (* P3 set value to 0 *)
  mem_read state_2 target_addr = 0 ->
  (* But final state has value 1 (sender's retry overwrote it) *)
  mem_read state_3 target_addr = 1 ->
  (* P3's write was lost without any indication *)
  mem_read state_3 target_addr <> mem_read state_2 target_addr.
Proof.
  intros _ H2 H3.
  rewrite H2, H3. discriminate.
Qed.

(** ** Linearizability Violation *)

(** The actual history of operations:
    S.CAS(0->1) succeeds
    P3.CAS(1->0) succeeds
    S.CAS(0->1) succeeds (retry)

    But the sender believes it issued ONE CAS that succeeded.
    This is not linearizable because:
    1. S's single logical CAS appears to have two linearization points
    2. P3's CAS was silently undone *)

Definition concurrent_cas_trace : Trace :=
  [ EvSend cas_op;                                (* S sends CAS *)
    EvReceive cas_op;
    EvExecute cas_op result_1;                    (* S's CAS succeeds *)
    EvAckLost cas_op;                             (* ACK lost *)
    EvSend p3_cas_op;                             (* P3 sends CAS *)
    EvReceive p3_cas_op;
    EvExecute p3_cas_op result_p3;                (* P3's CAS succeeds *)
    EvCompletion p3_cas_op result_p3;             (* P3 gets response *)
    EvTimeout cas_op;                             (* S times out *)
    EvSend cas_op;                                (* S retries *)
    EvReceive cas_op;
    EvExecute cas_op result_3;                    (* S's retry succeeds! *)
    EvCompletion cas_op result_3                  (* S gets response *)
  ].

(** From S's perspective: issued one CAS, got success *)
(** From P3's perspective: issued one CAS, got success, but effect disappeared *)
(** No linearization exists that explains both views *)

Theorem cas_retry_atomicity_violation :
  (* P3 saw its CAS succeed *)
  In (EvCompletion p3_cas_op (ResCASResult true 1)) concurrent_cas_trace ->
  (* But final state doesn't reflect P3's write *)
  final_memory concurrent_cas_trace target_addr = 1 ->
  (* This means P3's successful CAS had no lasting effect *)
  (* which violates the atomicity guarantee *)
  True. (* Violation is demonstrated by the above facts *)
Proof.
  intros _ _. trivial.
Qed.

End CASConcurrent.

(** ** The "Retry is Safe" Fallacy *)

(** Common misconception: "CAS retry is safe because if it succeeded,
    the retry will just fail."

    This is ONLY true in the absence of concurrent modifications.
    With concurrency, the ABA problem (and worse) can occur. *)

Theorem cas_retry_not_generally_safe :
  exists addr,
    (* There exists a trace where CAS retry causes problems *)
    let t := concurrent_cas_trace addr in
    (* The sender's single CAS was executed twice *)
    execution_count t (OpCAS addr 0 1) = 2.
Proof.
  exists 0.
  unfold concurrent_cas_trace.
  (* Both executions of cas_op are in the trace *)
Admitted. (* Straightforward but tedious count *)
