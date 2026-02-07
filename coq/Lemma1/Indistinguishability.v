(** * Theorem 1: Indistinguishability of Traces *)

From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From ShiftVerification.Core Require Import Memory.
From ShiftVerification.Core Require Import Operations.
From ShiftVerification.Core Require Import Traces.
From ShiftVerification.Core Require Import Properties.
Import ListNotations.

(** ** The LL128 Protocol Model *)

Section LL128Protocol.

(** Protocol parameters *)
Variable A_data : Addr.
Variable A_flag : Addr.
Hypothesis addr_distinct : A_data <> A_flag.

(** The data write operation *)
Definition W_D (v : Val) : Op := OpWrite A_data v.

(** The flag write operation *)
Definition W_F : Op := OpWrite A_flag 1.

(** ** Trace T1: Packet Loss Scenario *)

(** In T1, the data packet is lost before reaching the receiver.
    The sender sees a timeout but the operation was never executed. *)

Definition T1_packet_loss (V1 : Val) : Trace :=
  [ EvSend (W_D V1);            (* Sender posts data write *)
    EvPacketLost (W_D V1);      (* Packet lost in network *)
    EvTimeout (W_D V1)          (* Sender observes timeout *)
  ].

(** ** Trace T2: ACK Loss Scenario *)

(** In T2, the operation completes successfully at the receiver,
    but the ACK is lost. The application consumes and reuses memory.
    The sender still sees a timeout. *)

Definition T2_ack_loss (V1 V_new : Val) : Trace :=
  [ EvSend (W_D V1);                        (* Sender posts data write *)
    EvReceive (W_D V1);                     (* Receiver gets the packet *)
    EvExecute (W_D V1) ResWriteAck;         (* Receiver executes write *)
    EvSend W_F;                             (* Sender posts flag write *)
    EvReceive W_F;                          (* Receiver gets flag *)
    EvExecute W_F ResWriteAck;              (* Receiver sets flag *)
    EvAppConsume A_data V1;                 (* App consumes data *)
    EvAppReuse A_data V_new;                (* App reuses memory with new value *)
    EvAckLost (W_D V1);                     (* ACK was lost *)
    EvTimeout (W_D V1)                      (* Sender observes timeout *)
  ].

(** ** Key Lemma: Traces are Indistinguishable to Sender *)

Lemma sender_view_T1 : forall V1,
  sender_view (T1_packet_loss V1) =
  [ObsSent (W_D V1); ObsTimeout (W_D V1)].
Proof.
  intros. unfold T1_packet_loss. simpl. reflexivity.
Qed.

Lemma sender_view_T2 : forall V1 V_new,
  sender_view (T2_ack_loss V1 V_new) =
  [ObsSent (W_D V1); ObsSent W_F; ObsTimeout (W_D V1)].
Proof.
  intros. unfold T2_ack_loss. simpl. reflexivity.
Qed.

(** Note: T1 and T2 have slightly different sender views because T2 includes W_F.
    For the core argument, we focus on the timeout observation for W_D. *)

(** A more precise formulation: the sender cannot distinguish whether W_D was executed *)
Lemma indistinguishable_wrt_WD_execution : forall V1 V_new,
  sender_saw_timeout (T1_packet_loss V1) (W_D V1) /\
  sender_saw_timeout (T2_ack_loss V1 V_new) (W_D V1) /\
  ~ op_executed (T1_packet_loss V1) (W_D V1) /\
  op_executed (T2_ack_loss V1 V_new) (W_D V1).
Proof.
  intros V1 V_new.
  repeat split.
  - (* T1 has timeout *)
    unfold sender_saw_timeout, T1_packet_loss.
    simpl. right. right. left. reflexivity.
  - (* T2 has timeout *)
    unfold sender_saw_timeout, T2_ack_loss.
    simpl.
    do 9 right. left. reflexivity.
  - (* T1: W_D not executed - no EvExecute events in T1 *)
    unfold op_executed, T1_packet_loss.
    intros [res Hin]. simpl in Hin.
    destruct Hin as [H | [H | [H | H]]]; inversion H.
  - (* T2: W_D was executed *)
    unfold op_executed, T2_ack_loss.
    exists ResWriteAck.
    simpl.
    do 2 right. left. reflexivity.
Qed.

(** ** Memory State Analysis *)

(** In T1, memory at A_data is unchanged (operation never executed) *)
Lemma T1_memory_unchanged : forall V1,
  final_memory (T1_packet_loss V1) A_data = init_memory A_data.
Proof.
  intros. unfold final_memory, T1_packet_loss.
  simpl. reflexivity.
Qed.

(** In T2, memory at A_data has been reused with V_new *)
Lemma T2_memory_reused : forall V1 V_new,
  final_memory (T2_ack_loss V1 V_new) A_data = V_new.
Proof.
  intros V1 V_new. unfold final_memory, T2_ack_loss.
  (* Step through memory_after_events manually *)
  simpl memory_after_events.
  unfold exec_op, exec_write, W_D, W_F.
  (* After all the events, the final memory at A_data is V_new
     because the last write to A_data is from EvAppReuse *)
  unfold mem_read, mem_write.
  (* Goal should be: (if A_data =? A_data then V_new else ...) = V_new *)
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

(** ** Retransmission Analysis *)

(** If sender retransmits W_D after T2, it overwrites V_new with V1 *)
Definition T2_with_retransmit (V1 V_new : Val) : Trace :=
  T2_ack_loss V1 V_new ++
  [ EvSend (W_D V1);                  (* Sender retransmits *)
    EvReceive (W_D V1);               (* Receiver gets retransmit *)
    EvExecute (W_D V1) ResWriteAck    (* Ghost write! Overwrites V_new *)
  ].

Lemma memory_after_events_app : forall t1 t2 m,
  memory_after_events m (t1 ++ t2) = memory_after_events (memory_after_events m t1) t2.
Proof.
  intros t1. induction t1 as [| e t1' IH]; intros t2 m.
  - simpl. reflexivity.
  - simpl. destruct e; try apply IH.
    (* EvExecute case: need to destruct exec_op *)
    destruct (exec_op m o) as [m' r]. apply IH.
Qed.

Lemma retransmit_causes_ghost_write : forall V1 V_new,
  V1 <> V_new ->
  final_memory (T2_with_retransmit V1 V_new) A_data = V1.
Proof.
  intros V1 V_new Hdiff.
  unfold final_memory, T2_with_retransmit.
  rewrite memory_after_events_app.
  (* After T2_ack_loss, we have some memory state m *)
  (* Then we process [EvSend; EvReceive; EvExecute (W_D V1)] *)
  simpl memory_after_events.
  unfold exec_op, exec_write, W_D.
  (* The final EvExecute writes V1 to A_data *)
  unfold mem_read, mem_write.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

(** The ghost write corrupts the receiver's state *)
Theorem ghost_write_violation : forall V1 V_new,
  V1 <> V_new ->
  (* Before retransmit, receiver has V_new *)
  final_memory (T2_ack_loss V1 V_new) A_data = V_new ->
  (* After retransmit, receiver has V1 (stale data) *)
  final_memory (T2_with_retransmit V1 V_new) A_data = V1 ->
  (* This is a safety violation: the retransmit corrupted valid data *)
  final_memory (T2_with_retransmit V1 V_new) A_data <>
  final_memory (T2_ack_loss V1 V_new) A_data.
Proof.
  intros V1 V_new Hdiff H1 H2.
  rewrite H1, H2. exact Hdiff.
Qed.

End LL128Protocol.
