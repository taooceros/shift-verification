(** * Theorem 1: Impossibility of Reliable Cross-NIC Fallback *)

(** This theorem proves that a transparent overlay cannot simultaneously
    preserve safety and liveness for systems with non-idempotent operations. *)

From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Classical.
From ShiftVerification.Core Require Import Memory.
From ShiftVerification.Core Require Import Operations.
From ShiftVerification.Core Require Import Traces.
From ShiftVerification.Core Require Import Properties.
From ShiftVerification.Lemma1 Require Import Indistinguishability.
From ShiftVerification.Lemma2 Require Import Atomics.
Import ListNotations.

(** ** System Definitions *)

(* 
   SystemSafety: 
   For any scenario (like T2), if the operation has already executed, 
   the overlay must NOT cause a second execution (i.e., must not Retry).
*)
Definition SystemSafety (overlay : Overlay) : Prop :=
  forall t op,
    NonIdempotentOp op ->
    op_executed t op ->          (* If already executed *)
    sender_saw_timeout t op ->   (* And we are at a decision point *)
    overlay t op = false.        (* We must NOT retry *)

(* 
   SystemLiveness: 
   For any scenario (like T1), if the operation has NOT executed, 
   the overlay MUST ensure progress (i.e., must Retry).
*)
Definition SystemLiveness (overlay : Overlay) : Prop :=
  forall t op,
    In (EvSend op) t ->
    ~ op_executed t op ->        (* If NOT executed *)
    sender_saw_timeout t op ->   (* And we are at a decision point *)
    overlay t op = true.         (* We MUST retry *)

(** ** Theorem 1: Impossibility *)

(** A transparent overlay cannot simultaneously preserve safety and liveness for systems with these non-idempotent operations. *)

Theorem impossibility_main :
  forall overlay : Overlay,
    IsTransparent overlay ->
    (exists op, NonIdempotentOp op) ->
    ~ (SystemSafety overlay /\ SystemLiveness overlay).
Proof.
  intros overlay Htrans Hni [Hsafe Hlive].
  
  (* Get the non-idempotent operation *)
  destruct Hni as [op Hop].

  (* Instantiate traces from Lemma 1 *)
  (* T1 (Packet Loss) *)
  pose (t1 := T1_packet_loss op).
  (* T2 (ACK Loss). We can use any result for the trace existence. *)
  pose (t2 := T2_ack_loss op ResWriteAck).

  (* Apply Liveness to T1 *)
  assert (H_retry : overlay t1 op = true).
  {
    apply Hlive.
    - (* In (EvSend op) t1 *)
      unfold t1, T1_packet_loss. simpl. left. reflexivity.
    - (* ~ op_executed t1 op *)
      unfold t1, T1_packet_loss, op_executed.
      intros [res H]. simpl in H.
      destruct H as [H | [H | [H | H]]]; try discriminate; contradiction.
    - (* sender_saw_timeout t1 op *)
      unfold t1, T1_packet_loss, sender_saw_timeout. simpl.
      right. right. left. reflexivity.
  }

  (* Apply Safety to T2 *)
  assert (H_skip : overlay t2 op = false).
  {
    apply (Hsafe t2 op Hop).
    - (* op_executed t2 op *)
      unfold t2, T2_ack_loss, op_executed.
      exists ResWriteAck. simpl.
      right. right. left. reflexivity.
    - (* sender_saw_timeout t2 op *)
      unfold t2, T2_ack_loss, sender_saw_timeout. simpl.
      right. right. right. right. left. reflexivity.
  }

  (* From Lemma 1, we have conflicting traces *)
  (* indistinguishability_universal takes op res *)
  pose proof (indistinguishability_universal op ResWriteAck) as [H_view_eq _].

  (* We need to match the posed t1 and t2 with what Lemma 1 provides *)
  
  (* By Transparency, equality of views implies equality of decisions *)
  assert (H_dec_eq : overlay t1 op = overlay t2 op).
  {
    apply Htrans.
    unfold t1, t2.
    exact H_view_eq.
  }

  (* Contradiction: True = False *)
  rewrite H_retry in H_dec_eq.
  rewrite H_skip in H_dec_eq.
  discriminate.
Qed.
