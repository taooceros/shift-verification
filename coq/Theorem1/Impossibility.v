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

(** ** System Model & Definitions *)

(* Concrete parameter for the Safety definition *)
Parameter A_data : Addr.

(* Overlay and Transparency are imported from Lemma1 *)

(** Safety: Retransmission decision prevents ghost writes *)
Definition OverlaySafety (overlay : Overlay) : Prop :=
  forall t op V_new,
    (* If data was consumed and memory reused *)
    In (EvAppReuse A_data V_new) t ->
    op_executed t op ->
    (* Then retransmission decision doesn't cause ghost write *)
    overlay t op = false.

(** Liveness: Lost packets are eventually retransmitted.
    Note: A weaker definition would be "Eventually executed OR reported failed."
    For a transparent overlay promising reliability, strict retransmission is required. *)
Definition OverlayLiveness (overlay : Overlay) : Prop :=
  forall t op,
    (* If operation was sent but not executed (packet lost) *)
    In (EvSend op) t ->
    ~ op_executed t op ->
    sender_saw_timeout t op ->
    (* Then it will be retransmitted *)
    overlay t op = true.

(** ** Theorem 1: Impossibility *)

(** A transparent overlay cannot simultaneously preserve safety and liveness for systems with these non-idempotent operations. *)

Theorem impossibility_main :
  forall overlay : Overlay,
    IsTransparent overlay ->
    (exists op, NonIdempotentOp op) ->
    ~ (OverlaySafety overlay /\ OverlayLiveness overlay).
Proof.
  intros overlay Htrans Hni [Hsafe Hlive].
  
  (* Pick concrete values *)
  pose (op := OpWrite A_data 0).
  pose (V_new := 1).

  (* Instantiate traces from Lemma 1 *)
  (* T1 (Packet Loss) does not depend on A_data/V_new *)
  pose (t1 := T1_packet_loss op).
  (* T2 (ACK Loss) depends on A_data and V_new *)
  pose (t2 := T2_ack_loss A_data V_new op).

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
    apply (Hsafe t2 op V_new).
    - (* In (EvAppReuse A_data V_new) t2 *)
      unfold t2, T2_ack_loss. simpl.
      right. right. right. left. reflexivity.
    - (* op_executed t2 op *)
      unfold t2, T2_ack_loss, op_executed.
      exists ResWriteAck. simpl.
      right. right. left. reflexivity.
  }

  (* From Lemma 1, we have conflicting traces *)
  (* indistinguishability_universal takes A_data V_new op *)
  pose proof (indistinguishability_universal A_data V_new op) as [H_view_eq _].

  (* We need to match the posed t1 and t2 with what Lemma 1 provides *)
  (* Check Lemma 1 definitions:
     T1_packet_loss op 
     T2_ack_loss A_data V_new op
     (This matches our t1 and t2)
  *)
  
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
