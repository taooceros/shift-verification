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

(** Overlay: Decision function D(Trace, Op) -> {Retry, Skip} *)
(** True = Retry, False = Skip *)
Definition Overlay := Trace -> Op -> bool.

(** Transparency: D depends only on sender view *)
(** D(T, Op) = D(sigma(T), Op) *)
Definition IsTransparent (overlay : Overlay) : Prop :=
  forall t1 t2 op,
    sender_view t1 = sender_view t2 ->
    overlay t1 op = overlay t2 op.

(** Liveness: Every lost op must be retransmitted *)
(** "necessitating retry on loss" *)
Definition PreservesLiveness (overlay : Overlay) : Prop :=
  forall op,
    let t := T1_packet_loss op in
    (* In T1 (Packet Lost), we must Retry *)
    overlay t op = true.

(** Safety: No op executes more than once *)
(** "prohibiting retry if already executed..." *)
Definition PreservesSafety (overlay : Overlay) : Prop :=
  forall op,
    let t := T2_ack_loss op in
    (* In T2 (ACK Lost), we must Skip (not retry) *)
    overlay t op = false.

(** ** Theorem 1: Impossibility *)

Theorem impossibility_main :
  forall overlay : Overlay,
    IsTransparent overlay ->
    ~ (PreservesSafety overlay /\ PreservesLiveness overlay).
Proof.
  intros overlay Htrans [Hsafe Hlive].
  
  (* Pick any operation *)
  pose (op := OpWrite 0 0). 

  (* From Liveness, overlay must RETRY on Packet Loss *)
  assert (H_retry : overlay (T1_packet_loss op) op = true).
  { apply Hlive. }

  (* From Safety, overlay must SKIP on Ack Loss *)
  assert (H_skip : overlay (T2_ack_loss op) op = false).
  { apply Hsafe. }

  (* From Lemma 1 (Indistinguishability), views are identical *)
  assert (H_indist : sender_view (T1_packet_loss op) = sender_view (T2_ack_loss op)).
  { apply indistinguishability. }

  (* By Transparency, decisions must be identical *)
  assert (H_eq : overlay (T1_packet_loss op) op = overlay (T2_ack_loss op) op).
  { apply Htrans. exact H_indist. }

  (* Contradiction: True = False *)
  rewrite H_retry in H_eq.
  rewrite H_skip in H_eq.
  discriminate.
Qed.
