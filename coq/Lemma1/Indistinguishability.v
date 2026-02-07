(** * Lemma 1: Indistinguishability of Traces *)

(** This lemma formally proves the indistinguishability of packet loss
    and ACK loss scenarios to a transparent sender. *)

From Stdlib Require Import Arith.
From Stdlib Require Import List.
From ShiftVerification.Core Require Import Memory.
From ShiftVerification.Core Require Import Operations.
From ShiftVerification.Core Require Import Traces.
From ShiftVerification.Core Require Import Properties.
Import ListNotations.

(** ** Definitions *)

(** Overlay: Decision function D(Trace, Op) -> {Retry, Skip} *)
(** True = Retry, False = Skip *)
Definition Overlay := Trace -> Op -> bool.

(** Transparency: D depends only on sender view *)
Definition IsTransparent (overlay : Overlay) : Prop :=
  forall t1 t2 op,
    sender_view t1 = sender_view t2 ->
    overlay t1 op = overlay t2 op.

(** Two traces conflict if they are indistinguishable to the sender
    but have different execution outcomes (requiring different overlay actions). *)
Definition ConflictingTraces (t1 t2 : Trace) (op : Op) : Prop :=
  sender_view t1 = sender_view t2 /\
  (~ op_executed t1 op /\ op_executed t2 op).

(** ** Trace T1: Packet Loss Scenario *)
Section Indistinguishability.
Variable A_data : Addr.
Variable V_new : Val.

(** In T1, the request is lost in the network. The operation never executes. *)
Definition T1_packet_loss (op : Op) : Trace :=
  [ EvSend op;            (* Sender posts operation *)
    EvPacketLost op;      (* Packet lost in network *)
    EvTimeout op          (* Sender observes timeout *)
  ].

(** ** Trace T2: ACK Loss Scenario *)
(** In T2, the operation executes, but the ACK is lost in the network. 
    Crucially, the application REUSES the memory after execution. *)
Definition T2_ack_loss (op : Op) : Trace :=
  [ EvSend op;                  (* Sender posts operation *)
    EvReceive op;               (* Receiver gets the packet *)
    EvExecute op ResWriteAck;   (* Receiver executes op *)
    EvAppReuse A_data V_new;    (* Memory is reused! *)
    EvAckLost op;               (* ACK was lost *)
    EvTimeout op                (* Sender observes timeout *)
  ].


(** ** Lemma 1: Indistinguishability *)

(** Helper: The property holds for any operation. *)
Lemma indistinguishability_universal : forall op,
  ConflictingTraces (T1_packet_loss op) (T2_ack_loss op) op.
Proof.
  intros op.
  unfold ConflictingTraces.
  split.
  - unfold T1_packet_loss, T2_ack_loss. simpl. reflexivity.
  - split.
    + unfold op_executed, T1_packet_loss.
      intros [res H]. simpl in H.
      destruct H as [H | [H | [H | H]]].
      * discriminate.
      * discriminate.
      * discriminate.
      * contradiction.
    + unfold op_executed, T2_ack_loss.
      exists ResWriteAck. simpl.
      right. right. left. reflexivity.
Qed.

(** There exist two traces that are indistinguishable to the sender
    yet conflict in their execution status. *)
Lemma lemma1_indistinguishability_conflict : exists t1 t2 op,
  ConflictingTraces t1 t2 op.
Proof.
  exists (T1_packet_loss (OpWrite 0 0)).
  exists (T2_ack_loss (OpWrite 0 0)).
  exists (OpWrite 0 0).
  apply indistinguishability_universal.
Qed.

End Indistinguishability.
