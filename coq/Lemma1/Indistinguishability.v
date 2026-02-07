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

(** ** Trace T1: Packet Loss Scenario *)
Section Indistinguishability.
Variable A_data : Addr.

(** In T1, the request is lost in the network. The operation never executes. *)
Definition T1_packet_loss (op : Op) : Trace :=
  [ EvSend op;            (* Sender posts operation *)
    EvPacketLost op;      (* Packet lost in network *)
    EvTimeout op          (* Sender observes timeout *)
  ].

(** ** Trace T2: ACK Loss Scenario *)
(** In T2, the operation executes, but the ACK is lost in the network. *)
Definition T2_ack_loss (op : Op) : Trace :=
  [ EvSend op;                  (* Sender posts operation *)
    EvReceive op;               (* Receiver gets the packet *)
    EvExecute op ResWriteAck;   (* Receiver executes op *)
    EvAckLost op;               (* ACK was lost *)
    EvTimeout op                (* Sender observes timeout *)
  ].


(** ** Lemma 1: Indistinguishability *)

(** The sender view of T1 and T2 is identical: [ObsSent, ObsTimeout]. *)
Lemma indistinguishability : forall op,
  sender_view (T1_packet_loss op) = sender_view (T2_ack_loss op) /\
  sender_view (T1_packet_loss op) = [ObsSent op; ObsTimeout op].
Proof.
  intros op.
  split.
  - unfold T1_packet_loss, T2_ack_loss. simpl. reflexivity.
  - unfold T1_packet_loss. simpl. reflexivity.
Qed.

(** Yet they conflict in execution status *)
Lemma trace_conflict : forall op,
  ~ op_executed (T1_packet_loss op) op /\
  op_executed (T2_ack_loss op) op.
Proof.
  intros op. split.
  - unfold op_executed, T1_packet_loss.
    intros [res H]. simpl in H.
    destruct H as [H | [H | [H | H]]].
    + discriminate.
    + discriminate.
    + discriminate.
    + contradiction.
  - unfold op_executed, T2_ack_loss.
    exists ResWriteAck. simpl.
    right. right. left. reflexivity.
  Qed.

End Indistinguishability.
