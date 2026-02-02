(** * Execution Traces *)

From Coq Require Import Arith.
From Coq Require Import List.
From ShiftVerification.Core Require Import Memory.
From ShiftVerification.Core Require Import Operations.
Import ListNotations.

(** ** Event Types *)

(** Events that can occur in a distributed RDMA system *)
Inductive Event : Type :=
  (* Sender-side events *)
  | EvSend : Op -> Event              (* Sender posts an operation *)
  | EvTimeout : Op -> Event           (* Sender observes timeout for an operation *)
  | EvCompletion : Op -> OpResult -> Event  (* Sender receives completion *)

  (* Network events *)
  | EvPacketLost : Op -> Event        (* Operation packet lost in network *)
  | EvAckLost : Op -> Event           (* Acknowledgment lost in network *)

  (* Receiver-side events *)
  | EvReceive : Op -> Event           (* Receiver receives operation *)
  | EvExecute : Op -> OpResult -> Event     (* Receiver executes operation *)

  (* Application events *)
  | EvAppConsume : Addr -> Val -> Event     (* Application consumes data *)
  | EvAppReuse : Addr -> Val -> Event.      (* Application reuses memory *)

(** A trace is a sequence of events *)
Definition Trace := list Event.

(** ** Sender Observations *)

(** What the sender can observe (limited view) *)
Inductive SenderObs : Type :=
  | ObsSent : Op -> SenderObs
  | ObsCompleted : Op -> OpResult -> SenderObs
  | ObsTimeout : Op -> SenderObs.

(** Extract sender observations from a trace *)
Fixpoint sender_view (t : Trace) : list SenderObs :=
  match t with
  | [] => []
  | EvSend op :: rest => ObsSent op :: sender_view rest
  | EvCompletion op res :: rest => ObsCompleted op res :: sender_view rest
  | EvTimeout op :: rest => ObsTimeout op :: sender_view rest
  | _ :: rest => sender_view rest  (* Sender cannot observe other events *)
  end.

(** ** Trace Properties *)

(** Two traces are indistinguishable to the sender if they produce the same observations *)
Definition sender_indistinguishable (t1 t2 : Trace) : Prop :=
  sender_view t1 = sender_view t2.

(** A trace represents a packet loss scenario *)
Definition has_packet_loss (t : Trace) (op : Op) : Prop :=
  In (EvPacketLost op) t.

(** A trace represents an ACK loss scenario *)
Definition has_ack_loss (t : Trace) (op : Op) : Prop :=
  In (EvAckLost op) t /\ exists res, In (EvExecute op res) t.

(** Operation was executed in a trace *)
Definition op_executed (t : Trace) (op : Op) : Prop :=
  exists res, In (EvExecute op res) t.

(** Operation completed successfully from sender's view *)
Definition op_completed (t : Trace) (op : Op) : Prop :=
  exists res, In (EvCompletion op res) t.

(** Sender observed a timeout *)
Definition sender_saw_timeout (t : Trace) (op : Op) : Prop :=
  In (EvTimeout op) t.

(** ** Memory State in Traces *)

(** Compute memory state after executing a prefix of events *)
Fixpoint memory_after_events (m : Memory) (events : list Event) : Memory :=
  match events with
  | [] => m
  | EvExecute op _ :: rest =>
      let (m', _) := exec_op m op in
      memory_after_events m' rest
  | EvAppReuse a v :: rest =>
      memory_after_events (mem_write m a v) rest
  | _ :: rest => memory_after_events m rest
  end.

(** Memory state at the end of a trace *)
Definition final_memory (t : Trace) : Memory :=
  memory_after_events init_memory t.

(** ** Well-Formedness *)

(** An operation can only be executed if it was received *)
Definition wf_execute_after_receive (t : Trace) : Prop :=
  forall op res,
    In (EvExecute op res) t ->
    exists prefix suffix,
      t = prefix ++ [EvReceive op] ++ suffix /\
      In (EvExecute op res) suffix.

(** A packet can only be lost if it was sent *)
Definition wf_loss_after_send (t : Trace) : Prop :=
  forall op,
    In (EvPacketLost op) t \/ In (EvAckLost op) t ->
    exists prefix suffix,
      t = prefix ++ [EvSend op] ++ suffix.
