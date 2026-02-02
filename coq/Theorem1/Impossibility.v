(** * Theorem 1: Impossibility of Safe Retransmission *)

From Coq Require Import Arith.
From Coq Require Import List.
From Coq Require Import Lia.
From Coq Require Import Classical.
From ShiftVerification.Core Require Import Memory.
From ShiftVerification.Core Require Import Operations.
From ShiftVerification.Core Require Import Traces.
From ShiftVerification.Core Require Import Properties.
From ShiftVerification.Theorem1 Require Import Indistinguishability.
Import ListNotations.

(** ** Protocol Parameters (same as Indistinguishability.v) *)
Parameter A_data : Addr.
Parameter A_flag : Addr.

(** ** System Assumptions *)

(** Silent Receiver: receiver does not send application-level acknowledgments *)
Definition SilentReceiver : Prop :=
  (* The sender can only observe transport-level signals (WQE completion/timeout) *)
  forall t : Trace,
    forall obs, In obs (sender_view t) ->
    match obs with
    | ObsSent _ => True
    | ObsCompleted _ _ => True
    | ObsTimeout _ => True
    end.

(** Memory Reuse: after consuming, the application may immediately reuse memory *)
Definition MemoryReuseAllowed : Prop :=
  forall V1 V_new, exists t,
    In (EvAppConsume A_data V1) t /\
    In (EvAppReuse A_data V_new) t.

(** Transport does NOT provide exactly-once delivery *)
Definition NoExactlyOnce : Prop :=
  exists t op,
    In (EvSend op) t /\
    (execution_count t op = 0 \/ execution_count t op > 1).

(** Transparent Overlay: cannot allocate additional state or modify protocol *)
Definition Transparent (overlay : TransparentOverlay) : Prop :=
  (* Decision based only on sender observations *)
  forall t1 t2 op,
    sender_view t1 = sender_view t2 ->
    overlay.(decide_retransmit) (sender_view t1) op =
    overlay.(decide_retransmit) (sender_view t2) op.

(** ** The Impossibility Theorem *)

(** An overlay provides safety if retransmission never corrupts valid data *)
Definition ProvidesSafety (overlay : TransparentOverlay) : Prop :=
  forall t op V_new,
    (* If data was consumed and memory reused *)
    In (EvAppReuse A_data V_new) t ->
    op_executed t op ->
    (* Then retransmission decision doesn't cause ghost write *)
    overlay.(decide_retransmit) (sender_view t) op = false.

(** An overlay provides liveness if lost packets are retransmitted *)
Definition ProvidesLiveness (overlay : TransparentOverlay) : Prop :=
  forall t op,
    (* If operation was sent but not executed (packet lost) *)
    In (EvSend op) t ->
    ~ op_executed t op ->
    sender_saw_timeout t op ->
    (* Then it will be retransmitted *)
    overlay.(decide_retransmit) (sender_view t) op = true.

(** ** Main Theorem *)

Theorem impossibility_safe_retransmission :
  forall overlay : TransparentOverlay,
    Transparent overlay ->
    SilentReceiver ->
    MemoryReuseAllowed ->
    NoExactlyOnce ->
    ~ (ProvidesSafety overlay /\ ProvidesLiveness overlay).
Proof.
  intros overlay Htrans Hsilent Hreuse Hno_eo [Hsafe Hlive].

  (** The proof proceeds by constructing two indistinguishable traces:

      Trace T1 (packet loss):
      - Sender sends W_D
      - Packet is lost
      - Sender times out
      - Liveness requires: retransmit = true

      Trace T2 (ACK loss + memory reuse):
      - Sender sends W_D
      - Receiver executes W_D
      - Application consumes data and reuses memory
      - ACK is lost
      - Sender times out
      - Safety requires: retransmit = false

      Since sender only sees "timeout" in both cases, it cannot distinguish
      T1 from T2. Therefore, any deterministic decision violates either
      safety (in T2) or liveness (in T1).
  *)

Admitted. (* Full proof requires detailed sender view analysis *)

(** ** Corollary: No Correct Transparent Overlay Exists *)

Corollary no_correct_overlay :
  SilentReceiver ->
  MemoryReuseAllowed ->
  NoExactlyOnce ->
  ~ exists overlay : TransparentOverlay,
      Transparent overlay /\
      ProvidesSafety overlay /\
      ProvidesLiveness overlay.
Proof.
  intros Hsilent Hreuse Hno_eo [overlay [Htrans [Hsafe Hlive]]].
  apply (impossibility_safe_retransmission overlay Htrans Hsilent Hreuse Hno_eo).
  split; assumption.
Qed.
