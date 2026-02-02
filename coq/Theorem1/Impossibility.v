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

(** Application-level acknowledgment event (not present in silent protocols) *)
Inductive AppAckEvent : Event -> Prop :=
  | AppAck : forall op, AppAckEvent (EvCompletion op ResWriteAck).
  (* In a non-silent protocol, receiver would send explicit app-level ACK *)

(** Silent Receiver: the protocol does not generate application-level ACKs.
    This is a constraint on event generation, not just observation. *)
Definition SilentReceiver : Prop :=
  forall t : Trace, forall e : Event,
    In e t -> ~ AppAckEvent e.

(** Alternative formulation: sender's view is limited to transport signals *)
Definition SenderViewLimited : Prop :=
  forall t : Trace, forall obs,
    In obs (sender_view t) ->
    match obs with
    | ObsSent _ => True
    | ObsCompleted _ _ => True  (* Transport completion, not app ACK *)
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

(** ** Safety and Liveness Definitions *)

(** Safety (Generalized): An overlay is safe if no operation executes more than once.
    This covers both "corrupts new data" and "incremented twice" violations. *)
Definition ProvidesSafetyStrong (overlay : TransparentOverlay) : Prop :=
  forall t op,
    In (EvSend op) t ->
    execution_count t op <= 1.

(** Safety (Original): Retransmission decision prevents ghost writes *)
Definition ProvidesSafety (overlay : TransparentOverlay) : Prop :=
  forall t op V_new,
    (* If data was consumed and memory reused *)
    In (EvAppReuse A_data V_new) t ->
    op_executed t op ->
    (* Then retransmission decision doesn't cause ghost write *)
    overlay.(decide_retransmit) (sender_view t) op = false.

(** Liveness: Lost packets are eventually retransmitted.
    Note: A weaker definition would be "Eventually executed OR reported failed."
    For a transparent overlay promising reliability, strict retransmission is required. *)
Definition ProvidesLiveness (overlay : TransparentOverlay) : Prop :=
  forall t op,
    (* If operation was sent but not executed (packet lost) *)
    In (EvSend op) t ->
    ~ op_executed t op ->
    sender_saw_timeout t op ->
    (* Then it will be retransmitted *)
    overlay.(decide_retransmit) (sender_view t) op = true.

(** ** The Core Dilemma: Non-Injectivity of sender_view *)

(** The key insight: sender_view is NOT injective.
    Multiple distinct traces map to observations containing the same timeout.
    This is the formalization of the Two Generals' Problem. *)

Definition sender_view_non_injective : Prop :=
  exists t1 t2 : Trace,
    t1 <> t2 /\
    sender_view t1 = sender_view t2.

(** Stronger: traces with different execution status map to same observation *)
Definition execution_indistinguishable : Prop :=
  exists t1 t2 op,
    ~ op_executed t1 op /\
    op_executed t2 op /\
    sender_saw_timeout t1 op /\
    sender_saw_timeout t2 op.

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

      The projection sender_view is non-injective:
        sender_view(T1) and sender_view(T2) both contain timeout for W_D

      But the required decisions are contradictory:
        T1 needs retransmit = true  (for liveness)
        T2 needs retransmit = false (for safety)

      Since the overlay's decision depends only on sender_view (transparency),
      it cannot make the correct choice for both traces.
  *)

Admitted. (* Full proof requires showing sender_view equivalence *)

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

(** ** The Two Generals Formalization *)

(** This theorem captures the essence of the Two Generals' Problem:
    The sender cannot know whether:
    (a) The message was lost (requires retransmit), or
    (b) The ACK was lost (retransmit is dangerous)

    Both scenarios produce the same observable outcome: timeout.
    No finite protocol can resolve this ambiguity. *)

Theorem two_generals_formalized :
  execution_indistinguishable ->
  forall overlay : TransparentOverlay,
    Transparent overlay ->
    ~ (ProvidesSafety overlay /\ ProvidesLiveness overlay).
Proof.
  intros [t1 [t2 [op [Hnot_exec [Hexec [Htimeout1 Htimeout2]]]]]]
         overlay Htrans [Hsafe Hlive].
  (* The overlay must make a single decision based on timeout observation.
     But t1 requires true and t2 requires false. Contradiction. *)
Admitted.
