(** * Theorem 1: Impossibility of Safe Retransmission *)

From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Classical.
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

(** Helper: construct traces with identical sender_view but different execution status *)
Section ConcreteTraces.
  Variable V1 V_new : Val.
  Let op := OpWrite A_data V1.

  (** T1: Packet lost - operation NOT executed *)
  Definition T1_concrete : Trace :=
    [ EvSend op;
      EvPacketLost op;
      EvTimeout op ].

  (** T2: ACK lost - operation WAS executed, memory reused *)
  Definition T2_concrete : Trace :=
    [ EvSend op;
      EvReceive op;
      EvExecute op ResWriteAck;
      EvAppReuse A_data V_new;
      EvAckLost op;
      EvTimeout op ].

  (** Key: both traces have identical sender_view *)
  Lemma sender_views_equal :
    sender_view T1_concrete = sender_view T2_concrete.
  Proof.
    unfold T1_concrete, T2_concrete. simpl. reflexivity.
  Qed.

  (** T1 does not execute the operation *)
  Lemma T1_not_executed : ~ op_executed T1_concrete op.
  Proof.
    unfold op_executed, T1_concrete.
    intros [res Hin]. simpl in Hin.
    destruct Hin as [H | [H | [H | H]]].
    - discriminate.
    - discriminate.
    - discriminate.
    - destruct H.
  Qed.

  (** T2 does execute the operation *)
  Lemma T2_executed : op_executed T2_concrete op.
  Proof.
    unfold op_executed, T2_concrete.
    exists ResWriteAck. simpl.
    right. right. left. reflexivity.
  Qed.

  (** T1 has timeout *)
  Lemma T1_has_timeout : sender_saw_timeout T1_concrete op.
  Proof.
    unfold sender_saw_timeout, T1_concrete. simpl.
    right. right. left. reflexivity.
  Qed.

  (** T1 has the send event *)
  Lemma T1_has_send : In (EvSend op) T1_concrete.
  Proof.
    unfold T1_concrete. simpl. left. reflexivity.
  Qed.

  (** T2 has memory reuse *)
  Lemma T2_has_reuse : In (EvAppReuse A_data V_new) T2_concrete.
  Proof.
    unfold T2_concrete. simpl.
    right. right. right. left. reflexivity.
  Qed.

End ConcreteTraces.

Theorem impossibility_safe_retransmission :
  forall overlay : TransparentOverlay,
    Transparent overlay ->
    SilentReceiver ->
    MemoryReuseAllowed ->
    NoExactlyOnce ->
    ~ (ProvidesSafety overlay /\ ProvidesLiveness overlay).
Proof.
  intros overlay Htrans Hsilent Hreuse Hno_eo [Hsafe Hlive].

  (* Choose concrete values *)
  pose (V1 := 1).
  pose (V_new := 2).

  (* The operation in question - same as used in the section *)
  pose (the_op := OpWrite A_data V1).

  (* The traces *)
  pose (t1 := T1_concrete V1).
  pose (t2 := T2_concrete V1 V_new).

  (* From Liveness applied to t1:
     t1 has send, no execution, timeout → must retransmit *)
  assert (Hlive_T1 : overlay.(decide_retransmit) (sender_view t1) the_op = true).
  {
    unfold t1, the_op.
    apply (Hlive (T1_concrete V1) (OpWrite A_data V1)).
    - apply T1_has_send.
    - apply T1_not_executed.
    - apply T1_has_timeout.
  }

  (* From Safety applied to t2:
     t2 has memory reuse and execution → must NOT retransmit *)
  assert (Hsafe_T2 : overlay.(decide_retransmit) (sender_view t2) the_op = false).
  {
    unfold t2, the_op.
    apply (Hsafe (T2_concrete V1 V_new) (OpWrite A_data V1) V_new).
    - apply T2_has_reuse.
    - apply T2_executed.
  }

  (* But sender_views are equal, so decisions must be equal *)
  assert (Hviews_eq : sender_view t1 = sender_view t2).
  { unfold t1, t2. apply sender_views_equal. }

  (* By Transparent, equal sender_views → equal decisions *)
  assert (Hdec_eq : overlay.(decide_retransmit) (sender_view t1) the_op =
                    overlay.(decide_retransmit) (sender_view t2) the_op).
  {
    apply Htrans. exact Hviews_eq.
  }

  (* Contradiction: true = false *)
  rewrite Hlive_T1 in Hdec_eq.
  rewrite Hsafe_T2 in Hdec_eq.
  discriminate.
Qed.

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

(** The core theorem directly uses the trace construction *)
Theorem two_generals_core :
  forall overlay : TransparentOverlay,
    Transparent overlay ->
    forall t1 t2 op,
      sender_view t1 = sender_view t2 ->
      In (EvSend op) t1 ->
      ~ op_executed t1 op ->
      sender_saw_timeout t1 op ->
      op_executed t2 op ->
      (exists V_new, In (EvAppReuse A_data V_new) t2) ->
      ~ (ProvidesSafety overlay /\ ProvidesLiveness overlay).
Proof.
  intros overlay Htrans t1 t2 op Hview_eq Hsend1 Hnot_exec1 Htimeout1 Hexec2 [V_new Hreuse2] [Hsafe Hlive].

  (* Liveness on t1: must retransmit *)
  assert (H1 : overlay.(decide_retransmit) (sender_view t1) op = true).
  { apply (Hlive t1 op); assumption. }

  (* Safety on t2: must not retransmit *)
  assert (H2 : overlay.(decide_retransmit) (sender_view t2) op = false).
  { apply (Hsafe t2 op V_new); assumption. }

  (* Transparency: equal views → equal decisions *)
  assert (Heq : overlay.(decide_retransmit) (sender_view t1) op =
                overlay.(decide_retransmit) (sender_view t2) op).
  { apply Htrans. exact Hview_eq. }

  (* Contradiction *)
  rewrite H1, H2 in Heq. discriminate.
Qed.
