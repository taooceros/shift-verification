(** * Theorem 2: Atomic Operations Base Definitions *)

From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Classical.
From ShiftVerification.Core Require Import Memory.
From ShiftVerification.Core Require Import Operations.
From ShiftVerification.Core Require Import Traces.
From ShiftVerification.Core Require Import Properties.
From ShiftVerification.Theorem1 Require Import Impossibility.
Import ListNotations.

(** ** Atomic Operation Properties *)

(** An operation is atomic if it appears to execute instantaneously *)
Definition AtomicOp (op : Op) : Prop :=
  match op with
  | OpFADD _ _ => True
  | OpCAS _ _ _ => True
  | _ => False
  end.

(** ** Idempotency *)

(** An operation is idempotent if executing it twice produces the same result as once *)
Definition Idempotent (op : Op) (m : Memory) : Prop :=
  let (m1, r1) := exec_op m op in
  let (m2, r2) := exec_op m1 op in
  m1 = m2 /\ r1 = r2.

(** ** Non-Idempotency of FADD *)

Theorem fadd_non_idempotent : forall a delta m,
  delta <> 0 ->
  ~ Idempotent (OpFADD a delta) m.
Proof.
  intros a delta m Hdelta.
  unfold Idempotent.
  simpl. unfold exec_fadd.
  intros [Hmem Hres].

  (* Let old = mem_read m a *)
  (* m1 = mem_write m a (old + delta), so m1[a] = old + delta *)
  (* m2 = mem_write m1 a (m1[a] + delta) = mem_write m1 a (old + delta + delta) *)
  (* So m2[a] = old + 2*delta *)

  (* If m1 = m2, then m1[a] = m2[a], i.e., old + delta = old + 2*delta *)
  (* This implies delta = 0, contradicting delta <> 0 *)

  set (old := mem_read m a) in *.
  set (m1 := mem_write m a (old + delta)) in *.

  assert (Hm1_a : mem_read m1 a = old + delta).
  { unfold m1. apply mem_read_write_same. }

  set (m2 := mem_write m1 a (mem_read m1 a + delta)) in *.

  assert (Hm2_a : mem_read m2 a = old + delta + delta).
  { unfold m2. rewrite mem_read_write_same. rewrite Hm1_a. reflexivity. }

  (* From Hmem: m1 = m2 *)
  (* Therefore mem_read m1 a = mem_read m2 a *)
  assert (Heq : mem_read m1 a = mem_read m2 a).
  { rewrite Hmem. reflexivity. }

  rewrite Hm1_a, Hm2_a in Heq.
  (* old + delta = old + delta + delta *)
  (* old + delta = old + 2*delta *)
  lia.
Qed.

(** ** Conditional Non-Idempotency of CAS *)

(** CAS is idempotent only if it fails or if expected = new_val *)
Theorem cas_idempotent_iff : forall a expected new_val m,
  Idempotent (OpCAS a expected new_val) m <->
  (mem_read m a <> expected \/ expected = new_val).
Proof.
  intros a expected new_val m.
  unfold Idempotent, exec_op, exec_cas.
  (* Case split on whether first CAS succeeds *)
  destruct (Nat.eqb (mem_read m a) expected) eqn:Hcond.

  - (* mem_read m a = expected: first CAS succeeds *)
    apply Nat.eqb_eq in Hcond.
    rewrite mem_read_write_same.
    destruct (Nat.eqb new_val expected) eqn:Hcond2.
    + (* new_val = expected: second CAS also succeeds *)
      apply Nat.eqb_eq in Hcond2.
      split.
      * intros _. right. symmetry. exact Hcond2.
      * intros _. subst new_val. rewrite mem_write_write_same. rewrite Hcond.
        auto.
    + (* new_val <> expected: second CAS fails *)
      apply Nat.eqb_neq in Hcond2.
      split.
      * intros [_ Hcontra]. discriminate.
      * intros [Hcontra | Hcontra].
        -- exfalso. apply Hcontra. exact Hcond.
        -- exfalso. apply Hcond2. symmetry. exact Hcontra.

  - (* mem_read m a <> expected: first CAS fails *)
    (* Hcond : Nat.eqb (mem_read m a) expected = false *)
    (* In the failure case, both exec_cas calls return (m, ResCASResult false (mem_read m a)) *)
    (* Rewrite using the equation before converting to disequality *)
    rewrite Hcond.
    split.
    + intros _. left. apply Nat.eqb_neq. exact Hcond.
    + intros _. split; reflexivity.
Qed.

(** ** Retry Semantics *)

(** A retried operation trace: sender sends, receiver executes, ack lost, sender retries *)
Definition retry_trace (op : Op) : Trace :=
  [ EvSend op;
    EvReceive op;
    EvExecute op (snd (exec_op init_memory op));
    EvAckLost op;
    EvTimeout op;
    EvSend op;  (* Retry *)
    EvReceive op;
    EvExecute op (snd (exec_op (fst (exec_op init_memory op)) op))
  ].

(** Retry causes double execution *)
Lemma retry_double_execution : forall op,
  execution_count (retry_trace op) op = 2.
Proof.
  intros op.
  unfold retry_trace, execution_count.
  (* Unfold and simplify - but keep op_eq visible for rewriting *)
  simpl execution_count.
  (* The trace has two EvExecute events for op *)
  (* Each contributes (if op_eq op op then 1 else 0) = 1 *)
  repeat rewrite op_eq_refl.
  reflexivity.
Qed.

(** ** Linearizability Violation *)

(** A history where operation appears to execute twice *)
Definition double_execution_history (op : Op) : History :=
  [ HInvoke 0 op;
    HRespond 0 (snd (exec_op init_memory op));
    HInvoke 0 op;  (* "Ghost" invocation from retry *)
    HRespond 0 (snd (exec_op (fst (exec_op init_memory op)) op))
  ].

(** The responses in a double execution are different for non-idempotent ops *)
(** This captures the linearizability violation: a single logical operation
    cannot produce two different responses. *)
Theorem fadd_double_execution_different_responses : forall a delta,
  delta <> 0 ->
  let op := OpFADD a delta in
  snd (exec_op init_memory op) <> snd (exec_op (fst (exec_op init_memory op)) op).
Proof.
  intros a delta Hdelta op.
  unfold op. simpl. unfold exec_fadd, init_memory, default_val.
  simpl. rewrite mem_read_write_same.
  (* First response: ResFADDVal 0 *)
  (* Second response: ResFADDVal delta *)
  (* Goal: ResFADDVal 0 <> ResFADDVal delta *)
  intro H.
  (* Use injection to extract the equality 0 = delta *)
  injection H as H0.
  (* H0 : 0 = delta, but Hdelta : delta <> 0 *)
  (* Rewrite delta to 0 in Hdelta *)
  subst delta.
  (* Now Hdelta : 0 <> 0, which is absurd *)
  apply Hdelta. 
  reflexivity.
Qed.

(** Note: The full Linearizable definition is a placeholder (defined as True).
    For a complete proof, we would need to:
    1. Define linearizability properly (equivalent sequential history)
    2. Show that a single FADD invocation cannot have two different responses

    The theorem fadd_double_execution_different_responses captures the key insight:
    the retry produces a DIFFERENT response than the original, which means
    the client observes behavior inconsistent with a single atomic operation. *)

Theorem retry_not_linearizable : forall a delta,
  delta <> 0 ->
  (* A retry causes two executions with different results *)
  let op := OpFADD a delta in
  snd (exec_op init_memory op) <> snd (exec_op (fst (exec_op init_memory op)) op).
Proof.
  exact fadd_double_execution_different_responses.
Qed.

(** ** Non-Idempotent Operations Cannot Be Safely Retransmitted *)

(** For non-idempotent operations, retry after execution always causes a violation:
    either memory state diverges or response differs from original. *)

Lemma non_idempotent_retry_unsafe : forall op m,
  ~ Idempotent op m ->
  let (m1, r1) := exec_op m op in
  let (m2, r2) := exec_op m1 op in
  m1 <> m2 \/ r1 <> r2.
Proof.
  intros op m Hnot_idem.
  unfold Idempotent in Hnot_idem.
  destruct (exec_op m op) as [m1 r1] eqn:E1.
  destruct (exec_op m1 op) as [m2 r2] eqn:E2.
  (* Hnot_idem : ~(m1 = m2 /\ r1 = r2) *)
  (* By De Morgan's law (classical): ~(A /\ B) -> ~A \/ ~B *)
  destruct (classic (m1 = m2)) as [Hmeq | Hmneq].
  - (* m1 = m2, so must have r1 <> r2 *)
    right. intros Hreq. apply Hnot_idem. split; assumption.
  - (* m1 <> m2 *)
    left. exact Hmneq.
Qed.

(** Instantiation for FADD: any FADD with delta <> 0 cannot be safely retried *)
Lemma fadd_retry_unsafe : forall a delta m,
  delta <> 0 ->
  let op := OpFADD a delta in
  let (m1, r1) := exec_op m op in
  let (m2, r2) := exec_op m1 op in
  m1 <> m2 \/ r1 <> r2.
Proof.
  intros a delta m Hdelta.
  apply non_idempotent_retry_unsafe.
  apply fadd_non_idempotent.
  (* delta <> 0 implies delta <> 0 *)
  exact Hdelta.
Qed.

(** ** Main Result: Atomic Operations Cannot Be Transparently Retransmitted *)

(** Transparent retransmission requires that retry be safe (not corrupt state
    or produce different results). Atomic operations violate this requirement. *)

Corollary atomic_ops_no_transparent_retransmit : forall op m,
  AtomicOp op ->
  ~ Idempotent op m ->
  (* Retransmission causes state or result divergence *)
  let (m1, r1) := exec_op m op in
  let (m2, r2) := exec_op m1 op in
  m1 <> m2 \/ r1 <> r2.
Proof.
  intros op m _ Hnot_idem.
  apply non_idempotent_retry_unsafe.
  exact Hnot_idem.
Qed.

(** Concrete instance: FADD cannot be transparently retransmitted *)
Corollary fadd_no_transparent_retransmit : forall a delta m,
  delta <> 0 ->
  let op := OpFADD a delta in
  AtomicOp op /\
  (let (m1, r1) := exec_op m op in
   let (m2, r2) := exec_op m1 op in
   m1 <> m2 \/ r1 <> r2).
Proof.
  intros a delta m Hdelta.
  split.
  - (* AtomicOp (OpFADD a delta) *)
    simpl. trivial.
  - (* Retry causes divergence *)
    apply fadd_retry_unsafe. exact Hdelta.
Qed.

(** Concrete instance: CAS with successful first execution cannot be transparently retransmitted *)
Corollary cas_no_transparent_retransmit : forall a expected new_val m,
  mem_read m a = expected ->
  expected <> new_val ->
  let op := OpCAS a expected new_val in
  AtomicOp op /\
  (let (m1, r1) := exec_op m op in
   let (m2, r2) := exec_op m1 op in
   m1 <> m2 \/ r1 <> r2).
Proof.
  intros a expected new_val m Hsucc Hdiff.
  split.
  - (* AtomicOp (OpCAS a expected new_val) *)
    simpl. trivial.
  - (* Retry causes divergence *)
    apply non_idempotent_retry_unsafe.
    rewrite cas_idempotent_iff.
    intros [Hcontra | Hcontra].
    + apply Hcontra. exact Hsucc.
    + apply Hdiff. exact Hcontra.
Qed.

(** ** Combined Result: No Transparent Overlay for Non-Idempotent Operations *)

(** This combines insights from Theorem 1 (indistinguishability) and Theorem 2 (non-idempotency):

    From Theorem 1: A transparent overlay cannot distinguish packet loss from ACK loss,
    because both scenarios produce identical sender observations (timeout).

    From Theorem 2: Non-idempotent operations (including FADD and CAS) produce different
    memory states or results when executed twice.

    Combined: For non-idempotent operations, any transparent overlay must either:
    - Retry on timeout → violates safety when ACK was lost (double execution)
    - Not retry on timeout → violates liveness when packet was lost

    Therefore, no transparent overlay can provide both safety and liveness
    for non-idempotent operations. *)

(** Safety for non-idempotent ops: at most one execution *)
(* Definition SafeExecution (t : Trace) (op : Op) : Prop :=
  execution_count t op <= 1. *)

(** The core impossibility: identical sender views with different execution status *)
Definition IndistinguishableExecutionStatus : Prop :=
  forall op, exists t1 t2,
    sender_view t1 = sender_view t2 /\
    In (EvSend op) t1 /\
    In (EvSend op) t2 /\
    sender_saw_timeout t1 op /\
    sender_saw_timeout t2 op /\
    ~ op_executed t1 op /\
    op_executed t2 op.

(** Main theorem: No transparent overlay for non-idempotent operations *)
Theorem no_transparent_overlay_non_idempotent :
  IndistinguishableExecutionStatus ->
  forall (overlay : Overlay),
    IsTransparent overlay ->
    forall (op : Op) (m : Memory),
    ~ Idempotent op m ->
    (* Cannot have both safety and liveness *)
    ~ (OverlayLiveness overlay /\
       (forall t, op_executed t op -> overlay t op = false)).
Proof.
  intros Hindist overlay Htrans op m Hnon_idem [Hlive Hsafe].
  (* Get the two indistinguishable traces *)
  destruct (Hindist op) as [t1 [t2 [Hview_eq [Hsend1 [Hsend2 [Hto1 [Hto2 [Hno_exec1 Hexec2]]]]]]]].

  (* From liveness on t1: must retry *)
  assert (Hretry : overlay t1 op = true).
  { apply (Hlive t1 op); assumption. }

  (* From safety on t2: must not retry *)
  assert (Hno_retry : overlay t2 op = false).
  { apply (Hsafe t2). assumption. }

  (* By transparency: equal sender_views → equal decisions *)
  assert (Hdec_eq : overlay t1 op = overlay t2 op).
  { apply Htrans. exact Hview_eq. }

  (* Contradiction: true = false *)
  rewrite Hretry, Hno_retry in Hdec_eq.
  discriminate.
Qed.

(** Corollary: No transparent overlay for atomic operations *)
Corollary no_transparent_overlay_atomics :
  IndistinguishableExecutionStatus ->
  forall (overlay : Overlay),
    IsTransparent overlay ->
    (* For FADD with delta <> 0 *)
    (forall a delta, delta <> 0 ->
      ~ (OverlayLiveness overlay /\
         (forall t, op_executed t (OpFADD a delta) ->
           overlay t (OpFADD a delta) = false))) /\
    (* For CAS where first execution succeeds and expected <> new_val *)
    (forall a expected new_val,
      mem_read init_memory a = expected ->
      expected <> new_val ->
      ~ (OverlayLiveness overlay /\
         (forall t, op_executed t (OpCAS a expected new_val) ->
           overlay t (OpCAS a expected new_val) = false))).
Proof.
  intros Hindist overlay Htrans.
  split.
  - (* FADD case *)
    intros a delta Hdelta.
    apply (no_transparent_overlay_non_idempotent Hindist overlay Htrans (OpFADD a delta) init_memory).
    apply fadd_non_idempotent.
    (* delta <> 0 implies delta <> 0 *)
    lia.
  - (* CAS case *)
    intros a expected new_val Hmem Hdiff.
    apply (no_transparent_overlay_non_idempotent Hindist overlay Htrans (OpCAS a expected new_val) init_memory).
    rewrite cas_idempotent_iff.
    intros [Hcontra | Hcontra].
    + apply Hcontra. exact Hmem.
    + apply Hdiff. exact Hcontra.
Qed.


