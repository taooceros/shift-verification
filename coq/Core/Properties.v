(** * Safety and Liveness Properties *)

From Stdlib Require Import Arith.
From Stdlib Require Import List.
From ShiftVerification.Core Require Import Memory.
From ShiftVerification.Core Require Import Operations.
From ShiftVerification.Core Require Import Traces.
Import ListNotations.

(** ** Linearizability *)

(** A history is a sequence of operation invocations and responses *)
Inductive HistoryEvent : Type :=
  | HInvoke : nat -> Op -> HistoryEvent    (* process id, operation *)
  | HRespond : nat -> OpResult -> HistoryEvent.  (* process id, result *)

Definition History := list HistoryEvent.

(** A sequential specification: given initial memory and operation, what's the result? *)
Definition SequentialSpec := Memory -> Op -> Memory * OpResult.

(** The standard sequential spec for RDMA operations *)
Definition rdma_seq_spec : SequentialSpec := exec_op.

(** Extract history from a trace (simplified) *)
Fixpoint trace_to_history (t : Trace) (pid : nat) : History :=
  match t with
  | [] => []
  | EvSend op :: rest => HInvoke pid op :: trace_to_history rest pid
  | EvCompletion op res :: rest => HRespond pid res :: trace_to_history rest pid
  | _ :: rest => trace_to_history rest pid
  end.

(** A history is linearizable if there exists a legal sequential history
    that is equivalent (same operations and results) and respects real-time order *)
Definition Linearizable (h : History) (spec : SequentialSpec) : Prop :=
  (* Simplified: we'll expand this in the actual proofs *)
  True.  (* Placeholder - full definition requires more infrastructure *)

(** ** At-Most-Once Semantics *)

(** Operation equality (decidable) *)
Definition op_eq (op1 op2 : Op) : bool :=
  match op1, op2 with
  | OpWrite a1 v1, OpWrite a2 v2 => Nat.eqb a1 a2 && Nat.eqb v1 v2
  | OpRead a1, OpRead a2 => Nat.eqb a1 a2
  | OpFADD a1 d1, OpFADD a2 d2 => Nat.eqb a1 a2 && Nat.eqb d1 d2
  | OpCAS a1 e1 n1, OpCAS a2 e2 n2 => Nat.eqb a1 a2 && Nat.eqb e1 e2 && Nat.eqb n1 n2
  | _, _ => false
  end.

(** Proof that op_eq is a correct decision procedure *)
Lemma op_eq_refl : forall op, op_eq op op = true.
Proof.
  intros []; simpl; repeat rewrite Nat.eqb_refl; auto.
Qed.

Lemma op_eq_eq : forall op1 op2, op_eq op1 op2 = true <-> op1 = op2.
Proof.
  intros op1 op2; split; intros H.
  - destruct op1, op2; simpl in H; try discriminate;
    repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
    | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H; subst
    end; reflexivity.
  - subst. apply op_eq_refl.
Qed.

(** Count how many times an operation was executed *)
Fixpoint execution_count (t : Trace) (op : Op) : nat :=
  match t with
  | [] => 0
  | EvExecute op' _ :: rest =>
      (if op_eq op op' then 1 else 0) + execution_count rest op
  | _ :: rest => execution_count rest op
  end.

(** At-most-once: each operation is executed at most once *)
Definition AtMostOnce (t : Trace) : Prop :=
  forall op, execution_count t op <= 1.

(** Exactly-once: each sent operation is executed exactly once *)
Definition ExactlyOnce (t : Trace) : Prop :=
  forall op,
    In (EvSend op) t ->
    execution_count t op = 1.

(** ** Safety *)

(** A system is safe if all executions are linearizable *)
Definition Safe (traces : Trace -> Prop) (spec : SequentialSpec) : Prop :=
  forall t,
    traces t ->
    Linearizable (trace_to_history t 0) spec.

(** ** Liveness *)

(** Every sent operation eventually completes *)
Definition Live (t : Trace) : Prop :=
  forall op,
    In (EvSend op) t ->
    op_completed t op.

(** ** Overlay Model *)

(** An overlay is a function that decides whether to retransmit based on the trace.
    Importantly, the overlay can observe the FULL trace (including internal events),
    but a transparent overlay must make decisions based only on sender-observable events. *)
Definition Overlay := Trace -> Op -> bool.

(** A transparent overlay: decisions depend only on sender observations.
    This is the key constraint - if two traces have the same sender view,
    a transparent overlay must make the same retransmission decision. *)
Definition IsTransparent (overlay : Overlay) : Prop :=
  forall t1 t2 op,
    sender_view t1 = sender_view t2 ->
    overlay t1 op = overlay t2 op.

(** ** The Core Dilemma *)

(** If an overlay retransmits after timeout, it may violate safety *)
Definition retransmit_may_violate_safety (overlay : Overlay) : Prop :=
  exists t1 t2 op,
    (* Traces are indistinguishable *)
    sender_indistinguishable t1 t2 /\
    (* Sender sees timeout in both *)
    sender_saw_timeout t1 op /\
    sender_saw_timeout t2 op /\
    (* Retransmission is safe in t1 but unsafe in t2 *)
    (~ op_executed t1 op) /\  (* t1: packet was lost, retransmit is safe *)
    (op_executed t2 op).       (* t2: packet arrived, retransmit causes double execution *)

(** If an overlay doesn't retransmit after timeout, it may violate liveness *)
Definition no_retransmit_may_violate_liveness (overlay : Overlay) : Prop :=
  exists t op,
    sender_saw_timeout t op /\
    ~ op_executed t op /\
    overlay t op = false ->
    ~ op_completed t op.
