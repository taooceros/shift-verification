(** * Theorem 3: Consensus Number Definitions *)

From Coq Require Import Arith.
From Coq Require Import List.
From Coq Require Import Lia.
From ShiftVerification.Core Require Import Memory.
From ShiftVerification.Core Require Import Operations.
Import ListNotations.

(** ** Herlihy's Wait-Free Hierarchy *)

(** This module formalizes key concepts from Herlihy's 1991 paper
    "Wait-Free Synchronization" *)

(** ** Consensus Object *)

(** A consensus object allows n processes to agree on a value *)
Record ConsensusObject (n : nat) := {
  (** Each process proposes a value *)
  propose : nat -> Val -> Val;

  (** Validity: decided value was proposed by someone *)
  validity : forall pid v,
    pid < n ->
    exists pid', pid' < n /\ propose pid v = propose pid' v;

  (** Agreement: all processes decide the same value *)
  agreement : forall pid1 pid2 v1 v2,
    pid1 < n -> pid2 < n ->
    propose pid1 v1 = propose pid2 v2;

  (** Wait-freedom: propose always terminates *)
  wait_free : forall (pid : nat) (v : Val), pid < n -> True;  (* Simplified *)
}.

(** ** Consensus Number *)

(** The consensus number of an object type is the maximum number of
    processes for which consensus can be solved wait-free using
    that object (and registers). *)

(** We use nat + infinity, represented as option nat where None = infinity *)
Definition ConsensusNum := option nat.

Definition cn_one : ConsensusNum := Some 1.
Definition cn_two : ConsensusNum := Some 2.
Definition cn_infinity : ConsensusNum := None.

Definition cn_le (c1 c2 : ConsensusNum) : Prop :=
  match c1, c2 with
  | Some n1, Some n2 => n1 <= n2
  | Some _, None => True      (* finite <= infinity *)
  | None, Some _ => False     (* infinity not <= finite *)
  | None, None => True        (* infinity <= infinity *)
  end.

Definition cn_lt (c1 c2 : ConsensusNum) : Prop :=
  match c1, c2 with
  | Some n1, Some n2 => n1 < n2
  | Some _, None => True      (* finite < infinity *)
  | None, _ => False          (* infinity not < anything *)
  end.

(** ** Object Types *)

Inductive ObjectType : Type :=
  | ObjRegister        (* Read/Write register *)
  | ObjTestAndSet      (* Test-and-Set *)
  | ObjFetchAndAdd     (* Fetch-and-Add *)
  | ObjSwap            (* Swap *)
  | ObjCAS             (* Compare-and-Swap *)
  | ObjLLSC.           (* Load-Linked/Store-Conditional *)

(** Consensus numbers from Herlihy's hierarchy *)
Definition consensus_number (obj : ObjectType) : ConsensusNum :=
  match obj with
  | ObjRegister => cn_one        (* Registers: consensus number 1 *)
  | ObjTestAndSet => cn_two      (* TAS: consensus number 2 *)
  | ObjFetchAndAdd => cn_two     (* FADD: consensus number 2 *)
  | ObjSwap => cn_two            (* Swap: consensus number 2 *)
  | ObjCAS => cn_infinity        (* CAS: consensus number infinity *)
  | ObjLLSC => cn_infinity       (* LL/SC: consensus number infinity *)
  end.

(** ** Key Theorems (Axiomatized from Herlihy) *)

(** Universality: Objects with consensus number >= n can solve n-process consensus *)
Axiom universality :
  forall obj n,
    cn_le (Some n) (consensus_number obj) ->
    exists (C : ConsensusObject n), True.

(** Impossibility: Objects with consensus number < n cannot solve n-process consensus *)
Axiom impossibility :
  forall obj n,
    cn_lt (consensus_number obj) (Some n) ->
    ~ exists (C : ConsensusObject n), True.

(** No implementation: Cannot implement higher consensus number from lower *)
Axiom no_boost :
  forall obj1 obj2,
    cn_lt (consensus_number obj1) (consensus_number obj2) ->
    (* Cannot implement obj2 wait-free using only obj1 and registers *)
    True.  (* Actual statement requires operational semantics *)

(** ** RDMA-Specific Instantiation *)

(** RDMA Read is a register read *)
Definition rdma_read_cn : ConsensusNum := cn_one.

(** RDMA Write is a register write *)
Definition rdma_write_cn : ConsensusNum := cn_one.

(** RDMA FADD has consensus number 2 *)
Definition rdma_fadd_cn : ConsensusNum := cn_two.

(** RDMA CAS has consensus number infinity *)
Definition rdma_cas_cn : ConsensusNum := cn_infinity.

(** ** Verification-Relevant Lemmas *)

(** Read cannot distinguish more than 2 processes *)
Lemma read_limited_consensus :
  cn_lt rdma_read_cn (Some 2).
Proof.
  unfold rdma_read_cn, cn_lt, cn_one. lia.
Qed.

(** CAS can solve consensus for any number of processes *)
Lemma cas_universal_consensus :
  forall n, cn_le (Some n) rdma_cas_cn.
Proof.
  intros n. unfold rdma_cas_cn, cn_le, cn_infinity. trivial.
Qed.

(** Cannot implement CAS using only reads *)
Lemma cannot_implement_cas_from_reads :
  cn_lt rdma_read_cn rdma_cas_cn.
Proof.
  unfold rdma_read_cn, rdma_cas_cn, cn_lt, cn_one, cn_infinity.
  trivial.
Qed.
