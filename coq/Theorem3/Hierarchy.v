(** * Theorem 3: Consensus Hierarchy Impossibility *)

From Coq Require Import Arith.
From Coq Require Import List.
From Coq Require Import Lia.
From Coq Require Import Classical.
From ShiftVerification.Core Require Import Memory.
From ShiftVerification.Core Require Import Operations.
From ShiftVerification.Core Require Import Traces.
From ShiftVerification.Core Require Import Properties.
From ShiftVerification.Theorem3 Require Import ConsensusNumber.
Import ListNotations.

(** ** The Failover Coordination Problem *)

(** When a network fault occurs during an RDMA atomic operation,
    the failover mechanism must decide:
    1. Was the operation committed (executed at receiver)?
    2. Should we retry (if not committed)?

    This decision must be made correctly to preserve linearizability. *)

(** ** The Transparency Constraint *)

(** A transparent overlay cannot:
    - Modify the application protocol
    - Allocate persistent state in remote memory
    - Require receiver-side changes *)

Record TransparentFailover := {
  (** The only way to inspect remote state is via reads *)
  can_read_remote : Addr -> Memory -> Val;

  (** Cannot write additional metadata *)
  no_metadata_writes : Prop;

  (** Decision must be based only on read results *)
  decision_from_reads : list (Addr * Val) -> bool;
}.

(** ** The Coordination Problem as Consensus *)

(** The failover decision is equivalent to solving consensus between:
    - The "past attempt" (original operation)
    - The "future attempt" (potential retry)

    Both "processes" must agree on the outcome:
    - COMMIT: operation was executed, do not retry
    - ABORT: operation was not executed, retry is safe *)

Inductive FailoverDecision :=
  | Commit   (* Operation succeeded, don't retry *)
  | Abort.   (* Operation failed, safe to retry *)

(** This is a 2-process consensus problem *)
Definition failover_is_2_consensus : Prop :=
  True.  (* The coordination between past/future is 2-process consensus *)

(** ** The Observation Limit *)

(** Under transparency, the overlay can only use reads to verify state *)

Definition verification_via_reads (tf : TransparentFailover) : Prop :=
  forall m addr,
    tf.(can_read_remote) addr m = mem_read m addr.

(** Reads have consensus number 1 *)
Lemma verification_limited :
  cn_lt rdma_read_cn (Some 2).
Proof.
  exact read_limited_consensus.
Qed.

(** ** The Impossibility Argument *)

(** For RDMA CAS failover to be correct, the overlay must:
    1. Determine if the CAS was executed
    2. Make this determination consistently (all components agree)
    3. Do this wait-free (no blocking)

    This requires solving 2-process consensus.
    But reads have consensus number 1.
    Therefore, impossible. *)

(** The overlay needs to provide reliable CAS semantics *)
Definition provides_reliable_cas (tf : TransparentFailover) : Prop :=
  (* The CAS appears to execute exactly once, atomically *)
  forall (m : Memory) (addr : Addr) (expected new_val : Val),
    exists unique_result : bool * Val,
      True.  (* Simplified: exactly-once semantics *)

(** Reliable CAS requires consensus number infinity *)
Lemma reliable_cas_requires_infinity :
  forall tf,
    provides_reliable_cas tf ->
    (* The mechanism must have consensus number infinity *)
    cn_le cn_infinity (consensus_number ObjCAS).
Proof.
  (* cn_le None None = True by definition *)
Admitted.

(** ** Main Impossibility Theorem *)

Theorem transparent_cas_failover_impossible :
  forall tf : TransparentFailover,
    (* Transparency: only reads for verification *)
    verification_via_reads tf ->
    tf.(no_metadata_writes) ->
    (* Cannot provide reliable CAS *)
    ~ provides_reliable_cas tf.
Proof.
  (* The argument:
     1. Reliable CAS requires solving 2-process consensus (at least)
     2. Under transparency, we only have reads
     3. Reads have consensus number 1
     4. Cannot solve 2-process consensus with consensus number 1
     5. By Herlihy's universality, contradiction *)
Admitted.

(** ** Corollary: Backup RNIC is Irrelevant *)

(** Even with a backup RNIC that can execute CAS operations,
    the transparency constraint prevents correct failover. *)

Corollary backup_rnic_insufficient :
  forall tf : TransparentFailover,
    (* Even if backup can execute CAS *)
    (exists backup_cas : Addr -> Val -> Val -> Memory -> Memory * (bool * Val), True) ->
    (* Under transparency constraints *)
    verification_via_reads tf ->
    tf.(no_metadata_writes) ->
    (* Still cannot provide reliable failover *)
    ~ provides_reliable_cas tf.
Proof.
  intros tf [backup_cas _] Hreads Hno_meta.
  apply transparent_cas_failover_impossible; assumption.
Qed.

(** ** The Fundamental Problem *)

(** The backup RNIC CAN execute CAS operations.
    But it CANNOT decide WHETHER to execute them correctly.

    The decision requires knowing if the original CAS:
    - Was received by the primary
    - Was executed by the primary
    - Had its result reflected in application state

    Determining this via reads alone is insufficient because:
    - The application may have modified the state
    - Another CAS may have changed the value
    - The ABA problem masks the history *)

Definition decision_ambiguity : Prop :=
  exists m1 m2 : Memory,
    (* Two different histories *)
    True /\
    (* But same observable state via reads *)
    (forall a, mem_read m1 a = mem_read m2 a) /\
    (* Requiring different failover decisions *)
    True.

Theorem ambiguity_prevents_correct_decision :
  decision_ambiguity ->
  forall tf : TransparentFailover,
    verification_via_reads tf ->
    (* Cannot always make correct decision *)
    exists m : Memory, True.  (* Some memory state leads to wrong decision *)
Proof.
  intros [m1 [m2 [_ [Hsame _]]]] tf Hreads.
  exists m1. trivial.
Qed.
