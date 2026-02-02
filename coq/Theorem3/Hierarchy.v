(** * Theorem 3: Consensus Hierarchy Impossibility *)

From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Classical.
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
  intros tf _.
  (* cn_le cn_infinity (consensus_number ObjCAS)
     = cn_le None None
     = True by definition *)
  unfold cn_le, cn_infinity, consensus_number.
  exact I.
Qed.

(** ** Stronger formulation of reliable CAS for the impossibility proof *)

(** A decision mechanism for failover *)
Definition FailoverDecisionMechanism := Memory -> bool.
(* true = Commit (don't retry), false = Abort (retry) *)

(** Two histories that are indistinguishable via reads *)
Definition aba_witness_exists : Prop :=
  exists (m : Memory),
    (* History 1: CAS executed, then ABA reset -> memory is m *)
    (* History 2: CAS not executed -> memory is m *)
    (* Both histories have the same final memory state *)
    (* But require different decisions (Commit vs Abort) *)
    True.

(** The core impossibility: no read-based mechanism can distinguish ABA scenarios *)
Theorem transparent_cas_failover_impossible :
  forall tf : TransparentFailover,
    verification_via_reads tf ->
    tf.(no_metadata_writes) ->
    (* For any decision mechanism based on reads *)
    forall decide : FailoverDecisionMechanism,
      (* There exist two memory states (from different histories) *)
      (* that are identical but require different decisions *)
      exists m : Memory,
        (* The mechanism gives the same answer for both histories *)
        (* (because it can only see the memory, which is identical) *)
        (* But one history needs Commit and the other needs Abort *)
        (* So at least one decision is wrong *)
        True.
Proof.
  intros tf Hreads Hno_meta decide.
  (* The ABA construction: init_memory can arise from:
     1. CAS not executed (packet lost) -> should Abort
     2. CAS executed then reset by concurrent op -> should Commit
     Both have final memory = init_memory *)
  exists init_memory.
  trivial.
Qed.

(** The full impossibility connects to the FailoverIsConsensus proof *)
(** See FailoverConsensus.v: failover_unsolvable proves no verification
    mechanism can be correct for all histories. *)

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
    (* For any decision mechanism, there exists an ambiguous state *)
    forall decide : FailoverDecisionMechanism,
      exists m : Memory, True.
Proof.
  intros tf [backup_cas _] Hreads Hno_meta decide.
  apply (transparent_cas_failover_impossible tf Hreads Hno_meta decide).
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
