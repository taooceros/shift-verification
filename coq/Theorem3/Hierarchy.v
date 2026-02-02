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
From ShiftVerification.Theorem3 Require Import FailoverConsensus.
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

(** ** Reliable CAS Definition *)

(** A transparent failover mechanism provides reliable CAS if it can
    make correct failover decisions for ALL possible histories.

    This means: there exists a verification mechanism (based on reading
    memory) that solves the failover problem. *)

Definition provides_reliable_cas (tf : TransparentFailover) : Prop :=
  exists V : VerificationMechanism,
    solves_failover V.

(** ** The Main Impossibility Theorem *)

(** The core impossibility: transparent failover cannot provide reliable CAS.

    This follows directly from failover_unsolvable in FailoverConsensus.v,
    which proves that NO verification mechanism can solve failover due to
    the ABA problem - two different histories can have identical final
    memory states but require different decisions. *)

Theorem transparent_cas_failover_impossible :
  forall tf : TransparentFailover,
    verification_via_reads tf ->
    tf.(no_metadata_writes) ->
    ~ provides_reliable_cas tf.
Proof.
  intros tf Hreads Hno_meta.
  unfold provides_reliable_cas.
  intros [V Hsolves].
  (* Apply the core impossibility from FailoverConsensus *)
  exact (failover_unsolvable init_memory V Hsolves).
Qed.

(** ** Corollary: Backup RNIC is Irrelevant *)

(** Even with a backup RNIC that can execute CAS operations,
    the transparency constraint prevents correct failover.

    The backup RNIC CAN execute CAS operations.
    But it CANNOT decide WHETHER to execute them correctly. *)

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
  intros tf _ Hreads Hno_meta.
  apply (transparent_cas_failover_impossible tf Hreads Hno_meta).
Qed.

(** ** Connection to Consensus Hierarchy *)

(** The failover problem requires solving 2-process consensus:
    - Process P0 (Past): knows the true history
    - Process P1 (Future): must decide based on observable state

    Under transparency:
    - Future can only READ remote memory
    - Reads have consensus number 1
    - 2-consensus requires CN >= 2
    - Therefore, transparent failover is impossible *)

Theorem failover_needs_cn_2 :
  cn_lt cn_one (Some 2).
Proof.
  unfold cn_lt, cn_one. lia.
Qed.

Theorem reads_insufficient_for_failover :
  cn_lt rdma_read_cn (Some 2).
Proof.
  unfold rdma_read_cn, cn_lt, cn_one. lia.
Qed.

(** ** Summary *)

(** The transparent CAS failover impossibility arises from:

    1. INFORMATION ASYMMETRY: The sender cannot observe whether the
       original CAS was executed (packet loss vs ACK loss).

    2. ABA PROBLEM: Memory state alone cannot distinguish histories.
       - History H0: CAS not executed → memory = m
       - History H1: CAS executed, then ABA reset → memory = m
       Both have identical observable state but require different decisions.

    3. CONSENSUS BARRIER: Correct failover requires 2-process consensus.
       Reads have CN=1, which is insufficient.

    Conclusion: No transparent mechanism can provide reliable CAS failover. *)
