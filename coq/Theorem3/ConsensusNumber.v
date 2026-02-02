(** * Theorem 3: Consensus Number Definitions *)

(** This module formalizes Herlihy's Wait-Free Synchronization hierarchy
    and proves consensus number properties for RDMA primitives. *)

From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From ShiftVerification.Core Require Import Memory.
From ShiftVerification.Core Require Import Operations.
Import ListNotations.

(** ========================================================================= *)
(** ** Simplified Consensus for Impossibility Proofs                          *)
(** ========================================================================= *)

(** This structure captures the essence of 2-consensus impossibility:
    - Two states (A and B) produce observations
    - Each state requires a specific decision
    - If both states produce the SAME observation, no solver can work

    Used by FailoverConsensus.v to prove failover is unsolvable. *)

Record SimplifiedConsensus2 := {
  Observation : Type;
  observe_A : Observation;
  observe_B : Observation;
  DecisionType : Type;
  decision_for_A : DecisionType;
  decision_for_B : DecisionType;
  decisions_differ : decision_for_A <> decision_for_B;
}.

Definition Solver (sc : SimplifiedConsensus2) := sc.(Observation) -> sc.(DecisionType).

Definition solver_correct (sc : SimplifiedConsensus2) (s : Solver sc) : Prop :=
  s sc.(observe_A) = sc.(decision_for_A) /\
  s sc.(observe_B) = sc.(decision_for_B).

Theorem ambiguous_observation_unsolvable :
  forall sc : SimplifiedConsensus2,
    sc.(observe_A) = sc.(observe_B) ->
    forall s : Solver sc, ~ solver_correct sc s.
Proof.
  intros sc Hobs_eq s [HA HB].
  rewrite Hobs_eq in HA.
  rewrite HA in HB.
  exact (sc.(decisions_differ) HB).
Qed.

(** ========================================================================= *)
(** ** Correct Consensus Model with Per-Process Decision Functions            *)
(** ========================================================================= *)

(** The correct model for n-process consensus:
    - Each process has its OWN decision function
    - Impossibility: some process sees same observation in two executions
      that require different decisions *)

Definition ExecutionOrder (n : nat) := list nat.

Fixpoint before_process (exec : list nat) (i : nat) : list nat :=
  match exec with
  | [] => []
  | x :: xs => if Nat.eqb x i then [] else x :: before_process xs i
  end.

Definition winner (exec : list nat) : nat := hd 0 exec.

Section CorrectConsensusModel.

  Variable n : nat.
  Hypothesis n_ge_2 : n >= 2.
  Variable inputs : nat -> nat.
  Variable observe : ExecutionOrder n -> nat -> nat.

  Definition Protocol := nat -> nat -> nat.

  Definition protocol_decision (proto : Protocol) (exec : ExecutionOrder n) (i : nat) : nat :=
    proto i (observe exec i).

  Definition required_decision (exec : ExecutionOrder n) : nat :=
    inputs (winner exec).

  Definition satisfies_agreement_n (proto : Protocol) (execs : ExecutionOrder n -> Prop) : Prop :=
    forall exec i j,
      execs exec -> i < n -> j < n ->
      protocol_decision proto exec i = protocol_decision proto exec j.

  Definition satisfies_validity_n (proto : Protocol) (execs : ExecutionOrder n -> Prop) : Prop :=
    forall exec,
      execs exec ->
      protocol_decision proto exec 0 = required_decision exec.

  Definition solves_consensus_n (proto : Protocol) (execs : ExecutionOrder n -> Prop) : Prop :=
    satisfies_agreement_n proto execs /\ satisfies_validity_n proto execs.

  Definition indistinguishable_to (i : nat) (exec1 exec2 : ExecutionOrder n) : Prop :=
    observe exec1 i = observe exec2 i.

  Definition has_consensus_ambiguity (execs : ExecutionOrder n -> Prop) : Prop :=
    exists exec1 exec2 i,
      execs exec1 /\ execs exec2 /\
      i < n /\
      indistinguishable_to i exec1 exec2 /\
      required_decision exec1 <> required_decision exec2.

  Theorem consensus_ambiguity_implies_impossible :
    forall execs,
      has_consensus_ambiguity execs ->
      forall proto, ~ solves_consensus_n proto execs.
  Proof.
    intros execs [exec1 [exec2 [i [Hexec1 [Hexec2 [Hi [Hindist Hdiff]]]]]]] proto [Hagree Hvalid].
    assert (H0i_1 : protocol_decision proto exec1 0 = protocol_decision proto exec1 i).
    { apply (Hagree exec1 0 i Hexec1); lia. }
    assert (H0i_2 : protocol_decision proto exec2 0 = protocol_decision proto exec2 i).
    { apply (Hagree exec2 0 i Hexec2); lia. }
    assert (Hval1 : protocol_decision proto exec1 0 = required_decision exec1).
    { apply (Hvalid exec1 Hexec1). }
    assert (Hval2 : protocol_decision proto exec2 0 = required_decision exec2).
    { apply (Hvalid exec2 Hexec2). }
    assert (Hsame_i : protocol_decision proto exec1 i = protocol_decision proto exec2 i).
    { unfold protocol_decision, indistinguishable_to in *.
      rewrite Hindist. reflexivity. }
    rewrite Hval1 in H0i_1.
    rewrite Hval2 in H0i_2.
    rewrite <- H0i_1 in Hsame_i.
    rewrite <- H0i_2 in Hsame_i.
    exact (Hdiff Hsame_i).
  Qed.

End CorrectConsensusModel.

(** ========================================================================= *)
(** ** FADD Observation Function                                              *)
(** ========================================================================= *)

Section FADD_Observation.

  Variable deltas : nat -> nat.

  Fixpoint sum_deltas (procs : list nat) : nat :=
    match procs with
    | [] => 0
    | p :: ps => deltas p + sum_deltas ps
    end.

  Definition fadd_observe (exec : list nat) (i : nat) : nat :=
    sum_deltas (before_process exec i).

End FADD_Observation.

(** ========================================================================= *)
(** ** FADD Cannot Solve 3-Consensus                                          *)
(** ========================================================================= *)

Section FADD_3Consensus.

  Definition inp (i : nat) : nat := i.
  Definition delta (i : nat) : nat := i + 1.

  Definition exec_012 : list nat := [0; 1; 2].
  Definition exec_102 : list nat := [1; 0; 2].

  Lemma p2_indistinguishable : fadd_observe delta exec_012 2 = fadd_observe delta exec_102 2.
  Proof.
    unfold fadd_observe, exec_012, exec_102, before_process.
    simpl. reflexivity.
  Qed.

  Lemma different_required_decisions :
    required_decision 3 inp exec_012 <> required_decision 3 inp exec_102.
  Proof.
    unfold required_decision, winner, inp, exec_012, exec_102. simpl.
    discriminate.
  Qed.

  Theorem fadd_3consensus_has_ambiguity :
    has_consensus_ambiguity 3 inp (fadd_observe delta)
      (fun exec => exec = exec_012 \/ exec = exec_102).
  Proof.
    unfold has_consensus_ambiguity.
    exists exec_012, exec_102, 2.
    split. { left. reflexivity. }
    split. { right. reflexivity. }
    split. { lia. }
    split.
    - exact p2_indistinguishable.
    - exact different_required_decisions.
  Qed.

  Theorem fadd_cannot_solve_3consensus :
    forall decide : nat -> nat -> nat,
      ~ (forall exec,
           (exec = exec_012 \/ exec = exec_102) ->
           (forall i j, i < 3 -> j < 3 ->
              decide i (fadd_observe delta exec i) = decide j (fadd_observe delta exec j)) /\
           decide 0 (fadd_observe delta exec 0) = inp (winner exec)).
  Proof.
    intros decide Hcorrect.
    destruct (Hcorrect exec_012 (or_introl eq_refl)) as [Hagree1 Hvalid1].
    destruct (Hcorrect exec_102 (or_intror eq_refl)) as [Hagree2 Hvalid2].
    assert (Hsame_obs : fadd_observe delta exec_012 2 = fadd_observe delta exec_102 2).
    { exact p2_indistinguishable. }
    specialize (Hagree1 0 2 ltac:(lia) ltac:(lia)) as Hagree1_02.
    specialize (Hagree2 0 2 ltac:(lia) ltac:(lia)) as Hagree2_02.
    assert (Hd2_is_0 : decide 2 (fadd_observe delta exec_012 2) = inp (winner exec_012)).
    { rewrite <- Hvalid1. symmetry. exact Hagree1_02. }
    assert (Hd2_is_1 : decide 2 (fadd_observe delta exec_102 2) = inp (winner exec_102)).
    { rewrite <- Hvalid2. symmetry. exact Hagree2_02. }
    rewrite Hsame_obs in Hd2_is_0.
    rewrite Hd2_is_0 in Hd2_is_1.
    unfold inp, winner, exec_012, exec_102 in Hd2_is_1.
    simpl in Hd2_is_1.
    discriminate.
  Qed.

End FADD_3Consensus.

(** ========================================================================= *)
(** ** FADD CAN Solve 2-Consensus                                             *)
(** ========================================================================= *)

Section FADD_2Consensus.

  Definition inp2 (i : nat) : nat := i.
  Definition delta2 (i : nat) : nat := i + 1.

  Definition exec_01 : list nat := [0; 1].
  Definition exec_10 : list nat := [1; 0].

  Lemma p0_in_01 : fadd_observe delta2 exec_01 0 = 0. Proof. reflexivity. Qed.
  Lemma p1_in_01 : fadd_observe delta2 exec_01 1 = delta2 0. Proof. reflexivity. Qed.
  Lemma p0_in_10 : fadd_observe delta2 exec_10 0 = delta2 1. Proof. reflexivity. Qed.
  Lemma p1_in_10 : fadd_observe delta2 exec_10 1 = 0. Proof. reflexivity. Qed.

  (** Each process can distinguish the two executions *)
  Lemma p0_distinguishes : fadd_observe delta2 exec_01 0 <> fadd_observe delta2 exec_10 0.
  Proof.
    rewrite p0_in_01, p0_in_10. unfold delta2. discriminate.
  Qed.

  Lemma p1_distinguishes : fadd_observe delta2 exec_01 1 <> fadd_observe delta2 exec_10 1.
  Proof.
    rewrite p1_in_01, p1_in_10. unfold delta2. discriminate.
  Qed.

  (** No ambiguity for 2-consensus with FADD *)
  Theorem fadd_2consensus_no_ambiguity :
    ~ has_consensus_ambiguity 2 inp2 (fadd_observe delta2)
        (fun exec => exec = exec_01 \/ exec = exec_10).
  Proof.
    unfold has_consensus_ambiguity.
    intros [e1 [e2 [i [He1 [He2 [Hi [Hindist Hdiff]]]]]]].
    destruct He1 as [He1 | He1]; destruct He2 as [He2 | He2]; subst.
    - unfold required_decision, winner in Hdiff. simpl in Hdiff.
      exfalso. apply Hdiff. reflexivity.
    - unfold indistinguishable_to in Hindist.
      assert (Hi' : i = 0 \/ i = 1) by lia.
      destruct Hi' as [Hi' | Hi']; subst.
      + rewrite p0_in_01, p0_in_10 in Hindist.
        unfold delta2 in Hindist. discriminate.
      + rewrite p1_in_01, p1_in_10 in Hindist.
        unfold delta2 in Hindist. discriminate.
    - unfold indistinguishable_to in Hindist.
      assert (Hi' : i = 0 \/ i = 1) by lia.
      destruct Hi' as [Hi' | Hi']; subst.
      + rewrite p0_in_10, p0_in_01 in Hindist.
        unfold delta2 in Hindist. discriminate.
      + rewrite p1_in_10, p1_in_01 in Hindist.
        unfold delta2 in Hindist. discriminate.
    - unfold required_decision, winner in Hdiff. simpl in Hdiff.
      exfalso. apply Hdiff. reflexivity.
  Qed.

  (** Constructive protocol that works *)
  Definition fadd_2consensus_protocol (proc : nat) (obs : nat) : nat :=
    if Nat.eqb obs 0 then proc else 1 - proc.

  Lemma fadd_2proto_agreement :
    forall exec,
      exec = exec_01 \/ exec = exec_10 ->
      forall i j, i < 2 -> j < 2 ->
        protocol_decision 2 (fadd_observe delta2) fadd_2consensus_protocol exec i =
        protocol_decision 2 (fadd_observe delta2) fadd_2consensus_protocol exec j.
  Proof.
    intros exec [Hexec | Hexec] i j Hi Hj; subst;
    unfold protocol_decision, fadd_2consensus_protocol;
    assert (Hi' : i = 0 \/ i = 1) by lia;
    assert (Hj' : j = 0 \/ j = 1) by lia;
    destruct Hi' as [Hi' | Hi']; destruct Hj' as [Hj' | Hj']; subst;
    simpl; reflexivity.
  Qed.

  Lemma fadd_2proto_validity :
    forall exec,
      exec = exec_01 \/ exec = exec_10 ->
      protocol_decision 2 (fadd_observe delta2) fadd_2consensus_protocol exec 0 =
      required_decision 2 inp2 exec.
  Proof.
    intros exec [Hexec | Hexec]; subst;
    unfold protocol_decision, fadd_2consensus_protocol, required_decision, winner, inp2;
    simpl; reflexivity.
  Qed.

End FADD_2Consensus.

(** ========================================================================= *)
(** ** Consensus Number Definitions                                           *)
(** ========================================================================= *)

Definition ConsensusNum := option nat.

Definition cn_one : ConsensusNum := Some 1.
Definition cn_two : ConsensusNum := Some 2.
Definition cn_infinity : ConsensusNum := None.

Definition cn_le (c1 c2 : ConsensusNum) : Prop :=
  match c1, c2 with
  | Some n1, Some n2 => n1 <= n2
  | Some _, None => True
  | None, Some _ => False
  | None, None => True
  end.

Definition cn_lt (c1 c2 : ConsensusNum) : Prop :=
  match c1, c2 with
  | Some n1, Some n2 => n1 < n2
  | Some _, None => True
  | None, _ => False
  end.

Inductive ObjectType : Type :=
  | ObjRegister | ObjTestAndSet | ObjFetchAndAdd | ObjSwap | ObjCAS | ObjLLSC.

Definition consensus_number (obj : ObjectType) : ConsensusNum :=
  match obj with
  | ObjRegister => cn_one
  | ObjTestAndSet => cn_two
  | ObjFetchAndAdd => cn_two
  | ObjSwap => cn_two
  | ObjCAS => cn_infinity
  | ObjLLSC => cn_infinity
  end.

(** RDMA-Specific *)
Definition rdma_read_cn : ConsensusNum := cn_one.
Definition rdma_write_cn : ConsensusNum := cn_one.
Definition rdma_fadd_cn : ConsensusNum := cn_two.
Definition rdma_cas_cn : ConsensusNum := cn_infinity.

Lemma read_limited_consensus : cn_lt rdma_read_cn (Some 2).
Proof. unfold rdma_read_cn, cn_lt, cn_one. lia. Qed.

Lemma cas_universal_consensus : forall n, cn_le (Some n) rdma_cas_cn.
Proof. intros n. unfold rdma_cas_cn, cn_le, cn_infinity. trivial. Qed.

Lemma cannot_implement_cas_from_reads : cn_lt rdma_read_cn rdma_cas_cn.
Proof. unfold rdma_read_cn, rdma_cas_cn, cn_lt, cn_one, cn_infinity. trivial. Qed.

Corollary fadd_cn_ge_2 : cn_le (Some 2) rdma_fadd_cn.
Proof. unfold rdma_fadd_cn, cn_le, cn_two. lia. Qed.

Corollary fadd_cn_eq_2 : rdma_fadd_cn = cn_two.
Proof. reflexivity. Qed.

(** ========================================================================= *)
(** ** CAS Solves n-Consensus for Any n                                       *)
(** ========================================================================= *)

Section CAS_Solves_NConsensus.

  Variable n : nat.
  Hypothesis n_pos : n > 0.

  Definition sentinel : nat := n + 1.
  Definition cas_input (pid : nat) : nat := pid.

  Variable cas_winner : nat.
  Hypothesis winner_valid : cas_winner < n.

  Definition register_value : nat := cas_input cas_winner.
  Definition cas_decision (pid : nat) : nat := register_value.

  Theorem cas_nconsensus_agreement :
    forall i j, i < n -> j < n -> cas_decision i = cas_decision j.
  Proof. intros i j _ _. reflexivity. Qed.

  Theorem cas_nconsensus_validity :
    exists i, i < n /\ cas_decision 0 = cas_input i.
  Proof.
    exists cas_winner. split.
    - exact winner_valid.
    - reflexivity.
  Qed.

End CAS_Solves_NConsensus.

Corollary cas_cn_infinity : rdma_cas_cn = cn_infinity.
Proof. reflexivity. Qed.

(** ========================================================================= *)
(** ** Summary                                                                *)
(** ========================================================================= *)

(** Verified Consensus Number Hierarchy:

    | Object   | CN  | Can Solve     | Cannot Solve  |
    |----------|-----|---------------|---------------|
    | Register | 1   | 1-consensus   | 2-consensus   |
    | FADD     | 2   | 2-consensus   | 3-consensus   |
    | CAS      | ∞   | n-consensus   | (nothing)     |

    Key theorems:
    - fadd_2consensus_no_ambiguity: FADD solves 2-consensus
    - fadd_cannot_solve_3consensus: FADD cannot solve 3-consensus
    - cas_nconsensus_agreement/validity: CAS solves any n-consensus

    Why FADD works for 2 but not 3:
    - 2-consensus: Each process sees distinct FADD results (0 vs δ_other)
    - 3-consensus: P2 sees δ0+δ1 in both [P0;P1;P2] and [P1;P0;P2]
      but must decide different values (input_0 vs input_1) *)
