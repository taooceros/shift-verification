(** * Memory Model for RDMA Verification *)

From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import FunctionalExtensionality.
Import ListNotations.

(** ** Basic Types *)

(** Memory addresses *)
Definition Addr := nat.

(** Values stored in memory *)
Definition Val := nat.

(** A default value for uninitialized memory *)
Definition default_val : Val := 0.

(** ** Memory State *)

(** Memory is a function from addresses to values *)
Definition Memory := Addr -> Val.

(** Initial memory: all addresses contain the default value *)
Definition init_memory : Memory := fun _ => default_val.

(** Read from memory *)
Definition mem_read (m : Memory) (a : Addr) : Val := m a.

(** Write to memory *)
Definition mem_write (m : Memory) (a : Addr) (v : Val) : Memory :=
  fun a' => if Nat.eqb a' a then v else m a'.

(** ** Memory Properties *)

Lemma mem_read_write_same : forall m a v,
  mem_read (mem_write m a v) a = v.
Proof.
  intros. unfold mem_read, mem_write.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma mem_read_write_other : forall m a1 a2 v,
  a1 <> a2 ->
  mem_read (mem_write m a2 v) a1 = mem_read m a1.
Proof.
  intros. unfold mem_read, mem_write.
  destruct (Nat.eqb_spec a1 a2).
  - contradiction.
  - reflexivity.
Qed.

Lemma mem_write_write_same : forall m a v1 v2,
  mem_write (mem_write m a v1) a v2 = mem_write m a v2.
Proof.
  intros. unfold mem_write.
  extensionality a'.
  destruct (Nat.eqb_spec a' a); reflexivity.
Qed.

Lemma mem_write_write_comm : forall m a1 a2 v1 v2,
  a1 <> a2 ->
  mem_write (mem_write m a1 v1) a2 v2 = mem_write (mem_write m a2 v2) a1 v1.
Proof.
  intros. unfold mem_write.
  extensionality a'.
  destruct (Nat.eqb_spec a' a2); destruct (Nat.eqb_spec a' a1); subst; auto.
  contradiction.
Qed.

(** ** Memory Reuse Model *)

(** Predicate: memory at address a has been reused (written with a new value) *)
Definition memory_reused (m_before m_after : Memory) (a : Addr) : Prop :=
  m_before a <> m_after a.

(** Predicate: memory at address a is unchanged *)
Definition memory_unchanged (m_before m_after : Memory) (a : Addr) : Prop :=
  m_before a = m_after a.
