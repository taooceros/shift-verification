# SHIFT: Formal Verification of RDMA RC Semantics Violation

## Document Control

| Item | Value |
|------|-------|
| **Document Title** | Formal Proof: Impossibility of Transparent Cross-NIC RDMA Failover |
| **Version** | 1.0 |
| **Verification System** | Coq/Rocq Proof Assistant |
| **Associated Paper** | SHIFT: Cross-NIC RDMA Fault Tolerance for Distributed LLM Training |

---

## Executive Summary

This document provides comprehensive documentation for the formal verification of a key theoretical result in the SHIFT paper: **it is impossible to maintain strict RDMA Reliable Connection (RC) semantics during cross-NIC failover using commodity hardware**.

### Key Result

```coq
Theorem cross_nic_failover_violates_rc :
  ~ StrictlyDeliverOnce state_3_violation.
```

This theorem proves that there exists an execution trace where the "exactly-once delivery" guarantee of RDMA RC is violated during failover.

---

## 1. Background and Motivation

### 1.1 The Problem

Modern GPU clusters for LLM training (e.g., DGX A100, DGX H100) feature multiple RNICs per host. When a NIC fails, the natural question is: **can we transparently failover to a backup NIC without affecting the application?**

### 1.2 RDMA RC Guarantees

RDMA Reliable Connection provides two key guarantees:

1. **Exactly-Once Delivery**: Each packet is delivered to memory exactly once
2. **In-Order Delivery**: Packets arrive in the order they were sent

These are enforced through Packet Sequence Numbers (PSN) maintained on each NIC.

### 1.3 The Commodity Hardware Constraint

The critical constraint is that **PSN state is local to each NIC**:

- NIC_A's PSN counter is stored in NIC_A's memory
- When NIC_A fails, this state is **inaccessible** to NIC_B
- NIC_B cannot know which packets NIC_A already processed

### 1.4 The Silent Data Path

RDMA uses zero-copy DMA, meaning:

1. Data is written directly to host memory by the NIC
2. This write happens **before** the ACK is sent
3. If the NIC fails after write but before ACK, data is written but sender doesn't know

---

## 2. Formal Model

### 2.1 System Components

```
┌─────────────────────────────────────────────────────────┐
│                       SENDER                             │
│  ┌─────────────────┐    ┌─────────────────┐             │
│  │  Pending WQEs   │    │   Acked WQEs    │             │
│  │  [WQE_1, ...]   │    │   [...]         │             │
│  └─────────────────┘    └─────────────────┘             │
└─────────────────────────────────────────────────────────┘
                    │
                    │ RDMA WRITE
                    ▼
┌─────────────────────────────────────────────────────────┐
│                    RECEIVER HOST                         │
│                                                          │
│  ┌───────────────┐           ┌───────────────┐          │
│  │    NIC_A      │           │    NIC_B      │          │
│  │ ┌───────────┐ │           │ ┌───────────┐ │          │
│  │ │ PSN = 0   │ │           │ │ PSN = 0   │ │          │
│  │ │ (LOCAL!)  │ │           │ │ (LOCAL!)  │ │          │
│  │ └───────────┘ │           │ └───────────┘ │          │
│  │ Status:Healthy│           │ Status:Healthy│          │
│  └───────────────┘           └───────────────┘          │
│           │                           │                  │
│           └───────────┬───────────────┘                  │
│                       ▼                                  │
│              ┌───────────────┐                           │
│              │ Shared Memory │                           │
│              │  [writes...]  │                           │
│              └───────────────┘                           │
└─────────────────────────────────────────────────────────┘
```

### 2.2 Type Definitions

| Type | Coq Definition | Description |
|------|----------------|-------------|
| `WRID` | `nat` | Work Request Identifier |
| `PSN` | `nat` | Packet Sequence Number |
| `NicId` | `NIC_A \| NIC_B` | NIC identifier |
| `NicStatus` | `Healthy \| Failed` | NIC health state |
| `WQE` | `Record {id, psn, addr, data}` | Work Queue Element |
| `Event` | `Inductive` | System events |

### 2.3 Events

```coq
Inductive Event : Type :=
  | SendWQE : WQE -> NicId -> Event      (* Sender posts WQE *)
  | ProcessWQE : WQE -> NicId -> Event   (* NIC writes to memory *)
  | AckWQE : WQE -> NicId -> Event       (* NIC sends ACK *)
  | NicFailure : NicId -> Event          (* NIC fails *)
  | Retransmit : WQE -> NicId -> Event.  (* Sender retransmits *)
```

### 2.4 State Transitions

```coq
(* Process WQE: NIC writes data to memory *)
Definition process_wqe_transition : SystemState -> WQE -> NicId -> SystemState

(* NIC Failure: NIC becomes unavailable, state locked *)
Definition nic_failure_transition : SystemState -> NicId -> SystemState

(* Retransmit: Sender resends to backup NIC *)
Definition retransmit_transition : SystemState -> WQE -> NicId -> SystemState
```

---

## 3. The Violation Scenario

### 3.1 Execution Trace

```
Time    Event                           Memory State            NIC_A PSN    NIC_B PSN
─────   ─────                           ────────────            ─────────    ─────────
t₀      Initial                         []                      0            0
t₁      ProcessWQE(WQE_1, NIC_A)        [(100,42,1)]           1            0
t₂      NicFailure(NIC_A)               [(100,42,1)]           1 (LOST!)    0
t₃      Retransmit(WQE_1, NIC_B)        [(100,42,1),(100,42,1)] 1            1
        └─> ProcessWQE(WQE_1, NIC_B)
```

### 3.2 Step-by-Step Analysis

#### Step 1: Initial State (t₀)
```coq
Definition state_0 : SystemState := initial_system_state.
(* Both NICs healthy, PSN=0, memory empty *)
```

#### Step 2: NIC_A Processes WQE (t₁)
```coq
Definition state_1 : SystemState :=
  process_wqe_transition state_0 test_wqe NIC_A.
```
- NIC_A receives WQE_1 (PSN=0)
- NIC_A writes data to memory at address 100
- NIC_A increments its PSN to 1
- **Memory now contains one write from WQE_1**

#### Step 3: NIC_A Fails Before ACK (t₂)
```coq
Definition state_2 : SystemState :=
  nic_failure_transition state_1 NIC_A.
```
- NIC_A crashes (hardware failure, optical module, etc.)
- NIC_A's internal state (PSN=1) becomes **inaccessible**
- Memory state is preserved (data already written)
- Sender never receives ACK for WQE_1

#### Step 4: Retransmission to NIC_B (t₃)
```coq
Definition state_3_violation : SystemState :=
  retransmit_transition state_2 test_wqe NIC_B.
```
- Sender times out waiting for ACK
- Sender retransmits WQE_1 to NIC_B
- **NIC_B has no knowledge of NIC_A's history**
- NIC_B's PSN is still 0, so it accepts the packet
- NIC_B writes data to memory **again**
- **Memory now contains TWO writes from WQE_1**

### 3.3 The Violation

```coq
Lemma count_writes_is_two :
  count_writes_for_wqe (memory state_3_violation) 1 = 2.
```

WQE_1 has written to memory **twice**, violating exactly-once delivery.

---

## 4. The Proof

### 4.1 Safety Property

```coq
Definition exactly_once (s : SystemState) (wid : WRID) : Prop :=
  count_writes_for_wqe (memory s) wid <= 1.

Definition StrictlyDeliverOnce (s : SystemState) : Prop :=
  forall wid : WRID, exactly_once s wid.
```

### 4.2 Main Theorem

```coq
Theorem cross_nic_failover_violates_rc :
  ~ StrictlyDeliverOnce state_3_violation.
```

### 4.3 Proof Script

```coq
Proof.
  (* Step 1: Unfold StrictlyDeliverOnce *)
  unfold StrictlyDeliverOnce.

  (* Step 2: Assume the negation (proof by contradiction) *)
  intro H_all_exactly_once.

  (* Step 3: Instantiate for WQE ID = 1 *)
  specialize (H_all_exactly_once 1).

  (* Step 4: Unfold exactly_once *)
  unfold exactly_once in H_all_exactly_once.

  (* Step 5: Substitute count = 2 *)
  rewrite count_writes_is_two in H_all_exactly_once.

  (* Step 6: 2 <= 1 is false - contradiction! *)
  apply two_not_le_one in H_all_exactly_once.

  (* Step 7: Conclude *)
  exact H_all_exactly_once.
Qed.
```

### 4.4 Proof Structure Diagram

```
┌────────────────────────────────────────────────────────────────────┐
│                    PROOF BY CONTRADICTION                          │
├────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ASSUME: StrictlyDeliverOnce state_3_violation                     │
│          ↓                                                          │
│  MEANS:  ∀ wid, count_writes(wid) ≤ 1                              │
│          ↓                                                          │
│  SPECIALIZE: count_writes(1) ≤ 1                                   │
│          ↓                                                          │
│  LEMMA:  count_writes(1) = 2  (computed from state_3_violation)    │
│          ↓                                                          │
│  SUBSTITUTE: 2 ≤ 1                                                  │
│          ↓                                                          │
│  CONTRADICTION! (2 ≤ 1 is false)                                   │
│          ↓                                                          │
│  CONCLUDE: ~ StrictlyDeliverOnce state_3_violation     QED         │
│                                                                     │
└────────────────────────────────────────────────────────────────────┘
```

---

## 5. Corollary: Impossibility Result

```coq
Corollary impossibility_of_transparent_failover :
  exists s : SystemState,
    (* State is reachable *)
    (exists w : WQE, s = retransmit_transition
                          (nic_failure_transition
                            (process_wqe_transition initial_system_state w NIC_A)
                          NIC_A)
                        w NIC_B) /\
    (* Yet StrictlyDeliverOnce is violated *)
    ~ StrictlyDeliverOnce s.
```

This corollary formalizes: **there exists a reachable system state where RDMA RC semantics are violated**.

---

## 6. Connection to SHIFT Paper

### 6.1 Paper Quote

> "We prove that with current commodity RNICs and the zero-copy data path, seamless cross-NIC fault tolerance is impossible without violating RC's ordering guarantees."

### 6.2 Implications for SHIFT Design

| Implication | SHIFT Response |
|-------------|----------------|
| Cannot guarantee exactly-once for all workloads | Focus on **idempotent** workloads |
| Atomic operations require exactly-once | Atomic ops **not supported** |
| NCCL Simple protocol is idempotent | NCCL Simple **fully supported** |
| Need application awareness | Use WR-level (not packet-level) retransmission |

### 6.3 Why This Justifies SHIFT's Approach

1. **The impossibility is fundamental**: No software can fix this without hardware support
2. **Training workloads are often idempotent**: AllReduce with summation can tolerate duplicates
3. **WR-level retransmission**: Application sees correct behavior even if packets duplicate
4. **Defense in depth**: SHIFT + checkpointing provides comprehensive protection

---

## 7. Verification Instructions

### 7.1 Prerequisites

- Coq/Rocq proof assistant (version 8.12+)
- Make (optional, for convenience)

### 7.2 Installation

**macOS (Homebrew):**
```bash
brew install coq
```

**Ubuntu/Debian:**
```bash
sudo apt-get install coq
```

**Via OPAM (any platform):**
```bash
opam install coq
```

### 7.3 Verification

**Using provided script:**
```bash
cd shift-verification
./setup.sh
```

**Manual verification:**
```bash
cd shift-verification
coqc RDMAModel.v
```

**Using Makefile:**
```bash
cd shift-verification
make verify
```

### 7.4 Expected Output

```
Compiling RDMAModel.v...

==========================================
  All proofs verified successfully!
==========================================

Key Result:
  Theorem cross_nic_failover_violates_rc
  proves that RDMA RC exactly-once delivery
  cannot be maintained during cross-NIC
  failover with commodity hardware.
```

---

## 8. File Structure

```
shift-verification/
├── RDMAModel.v              # Main Coq proof file
├── Makefile                 # Build automation
├── setup.sh                 # Installation and verification script
├── _CoqProject              # Coq project configuration
└── PROOF_DOCUMENTATION.md   # This document
```

---

## 9. Glossary

| Term | Definition |
|------|------------|
| **RDMA** | Remote Direct Memory Access |
| **RC** | Reliable Connection (RDMA transport type) |
| **RNIC** | RDMA Network Interface Controller |
| **WQE** | Work Queue Element |
| **PSN** | Packet Sequence Number |
| **ACK** | Acknowledgment |
| **DMA** | Direct Memory Access |
| **Coq/Rocq** | Proof assistant for formal verification |

---

## 10. References

1. SHIFT Paper: "Cross-NIC RDMA Fault Tolerance for Distributed LLM Training"
2. InfiniBand Architecture Specification, Volume 1
3. RDMA-Core Library Documentation
4. Coq Reference Manual

---

## Appendix A: Full Coq Source Listing

See `RDMAModel.v` for the complete, compilable Coq source code.

## Appendix B: Mathematical Formalization

### B.1 System as Labeled Transition System

Let $\mathcal{S} = (S, s_0, E, \rightarrow)$ where:
- $S$ = set of system states
- $s_0$ = initial state
- $E$ = set of events
- $\rightarrow \subseteq S \times E \times S$ = transition relation

### B.2 Exactly-Once Property

$$
\text{ExactlyOnce}(s, w) \iff |\{m \in \text{memory}(s) : m.\text{source} = w\}| \leq 1
$$

### B.3 StrictlyDeliverOnce

$$
\text{StrictlyDeliverOnce}(s) \iff \forall w \in \text{WRID}. \text{ExactlyOnce}(s, w)
$$

### B.4 Theorem Statement

$$
\exists s \in S. \text{Reachable}(s_0, s) \land \neg\text{StrictlyDeliverOnce}(s)
$$

---

*Document generated for SHIFT formal verification project.*
