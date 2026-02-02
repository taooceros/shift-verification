# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This repository contains formal proofs of three impossibility theorems for transparent RDMA failover:

1. **Theorem 1**: Impossibility of safe retransmission for pure-write protocols (indistinguishability argument)
2. **Theorem 2**: Non-idempotency of FADD and CAS makes retry unsafe (linearizability violation)
3. **Theorem 3**: Herlihy's consensus hierarchy prevents transparent failover (CN=1 reads cannot solve 2-consensus)

## Development Environment

Uses [devenv](https://devenv.sh/) with Nix. Enter the shell before running commands:

```bash
devenv shell
```

## Build Commands

**Build Coq proofs:**
```bash
cd coq && make
```

**Rebuild from scratch (regenerate Makefile):**
```bash
cd coq && coq_makefile -f _CoqProject -o Makefile && make clean && make
```

**Build single Coq file:**
```bash
coqc -Q coq ShiftVerification coq/Path/To/File.v
```

**Compile Typst document:**
```bash
typst compile proof_specs.typ proof_specs.pdf
```

**Open CoqIDE:**
```bash
coqide
```

## Coq Project Architecture

All Coq files use the `ShiftVerification` namespace (defined in `coq/_CoqProject`).

### Core/ - Foundational definitions

- **Memory.v**: Memory model (`Addr`, `Val`, `Memory := Addr -> Val`, `mem_read`, `mem_write`)
- **Operations.v**: RDMA operations (`Op`, `OpResult`, `exec_op`, `exec_fadd`, `exec_cas`)
- **Traces.v**: Execution traces (`Event`, `Trace`, `SenderObs`, `sender_view`)
- **Properties.v**: Safety properties (`TransparentOverlay`, `execution_count`, `AtMostOnce`)

### Theorem1/ - Indistinguishability impossibility

- **Indistinguishability.v**: Constructs two traces (packet loss vs ACK loss) that are indistinguishable to sender
- **Impossibility.v**: Main theorem: `impossibility_safe_retransmission`

### Theorem2/ - Atomics non-idempotency

- **Atomics.v**: Idempotency definitions
- **FADD.v**: Proves FADD retry corrupts state (`fadd_not_idempotent`)
- **CAS.v**: Proves CAS retry with concurrency violates atomicity (`cas_double_success`)

### Theorem3/ - Consensus hierarchy barrier

- **ConsensusNumber.v**: Herlihy hierarchy formalization (`consensus_number`, `cn_lt`)
- **FailoverConsensus.v**: Models failover as 2-process consensus (`no_correct_future_decision`)
- **Hierarchy.v**: Main theorem: `transparent_cas_failover_impossible`

## Key Abstractions

**sender_view**: The projection function that extracts only sender-observable events from a trace. This is central to Theorem 1 - the sender cannot distinguish packet loss from ACK loss.

**TransparentOverlay**: A failover mechanism constrained to make decisions based solely on sender observations, without modifying application semantics.

**Consensus Number**: From Herlihy's hierarchy - reads have CN=1, CAS has CN=infinity. Failover requires 2-consensus, which CN=1 primitives cannot solve.

## Documentation

- `proof_specs.typ`: Detailed formal specifications with Coq code excerpts
- `coq_verification_plan.md`: Original development plan
- `proofs.typ`: Paper-style presentation of theorems (if exists)
