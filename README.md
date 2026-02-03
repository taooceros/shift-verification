# SHIFT: Formal Verification of RDMA RC Impossibility

This directory contains a formal Coq proof demonstrating that **strict RDMA Reliable Connection (RC) semantics cannot be maintained during cross-NIC failover** using commodity hardware.

## Quick Start

### Option 1: Using Docker (Recommended)
```bash
./docker-verify.sh
```

### Option 2: Local Installation
```bash
./setup.sh
```

### Option 3: Manual
```bash
# Install Coq (macOS)
brew install coq

# Or Ubuntu
sudo apt-get install coq

# Verify proof
coqc RDMAModel.v
```

## Key Result

```coq
Theorem cross_nic_failover_violates_rc :
  ~ StrictlyDeliverOnce state_3_violation.
```

This proves there exists an execution trace where a Work Queue Element writes to memory **twice** during cross-NIC failover, violating the exactly-once delivery guarantee of RDMA RC.

## Files

| File | Description |
|------|-------------|
| `RDMAModel.v` | Main Coq proof (~400 lines, heavily commented) |
| `PROOF_DOCUMENTATION.md` | Comprehensive technical documentation |
| `setup.sh` | Installation and verification script |
| `docker-verify.sh` | Docker-based verification |
| `Makefile` | Build automation |

## Why This Matters for SHIFT

The proof justifies SHIFT's design decision to:
1. Not attempt transparent failover for all RDMA workloads
2. Focus on **idempotent** communication patterns (e.g., NCCL Simple)
3. Use WR-level retransmission instead of packet-level

See `PROOF_DOCUMENTATION.md` for full technical details.
