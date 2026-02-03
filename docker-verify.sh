#!/bin/bash
# ============================================================================ #
#            SHIFT Formal Verification - Docker Verification Script            #
# ============================================================================ #
#
# This script verifies the Coq proof using Docker, ensuring reproducibility
# across different environments without requiring local Coq installation.
#
# Usage:
#   ./docker-verify.sh
#
# Requirements:
#   - Docker installed and running
#
# ============================================================================ #

set -e

# Colors
GREEN='\033[0;32m'
BLUE='\033[0;34m'
RED='\033[0;31m'
NC='\033[0m'

info() { echo -e "${BLUE}[INFO]${NC} $1"; }
success() { echo -e "${GREEN}[SUCCESS]${NC} $1"; }
error() { echo -e "${RED}[ERROR]${NC} $1"; exit 1; }

echo ""
echo "=============================================="
echo "  SHIFT Formal Verification (Docker)"
echo "=============================================="
echo ""

# Check Docker
if ! command -v docker &> /dev/null; then
    error "Docker is not installed. Please install Docker first."
fi

info "Using Docker to verify Coq proof..."

# Get script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Run Coq in Docker
docker run --rm \
    -v "$SCRIPT_DIR:/workspace" \
    -w /workspace \
    coqorg/coq:8.18 \
    coqc RDMAModel.v

if [[ $? -eq 0 ]]; then
    echo ""
    success "Proof verified successfully!"
    echo ""
    echo "=============================================="
    echo "  VERIFICATION COMPLETE"
    echo "=============================================="
    echo ""
    echo "Theorems verified:"
    echo "  - cross_nic_failover_violates_rc"
    echo "  - impossibility_of_transparent_failover"
    echo ""
else
    error "Proof verification failed!"
fi
