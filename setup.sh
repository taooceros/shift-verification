#!/bin/bash
# ============================================================================ #
#                     SHIFT Formal Verification - Setup Script                  #
# ============================================================================ #
#
# This script installs the Coq proof assistant and verifies the RDMA
# impossibility proof.
#
# Supported platforms:
#   - macOS (via Homebrew)
#   - Ubuntu/Debian (via apt)
#   - Any platform with OPAM
#
# Usage:
#   ./setup.sh          # Install Coq and verify proof
#   ./setup.sh --verify # Only verify (assumes Coq installed)
#
# ============================================================================ #

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Print functions
info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

warn() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

error() {
    echo -e "${RED}[ERROR]${NC} $1"
    exit 1
}

# Header
echo ""
echo "=============================================="
echo "  SHIFT: Cross-NIC RDMA Fault Tolerance"
echo "  Formal Verification Setup"
echo "=============================================="
echo ""

# Check if only verification requested
if [[ "$1" == "--verify" ]]; then
    info "Skipping installation, running verification only..."
    VERIFY_ONLY=true
else
    VERIFY_ONLY=false
fi

# Function to check if Coq is installed
check_coq() {
    if command -v coqc &> /dev/null; then
        COQ_VERSION=$(coqc --version | head -n 1)
        success "Coq is installed: $COQ_VERSION"
        return 0
    else
        return 1
    fi
}

# Function to install Coq on macOS
install_coq_macos() {
    info "Detected macOS"

    if command -v brew &> /dev/null; then
        info "Installing Coq via Homebrew..."
        brew install coq
    else
        warn "Homebrew not found. Installing via OPAM..."
        install_coq_opam
    fi
}

# Function to install Coq on Linux
install_coq_linux() {
    info "Detected Linux"

    if command -v apt-get &> /dev/null; then
        info "Installing Coq via apt..."
        sudo apt-get update
        sudo apt-get install -y coq
    elif command -v dnf &> /dev/null; then
        info "Installing Coq via dnf..."
        sudo dnf install -y coq
    elif command -v pacman &> /dev/null; then
        info "Installing Coq via pacman..."
        sudo pacman -S --noconfirm coq
    else
        warn "No supported package manager found. Installing via OPAM..."
        install_coq_opam
    fi
}

# Function to install Coq via OPAM
install_coq_opam() {
    info "Installing Coq via OPAM (OCaml Package Manager)..."

    # Install OPAM if not present
    if ! command -v opam &> /dev/null; then
        info "Installing OPAM first..."

        if [[ "$OSTYPE" == "darwin"* ]]; then
            brew install opam
        elif command -v apt-get &> /dev/null; then
            sudo apt-get update
            sudo apt-get install -y opam
        else
            error "Cannot install OPAM automatically. Please install OPAM manually."
        fi
    fi

    # Initialize OPAM
    info "Initializing OPAM..."
    opam init -y --auto-setup
    eval $(opam env)

    # Install Coq
    info "Installing Coq (this may take several minutes)..."
    opam install coq -y
    eval $(opam env)
}

# Main installation logic
install_coq() {
    if check_coq; then
        info "Coq already installed, skipping installation."
        return 0
    fi

    info "Coq not found. Installing..."

    case "$OSTYPE" in
        darwin*)
            install_coq_macos
            ;;
        linux*)
            install_coq_linux
            ;;
        *)
            warn "Unknown OS. Attempting OPAM installation..."
            install_coq_opam
            ;;
    esac

    # Verify installation
    if check_coq; then
        success "Coq installation complete!"
    else
        error "Coq installation failed. Please install manually."
    fi
}

# Function to verify the proof
verify_proof() {
    echo ""
    echo "=============================================="
    echo "  Verifying RDMA Impossibility Proof"
    echo "=============================================="
    echo ""

    # Change to script directory
    SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
    cd "$SCRIPT_DIR"

    if [[ ! -f "RDMAModel.v" ]]; then
        error "RDMAModel.v not found in $SCRIPT_DIR"
    fi

    info "Compiling Coq proof..."
    echo ""

    # Compile the proof
    if coqc RDMAModel.v; then
        echo ""
        success "Proof compilation successful!"
        echo ""
        echo "=============================================="
        echo "  VERIFICATION COMPLETE"
        echo "=============================================="
        echo ""
        echo "The following theorems have been verified:"
        echo ""
        echo "  1. cross_nic_failover_violates_rc"
        echo "     Proves that RDMA RC exactly-once delivery"
        echo "     is violated during cross-NIC failover."
        echo ""
        echo "  2. impossibility_of_transparent_failover"
        echo "     Corollary establishing impossibility of"
        echo "     transparent failover with commodity hardware."
        echo ""
        echo "=============================================="
        echo ""
        echo "Key Insight for SHIFT paper:"
        echo ""
        echo "  With commodity RNICs, PSN state is local to"
        echo "  each NIC. When NIC_A fails after writing data"
        echo "  but before ACK, the sender must retransmit to"
        echo "  NIC_B, which cannot detect duplicates. This"
        echo "  fundamentally violates exactly-once delivery."
        echo ""
        echo "  This justifies SHIFT's focus on idempotent"
        echo "  workloads (e.g., NCCL Simple protocol) that"
        echo "  can tolerate duplicate deliveries."
        echo ""
    else
        error "Proof compilation failed!"
    fi
}

# Main execution
if [[ "$VERIFY_ONLY" == "false" ]]; then
    install_coq
fi

verify_proof

echo ""
success "Setup complete!"
echo ""
