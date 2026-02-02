{ pkgs, lib, config, inputs, ... }:

{
  name = "shift-verification";

  # Rocq and proof assistant tools
  packages = with pkgs; [
    # Rocq 9.0 (the renamed Coq)
    rocqPackages.rocq-core
    rocqPackages.stdlib
    coqPackages.coq-lsp  # Modern LSP-based IDE support

    # Build tools
    gnumake

    # Typst for document compilation
    typst
  ];

  # Environment variables
  env = {
    ROCQPATH = "${pkgs.rocqPackages.stdlib}/lib/rocq/9.0/user-contrib";
  };

  # Shell hook
  enterShell = ''
    echo "=========================================="
    echo "  RDMA Failover Impossibility Proofs"
    echo "  Rocq Development Environment"
    echo "=========================================="
    echo ""
    echo "Rocq version: $(rocq --version | head -1)"
    echo ""
    echo "Available commands:"
    echo "  cd coq && make   - Build Rocq proofs"
    echo "  rocq-lsp         - Language server for IDE integration"
    echo "  typst compile proofs.typ - Compile Typst document"
    echo ""
  '';

  # Scripts
  scripts = {
    build-proofs.exec = ''
      cd coq && make
    '';

    clean-proofs.exec = ''
      cd coq && make clean
    '';

    build-doc.exec = ''
      typst compile proofs.typ proofs.pdf
    '';

    check-proof.exec = ''
      rocq compile -Q coq ShiftVerification "$1"
    '';
  };
}
