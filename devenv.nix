{ pkgs, lib, config, inputs, ... }:

{
  name = "shift-verification";

  # Coq and proof assistant tools
  packages = with pkgs; [
    # Coq 8.18 and packages
    coqPackages_8_18.coq
    coqPackages_8_18.coqide
    coqPackages_8_18.stdpp

    # Build tools
    gnumake

    # Typst for document compilation
    typst
  ];

  # Environment variables
  env = {
    COQPATH = "${pkgs.coqPackages_8_18.stdpp}/lib/coq/8.18/user-contrib";
  };

  # Shell hook
  enterShell = ''
    echo "=========================================="
    echo "  RDMA Failover Impossibility Proofs"
    echo "  Coq Development Environment"
    echo "=========================================="
    echo ""
    echo "Coq version: $(coqc --version | head -1)"
    echo ""
    echo "Available commands:"
    echo "  cd coq && make   - Build Coq proofs"
    echo "  coqide           - Launch CoqIDE"
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
      coqc -Q coq ShiftVerification "$1"
    '';
  };
}
