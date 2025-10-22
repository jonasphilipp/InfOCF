{
  description = "InfOCF: Modern Python environment with system SAT/SMT solvers";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfree = true;
        };

        # ANTLR version for parser generation
        antlr4_13_2 = pkgs.antlr4.overrideAttrs (oldAttrs: rec {
          version = "4.13.2";
          src = pkgs.fetchurl {
            url = "https://www.antlr.org/download/antlr-${version}-complete.jar";
            sha256 = "sha256-6uLfoRmmQydERnKv9j6ew1ogGA3FuAkLemq4USXfTXY=";
          };
        });

      in {
        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            # Python and modern package management
            python311
            uv                    # Fast Python package manager

            # System build tools and libraries
            jdk11                 # Java for ANTLR
            gcc                   # C compiler for extensions
            cmake swig autoconf gperf  # Build tools
            gmp.dev zlib.dev      # Development libraries

            # SAT/SMT Solvers (system level) - Rich ecosystem for research
            yices                 # Yices SMT solver
            z3                    # Z3 SMT solver (also via Python)

            # Modern SMT Solvers
            cvc5                  # High-performance SMT solver
            boolector             # Bit-vector & array SMT solver
            opensmt               # General purpose SMT solver

            # SAT Solvers - Various algorithms and optimizations
            glucose               # Modern parallel SAT solver
            lingeling             # Fast SAT solver
            minisat               # Classic compact SAT solver
            cadical               # Simplified satisfiability solver

            # Specialized Solvers
            open-wbo              # MaxSAT and Pseudo-Boolean solver
          ];

          shellHook = ''
            # ANTLR setup
            export CLASSPATH=".:${antlr4_13_2}/share/java/antlr-${antlr4_13_2.version}-complete.jar:$CLASSPATH"
            alias antlr4='java -jar ${antlr4_13_2}/share/java/antlr-${antlr4_13_2.version}-complete.jar'
            alias grun='java org.antlr.v4.gui.TestRig'

            # Library paths for comprehensive solver ecosystem
            export LD_LIBRARY_PATH="${pkgs.stdenv.cc.cc.lib}/lib:${pkgs.yices}/lib:${pkgs.zlib}/lib:${pkgs.boolector}/lib:$LD_LIBRARY_PATH"

            # Python environment with uv (fast and modern)
            echo "🚀 Setting up InfOCF environment with uv..."

            # Create venv if it doesn't exist
            if [ ! -d ".venv" ]; then
              echo "Creating Python virtual environment..."
              uv venv .venv
            fi

            # Activate environment
            source .venv/bin/activate

            # Install project in development mode with all extras
            echo "Installing InfOCF with dependencies..."
            uv pip install -e ".[dev,solvers,testing]"

            # Install Python bindings for system solvers (Nix-only enhancement)
            echo "🧮 Installing working solver Python bindings..."
            uv pip install yices==1.1.5        # Yices SMT solver bindings
            # Note: pyboolector needs system Boolector headers (complex build)
            # Note: PicoSAT/CUDD Python bindings not available on PyPI
            # Note: MathSAT (msat) requires license agreement and manual install

            # Verify installation
            echo ""
            echo "✅ InfOCF Environment Ready!"
            echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
            echo "Python: $(python --version)"
            echo "ANTLR: ${antlr4_13_2.version}"

            if python -c "import infocf" 2>/dev/null; then
              echo "InfOCF: $(python -c 'import infocf; print(f"v{infocf.__version__}")')"
              echo ""
              echo "🧮 Comprehensive Solver Ecosystem:"
              if python -c "import pysmt" 2>/dev/null; then
                echo "  • PySMT Integration: $(python -c 'from pysmt.shortcuts import get_env; solvers = get_env().factory.all_solvers(); print(", ".join(sorted(solvers)) + f" ({len(solvers)} solvers)")')"
              else
                echo "  • PySMT Integration: Not available"
              fi
              echo "  • System Binaries: $(which boolector opensmt glucose lingeling minisat cadical open-wbo 2>/dev/null | wc -l) solvers available"
              echo "  • Direct Use: All system solvers available via command line"
              echo ""
              echo "🔧 Available CLI commands:"
              echo "  infocf --version        # Show version"
              echo "  infocf --system-check   # Verify all solvers"
              echo "  infocf --help          # Show all options"
            else
              echo "⚠️  InfOCF: Installation issue detected"
            fi
            echo ""
          '';
        };
      }
    );
}
