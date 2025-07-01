# core-env-uv.nix - Alternative with uv for ultra-fast package management
{ pkgs, antlr4_13_2 }:

{
  buildInputs = with pkgs; [
    python311
    # Use uv instead of pip for 10-100x faster package management
    uv
    python311Packages.hatchling  # Build backend for pyproject.toml
    jdk11
    gmp.dev
    cmake
    swig
    autoconf
    gperf
    glibc
    glibc.bin
    yices
    gcc
    zlib
    zlib.dev
  ];

  shellHook = ''
    export IN_NIX_FLAKE=1
    export CLASSPATH=".:${antlr4_13_2}/share/java/antlr-${antlr4_13_2.version}-complete.jar:$CLASSPATH"
    alias antlr4='java -jar ${antlr4_13_2}/share/java/antlr-${antlr4_13_2.version}-complete.jar'
    alias grun='java org.antlr.v4.gui.TestRig'

    # Create virtual environment with uv (much faster than venv)
    if [ ! -d ".venv" ]; then
      echo "Creating virtual environment with uv..."
      uv venv .venv
    fi

    # Activate the virtual environment
    source .venv/bin/activate
    export PATH="$PWD/.venv/bin:$PATH"
    
    echo "Using Python: $(which python)"
    echo "Python version: $(python --version)"

    echo "Installing InfOCF project dependencies with uv..."
    
    # Check if pyproject.toml exists and install accordingly
    if [ -f "pyproject.toml" ]; then
      echo "Found pyproject.toml - installing project with uv..."
      
      # Install the project in development mode with uv (extremely fast)
      uv pip install -e ".[dev,solvers,testing]"
      
      # Verify installation
      echo "Verifying installation..."
      python -c "import infocf; print(f'InfOCF version: {infocf.__version__}')"
      
    else
      echo "pyproject.toml not found - installing core dependencies with uv..."
      
      # Use uv to install dependencies (much faster than pip)
      uv pip install \
        "antlr4-python3-runtime==${antlr4_13_2.version}" \
        numpy \
        z3-solver \
        pandas \
        func-timeout \
        python-sat \
        pysmt \
        BitVector \
        frozenlist
      
      # Install from requirements.txt if it exists
      if [ -f "requirements.txt" ]; then
        uv pip install -r requirements.txt
      fi
    fi

    # Set up library paths for system solvers
    export LD_LIBRARY_PATH=${pkgs.stdenv.cc.cc.lib}/lib:$LD_LIBRARY_PATH
    export Z3_LIBRARY_PATH=$(python -c "import z3; print(z3.__file__)")/lib
    export LD_LIBRARY_PATH=${pkgs.yices}/lib:$LD_LIBRARY_PATH
    export LD_LIBRARY_PATH=${pkgs.zlib}/lib:$LD_LIBRARY_PATH

    # Install additional SAT/SMT solvers via pySMT
    echo "Installing additional SAT/SMT solvers..."
    
    # MathSAT
    if ! python -c "from pysmt.shortcuts import Solver; Solver('msat')" 2>/dev/null; then
      echo "Installing MathSAT..."
      pysmt-install --msat --confirm-agreement
    else
      echo "MathSAT already installed"
    fi
    
    # CVC5
    if ! python -c "from pysmt.shortcuts import Solver; Solver('cvc5')" 2>/dev/null; then
      echo "Installing CVC5..."
      pysmt-install --cvc5 --confirm-agreement  
    else
      echo "CVC5 already installed"
    fi
    
    # Yices (Python bindings) - use uv for speed
    if ! python -c "import yices" 2>/dev/null; then
      echo "Installing Yices Python bindings with uv..."
      uv pip install yices
    else
      echo "Yices Python bindings already installed"
    fi

    # PyBoolector - use uv for speed
    if ! python -c "import pyboolector" 2>/dev/null; then
      echo "Installing PyBoolector with uv..."
      uv pip install PyBoolector
    else
      echo "PyBoolector already installed"
    fi

    # Display environment information
    echo ""
    echo "=================================================="
    echo "InfOCF Development Environment Ready! (uv edition)"
    echo "=================================================="
    echo "Python version: $(python --version)"
    echo "Package manager: uv (ultra-fast!)"
    echo "ANTLR version: ${antlr4_13_2.version}"
    echo ""
    
    # Check if InfOCF is properly installed
    if python -c "import infocf" 2>/dev/null; then
      echo "InfOCF package: $(python -c 'import infocf; print(f"v{infocf.__version__}")')"
      echo "CLI available: $(which infocf || echo 'Not in PATH')"
      echo ""
      echo "Available inference operators:"
      python -c "import infocf; [print(f'  • {op}') for op in infocf.list_inference_operators()]"
      echo ""
    else
      echo "InfOCF package: Not properly installed"
      echo ""
    fi
    
    echo "Available solvers for pySMT:"
    python -c "
try:
    from pysmt.shortcuts import get_env
    solvers = get_env().factory.all_solvers()
    for solver in sorted(solvers):
        print(f'  • {solver}')
except Exception as e:
    print(f'  Error checking solvers: {e}')
"
    echo ""
    echo "To run system check: infocf --system-check"
    echo "To see all CLI options: infocf --help"
    echo "=================================================="
    echo "Note: This environment uses uv for 10-100x faster"
    echo "package management compared to pip!"
    echo "=================================================="
  '';
} 