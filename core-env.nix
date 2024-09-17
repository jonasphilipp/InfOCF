
# core-env.nix
{ pkgs, antlr4_13_2 }:

{
  buildInputs = with pkgs; [
    python311
    python311Packages.pip
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


    # Create and activate venv
    if [ ! -d "venv" ]; then
      python -m venv venv
    fi

		
    # Ensure pip and python use the venv
    unset PYTHONPATH
    export PATH="$PWD/venv/bin:$PATH"
    
		which python
		source venv/bin/activate
		which python

    # Install antlr4-python3-runtime in venv
    pip install --upgrade pip
    pip install antlr4-python3-runtime==${antlr4_13_2.version}
		pip install numpy
		pip install z3-solver
		pip install pandas
		pip install func-timeout
		pip install python-sat
		pip install pysmt

		export LD_LIBRARY_PATH=${pkgs.stdenv.cc.cc.lib}/lib:$LD_LIBRARY_PATH
		export Z3_LIBRARY_PATH=$(python -c "import z3; print(z3.__file__)")/lib
		# Library Path for Yices
    export LD_LIBRARY_PATH=${pkgs.yices}/lib:$LD_LIBRARY_PATH
		export LD_LIBRARY_PATH=${pkgs.zlib}/lib:$LD_LIBRARY_PATH

		# msat
		pysmt-install --msat --confirm-agreement
		
		# cvc5
		pysmt-install --cvc5 --confirm-agreement
		
		# yices
		pip install yices

		# btor
		pip install PyBoolector

  
		echo "Welcome to your work environment!"
    echo "Python version: $(python --version)"
    echo "ANTLR version: ${antlr4_13_2.version}"
    echo "Available solvers for pySMT:"
    python -c "from pysmt.shortcuts import get_env; print('\n'.join(get_env().factory.all_solvers()))"
  '';
}
