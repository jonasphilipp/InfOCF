# InfOCF Migration Plan: Modern Python Packaging

## Overview

This plan transitions InfOCF from Nix + requirements.txt to modern Python packaging with uv and pyproject.toml, while maintaining backward compatibility and adding proper package distribution capabilities.

## Phase 1: Add pyproject.toml (Week 1) 🚀

**Goal**: Establish modern Python packaging standards while keeping existing workflow intact.

### Step 1.1: Create pyproject.toml

Create the main configuration file that replaces setup.py and provides modern dependency management:

```toml
[build-system]
requires = ["hatchling>=1.21.0"]
build-backend = "hatchling.build"

[project]
name = "infocf"
version = "0.1.0"
description = "Reasoning With Conditional Belief Bases - A library for non-monotonic inference operators"
readme = "README.md"
license = {text = "MIT"}
authors = [
    {name = "Your Name", email = "your.email@example.com"},
]
maintainers = [
    {name = "Your Name", email = "your.email@example.com"},
]
keywords = ["reasoning", "conditional-logic", "sat-solving", "belief-bases", "ai"]
classifiers = [
    "Development Status :: 4 - Beta",
    "Intended Audience :: Science/Research",
    "License :: OSI Approved :: MIT License",
    "Operating System :: OS Independent",
    "Programming Language :: Python :: 3",
    "Programming Language :: Python :: 3.11",
    "Programming Language :: Python :: 3.12",
    "Topic :: Scientific/Engineering :: Artificial Intelligence",
    "Topic :: Software Development :: Libraries :: Python Modules",
]
requires-python = ">=3.11"

dependencies = [
    "antlr4-python3-runtime>=4.13.2,<5.0.0",
    "z3-solver>=4.13.0.0",
    "pysmt>=0.9.6",
    "python-sat>=1.8.dev13",
    "numpy>=2.1.1",
    "pandas>=2.2.2",
    "func-timeout>=4.3.5",
    "PyBoolector>=3.2.4.20240823.1",
    "python-dateutil>=2.9.0.post0",
    "pytz>=2024.2",
    "six>=1.16.0",
    "tzdata>=2024.1",
    "bitvector>=3.0.0",
]

[project.optional-dependencies]
dev = [
    "pytest>=7.0.0",
    "pytest-cov>=4.0.0",
    "black>=23.0.0",
    "isort>=5.12.0",
    "mypy>=1.0.0",
    "flake8>=6.0.0",
    "sphinx>=6.0.0",
    "sphinx-rtd-theme>=1.2.0",
]
solvers = [
    "cvc5>=1.1.2",
]
testing = [
    "pytest>=7.0.0",
    "pytest-cov>=4.0.0",
    "pytest-benchmark>=4.0.0",
]

[project.scripts]
infocf = "infocf.cli:main"

[project.urls]
Homepage = "https://github.com/yourusername/InfOCF"
Documentation = "https://infocf.readthedocs.io"
Repository = "https://github.com/yourusername/InfOCF"
"Bug Tracker" = "https://github.com/yourusername/InfOCF/issues"

[tool.hatch.build.targets.wheel]
packages = ["infocf", "inference", "parser"]

[tool.hatch.build.targets.sdist]
include = [
    "/infocf",
    "/inference",
    "/parser",
    "/docs",
    "/examples",
    "/unittests",
    "README.md",
    "LICENSE",
    "requirements.txt",
]
exclude = [
    "/.git",
    "/output",
    "/local",
    "*.nix",
    "flake.*",
]

# Tool configurations
[tool.black]
line-length = 88
target-version = ['py311']
include = '\.pyi?$'
extend-exclude = '''
/(
  parser/CKB.*\.py
)/
'''

[tool.isort]
profile = "black"
multi_line_output = 3
line_length = 88
skip = ["parser/CKB*.py"]

[tool.mypy]
python_version = "3.11"
warn_return_any = true
warn_unused_configs = true
disallow_untyped_defs = true
exclude = [
    "parser/CKB.*\\.py$",
]

[tool.pytest.ini_options]
testpaths = ["unittests"]
python_files = ["test_*.py"]
python_classes = ["Test*"]
python_functions = ["test_*"]
addopts = [
    "--strict-markers",
    "--strict-config",
    "--verbose",
]
markers = [
    "slow: marks tests as slow",
    "integration: marks tests as integration tests",
]
```

### Step 1.2: Update infocf/__init__.py

```python
"""
InfOCF - Reasoning With Conditional Belief Bases

A library providing implementations for non-monotonic inference operators
including p-entailment, system Z, c-inference, and system W.
"""

from .log_setup import get_logger, setup_logging

__version__ = "0.1.0"
__author__ = "Your Name"
__email__ = "your.email@example.com"

__all__ = [
    "get_logger",
    "setup_logging",
]
```

### Step 1.3: Update core-env.nix for pyproject.toml compatibility

```nix
# core-env.nix (updated)
{ pkgs, antlr4_13_2 }:

{
  buildInputs = with pkgs; [
    python311
    python311Packages.pip
    python311Packages.build
    uv
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

    unset PYTHONPATH
    export PATH="$PWD/venv/bin:$PATH"
    source venv/bin/activate

    # Use uv for faster package installation
    pip install --upgrade pip uv

    # Install packages from pyproject.toml
    echo "Installing InfOCF in development mode..."
    uv pip install -e ".[dev,solvers,testing]"

    # Set up library paths
    export LD_LIBRARY_PATH=${pkgs.stdenv.cc.cc.lib}/lib:$LD_LIBRARY_PATH
    export Z3_LIBRARY_PATH=$(python -c "import z3; print(z3.__file__)")/lib
    export LD_LIBRARY_PATH=${pkgs.yices}/lib:$LD_LIBRARY_PATH
    export LD_LIBRARY_PATH=${pkgs.zlib}/lib:$LD_LIBRARY_PATH

    # Install additional solvers
    echo "Installing SMT solvers..."
    pysmt-install --msat --confirm-agreement || echo "MathSAT installation failed (optional)"
    pysmt-install --cvc5 --confirm-agreement || echo "CVC5 installation failed (optional)"

    echo "✅ InfOCF development environment ready!"
    echo "Python version: $(python --version)"
    echo "ANTLR version: ${antlr4_13_2.version}"
  '';
}
```

## Phase 2: Introduce uv (Week 2) ⚡

### Step 2.1: Create cross-platform setup script

```bash
#!/bin/bash
# setup-uv.sh - Pure uv setup (no Nix)

set -e
echo "🚀 Setting up InfOCF with uv..."

# Install uv if not present
if ! command -v uv &> /dev/null; then
    echo "Installing uv..."
    curl -LsSf https://astral.sh/uv/install.sh | sh
    source $HOME/.cargo/env
fi

# Create virtual environment
echo "Creating virtual environment..."
uv venv venv --python 3.11
source venv/bin/activate

# Install dependencies
echo "Installing dependencies..."
uv pip install -e ".[dev,testing]"

# System-specific solver setup
if [[ "$OSTYPE" == "linux-gnu"* ]]; then
    echo "Setting up Linux-specific solvers..."
    if command -v apt-get &> /dev/null; then
        sudo apt-get update
        sudo apt-get install -y yices2 || echo "Yices not available via apt"
    fi
elif [[ "$OSTYPE" == "darwin"* ]]; then
    echo "Setting up macOS-specific solvers..."
    if command -v brew &> /dev/null; then
        brew install yices2 || echo "Yices not available via brew"
    fi
fi

# Install additional solvers via pysmt
echo "Installing SMT solvers via pysmt..."
pysmt-install --msat --confirm-agreement || echo "MathSAT installation failed (optional)"
pysmt-install --cvc5 --confirm-agreement || echo "CVC5 installation failed (optional)"

echo "✅ InfOCF setup complete!"
echo "Test with: python -c 'import infocf; print(\"InfOCF imported successfully!\")'"
```

### Step 2.2: Create GitHub Actions workflow

```yaml
# .github/workflows/test.yml
name: Test InfOCF

on:
  push:
    branches: [ main, develop, feature/* ]
  pull_request:
    branches: [ main, develop ]

jobs:
  test:
    runs-on: ${{ matrix.os }}
    strategy:
      matrix:
        os: [ubuntu-latest, macos-latest, windows-latest]
        python-version: ['3.11', '3.12']

    steps:
    - uses: actions/checkout@v4

    - name: Install uv
      uses: astral-sh/setup-uv@v2
      with:
        version: "latest"

    - name: Set up Python
      run: uv python install ${{ matrix.python-version }}

    - name: Install dependencies
      run: uv sync --extra testing --extra dev

    - name: Install system dependencies (Linux)
      if: matrix.os == 'ubuntu-latest'
      run: |
        sudo apt-get update
        sudo apt-get install -y yices2 || true

    - name: Install system dependencies (macOS)
      if: matrix.os == 'macos-latest'
      run: brew install yices2 || true

    - name: Install SMT solvers
      run: |
        uv run pysmt-install --msat --confirm-agreement || true
        uv run pysmt-install --cvc5 --confirm-agreement || true

    - name: Run tests
      run: uv run pytest unittests/ -v --cov=infocf --cov-report=xml

    - name: Upload coverage
      uses: codecov/codecov-action@v3
      with:
        file: ./coverage.xml
```

## Phase 3: Hybrid Approach (Week 3-4) 🔄

### Step 3.1: Create justfile for task automation

```justfile
# justfile - Cross-platform task runner

# Set up development environment with uv
setup:
    uv venv venv --python 3.11
    uv pip install -e ".[dev,testing,solvers]"
    @echo "✅ Development environment ready!"

# Run tests
test:
    uv run pytest unittests/ -v

# Run tests with coverage
test-cov:
    uv run pytest unittests/ -v --cov=infocf --cov-report=html --cov-report=term

# Format code
format:
    uv run black infocf/ inference/ parser/ unittests/
    uv run isort infocf/ inference/ parser/ unittests/

# Lint code
lint:
    uv run flake8 infocf/ inference/ parser/ unittests/
    uv run mypy infocf/ inference/ parser/

# Build package
build:
    uv build

# Clean build artifacts
clean:
    rm -rf dist/ build/ *.egg-info/ .coverage htmlcov/ .pytest_cache/ .mypy_cache/

# Generate requirements files for compatibility
freeze:
    uv pip compile pyproject.toml -o requirements.txt
    uv pip compile pyproject.toml --extra dev -o requirements-dev.txt

# Run example scripts
example script="show.py":
    uv run python {{script}}

# Update dependencies
update:
    uv pip compile --upgrade pyproject.toml -o requirements.txt
```

### Step 3.2: Update INSTALL.md with multiple methods

```markdown
# Installation Guide

InfOCF supports multiple installation methods to accommodate different environments.

## Method 1: uv (Recommended - Cross-platform)

```bash
curl -LsSf https://astral.sh/uv/install.sh | sh
git clone https://github.com/yourusername/InfOCF.git
cd InfOCF
chmod +x setup-uv.sh
./setup-uv.sh
```

## Method 2: pip + Virtual Environment

```bash
git clone https://github.com/yourusername/InfOCF.git
cd InfOCF
python -m venv venv
source venv/bin/activate
pip install -e ".[dev,testing]"
```

## Method 3: Nix Flakes (Linux/macOS)

```bash
git clone https://github.com/yourusername/InfOCF.git
cd InfOCF
nix develop
```

## Verifying Installation

```python
import infocf
print(f"InfOCF version: {infocf.__version__}")
```
```

## Phase 4: Proper Python Package (Week 5-6) 📦

### Step 4.1: Create CLI entry point

```python
# infocf/cli.py
"""Command-line interface for InfOCF."""

import argparse
import sys
from pathlib import Path

from infocf import __version__
from infocf.log_setup import setup_logging


def main() -> int:
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        description="InfOCF - Reasoning With Conditional Belief Bases",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  infocf --version
  infocf parse examples/birds.cl
  infocf infer --method system-z examples/birds.cl "bird(tweety) -> flies(tweety)"
        """
    )

    parser.add_argument("--version", action="version", version=f"InfOCF {__version__}")
    parser.add_argument("--verbose", "-v", action="store_true", help="Enable verbose logging")

    subparsers = parser.add_subparsers(dest="command", help="Available commands")

    # Parse command
    parse_parser = subparsers.add_parser("parse", help="Parse a .cl file")
    parse_parser.add_argument("file", type=Path, help="Path to .cl file")

    # Infer command
    infer_parser = subparsers.add_parser("infer", help="Perform inference")
    infer_parser.add_argument("file", type=Path, help="Path to .cl file")
    infer_parser.add_argument("query", help="Query to evaluate")
    infer_parser.add_argument(
        "--method",
        choices=["system-z", "system-w", "c-inference", "p-entailment"],
        default="system-z",
        help="Inference method to use"
    )

    args = parser.parse_args()

    if args.verbose:
        setup_logging(level="DEBUG")
    else:
        setup_logging(level="INFO")

    if args.command == "parse":
        return cmd_parse(args.file)
    elif args.command == "infer":
        return cmd_infer(args.file, args.query, args.method)
    else:
        parser.print_help()
        return 1


def cmd_parse(file_path: Path) -> int:
    """Parse a .cl file and display the knowledge base."""
    try:
        from parser.myVisitor import parse_knowledge_base

        print(f"Parsing {file_path}...")
        kb = parse_knowledge_base(str(file_path))
        print(f"Successfully parsed {len(kb)} conditionals")
        for i, conditional in enumerate(kb, 1):
            print(f"  {i}. {conditional}")
        return 0
    except Exception as e:
        print(f"Error parsing file: {e}", file=sys.stderr)
        return 1


def cmd_infer(file_path: Path, query: str, method: str) -> int:
    """Perform inference on a knowledge base."""
    try:
        from parser.myVisitor import parse_knowledge_base

        print(f"Loading knowledge base from {file_path}...")
        kb = parse_knowledge_base(str(file_path))

        print(f"Performing {method} inference...")
        print(f"Query: {query}")
        print(f"Method {method} not yet fully implemented in CLI")
        return 0
    except Exception as e:
        print(f"Error during inference: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
```

### Step 4.2: Create core API module

```python
# infocf/core.py
"""Core InfOCF classes for easy importing."""

from typing import List, Optional, Any
from pathlib import Path


class KnowledgeBase:
    """Wrapper for knowledge base operations."""

    def __init__(self, conditionals: Optional[List] = None):
        self.conditionals = conditionals or []

    @classmethod
    def from_file(cls, file_path: Path) -> "KnowledgeBase":
        """Load knowledge base from .cl file."""
        from parser.myVisitor import parse_knowledge_base
        conditionals = parse_knowledge_base(str(file_path))
        return cls(conditionals)

    def __len__(self) -> int:
        return len(self.conditionals)

    def __repr__(self) -> str:
        return f"KnowledgeBase({len(self.conditionals)} conditionals)"


class InferenceEngine:
    """Main inference engine with multiple methods."""

    def __init__(self, method: str = "system-z"):
        self.method = method
        self._engine = self._create_engine(method)

    def _create_engine(self, method: str):
        """Create the appropriate inference engine."""
        if method == "system-z":
            from inference.system_z import SystemZ
            return SystemZ()
        # Add other methods as they become available
        else:
            raise ValueError(f"Unknown inference method: {method}")

    def query(self, kb: KnowledgeBase, query: str) -> Any:
        """Perform inference query."""
        return self._engine.query(kb.conditionals, query)
```

## Phase 5: Distribution Ready (Week 7-8) 🚀

### Step 5.1: Release preparation script

```python
# scripts/prepare_release.py
"""Release preparation script."""

import subprocess
import sys


def run_command(cmd: str) -> None:
    """Run a shell command."""
    print(f"Running: {cmd}")
    result = subprocess.run(cmd, shell=True)
    if result.returncode != 0:
        sys.exit(1)


def main():
    """Prepare release."""
    print("🚀 Preparing InfOCF release...")

    # Run tests
    print("\n1. Running tests...")
    run_command("uv run pytest unittests/ -v")

    # Run linting
    print("\n2. Running linting...")
    run_command("uv run black --check infocf/ inference/ parser/")
    run_command("uv run isort --check infocf/ inference/ parser/")
    run_command("uv run flake8 infocf/ inference/ parser/")

    # Build package
    print("\n3. Building package...")
    run_command("uv build")

    print("\n✅ Release preparation complete!")
    print("Next steps:")
    print("  1. Update version in pyproject.toml")
    print("  2. Create git tag: git tag v0.1.0")
    print("  3. Upload to PyPI: uv publish")


if __name__ == "__main__":
    main()
```

## Implementation Timeline

| Phase | Duration | Key Deliverables | Benefits |
|-------|----------|------------------|----------|
| **Phase 1** | Week 1 | pyproject.toml, updated Nix | Modern packaging standards |
| **Phase 2** | Week 2 | uv integration, CI/CD | Fast installs, cross-platform |
| **Phase 3** | Week 3-4 | Multiple install methods | User choice, compatibility |
| **Phase 4** | Week 5-6 | Proper package, CLI | Professional tooling |
| **Phase 5** | Week 7-8 | PyPI ready, docs | Wide distribution |

## Benefits Summary

### Immediate
- ✅ Modern Python packaging standards
- ✅ Cross-platform compatibility
- ✅ Faster dependency resolution
- ✅ Better development workflow

### Long-term
- ✅ Easy PyPI distribution
- ✅ Professional CLI tools
- ✅ Broader research community adoption
- ✅ Simplified contribution process

## Risk Mitigation

1. **Backward Compatibility**: Nix setup continues working
2. **Gradual Migration**: Each phase builds incrementally
3. **Multiple Options**: Support legacy and modern workflows
4. **Comprehensive Testing**: CI/CD across all platforms
5. **Clear Documentation**: Installation guides for all methods

This migration plan provides a clear path to modernize your Python packaging while maintaining compatibility and adding professional distribution capabilities. Would you like me to start implementing any specific phase?
