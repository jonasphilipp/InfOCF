# Installation

InfOCF uses modern Python package management with `pyproject.toml` and supports multiple installation methods.

## Prerequisites

- **Python 3.11 or higher** is required
- We recommend using **[uv](https://docs.astral.sh/uv/)** for the fastest and most reliable package management

## Method 1: Using uv (Recommended)

[uv](https://docs.astral.sh/uv/) is a fast Python package and project manager that provides the best experience for InfOCF development.

### Install uv

If you don't have uv installed:

```bash
# On macOS and Linux
curl -LsSf https://astral.sh/uv/install.sh | sh

# On Windows
powershell -c "irm https://astral.sh/uv/install.ps1 | iex"

# Alternative: Install via pip
pip install uv
```

### Clone and Set Up the Project

```bash
# Clone the repository
git clone https://github.com/InfOCF-Team/InfOCF.git
cd InfOCF

# Create virtual environment and install dependencies
uv sync

# Activate the environment (optional, uv run handles this automatically)
source .venv/bin/activate  # On Linux/macOS
# or
.venv\Scripts\activate     # On Windows
```

### Install Additional Dependencies (Optional)

InfOCF offers several optional dependency groups:

```bash
# Install development tools (linting, formatting, testing)
uv sync --extra dev

# Install additional SAT/SMT solvers
uv sync --extra solvers

# Install documentation tools
uv sync --extra docs

# Install testing utilities
uv sync --extra testing

# Install everything
uv sync --all-extras
```

### Running InfOCF

```bash
# Run with uv (recommended - handles environment automatically)
uv run infocf --system-check

# Or activate environment first, then run directly
source .venv/bin/activate
infocf --system-check
```

## Method 2: Using pip and venv

If you prefer the traditional pip approach:

### Set Up Virtual Environment

```bash
# Clone the repository
git clone https://github.com/InfOCF-Team/InfOCF.git
cd InfOCF

# Create virtual environment
python -m venv venv

# Activate virtual environment
source venv/bin/activate  # On Linux/macOS
# or
venv\Scripts\activate     # On Windows
```

### Install the Package

```bash
# Install in development mode with core dependencies
pip install -e .

# Install with optional dependencies
pip install -e ".[dev,solvers,testing,docs]"
```

## Method 3: Using nix

For reproducible environments using the nix package manager:

```bash
# Clone the repository
git clone https://github.com/InfOCF-Team/InfOCF.git
cd InfOCF

# Enter development environment
nix develop
```

## Verifying Installation

After installation, verify that everything works correctly:

```bash
# Check system status
uv run infocf --system-check

# View available inference operators
uv run infocf --operators

# Check solver availability
uv run infocf --check-solvers
```

## Development Setup

For development work, install the development dependencies:

```bash
# Using uv (recommended)
uv sync --extra dev

# Using pip
pip install -e ".[dev]"
```

This includes tools for:
- Code formatting (black, isort)
- Linting (ruff, flake8, mypy)
- Testing (pytest)
- Pre-commit hooks

## Troubleshooting

### Missing SAT/SMT Solvers

If you encounter solver-related issues, install additional solvers:

```bash
uv sync --extra solvers
```

### Python Version Issues

Ensure you're using Python 3.11 or higher:

```bash
python --version
uv run python --version
```

### Import Errors

If you encounter import errors, ensure the package is installed in development mode:

```bash
uv sync  # This installs in development mode by default
```

## Resources

- [uv documentation](https://docs.astral.sh/uv/)
- [pip documentation](https://pypi.org/project/pip/)
- [venv documentation](https://docs.python.org/3/library/venv.html)
- [nix documentation](https://nixos.org/learn.html)
