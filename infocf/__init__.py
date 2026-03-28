"""
InfOCF - Reasoning With Conditional Belief Bases

A library for non-monotonic inference operators including p-entailment,
system Z, c-inference, and system W. The implementations use current SAT
and MaxSAT solvers such as Z3 via established interfaces like PySMT.

Key Features:
- Multiple inference operators: System Z, System W, c-inference, p-entailment, lexicographic inference
- SAT/SMT solver integration via PySMT (Z3, CVC5, etc.)
- Conditional logic parsing for .cl format files
- Performance measurement and logging infrastructure
- Support for belief base consistency checking
"""

import sys
from importlib import import_module
from importlib.metadata import PackageNotFoundError, version

# Version management - sync with pyproject.toml
try:
    __version__ = version("infocf")
except PackageNotFoundError:
    # Fallback for development installations
    __version__ = "0.1.0-dev"

# Minimum Python version check
if sys.version_info < (3, 11):
    raise RuntimeError("InfOCF requires Python 3.11 or higher")

# Core logging functionality (always available)
from .log_setup import get_logger, setup_logging

_LAZY_IMPORTS = {
    "BeliefBase": ("inference.belief_base", "BeliefBase"),
    "CInference": ("inference.c_inference", "CInference"),
    "Conditional": ("inference.conditional", "Conditional"),
    "consistency": ("inference.consistency_sat", "consistency"),
    "Inference": ("inference.inference", "Inference"),
    "InferenceManager": ("inference.inference_manager", "InferenceManager"),
    "LexInf": ("inference.lex_inf", "LexInf"),
    "LexInfZ3": ("inference.lex_inf_z3", "LexInfZ3"),
    "PEntailment": ("inference.p_entailment", "PEntailment"),
    "PreOCF": ("inference.preocf", "PreOCF"),
    "SystemZPreOCF": ("inference.preocf", "SystemZPreOCF"),
    "RandomMinCRepPreOCF": ("inference.preocf", "RandomMinCRepPreOCF"),
    "CustomPreOCF": ("inference.preocf", "CustomPreOCF"),
    "Queries": ("inference.queries", "Queries"),
    "SystemW": ("inference.system_w", "SystemW"),
    "SystemWZ3": ("inference.system_w_z3", "SystemWZ3"),
    "SystemZ": ("inference.system_z", "SystemZ"),
    "parse_belief_base": ("parser.Wrappers", "parse_belief_base"),
    "parse_belief_base_from_str": ("parser.Wrappers", "parse_belief_base_from_str"),
    "parse_formula": ("parser.Wrappers", "parse_formula"),
    "parse_queries": ("parser.Wrappers", "parse_queries"),
    "parse_queries_from_str": ("parser.Wrappers", "parse_queries_from_str"),
    "parseCKB": ("parser.Wrappers", "parseCKB"),
    "parseQuery": ("parser.Wrappers", "parseQuery"),
}

_INFERENCE_AVAILABLE = True

# Package metadata
__author__ = "Christoph Beierle, Jonas Haldimann, Arthur Sanin, Aron Spang, Leon Schwarzer, Lars-Phillip Spiegel, Martin von Berg"
__email__ = "christoph.beierle@fernuni-hagen.de"
__license__ = "MIT"
__description__ = "InfOCF - Reasoning With Conditional Belief Bases: A library for non-monotonic inference operators"
__url__ = "https://github.com/InfOCF-Team/InfOCF"

# Public API definition
__all__ = [
    # Version and metadata
    "__version__",
    "__author__",
    "__email__",
    "__license__",
    "__description__",
    "__url__",
    # Core logging (always available)
    "get_logger",
    "setup_logging",
]

# Add inference components to __all__ if available
if _INFERENCE_AVAILABLE:
    __all__.extend(
        [
            # Core framework
            "Inference",
            "InferenceManager",
            # Main inference operators
            "SystemZ",
            "SystemW",
            "CInference",
            "PEntailment",
            "LexInf",
            # Z3-optimized variants
            "SystemWZ3",
            "LexInfZ3",
            # Core data structures
            "Conditional",
            "BeliefBase",
            "Queries",
            # PreOCF functionality
            "PreOCF",
            "SystemZPreOCF",
            "RandomMinCRepPreOCF",
            "CustomPreOCF",
            # Utility functions
            "consistency",
            # Parser functionality
            "parse_belief_base",
            "parse_queries",
            "parse_queries_from_str",
            "parse_belief_base_from_str",
            "parse_formula",
            "parseCKB",
            "parseQuery",
        ]
    )


def __getattr__(name):
    """Lazily import heavy inference modules to avoid package init cycles."""
    if name not in _LAZY_IMPORTS:
        raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
    module_name, attr_name = _LAZY_IMPORTS[name]
    module = import_module(module_name)
    value = getattr(module, attr_name)
    globals()[name] = value
    return value


def get_package_info():
    """Return package information dictionary."""
    return {
        "name": "infocf",
        "version": __version__,
        "author": __author__,
        "license": __license__,
        "description": __description__,
        "url": __url__,
        "python_requires": ">=3.11",
        "inference_available": _INFERENCE_AVAILABLE,
    }


def list_inference_operators():
    """Return list of available inference operators."""
    if not _INFERENCE_AVAILABLE:
        return []

    return [
        "SystemZ - System Z inference with ranking-based approach",
        "SystemW - System W inference with partial MaxSAT",
        "CInference - c-inference using constraint satisfaction",
        "PEntailment - p-entailment using SAT checks",
        "LexInf - Lexicographic inference",
        "SystemWZ3 - Z3-optimized System W implementation",
        "LexInfZ3 - Z3-optimized lexicographic inference",
    ]


def check_solvers():
    """Check availability of SAT/SMT solvers."""
    solver_status = {}

    try:
        import z3

        solver_status["z3"] = True
    except ImportError:
        solver_status["z3"] = False

    try:
        import pysmt
        from pysmt.shortcuts import Solver

        try:
            with Solver("z3"):
                solver_status["pysmt_z3"] = True
        except Exception:
            solver_status["pysmt_z3"] = False

        try:
            with Solver("cvc5"):
                solver_status["pysmt_cvc5"] = True
        except Exception:
            solver_status["pysmt_cvc5"] = False
    except ImportError:
        solver_status["pysmt_z3"] = False
        solver_status["pysmt_cvc5"] = False

    try:
        from pysat.solvers import Glucose3

        solver_status["pysat"] = True
    except ImportError:
        solver_status["pysat"] = False

    return solver_status
