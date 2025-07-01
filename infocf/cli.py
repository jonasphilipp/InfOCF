"""
InfOCF Command Line Interface

Basic CLI for InfOCF package management and information.
"""

import argparse
import sys
from typing import Optional

import infocf


def print_version():
    """Print version information."""
    print(f"InfOCF version {infocf.__version__}")


def print_package_info():
    """Print comprehensive package information."""
    info = infocf.get_package_info()
    
    print("InfOCF - Reasoning With Conditional Belief Bases")
    print("=" * 50)
    print(f"Version: {info['version']}")
    print(f"Author: {info['author']}")
    print(f"License: {info['license']}")
    print(f"Description: {info['description']}")
    print(f"URL: {info['url']}")
    print(f"Python requirement: {info['python_requires']}")
    print(f"Inference modules available: {'Yes' if info['inference_available'] else 'No'}")


def print_inference_operators():
    """Print available inference operators."""
    operators = infocf.list_inference_operators()
    
    if not operators:
        print("No inference operators available. Install missing dependencies.")
        return
    
    print("Available Inference Operators:")
    print("-" * 30)
    for op in operators:
        print(f"• {op}")


def check_and_print_solvers():
    """Check and print solver availability."""
    solvers = infocf.check_solvers()
    
    print("SAT/SMT Solver Status:")
    print("-" * 25)
    
    for solver, available in solvers.items():
        status = "✓ Available" if available else "✗ Not available"
        print(f"{solver:<12}: {status}")
    
    # Summary
    available_count = sum(solvers.values())
    total_count = len(solvers)
    
    print(f"\nSummary: {available_count}/{total_count} solvers available")
    
    if available_count == 0:
        print("\nWarning: No solvers available. InfOCF requires at least one SAT/SMT solver.")
        print("Install solvers using: pip install 'infocf[solvers]'")
        return False
    
    return True


def run_system_check():
    """Run comprehensive system check."""
    print("InfOCF System Check")
    print("=" * 20)
    print()
    
    # Package info
    print_package_info()
    print()
    
    # Check inference availability
    if infocf._INFERENCE_AVAILABLE:
        print_inference_operators()
        print()
    else:
        print("Warning: Inference modules not available.")
        print("This may be due to missing dependencies.")
        print()
    
    # Check solvers
    solvers_ok = check_and_print_solvers()
    print()
    
    # Overall status
    if infocf._INFERENCE_AVAILABLE and solvers_ok:
        print("✓ System check passed. InfOCF is ready to use!")
        return True
    else:
        print("✗ System check failed. Some components are missing.")
        return False


def create_parser() -> argparse.ArgumentParser:
    """Create the argument parser."""
    parser = argparse.ArgumentParser(
        prog="infocf",
        description="InfOCF - Reasoning With Conditional Belief Bases",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s --version                Show version information
  %(prog)s --info                   Show package information  
  %(prog)s --operators              List inference operators
  %(prog)s --check-solvers          Check solver availability
  %(prog)s --system-check           Run comprehensive system check
        """
    )
    
    parser.add_argument(
        "--version", "-v",
        action="store_true",
        help="Show version information"
    )
    
    parser.add_argument(
        "--info", "-i",
        action="store_true", 
        help="Show package information"
    )
    
    parser.add_argument(
        "--operators", "-o",
        action="store_true",
        help="List available inference operators"
    )
    
    parser.add_argument(
        "--check-solvers", "-s",
        action="store_true",
        help="Check SAT/SMT solver availability"
    )
    
    parser.add_argument(
        "--system-check", "-c",
        action="store_true", 
        help="Run comprehensive system check"
    )
    
    return parser


def main(argv: Optional[list] = None) -> int:
    """Main CLI entry point."""
    parser = create_parser()
    args = parser.parse_args(argv)
    
    # If no arguments provided, show help
    if not any(vars(args).values()):
        parser.print_help()
        return 0
    
    try:
        if args.version:
            print_version()
        
        if args.info:
            print_package_info()
        
        if args.operators:
            print_inference_operators()
        
        if args.check_solvers:
            solvers_ok = check_and_print_solvers()
            if not solvers_ok:
                return 1
        
        if args.system_check:
            system_ok = run_system_check()
            if not system_ok:
                return 1
        
        return 0
        
    except KeyboardInterrupt:
        print("\nOperation cancelled by user.")
        return 130
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main()) 