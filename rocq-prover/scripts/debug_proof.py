#!/usr/bin/env python3
"""
Debug failing Rocq/Coq proofs with detailed output.

Usage:
    python debug_proof.py file.v
    python debug_proof.py file.v --verbose
    python debug_proof.py file.v --show-goals
    python debug_proof.py file.v --check-universes
"""

import sys
import subprocess
import argparse
from pathlib import Path


def get_coqtop_path():
    """Get the path to coqtop executable."""
    windows_path = Path("C:/Coq-Platform~8.19~2024.10/bin/coqtop.exe")
    if windows_path.exists():
        return str(windows_path)

    windows_coqc = Path("C:/Coq-Platform~8.19~2024.10/bin/coqc.exe")
    if windows_coqc.exists():
        return str(windows_coqc)

    return "coqtop"


def debug_proof(proof_file, verbose=False, show_goals=False, check_universes=False):
    """
    Debug a Rocq/Coq proof file with detailed diagnostics.

    Args:
        proof_file: Path to .v file
        verbose: Show detailed output
        show_goals: Extract goal states
        check_universes: Check universe constraints

    Returns:
        (success: bool, output: str, diagnostics: dict)
    """
    proof_path = Path(proof_file)

    if not proof_path.exists():
        return False, f"Error: File not found: {proof_file}", {}

    if not proof_path.suffix == '.v':
        return False, f"Error: Not a .v file: {proof_file}", {}

    coqtop = get_coqtop_path()
    diagnostics = {}

    # Try compilation first
    cmd = [coqtop, "-batch", "-l", str(proof_path)]

    if verbose:
        print(f"Running: {' '.join(cmd)}\n")

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=120
        )

        output = result.stdout + result.stderr
        diagnostics['return_code'] = result.returncode
        diagnostics['stdout'] = result.stdout
        diagnostics['stderr'] = result.stderr

        # Extract error information
        if result.returncode != 0:
            # Parse error location
            for line in output.split('\n'):
                if 'File' in line and 'line' in line:
                    diagnostics['error_location'] = line.strip()
                if 'Error:' in line:
                    diagnostics['error_message'] = line.strip()

        # Check for universe issues if requested
        if check_universes:
            universe_cmd = [coqtop, "-batch", "-l", str(proof_path)]
            try:
                uni_result = subprocess.run(
                    universe_cmd,
                    capture_output=True,
                    text=True,
                    timeout=30
                )
                if 'Universe' in uni_result.stderr or 'Universe' in uni_result.stdout:
                    diagnostics['universe_issues'] = True
            except:
                pass

        success = result.returncode == 0
        return success, output, diagnostics

    except subprocess.TimeoutExpired:
        return False, "Error: Compilation timed out after 120 seconds", {'timeout': True}
    except FileNotFoundError:
        return False, f"Error: coqtop not found at {coqtop}", {}
    except Exception as e:
        return False, f"Error: {str(e)}", {}


def print_diagnostics(diagnostics, verbose=False):
    """Print diagnostic information."""
    print("\n" + "="*60)
    print("DIAGNOSTICS")
    print("="*60)

    if 'error_location' in diagnostics:
        print(f"\nError Location: {diagnostics['error_location']}")

    if 'error_message' in diagnostics:
        print(f"Error Message: {diagnostics['error_message']}")

    if 'universe_issues' in diagnostics:
        print("\n[WARNING] Potential universe consistency issues detected")

    if 'timeout' in diagnostics:
        print("\n[WARNING] Compilation timed out - possible infinite loop")

    if verbose and 'stdout' in diagnostics:
        if diagnostics['stdout'].strip():
            print("\nStandard Output:")
            print(diagnostics['stdout'])

    if verbose and 'stderr' in diagnostics:
        if diagnostics['stderr'].strip():
            print("\nStandard Error:")
            print(diagnostics['stderr'])


def main():
    parser = argparse.ArgumentParser(
        description="Debug failing Rocq/Coq proofs with detailed output"
    )
    parser.add_argument('file', help='Path to .v file to debug')
    parser.add_argument('--verbose', action='store_true', help='Show detailed output')
    parser.add_argument('--show-goals', action='store_true', help='Extract goal states (not yet implemented)')
    parser.add_argument('--check-universes', action='store_true', help='Check universe constraints')

    args = parser.parse_args()

    print(f"Debugging: {args.file}")

    success, output, diagnostics = debug_proof(
        args.file,
        verbose=args.verbose,
        show_goals=args.show_goals,
        check_universes=args.check_universes
    )

    if success:
        print("\n[SUCCESS] No errors found!")
        if args.verbose and output.strip():
            print("\nOutput:")
            print(output)
        return 0
    else:
        print("\n[FAILED] Compilation failed")
        print("\nError Output:")
        print(output)

        print_diagnostics(diagnostics, args.verbose)

        print("\n" + "="*60)
        print("SUGGESTED ACTIONS")
        print("="*60)
        print("1. Check the error location and line number")
        print("2. Review error_resolution.md for this error type")
        print("3. Try simplifying the problematic proof step")
        print("4. Run: python scripts/find_admits.py to check for incomplete proofs")

        return 1


if __name__ == "__main__":
    sys.exit(main())
