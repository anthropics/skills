#!/usr/bin/env python3
"""
Verify Rocq/Coq proof files compile successfully.

Usage:
    python verify_proof.py file.v
    python verify_proof.py file.v --project-file _CoqProject
    python verify_proof.py file.v --coq-flags "-R theories MyProject"
    python verify_proof.py file.v --interactive
    python verify_proof.py file.v --verbose

Examples:
    # Standard verification
    python verify_proof.py MyProof.v

    # HoTT project
    python verify_proof.py file.v --coq-flags "-R path/to/HoTT/theories HoTT -noinit -indices-matter"

    # With project file
    python verify_proof.py file.v --project-file _CoqProject
"""

import sys
import subprocess
import argparse
from pathlib import Path


def get_coqtop_path():
    """Get the path to coqtop executable with robust detection."""
    import os

    # Check COQBIN environment variable first (highest priority)
    if 'COQBIN' in os.environ:
        coqtop = Path(os.environ['COQBIN']) / 'coqtop'
        if coqtop.exists():
            return str(coqtop)
        coqtop_exe = Path(os.environ['COQBIN']) / 'coqtop.exe'
        if coqtop_exe.exists():
            return str(coqtop_exe)

    # Try to find coqtop in system PATH
    try:
        result = subprocess.run(['coqtop', '--version'],
                              capture_output=True, timeout=5)
        if result.returncode == 0:
            return 'coqtop'
    except:
        pass

    # Try common Windows installation paths
    windows_paths = [
        "C:/Coq-Platform~8.19~2024.10/bin/coqtop.exe",
        "C:/Coq-Platform~8.18~2024.01/bin/coqtop.exe",
        "C:/Coq/bin/coqtop.exe",
    ]

    for path_str in windows_paths:
        path = Path(path_str)
        if path.exists():
            return str(path)

    # Try coqc as alternative
    try:
        result = subprocess.run(['coqc', '--version'],
                              capture_output=True, timeout=5)
        if result.returncode == 0:
            return 'coqc'
    except:
        pass

    # Last resort fallback
    return "coqtop"


def read_project_file(project_file):
    """Read _CoqProject file and extract coq flags."""
    flags = []
    try:
        with open(project_file, 'r') as f:
            for line in f:
                line = line.strip()
                # Skip comments and empty lines
                if not line or line.startswith('#'):
                    continue
                # Skip .v file entries
                if line.endswith('.v'):
                    continue
                # Add flags
                flags.append(line)
        return ' '.join(flags)
    except FileNotFoundError:
        print(f"Warning: Project file not found: {project_file}")
        return ""


def verify_proof(proof_file, coq_flags="", interactive=False, verbose=False):
    """
    Verify a Rocq/Coq proof file.

    Args:
        proof_file: Path to .v file
        coq_flags: Additional flags to pass to coqtop
        interactive: Whether to run in interactive mode
        verbose: Whether to show detailed output

    Returns:
        (success: bool, output: str)
    """
    proof_path = Path(proof_file)

    if not proof_path.exists():
        return False, f"Error: File not found: {proof_file}"

    if not proof_path.suffix == '.v':
        return False, f"Error: Not a .v file: {proof_file}"

    coqtop = get_coqtop_path()

    # Build command
    # Use -batch -l to load and execute file
    cmd = [coqtop, "-batch", "-l", str(proof_path)]

    # Add custom flags if provided
    if coq_flags:
        # Split flags and insert them before -batch
        flag_list = coq_flags.split()
        cmd = [coqtop] + flag_list + ["-batch", "-l", str(proof_path)]

    if verbose:
        print(f"Running command: {' '.join(cmd)}")

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=120  # 2 minute timeout
        )

        output = result.stdout + result.stderr

        if result.returncode == 0:
            return True, output
        else:
            return False, output

    except subprocess.TimeoutExpired:
        return False, "Error: Compilation timed out after 120 seconds"
    except FileNotFoundError:
        return False, f"Error: coqtop not found at {coqtop}. Please check your Coq installation."
    except Exception as e:
        return False, f"Error: {str(e)}"


def main():
    parser = argparse.ArgumentParser(
        description="Verify Rocq/Coq proof files compile successfully"
    )
    parser.add_argument('file', help='Path to .v file to verify')
    parser.add_argument('--project-file', help='Path to _CoqProject file')
    parser.add_argument('--coq-flags', default='', help='Additional flags for coqtop')
    parser.add_argument('--interactive', action='store_true', help='Interactive mode (not yet implemented)')
    parser.add_argument('--verbose', action='store_true', help='Show detailed output')

    args = parser.parse_args()

    # Read project file if provided
    coq_flags = args.coq_flags
    if args.project_file:
        project_flags = read_project_file(args.project_file)
        coq_flags = f"{project_flags} {coq_flags}".strip()

    print(f"Verifying: {args.file}")
    if coq_flags and args.verbose:
        print(f"Flags: {coq_flags}")

    success, output = verify_proof(
        args.file,
        coq_flags=coq_flags,
        interactive=args.interactive,
        verbose=args.verbose
    )

    if success:
        print("[SUCCESS] Verification successful!")
        if args.verbose and output.strip():
            print("\nOutput:")
            print(output)
        return 0
    else:
        print("[FAILED] Verification failed!")
        print("\nError output:")
        print(output)
        return 1


if __name__ == "__main__":
    sys.exit(main())
