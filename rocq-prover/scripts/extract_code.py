#!/usr/bin/env python3
"""
Extract executable code from Rocq/Coq proofs.

Usage:
    python extract_code.py file.v --target ocaml
    python extract_code.py file.v --target haskell --output extracted.hs
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

    return "coqtop"


def extract_code(proof_file, target='ocaml', output=None):
    """
    Extract executable code from a Rocq/Coq proof file.

    Args:
        proof_file: Path to .v file
        target: Target language (ocaml, haskell, scheme)
        output: Output file path

    Returns:
        (success: bool, message: str)
    """
    proof_path = Path(proof_file)

    if not proof_path.exists():
        return False, f"Error: File not found: {proof_file}"

    if not proof_path.suffix == '.v':
        return False, f"Error: Not a .v file: {proof_file}"

    # Determine output file
    if not output:
        if target == 'ocaml':
            output = proof_path.with_suffix('.ml')
        elif target == 'haskell':
            output = proof_path.with_suffix('.hs')
        elif target == 'scheme':
            output = proof_path.with_suffix('.scm')
        else:
            return False, f"Error: Unknown target language: {target}"

    # Create extraction file
    extract_file = proof_path.with_suffix('.extract.v')

    extraction_code = f'''(* Auto-generated extraction file *)
Require Import {proof_path.stem}.

'''

    if target == 'ocaml':
        extraction_code += f'''Extraction Language OCaml.
Extraction "{output}" {proof_path.stem}.
'''
    elif target == 'haskell':
        extraction_code += f'''Extraction Language Haskell.
Extraction "{output}" {proof_path.stem}.
'''
    elif target == 'scheme':
        extraction_code += f'''Extraction Language Scheme.
Extraction "{output}" {proof_path.stem}.
'''

    try:
        with open(extract_file, 'w') as f:
            f.write(extraction_code)
    except Exception as e:
        return False, f"Error writing extraction file: {e}"

    # Run Coq extraction
    coqtop = get_coqtop_path()
    cmd = [coqtop, "-batch", "-l", str(extract_file)]

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=120
        )

        # Clean up extraction file
        extract_file.unlink()

        if result.returncode == 0:
            if Path(output).exists():
                return True, f"Code extracted to: {output}"
            else:
                return False, "Extraction completed but output file not found"
        else:
            output_text = result.stdout + result.stderr
            return False, f"Extraction failed:\n{output_text}"

    except subprocess.TimeoutExpired:
        extract_file.unlink()
        return False, "Extraction timed out after 120 seconds"
    except Exception as e:
        if extract_file.exists():
            extract_file.unlink()
        return False, f"Error: {str(e)}"


def main():
    parser = argparse.ArgumentParser(
        description="Extract executable code from Rocq/Coq proofs"
    )
    parser.add_argument('file', help='Path to .v file')
    parser.add_argument('--target', '-t', choices=['ocaml', 'haskell', 'scheme'],
                        default='ocaml', help='Target language (default: ocaml)')
    parser.add_argument('--output', '-o', help='Output file path')

    args = parser.parse_args()

    print(f"Extracting code from: {args.file}")
    print(f"Target language: {args.target}")

    success, message = extract_code(args.file, args.target, args.output)

    if success:
        print(f"\n[SUCCESS] {message}")
        print("\nNote: Proofs are erased during extraction - only computational content is extracted")
        print("You may need to add custom extraction rules for some types")
        return 0
    else:
        print(f"\n[FAILED] {message}")
        print("\nNote: Extraction requires the .v file to be compiled first")
        print("Run: python scripts/verify_proof.py file.v")
        return 1


if __name__ == "__main__":
    sys.exit(main())
