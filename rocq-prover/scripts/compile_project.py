#!/usr/bin/env python3
"""
Compile entire Rocq/Coq projects using _CoqProject files.

Usage:
    python compile_project.py
    python compile_project.py --project-file _CoqProject
    python compile_project.py --clean
"""

import sys
import subprocess
import argparse
from pathlib import Path


def get_coqtop_path():
    """Get the path to coqtop executable."""
    windows_path = Path("C:/Coq-Platform~8.19~2024.10/bin/coqc.exe")
    if windows_path.exists():
        return str(windows_path)

    return "coqc"


def read_project_file(project_file):
    """Read _CoqProject and extract files and flags."""
    files = []
    flags = []

    try:
        with open(project_file, 'r') as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith('#'):
                    continue
                if line.endswith('.v'):
                    files.append(line)
                else:
                    flags.append(line)
        return files, ' '.join(flags)
    except FileNotFoundError:
        print(f"Error: Project file not found: {project_file}")
        return [], ""


def compile_file(coqc_path, file_path, coq_flags=""):
    """Compile a single .v file."""
    cmd = [coqc_path]

    if coq_flags:
        cmd.extend(coq_flags.split())

    cmd.append(file_path)

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=180
        )
        return result.returncode == 0, result.stdout + result.stderr
    except subprocess.TimeoutExpired:
        return False, f"Timeout compiling {file_path}"
    except Exception as e:
        return False, str(e)


def compile_project(project_file="_CoqProject", clean=False):
    """Compile entire project."""
    if not Path(project_file).exists():
        print(f"Error: Project file not found: {project_file}")
        return 1

    coqc = get_coqtop_path()

    # Read project configuration
    files, flags = read_project_file(project_file)

    if not files:
        print("No .v files found in project file")
        return 1

    print(f"Found {len(files)} files to compile")
    if flags:
        print(f"Flags: {flags}\n")

    # Clean if requested
    if clean:
        print("Cleaning .vo files...")
        for f in files:
            vo_file = Path(f).with_suffix('.vo')
            if vo_file.exists():
                vo_file.unlink()
                print(f"  Removed: {vo_file}")

    # Compile each file
    failed = []
    succeeded = []

    for i, file_path in enumerate(files, 1):
        print(f"[{i}/{len(files)}] Compiling {file_path}...", end=" ")

        success, output = compile_file(coqc, file_path, flags)

        if success:
            print("[OK]")
            succeeded.append(file_path)
        else:
            print("[FAILED]")
            print(f"\nError output:\n{output}\n")
            failed.append(file_path)

    # Summary
    print("\n" + "="*60)
    print("COMPILATION SUMMARY")
    print("="*60)
    print(f"Total files: {len(files)}")
    print(f"Succeeded: {len(succeeded)}")
    print(f"Failed: {len(failed)}")

    if failed:
        print("\nFailed files:")
        for f in failed:
            print(f"  - {f}")
        return 1
    else:
        print("\n[SUCCESS] All files compiled successfully!")
        return 0


def main():
    parser = argparse.ArgumentParser(
        description="Compile entire Rocq/Coq projects"
    )
    parser.add_argument('--project-file', default='_CoqProject',
                        help='Path to _CoqProject file (default: _CoqProject)')
    parser.add_argument('--clean', action='store_true',
                        help='Clean .vo files before compiling')

    args = parser.parse_args()

    return compile_project(args.project_file, args.clean)


if __name__ == "__main__":
    sys.exit(main())
