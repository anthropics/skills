#!/usr/bin/env python3
"""
Model Integrity Verification

Verify downloaded models against SHA256 checksums to detect corruption,
tampering, or incomplete downloads. Supports batch verification and detailed
diagnostics.

Usage:
    python verify-model-integrity.py --file <PATH> --checksum <HASH>
    python verify-model-integrity.py --registry <JSON> --model-dir <PATH>
"""

import os
import sys
import json
import hashlib
import argparse
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass, asdict
from datetime import datetime
import concurrent.futures


@dataclass
class VerificationResult:
    """Result of model integrity verification."""
    model_id: str
    file_path: str
    file_exists: bool
    expected_checksum: str
    actual_checksum: Optional[str] = None
    checksum_valid: bool = False
    file_size: int = 0
    expected_size: Optional[int] = None
    size_valid: bool = False
    error: Optional[str] = None
    verification_time: str = ""

    @property
    def is_valid(self) -> bool:
        """Check if model passed all validations."""
        return self.checksum_valid and (not self.expected_size or self.size_valid)


class ModelVerifier:
    """Verify model integrity using SHA256 checksums."""

    def __init__(self, chunk_size: int = 8192):
        self.chunk_size = chunk_size

    def verify_file(
        self,
        file_path: Path,
        expected_checksum: str,
        expected_size: Optional[int] = None,
        model_id: str = "",
    ) -> VerificationResult:
        """
        Verify a single file against expected checksum.

        Args:
            file_path: Path to file to verify
            expected_checksum: Expected SHA256 checksum
            expected_size: Expected file size in bytes
            model_id: Model identifier for reporting

        Returns:
            VerificationResult object with detailed results
        """
        result = VerificationResult(
            model_id=model_id or file_path.name,
            file_path=str(file_path),
            expected_checksum=expected_checksum,
            file_exists=file_path.exists(),
            verification_time=datetime.now().isoformat(),
        )

        if not result.file_exists:
            result.error = "File does not exist"
            return result

        try:
            # Get file size
            result.file_size = file_path.stat().st_size

            # Verify size if provided
            if expected_size is not None:
                result.expected_size = expected_size
                result.size_valid = result.file_size == expected_size

                if not result.size_valid:
                    result.error = (
                        f"Size mismatch: expected {expected_size}, "
                        f"got {result.file_size}"
                    )

            # Calculate checksum
            result.actual_checksum = self._calculate_checksum(file_path)

            # Verify checksum
            result.checksum_valid = (
                result.actual_checksum.lower() == expected_checksum.lower()
            )

            if not result.checksum_valid:
                result.error = "Checksum mismatch"

        except Exception as e:
            result.error = f"Verification error: {str(e)}"

        return result

    def verify_batch(
        self,
        models: Dict[str, Dict],
        model_dir: Path,
        num_workers: int = 4,
    ) -> List[VerificationResult]:
        """
        Verify multiple models in parallel.

        Args:
            models: Dict of model_id -> {checksum, size, ...}
            model_dir: Directory containing models
            num_workers: Number of parallel verification workers

        Returns:
            List of VerificationResult objects
        """
        results = []

        with concurrent.futures.ThreadPoolExecutor(max_workers=num_workers) as executor:
            futures = {}

            for model_id, metadata in models.items():
                file_path = model_dir / metadata.get('filename', f"{model_id}.bin")
                future = executor.submit(
                    self.verify_file,
                    file_path=file_path,
                    expected_checksum=metadata['checksum'],
                    expected_size=metadata.get('size'),
                    model_id=model_id,
                )
                futures[future] = model_id

            # Collect results in completion order
            for future in concurrent.futures.as_completed(futures):
                results.append(future.result())

        return results

    def verify_with_progress(
        self,
        file_path: Path,
        expected_checksum: str,
        on_progress=None,
    ) -> Tuple[bool, str]:
        """
        Verify file with progress callback.

        Args:
            file_path: Path to verify
            expected_checksum: Expected checksum
            on_progress: Callback(current_bytes, total_bytes)

        Returns:
            Tuple of (is_valid, actual_checksum)
        """
        sha256_hash = hashlib.sha256()
        file_size = file_path.stat().st_size
        bytes_processed = 0

        with open(file_path, 'rb') as f:
            while True:
                chunk = f.read(self.chunk_size)
                if not chunk:
                    break

                sha256_hash.update(chunk)
                bytes_processed += len(chunk)

                if on_progress:
                    on_progress(bytes_processed, file_size)

        actual_checksum = sha256_hash.hexdigest()
        is_valid = actual_checksum.lower() == expected_checksum.lower()

        return is_valid, actual_checksum

    @staticmethod
    def _calculate_checksum(file_path: Path, chunk_size: int = 8192) -> str:
        """Calculate SHA256 checksum of file."""
        sha256_hash = hashlib.sha256()

        with open(file_path, 'rb') as f:
            for chunk in iter(lambda: f.read(chunk_size), b''):
                sha256_hash.update(chunk)

        return sha256_hash.hexdigest()


class ModelRegistry:
    """Manage model registry with checksums."""

    def __init__(self, registry_file: Path):
        self.registry_file = Path(registry_file)
        self.models = self._load_registry()

    def _load_registry(self) -> Dict:
        """Load model registry from JSON file."""
        if not self.registry_file.exists():
            return {}

        try:
            with open(self.registry_file, 'r') as f:
                data = json.load(f)
                return data.get('models', {})
        except (json.JSONDecodeError, IOError) as e:
            print(f"Error loading registry: {e}", file=sys.stderr)
            return {}

    def get_model(self, model_id: str) -> Optional[Dict]:
        """Get model metadata from registry."""
        return self.models.get(model_id)

    def list_models(self) -> List[str]:
        """List all registered models."""
        return list(self.models.keys())


def diagnose_corruption(
    file_path: Path,
    expected_checksum: str,
    expected_size: Optional[int] = None,
) -> Dict:
    """
    Diagnose types and causes of file corruption.

    Returns:
        Dict with detailed diagnostics
    """
    diagnosis = {
        'file_exists': False,
        'file_size': 0,
        'size_valid': True,
        'checksum_valid': False,
        'corruption_type': None,
        'recovery_possible': True,
    }

    if not file_path.exists():
        diagnosis['corruption_type'] = 'missing_file'
        diagnosis['recovery_possible'] = False
        return diagnosis

    diagnosis['file_exists'] = True
    diagnosis['file_size'] = file_path.stat().st_size

    # Check size
    if expected_size:
        size_valid = diagnosis['file_size'] == expected_size
        diagnosis['size_valid'] = size_valid

        if not size_valid:
            if diagnosis['file_size'] < expected_size:
                diagnosis['corruption_type'] = 'incomplete_download'
                diagnosis['recovery_possible'] = True
                diagnosis['missing_bytes'] = expected_size - diagnosis['file_size']
            else:
                diagnosis['corruption_type'] = 'file_too_large'
                diagnosis['recovery_possible'] = False

    # Check checksum
    verifier = ModelVerifier()
    actual_checksum = verifier._calculate_checksum(file_path)
    checksum_valid = actual_checksum.lower() == expected_checksum.lower()
    diagnosis['checksum_valid'] = checksum_valid
    diagnosis['actual_checksum'] = actual_checksum

    if not checksum_valid:
        if diagnosis['corruption_type'] is None:
            diagnosis['corruption_type'] = 'data_corruption'
        diagnosis['recovery_possible'] = True

    return diagnosis


def format_size(bytes_size: int) -> str:
    """Format bytes to human-readable size."""
    for unit in ['B', 'KB', 'MB', 'GB', 'TB']:
        if bytes_size < 1024:
            return f"{bytes_size:.2f} {unit}"
        bytes_size /= 1024
    return f"{bytes_size:.2f} PB"


def print_verification_result(result: VerificationResult, verbose: bool = False) -> None:
    """Print formatted verification result."""
    status = "✓" if result.is_valid else "✗"
    checksum_status = "✓" if result.checksum_valid else "✗"
    size_status = "✓" if result.size_valid else "✗"

    print(f"{status} {result.model_id}")

    if verbose:
        print(f"  File: {result.file_path}")
        print(f"  Exists: {'Yes' if result.file_exists else 'No'}")

        if result.file_exists:
            print(f"  Size: {format_size(result.file_size)}", end="")
            if result.expected_size:
                print(f" {size_status} (expected: {format_size(result.expected_size)})")
            else:
                print()

            if result.actual_checksum:
                print(f"  Checksum: {result.actual_checksum[:16]}... {checksum_status}")
                if not result.checksum_valid:
                    print(f"  Expected: {result.expected_checksum[:16]}...")

        if result.error:
            print(f"  Error: {result.error}")

        print()


def main():
    """CLI interface for model verification."""
    parser = argparse.ArgumentParser(
        description='Verify model file integrity with SHA256 checksums'
    )

    # Single file verification
    parser.add_argument('--file', help='File to verify')
    parser.add_argument('--checksum', help='Expected SHA256 checksum')
    parser.add_argument('--size', type=int, help='Expected file size in bytes')

    # Batch verification
    parser.add_argument(
        '--registry',
        help='Model registry JSON file',
    )
    parser.add_argument(
        '--model-dir',
        help='Directory containing models',
    )
    parser.add_argument(
        '--model-id',
        help='Verify specific model from registry',
    )

    # Options
    parser.add_argument(
        '-v', '--verbose',
        action='store_true',
        help='Verbose output',
    )
    parser.add_argument(
        '--diagnose',
        action='store_true',
        help='Show detailed corruption diagnostics',
    )
    parser.add_argument(
        '--workers',
        type=int,
        default=4,
        help='Parallel workers for batch verification (default: 4)',
    )
    parser.add_argument(
        '--output',
        choices=['text', 'json'],
        default='text',
        help='Output format (default: text)',
    )

    args = parser.parse_args()

    verifier = ModelVerifier()
    exit_code = 0

    # Single file verification
    if args.file and args.checksum:
        file_path = Path(args.file)
        result = verifier.verify_file(
            file_path=file_path,
            expected_checksum=args.checksum,
            expected_size=args.size,
        )

        if args.output == 'json':
            print(json.dumps(asdict(result), indent=2))
        else:
            print_verification_result(result, args.verbose)

            if args.diagnose and not result.is_valid:
                diagnosis = diagnose_corruption(
                    file_path,
                    args.checksum,
                    args.size,
                )
                print("Corruption Diagnosis:")
                print(json.dumps(diagnosis, indent=2))

        exit_code = 0 if result.is_valid else 1

    # Batch verification from registry
    elif args.registry and args.model_dir:
        registry = ModelRegistry(Path(args.registry))
        model_dir = Path(args.model_dir)

        if args.model_id:
            models = {args.model_id: registry.get_model(args.model_id)}
        else:
            models = registry.models

        results = verifier.verify_batch(
            models=models,
            model_dir=model_dir,
            num_workers=args.workers,
        )

        if args.output == 'json':
            print(json.dumps(
                [asdict(r) for r in results],
                indent=2,
            ))
        else:
            print(f"Verifying {len(results)} models...\n")

            valid_count = sum(1 for r in results if r.is_valid)
            invalid_count = len(results) - valid_count

            for result in results:
                print_verification_result(result, args.verbose)

            print(f"\nSummary: {valid_count} valid, {invalid_count} invalid")
            exit_code = 0 if invalid_count == 0 else 1

    else:
        parser.print_help()
        exit_code = 1

    return exit_code


if __name__ == '__main__':
    sys.exit(main())
