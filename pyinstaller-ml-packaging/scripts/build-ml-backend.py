#!/usr/bin/env python3
"""
PyInstaller ML Backend Build Script
Automated build orchestration for ML inference executable packaging

Features:
- Automated spec file validation
- Dependency verification
- Build process management
- Bundle validation and testing
- Size optimization reporting
"""

import os
import sys
import subprocess
import json
import shutil
import argparse
from pathlib import Path
from datetime import datetime


class MLBackendBuilder:
    """Orchestrates PyInstaller builds for ML backends"""

    def __init__(self, spec_file, output_dir="dist", verbose=False):
        self.spec_file = Path(spec_file)
        self.output_dir = Path(output_dir)
        self.verbose = verbose
        self.build_log = []

    def log(self, message, level="INFO"):
        """Log messages with timestamp"""
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        log_entry = f"[{timestamp}] {level}: {message}"
        self.build_log.append(log_entry)
        if self.verbose or level in ["ERROR", "WARNING"]:
            print(log_entry)

    def validate_spec_file(self):
        """Validate spec file exists and is readable"""
        self.log(f"Validating spec file: {self.spec_file}")

        if not self.spec_file.exists():
            self.log(f"Spec file not found: {self.spec_file}", "ERROR")
            return False

        try:
            with open(self.spec_file) as f:
                content = f.read()

            # Check for required spec components
            required = ["Analysis", "PYZ", "EXE", "COLLECT"]
            for component in required:
                if component not in content:
                    self.log(f"Missing component in spec: {component}", "WARNING")

            self.log("Spec file validation passed")
            return True
        except Exception as e:
            self.log(f"Spec file validation failed: {e}", "ERROR")
            return False

    def check_dependencies(self):
        """Verify required Python packages are installed"""
        self.log("Checking dependencies")

        required_packages = {
            "pyinstaller": "6.16.0",
        }

        optional_packages = ["torch", "diffusers", "transformers", "onnx"]

        missing = []
        for package in required_packages:
            try:
                __import__(package)
                self.log(f"Found {package}")
            except ImportError:
                missing.append(package)
                self.log(f"Missing required package: {package}", "ERROR")

        for package in optional_packages:
            try:
                __import__(package)
                self.log(f"Found optional package: {package}")
            except ImportError:
                self.log(f"Optional package not found: {package}")

        return len(missing) == 0

    def build(self):
        """Execute PyInstaller build"""
        self.log(f"Starting build with spec: {self.spec_file}")

        try:
            cmd = [
                "pyinstaller",
                "--noconfirm",
                str(self.spec_file)
            ]

            self.log(f"Build command: {' '.join(cmd)}")

            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=3600
            )

            if result.returncode != 0:
                self.log(f"Build failed: {result.stderr}", "ERROR")
                return False

            self.log("Build completed successfully")
            return True
        except subprocess.TimeoutExpired:
            self.log("Build timed out after 1 hour", "ERROR")
            return False
        except Exception as e:
            self.log(f"Build error: {e}", "ERROR")
            return False

    def validate_bundle(self, binary_path):
        """Validate built executable"""
        self.log(f"Validating bundle: {binary_path}")

        if not Path(binary_path).exists():
            self.log(f"Binary not found: {binary_path}", "ERROR")
            return False

        # Check file size
        size_mb = Path(binary_path).stat().st_size / (1024 * 1024)
        self.log(f"Binary size: {size_mb:.1f} MB")

        # Check executable permissions
        if not os.access(binary_path, os.X_OK):
            self.log(f"Binary is not executable", "WARNING")

        self.log("Bundle validation passed")
        return True

    def get_build_stats(self):
        """Calculate and report build statistics"""
        stats = {
            "timestamp": datetime.now().isoformat(),
            "spec_file": str(self.spec_file),
            "log_entries": len(self.build_log),
        }

        if self.output_dir.exists():
            total_size = sum(
                f.stat().st_size
                for f in self.output_dir.rglob("*")
                if f.is_file()
            )
            stats["bundle_size_mb"] = round(total_size / (1024 * 1024), 1)

        return stats

    def save_build_log(self):
        """Save build log to file"""
        log_file = self.output_dir / "build.log"
        log_file.parent.mkdir(parents=True, exist_ok=True)

        with open(log_file, "w") as f:
            f.write("\n".join(self.build_log))

        self.log(f"Build log saved: {log_file}")

    def run(self):
        """Execute complete build workflow"""
        self.log("=== PyInstaller ML Backend Build ===")

        # Validation phase
        if not self.validate_spec_file():
            return False

        if not self.check_dependencies():
            return False

        # Build phase
        if not self.build():
            return False

        # Post-build validation
        # Determine binary name from spec
        spec_name = self.spec_file.stem

        self.log("=== Build Complete ===")
        stats = self.get_build_stats()
        self.log(json.dumps(stats, indent=2))

        self.save_build_log()
        return True


def main():
    parser = argparse.ArgumentParser(
        description="Build ML backend executables with PyInstaller"
    )
    parser.add_argument(
        "spec_file",
        help="Path to PyInstaller spec file"
    )
    parser.add_argument(
        "--output-dir",
        default="dist",
        help="Output directory for build (default: dist)"
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Verbose output"
    )

    args = parser.parse_args()

    builder = MLBackendBuilder(
        args.spec_file,
        args.output_dir,
        args.verbose
    )

    success = builder.run()
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
