"""Check version-dependent scaffold and package-manager commands."""

import os
import subprocess
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).with_name("init-artifact.sh")


class CreateViteVersionTests(unittest.TestCase):
    def scaffold_command_for(self, version: str) -> str:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            bin_dir = root / "bin"
            bin_dir.mkdir()
            node = bin_dir / "node"
            node.write_text(
                '#!/bin/sh\n'
                'if [ "$1" = "-v" ]; then echo "v$FAKE_NODE_VERSION"; '
                'else echo "$FAKE_NODE_VERSION"; fi\n',
                encoding="utf-8",
            )
            node.chmod(0o755)
            pnpm = bin_dir / "pnpm"
            pnpm.write_text(
                '#!/bin/sh\nprintf "%s\\n" "$*" >> "$PNPM_LOG"\nexit 77\n',
                encoding="utf-8",
            )
            pnpm.chmod(0o755)
            log = root / "pnpm.log"
            env = {
                **os.environ,
                "PATH": f"{bin_dir}:{os.environ['PATH']}",
                "FAKE_NODE_VERSION": version,
                "PNPM_LOG": str(log),
            }
            result = subprocess.run(
                ["bash", str(SCRIPT), "sample-app"],
                cwd=root, env=env, capture_output=True, text=True, check=False,
            )
            self.assertEqual(result.returncode, 77, result.stdout + result.stderr)
            return log.read_text(encoding="utf-8").strip()

    def install_command_for(self, version: str) -> str:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            bin_dir = root / "bin"
            bin_dir.mkdir()
            node = bin_dir / "node"
            node.write_text(
                '#!/bin/sh\n'
                'if [ "$1" = "-v" ]; then echo "v$FAKE_NODE_VERSION"; '
                'else echo "$FAKE_NODE_VERSION"; fi\n',
                encoding="utf-8",
            )
            node.chmod(0o755)
            npm = bin_dir / "npm"
            npm.write_text(
                '#!/bin/sh\nprintf "%s\\n" "$*" >> "$NPM_LOG"\nexit 77\n',
                encoding="utf-8",
            )
            npm.chmod(0o755)
            log = root / "npm.log"
            env = {
                **os.environ,
                "PATH": f"{bin_dir}:/usr/bin:/bin",
                "FAKE_NODE_VERSION": version,
                "NPM_LOG": str(log),
            }
            result = subprocess.run(
                ["/bin/bash", str(SCRIPT), "sample-app"],
                cwd=root, env=env, capture_output=True, text=True, check=False,
            )
            self.assertEqual(result.returncode, 77, result.stdout + result.stderr)
            return log.read_text(encoding="utf-8").strip()

    def test_node_18_uses_compatible_scaffolder(self):
        self.assertEqual(
            self.scaffold_command_for("18.20.8"),
            "create vite@5.5.5 sample-app --template react-ts",
        )

    def test_older_node_20_uses_compatible_scaffolder(self):
        self.assertEqual(
            self.scaffold_command_for("20.18.3"),
            "create vite@5.5.5 sample-app --template react-ts",
        )

    def test_supported_node_20_uses_latest(self):
        self.assertEqual(
            self.scaffold_command_for("20.19.0"),
            "create vite sample-app --template react-ts",
        )

    def test_older_node_22_uses_compatible_scaffolder(self):
        self.assertEqual(
            self.scaffold_command_for("22.11.0"),
            "create vite@5.5.5 sample-app --template react-ts",
        )

    def test_supported_node_22_uses_latest(self):
        self.assertEqual(
            self.scaffold_command_for("22.12.0"),
            "create vite sample-app --template react-ts",
        )

    def test_node_18_installs_compatible_pnpm(self):
        self.assertEqual(self.install_command_for("18.20.8"), "install -g pnpm@9.15.9")

    def test_supported_node_22_installs_latest_pnpm(self):
        self.assertEqual(self.install_command_for("22.13.0"), "install -g pnpm")


if __name__ == "__main__":
    unittest.main()
