import json
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "init-artifact.sh"


class InitArtifactTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if shutil.which("node") is None:
            raise unittest.SkipTest("Node.js is required by the initializer")

        cls.temporary = tempfile.TemporaryDirectory()
        cls.root = Path(cls.temporary.name)
        bin_dir = cls.root / "bin"
        bin_dir.mkdir()
        pnpm = bin_dir / "pnpm"
        pnpm.write_text(
            "#!/bin/sh\n"
            "printf '%s\\n' \"$*\" >> \"$PNPM_LOG\"\n"
            "if [ \"$1 $2\" = 'create vite' ]; then\n"
            "  mkdir -p \"$3/src\"\n"
            "  printf '<link rel=\"icon\" href=\"/vite.svg\">\\n<title>Vite</title>\\n' > \"$3/index.html\"\n"
            "  printf '{\"compilerOptions\":{}}' > \"$3/tsconfig.json\"\n"
            "  printf '{\"compilerOptions\":{}}' > \"$3/tsconfig.app.json\"\n"
            "fi\n"
        )
        pnpm.chmod(0o755)
        env = os.environ.copy()
        env["PATH"] = f"{bin_dir}:{env['PATH']}"
        env["PNPM_LOG"] = str(cls.root / "pnpm.log")
        result = subprocess.run(
            ["bash", str(SCRIPT), "example"],
            cwd=cls.root,
            env=env,
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            cls.temporary.cleanup()
            raise AssertionError(f"initializer failed:\n{result.stdout}\n{result.stderr}")

    @classmethod
    def tearDownClass(cls):
        if hasattr(cls, "temporary"):
            cls.temporary.cleanup()

    def test_paths_do_not_require_deprecated_base_url(self):
        for name in ("tsconfig.json", "tsconfig.app.json"):
            with self.subTest(name=name):
                config = json.loads((self.root / "example" / name).read_text())
                self.assertNotIn("baseUrl", config["compilerOptions"])
                self.assertEqual(config["compilerOptions"]["paths"], {"@/*": ["./src/*"]})

    def test_calendar_dependency_matches_vendored_component(self):
        commands = (self.root / "pnpm.log").read_text()
        self.assertIn("react-day-picker@^9", commands)


if __name__ == "__main__":
    unittest.main()
