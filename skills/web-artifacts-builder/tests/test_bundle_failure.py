import os
import subprocess
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "bundle-artifact.sh"


class BundleFailureTests(unittest.TestCase):
    def run_bundle(self, failure_stage):
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            (project / "package.json").write_text("{}")
            (project / "index.html").write_text("<html>source</html>")
            (project / "bundle.html").write_text("known good bundle")
            bin_dir = project / "bin"
            bin_dir.mkdir()
            pnpm = bin_dir / "pnpm"
            pnpm.write_text(
                "#!/bin/sh\n"
                "if [ \"$1\" = add ]; then exit 0; fi\n"
                "if [ \"$1 $2\" = 'exec parcel' ]; then\n"
                "  mkdir -p dist\n"
                "  printf '<html>new bundle</html>' > dist/index.html\n"
                "  if [ \"$FAIL_STAGE\" = parcel ]; then exit 3; fi\n"
                "  exit 0\n"
                "fi\n"
                "if [ \"$1 $2\" = 'exec html-inline' ]; then\n"
                "  if [ \"$FAIL_STAGE\" = inline ]; then\n"
                "    printf 'partial output'\n"
                "    exit 4\n"
                "  fi\n"
                "  if [ \"$FAIL_STAGE\" = empty ]; then exit 0; fi\n"
                "  cat \"$3\"\n"
                "  exit 0\n"
                "fi\n"
                "exit 5\n"
            )
            pnpm.chmod(0o755)
            env = os.environ.copy()
            env["PATH"] = f"{bin_dir}:{env['PATH']}"
            env["FAIL_STAGE"] = failure_stage
            result = subprocess.run(
                ["bash", str(SCRIPT)], cwd=project, env=env, capture_output=True, text=True
            )
            bundle_path = project / "bundle.html"
            return result.returncode, bundle_path.read_text() if bundle_path.exists() else None

    def test_existing_bundle_survives_build_failure(self):
        code, bundle = self.run_bundle("parcel")
        self.assertNotEqual(code, 0)
        self.assertEqual(bundle, "known good bundle")

    def test_existing_bundle_survives_partial_inline_failure(self):
        code, bundle = self.run_bundle("inline")
        self.assertNotEqual(code, 0)
        self.assertEqual(bundle, "known good bundle")

    def test_existing_bundle_survives_empty_inline_output(self):
        code, bundle = self.run_bundle("empty")
        self.assertNotEqual(code, 0)
        self.assertEqual(bundle, "known good bundle")

    def test_successful_build_replaces_existing_bundle(self):
        code, bundle = self.run_bundle("")
        self.assertEqual(code, 0)
        self.assertEqual(bundle, "<html>new bundle</html>")


if __name__ == "__main__":
    unittest.main()
