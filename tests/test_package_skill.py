"""Real CLI regressions for skill archive contents (requires PyYAML)."""

from contextlib import redirect_stdout
import io
import os
from pathlib import Path
import random
import signal
import subprocess
import sys
import tempfile
import unittest
from unittest import mock
import zipfile


SKILL_CREATOR = Path(__file__).resolve().parents[1] / "skills/skill-creator"


def limit_output_size():
    # Bound the original self-inclusion failure when running the regression on
    # an unfixed checkout. This limit applies only to the test subprocess.
    import resource

    limit = 16 * 1024 * 1024
    resource.setrlimit(resource.RLIMIT_FSIZE, (limit, limit))
    signal.signal(signal.SIGXFSZ, signal.SIG_IGN)


class PackageSkillTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.skill = self.root / "sample-skill"
        self.skill.mkdir()
        self.skill_text = (
            "---\nname: sample-skill\ndescription: A packaging test.\n---\n# Test\n"
        ).encode("utf-8")
        (self.skill / "SKILL.md").write_bytes(self.skill_text)

    def package(self, output=None, *, cwd=None):
        command = [sys.executable, "-m", "scripts.package_skill", str(self.skill)]
        if output is not None:
            command.append(str(output))
        return subprocess.run(
            command,
            cwd=cwd or self.root,
            env=dict(
                os.environ,
                PYTHONPATH=str(SKILL_CREATOR),
                PYTHONUTF8="1",
                PYTHONIOENCODING="utf-8",
                PYTHONDONTWRITEBYTECODE="1",
            ),
            capture_output=True,
            text=True,
            encoding="utf-8",
            timeout=10,
            preexec_fn=limit_output_size if os.name == "posix" else None,
        )

    def assert_archive(self, output, assets=None):
        expected = {"SKILL.md": self.skill_text, **(assets or {})}
        with zipfile.ZipFile(output / "sample-skill.skill") as archive:
            self.assertIsNone(archive.testzip())
            self.assertCountEqual(
                archive.namelist(), [f"sample-skill/{name}" for name in expected]
            )
            for name, data in expected.items():
                self.assertEqual(archive.read(f"sample-skill/{name}"), data)
                self.assertEqual((self.skill / name).read_bytes(), data)

    def assert_packaged(self, output, *, cwd=None, assets=None):
        result = self.package(output, cwd=cwd)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assert_archive(output, assets)

    def test_output_at_skill_root(self):
        self.assert_packaged(self.skill)

    def test_output_in_nested_directory(self):
        self.assert_packaged(self.skill / "dist")

    def test_default_output_from_skill_directory(self):
        result = self.package(cwd=self.skill)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assert_archive(self.skill)

    def test_relative_output_directory(self):
        result = self.package("dist", cwd=self.skill)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assert_archive(self.skill / "dist")

    @unittest.skipUnless(os.name == "nt", "requires a Windows directory junction")
    def test_default_output_from_junction(self):
        alias = self.root / "skill-junction"
        result = subprocess.run(
            ["cmd.exe", "/d", "/c", "mklink", "/J", str(alias), str(self.skill)],
            capture_output=True, text=True, errors="replace", timeout=10,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.addCleanup(os.rmdir, alias)
        result = self.package(cwd=alias)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assert_archive(self.skill)

    def test_rebuilding_existing_output(self):
        output = self.skill / "dist"
        output.mkdir()
        (output / "sample-skill.skill").write_bytes(b"old output")
        self.assert_packaged(output)
        self.assert_packaged(output)

    def test_other_skill_archives_remain_assets(self):
        # Only the current output should be skipped, not all .skill files or
        # all files in the output directory.
        output = self.skill / "dist"
        output.mkdir()
        assets = {"other.skill": b"root asset", "dist/other.skill": b"nested asset"}
        for name, data in assets.items():
            (self.skill / name).write_bytes(data)
        self.assert_packaged(output, assets=assets)

    def test_hard_link_to_output_archive_is_not_packaged(self):
        output = self.root / "external"
        output.mkdir()
        archive_path = output / "sample-skill.skill"
        archive_path.write_bytes(b"old output")
        alias = self.skill / "linked-output.skill"
        os.link(archive_path, alias)

        # Do not allow a failing implementation to read the archive while it
        # writes through another name for the same file.
        original_write = zipfile.ZipFile.write

        def guarded_write(zipf, filename, *args, **kwargs):
            if Path(filename).samefile(archive_path):
                raise AssertionError("attempted to package the output archive")
            return original_write(zipf, filename, *args, **kwargs)

        with mock.patch.object(zipfile.ZipFile, "write", guarded_write):
            with mock.patch.object(sys, "path", [str(SKILL_CREATOR), *sys.path]):
                from scripts.package_skill import package_skill

                output_text = io.StringIO()
                with redirect_stdout(output_text):
                    result = package_skill(self.skill, output)

        self.assertEqual(result, archive_path, output_text.getvalue())
        self.assert_archive(output)

    @unittest.skipUnless(os.name == "posix", "requires an output-size resource limit")
    def test_binary_asset_does_not_feed_output_back_into_input(self):
        data = random.Random(17).randbytes(65536)
        (self.skill / "reference.bin").write_bytes(data)
        output = self.skill / "dist"
        self.assert_packaged(output, assets={"reference.bin": data})
        self.assertLess((output / "sample-skill.skill").stat().st_size, 131072)

    def test_external_output_preserves_existing_exclusions(self):
        for name in (
            "node_modules/x.txt", "evals/eval.json", "__pycache__/x.pyc", ".DS_Store"
        ):
            path = self.skill / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b"excluded")
        self.assert_packaged(self.root / "external")

    def test_invalid_skill_does_not_create_archive(self):
        (self.skill / "SKILL.md").write_bytes(b"invalid")
        result = self.package(self.root / "external")
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse((self.root / "external/sample-skill.skill").exists())


if __name__ == "__main__":
    unittest.main()
