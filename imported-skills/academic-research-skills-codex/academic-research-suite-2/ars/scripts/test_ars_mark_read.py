"""Unit tests for scripts/ars_mark_read.py.

Per v3.6.8 spec §3.6 + Step 7 (round-2 R2-002, round-5 R5-003 amends).
Covers:
- 4 fail-fast modes (no active passport / passport not found / parent unreadable / read-log unwritable)
- First-time write (creates file with YAML schema header)
- Citation-key validation against active literature_corpus[]
- Batch form (space-separated keys)
- Append-only write (existing entries preserved)
- /ars-unmark-read writes rescinded_at (never deletes)
- Idempotency on re-mark of same key (append, not in-place)
"""
from __future__ import annotations

import os
import stat
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

import yaml

from tests.test_helpers import run_script


SCRIPT = Path(__file__).parent / "ars_mark_read.py"


# Minimal Material Passport carrying a literature_corpus[] with 2 entries.
# Passport is YAML per adapter contract (folder_scan / zotero / obsidian all
# emit YAML); only the literature_corpus[] field is consulted by
# ars_mark_read for citation_key validation.
def _write_passport(path: Path, *, citation_keys: list[str]) -> None:
    payload = {
        "literature_corpus": [
            {"citation_key": k, "year": 2024, "title": f"Title {k}"}
            for k in citation_keys
        ],
    }
    with path.open("w", encoding="utf-8") as f:
        yaml.safe_dump(payload, f, sort_keys=False, allow_unicode=True)


def _read_log(passport_path: Path) -> dict:
    log_path = passport_path.parent / f"{passport_path.stem}_human_read_log.yaml"
    with log_path.open(encoding="utf-8") as f:
        return yaml.safe_load(f)


class TestMarkReadHappyPath(unittest.TestCase):
    def test_first_time_write_creates_file_with_schema_header(self) -> None:
        """Spec §3.6 R5-003: first-time write creates the file with the YAML
        schema header before appending. Not a fail-fast mode."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            passport = root / "passport_abc123.json"
            _write_passport(passport, citation_keys=["smith2024"])

            result = run_script(SCRIPT, "smith2024", "--passport-path", str(passport))

            self.assertEqual(result.returncode, 0, msg=f"stderr: {result.stderr}")
            log_data = _read_log(passport)
            self.assertIn("session_id", log_data)
            self.assertIn("created_at", log_data)
            self.assertEqual(len(log_data["human_read"]), 1)
            self.assertEqual(log_data["human_read"][0]["citation_key"], "smith2024")
            self.assertIn("marked_at", log_data["human_read"][0])

    def test_batch_form_appends_multiple_entries(self) -> None:
        """Spec §3.6: /ars-mark-read accepts space-separated keys (batch form).
        Each key produces one entry."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            passport = root / "passport_abc123.json"
            _write_passport(passport, citation_keys=["smith2024", "jones2023"])

            result = run_script(
                SCRIPT, "smith2024", "jones2023", "--passport-path", str(passport)
            )

            self.assertEqual(result.returncode, 0, msg=f"stderr: {result.stderr}")
            log_data = _read_log(passport)
            keys = [e["citation_key"] for e in log_data["human_read"]]
            self.assertEqual(keys, ["smith2024", "jones2023"])

    def test_append_only_preserves_existing_entries(self) -> None:
        """Spec §3.6 firm rule 3: log is append-only. New marks do not
        rewrite or replace prior entries."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            passport = root / "passport_abc123.json"
            _write_passport(passport, citation_keys=["smith2024", "jones2023"])

            # First mark
            run_script(SCRIPT, "smith2024", "--passport-path", str(passport))
            # Second mark, different key
            result = run_script(
                SCRIPT, "jones2023", "--passport-path", str(passport)
            )

            self.assertEqual(result.returncode, 0, msg=f"stderr: {result.stderr}")
            log_data = _read_log(passport)
            keys = [e["citation_key"] for e in log_data["human_read"]]
            self.assertEqual(keys, ["smith2024", "jones2023"])


class TestMarkReadFailFast(unittest.TestCase):
    """4 fail-fast modes per spec §3.6 R5-003 amend."""

    def test_no_active_passport_fails(self) -> None:
        """Fail-fast mode 1: --passport-path omitted and no ambient
        passport discoverable. Emit canonical error, exit non-zero."""
        with TemporaryDirectory() as tmp:
            result = run_script(SCRIPT, "smith2024", cwd=Path(tmp))

            self.assertNotEqual(result.returncode, 0)
            self.assertIn("[ARS-MARK-READ ERROR:", result.stderr + result.stdout)
            self.assertIn("no active passport path", result.stderr + result.stdout)

    def test_passport_not_found_fails(self) -> None:
        """Fail-fast mode 2: --passport-path points to non-existent file."""
        with TemporaryDirectory() as tmp:
            phantom = Path(tmp) / "does_not_exist.json"

            result = run_script(
                SCRIPT, "smith2024", "--passport-path", str(phantom)
            )

            self.assertNotEqual(result.returncode, 0)
            self.assertIn("[ARS-MARK-READ ERROR:", result.stderr + result.stdout)
            self.assertIn("passport file not found", result.stderr + result.stdout)

    def test_passport_parent_unreadable_fails(self) -> None:
        """Fail-fast mode 3: passport parent directory lacks R_OK."""
        if os.geteuid() == 0:
            self.skipTest("root bypasses POSIX permissions")
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            locked = root / "locked"
            locked.mkdir()
            passport = locked / "passport.json"
            _write_passport(passport, citation_keys=["smith2024"])
            # Strip read permission from the parent dir.
            os.chmod(locked, 0o000)
            try:
                result = run_script(
                    SCRIPT, "smith2024", "--passport-path", str(passport)
                )

                self.assertNotEqual(result.returncode, 0)
                self.assertIn(
                    "[ARS-MARK-READ ERROR:", result.stderr + result.stdout
                )
                self.assertIn(
                    "unreadable", result.stderr + result.stdout
                )
            finally:
                # Restore permissions so TemporaryDirectory cleanup works.
                os.chmod(locked, 0o700)

    def test_readlog_unwritable_fails(self) -> None:
        """Fail-fast mode 4: read-log parent (== passport parent) lacks W_OK.
        Spec §3.6 R5-003: refuse to write when target is unwritable."""
        if os.geteuid() == 0:
            self.skipTest("root bypasses POSIX permissions")
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            passport = root / "passport.json"
            _write_passport(passport, citation_keys=["smith2024"])
            # Read-only parent: can stat the passport but cannot create the
            # sibling read-log file.
            os.chmod(root, 0o500)
            try:
                result = run_script(
                    SCRIPT, "smith2024", "--passport-path", str(passport)
                )

                self.assertNotEqual(result.returncode, 0)
                self.assertIn(
                    "[ARS-MARK-READ ERROR:", result.stderr + result.stdout
                )
                self.assertIn("unwritable", result.stderr + result.stdout)
            finally:
                os.chmod(root, 0o700)


class TestMarkReadCitationKeyValidation(unittest.TestCase):
    def test_invalid_citation_key_hard_errors(self) -> None:
        """Spec §3.6 firm rule 2: invalid <citation_key> is a hard error,
        not a silent miss. Canonical message includes the slug."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            passport = root / "passport.json"
            _write_passport(passport, citation_keys=["smith2024"])

            result = run_script(
                SCRIPT, "bogus_key", "--passport-path", str(passport)
            )

            self.assertNotEqual(result.returncode, 0)
            combined = result.stderr + result.stdout
            self.assertIn("[ARS-MARK-READ ERROR:", combined)
            self.assertIn("'bogus_key'", combined)
            self.assertIn("not in literature_corpus[]", combined)
            # Spec firm rule 2: refuse to write. No read-log file should be
            # created from an invalid attempt.
            log_path = passport.parent / "passport_human_read_log.yaml"
            self.assertFalse(
                log_path.exists(),
                msg="invalid key must not create the read-log file",
            )

    def test_batch_with_one_invalid_key_rejects_whole_batch(self) -> None:
        """Spec firm rule 2 (refuse to write) applied to batch: if any key
        in the batch is invalid, the whole batch is rejected. No partial
        writes. This preserves the all-or-nothing semantic that audit
        replay relies on."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            passport = root / "passport.json"
            _write_passport(passport, citation_keys=["smith2024"])

            result = run_script(
                SCRIPT,
                "smith2024",
                "bogus_key",
                "--passport-path",
                str(passport),
            )

            self.assertNotEqual(result.returncode, 0)
            self.assertIn(
                "[ARS-MARK-READ ERROR:", result.stderr + result.stdout
            )
            log_path = passport.parent / "passport_human_read_log.yaml"
            self.assertFalse(
                log_path.exists(),
                msg="partial batch write must not occur on any invalid key",
            )


class TestUnmarkRead(unittest.TestCase):
    def test_unmark_writes_rescinded_at(self) -> None:
        """Spec §3.6 firm rule 3 + Step 7: /ars-unmark-read writes
        rescinded_at to the matching entry, never deletes."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            passport = root / "passport.json"
            _write_passport(passport, citation_keys=["smith2024"])
            run_script(SCRIPT, "smith2024", "--passport-path", str(passport))

            result = run_script(
                SCRIPT, "smith2024", "--passport-path", str(passport), "--unmark"
            )

            self.assertEqual(result.returncode, 0, msg=f"stderr: {result.stderr}")
            log_data = _read_log(passport)
            # Original entry preserved (not deleted).
            self.assertEqual(len(log_data["human_read"]), 1)
            entry = log_data["human_read"][0]
            self.assertEqual(entry["citation_key"], "smith2024")
            self.assertIn("marked_at", entry)
            self.assertIn("rescinded_at", entry)

    def test_unmark_unknown_key_hard_errors(self) -> None:
        """/ars-unmark-read for a citation_key that was never marked is
        a hard error. Audit-replay requires the rescind target exist."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            passport = root / "passport.json"
            _write_passport(passport, citation_keys=["smith2024", "jones2023"])
            run_script(SCRIPT, "smith2024", "--passport-path", str(passport))

            result = run_script(
                SCRIPT, "jones2023", "--passport-path", str(passport), "--unmark"
            )

            self.assertNotEqual(result.returncode, 0)
            self.assertIn(
                "[ARS-MARK-READ ERROR:", result.stderr + result.stdout
            )


class TestMarkReadYAMLPassport(unittest.TestCase):
    """Issue #195: real adapter output is YAML, not JSON. Earlier fixtures
    wrote JSON which was a parser-coincidence pass (YAML is a JSON superset).
    These tests pin the real adapter-format expectation with .yaml extension
    + canonical YAML serializer output."""

    def test_yaml_passport_happy_path(self) -> None:
        """A passport written by any adapter (folder_scan / zotero / obsidian)
        is YAML. /ars-mark-read must read it without crashing."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            passport = root / "passport.yaml"
            _write_passport(passport, citation_keys=["smith2024"])

            result = run_script(
                SCRIPT, "smith2024", "--passport-path", str(passport)
            )

            self.assertEqual(result.returncode, 0, msg=f"stderr: {result.stderr}")
            log_data = _read_log(passport)
            self.assertEqual(len(log_data["human_read"]), 1)
            self.assertEqual(
                log_data["human_read"][0]["citation_key"], "smith2024"
            )

    def test_yaml_passport_invalid_citation_key_hard_errors(self) -> None:
        """Citation-key validation works the same against a YAML passport."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            passport = root / "passport.yaml"
            _write_passport(passport, citation_keys=["smith2024"])

            result = run_script(
                SCRIPT, "nobody2099", "--passport-path", str(passport)
            )

            self.assertNotEqual(result.returncode, 0)
            self.assertIn(
                "not in literature_corpus[]", result.stderr + result.stdout
            )


class TestReadLogUnwritableExistingFile(unittest.TestCase):
    """Issue #195 companion P2: parent W_OK check passes but the log file
    itself is unwritable. Must surface canonical fail-fast, not bare
    PermissionError."""

    def test_existing_unwritable_log_file_fails_fast(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            passport = root / "passport.yaml"
            _write_passport(passport, citation_keys=["smith2024"])
            log_path = root / f"{passport.stem}_human_read_log.yaml"
            log_path.write_text("human_read: []\n", encoding="utf-8")
            # Read-only on the existing log file. Parent dir stays writable.
            log_path.chmod(stat.S_IRUSR)
            try:
                result = run_script(
                    SCRIPT, "smith2024", "--passport-path", str(passport)
                )
                self.assertNotEqual(
                    result.returncode, 0, msg="should fail-fast not succeed"
                )
                combined = result.stderr + result.stdout
                self.assertIn("[ARS-MARK-READ ERROR:", combined)
                # Bare Python traceback is the failure mode we are guarding
                # against. Spec §3.6 firm rule 4 wants a canonical surface.
                self.assertNotIn("Traceback (most recent call last)", combined)
            finally:
                log_path.chmod(stat.S_IRUSR | stat.S_IWUSR)


if __name__ == "__main__":
    unittest.main()
