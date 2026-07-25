"""Unit tests for check_prisma_trAIce_freshness.py."""
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from tests.test_helpers import run_script

SCRIPT = Path(__file__).resolve().parent / "check_prisma_trAIce_freshness.py"


def _write_protocol(path: Path, snapshot_date: str) -> None:
    path.write_text(
        f"""---
snapshot_date: "{snapshot_date}"
upstream_source: "https://github.com/cqh4046/PRISMA-trAIce"
---

# Protocol
body
""",
        encoding="utf-8",
    )


class TestFreshnessCheck(unittest.TestCase):
    def test_recent_snapshot_passes(self) -> None:
        with TemporaryDirectory() as tmp:
            p = Path(tmp) / "prisma_trAIce_protocol.md"
            _write_protocol(p, "2026-03-01")
            result = run_script(SCRIPT, str(p))
            self.assertEqual(result.returncode, 0, msg=result.stderr)

    def test_stale_snapshot_warns_but_exits_zero(self) -> None:
        with TemporaryDirectory() as tmp:
            p = Path(tmp) / "prisma_trAIce_protocol.md"
            _write_protocol(p, "2024-01-01")
            result = run_script(SCRIPT, str(p))
            self.assertEqual(result.returncode, 0)
            self.assertIn("stale", (result.stdout + result.stderr).lower())

    def test_missing_snapshot_date_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            p = Path(tmp) / "prisma_trAIce_protocol.md"
            p.write_text("# No frontmatter\n", encoding="utf-8")
            result = run_script(SCRIPT, str(p))
            self.assertEqual(result.returncode, 1)

    def test_malformed_date_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            p = Path(tmp) / "prisma_trAIce_protocol.md"
            _write_protocol(p, "not-a-date")
            result = run_script(SCRIPT, str(p))
            self.assertEqual(result.returncode, 1)

    def test_malformed_yaml_fails_cleanly(self) -> None:
        with TemporaryDirectory() as tmp:
            p = Path(tmp) / "prisma_trAIce_protocol.md"
            p.write_text(
                '---\nsnapshot_date: "2026-03-01\nunclosed_quote: "yes\n---\n# body\n',
                encoding="utf-8",
            )
            result = run_script(SCRIPT, str(p))
            self.assertEqual(result.returncode, 1)
            self.assertIn("ERROR", result.stderr)


if __name__ == "__main__":
    unittest.main()
