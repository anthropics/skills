import sys
import tempfile
from pathlib import Path

# Add scripts directory to sys.path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from package_skill import package_skill  # noqa: E402
from quick_validate import validate_skill  # noqa: E402
from utils import parse_skill_md  # noqa: E402



def test_quick_validate_with_non_ascii_and_bom():
    with tempfile.TemporaryDirectory() as tmpdir:
        skill_dir = Path(tmpdir) / "test-unicode-skill"
        skill_dir.mkdir()
        skill_md = skill_dir / "SKILL.md"

        # UTF-8 with BOM (\ufeff) and non-ASCII characters (ō, CJK, emoji, dashes)
        content = (
            "\ufeff---\n"
            "name: test-unicode-skill\n"
            "description: \"Provjeri dostupnost artikla — Tōkyō 城市指南。\"\n"
            "---\n"
            "\n"
            "# Test Unicode Skill\n"
            "This skill handles café, 日本語, and 🚀 emoji.\n"
        )
        skill_md.write_bytes(content.encode("utf-8"))

        valid, msg = validate_skill(skill_dir)
        assert valid, f"Validation failed: {msg}"

        name, desc, full = parse_skill_md(skill_dir)
        assert name == "test-unicode-skill"
        assert "Tōkyō" in desc


def test_package_skill_with_non_ascii():
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp_path = Path(tmpdir)
        skill_dir = tmp_path / "unicode-package-skill"
        skill_dir.mkdir()
        skill_md = skill_dir / "SKILL.md"

        content = (
            "---\n"
            "name: unicode-package-skill\n"
            "description: \"Package test with non-ASCII: café, Tōkyō, 🚀.\"\n"
            "---\n"
            "\n"
            "Body.\n"
        )
        skill_md.write_text(content, encoding="utf-8")

        out_dir = tmp_path / "dist"
        out_dir.mkdir()
        packaged = package_skill(skill_dir, out_dir)
        assert packaged is not None
        assert packaged.exists()
        assert packaged.suffix == ".skill"
