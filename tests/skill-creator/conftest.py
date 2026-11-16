"""Pytest setup for the skill-creator scripts.

The scripts import each other as ``scripts.<module>`` relative to the
skill directory, so that directory is put on ``sys.path`` here. Run from the
repository root with ``python3 -m pytest tests/skill-creator``.
"""

import sys
from pathlib import Path

SKILL_DIR = Path(__file__).resolve().parent.parent.parent / "skills" / "skill-creator"

sys.path.insert(0, str(SKILL_DIR))
