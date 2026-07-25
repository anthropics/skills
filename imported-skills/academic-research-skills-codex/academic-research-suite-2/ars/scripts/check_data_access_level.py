#!/usr/bin/env python3
"""Lint: every top-level SKILL.md must declare metadata.data_access_level.

Legal values: raw | redacted | verified_only.
"""
from __future__ import annotations

import sys

from _skill_lint import run_lint

LEGAL_VALUES = frozenset({"raw", "redacted", "verified_only"})


if __name__ == "__main__":
    sys.exit(
        run_lint(
            field="data_access_level",
            legal_values=LEGAL_VALUES,
            ok_message="OK: all SKILL.md files declare a valid data_access_level.",
        )
    )
