#!/usr/bin/env python3
"""Lint: every top-level SKILL.md must declare metadata.task_type.

Legal values: open-ended | outcome-gradable.
"""
from __future__ import annotations

import sys

from _skill_lint import run_lint

LEGAL_VALUES = frozenset({"open-ended", "outcome-gradable"})


if __name__ == "__main__":
    sys.exit(
        run_lint(
            field="task_type",
            legal_values=LEGAL_VALUES,
            ok_message="OK: all SKILL.md files declare a valid task_type.",
        )
    )
