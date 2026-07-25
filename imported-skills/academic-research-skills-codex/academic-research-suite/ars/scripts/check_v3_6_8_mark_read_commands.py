"""CI lint for the /ars-mark-read + /ars-unmark-read plugin commands.

Per v3.6.8 spec §3.6 + Step 7 (round-2 R2-002 amend) acceptance criteria:
the 2 commands must exist, carry the validation rule (citation_key against
`literature_corpus[]`), reference the peer-file write target
(`<passport-stem>_human_read_log.yaml`) NOT entry frontmatter, and declare
`model: sonnet` routing (per feedback_no_haiku.md discipline).

Run from repo root:
    python3 scripts/check_v3_6_8_mark_read_commands.py
"""
from __future__ import annotations

import sys
from pathlib import Path


REQUIRED_COMMANDS = ("ars-mark-read.md", "ars-unmark-read.md")

# Tokens each command body MUST carry to preserve the user-visible contract.
# Drift on any of these silently weakens the gate.
REQUIRED_TOKENS = (
    "literature_corpus",  # validation rule reference
    "human_read_log",     # peer-file write target
    "model: sonnet",      # routing per feedback_no_haiku.md
)

# Enforce canonical CLI dispatch pattern (PR #197 local convention):
# Prose instructions are fragile; using a literal bash block with $ARGUMENTS
# ensures deterministic argument parsing and shell-safe token handling.
# This is a repo-local policy introduced by #197, not a §3.6 Step 7 spec rule.
REQUIRED_BLOCK = "Implementation:\n```bash\npython3 scripts/ars_mark_read.py $ARGUMENTS"


def main(argv: list[str] | None = None) -> int:
    repo_root = Path.cwd()
    cmds_dir = repo_root / "commands"
    errors: list[str] = []

    for cmd_name in REQUIRED_COMMANDS:
        path = cmds_dir / cmd_name
        if not path.exists():
            errors.append(
                f"commands/{cmd_name}: missing (spec §3.6 Step 7 acceptance: "
                f"2 commands MUST exist)"
            )
            continue
            
        body = path.read_text(encoding="utf-8")
        
        # 1. Check for required tokens
        for token in REQUIRED_TOKENS:
            if token not in body:
                errors.append(
                    f"commands/{cmd_name}: missing required token "
                    f"{token!r} (spec §3.6 Step 7 contract)"
                )
        
        # 2. Check for canonical implementation block (Moved outside token loop)
        if REQUIRED_BLOCK not in body:
            errors.append(
                f"commands/{cmd_name}: missing compliant 'Implementation: ```bash' block "
                f"(PR #197 local convention: must use canonical bash block with $ARGUMENTS for deterministic argument parsing)"
            )

    if errors:
        for e in errors:
            print(e, file=sys.stderr)
        return 1

    print(
        f"[v3.6.8 mark-read commands lint] PASSED "
        f"({len(REQUIRED_COMMANDS)} command(s) scanned)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
