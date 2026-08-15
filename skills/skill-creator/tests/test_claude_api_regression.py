"""Regression tests for anthropics/skills issue #1487.

The pre-fix claude-api skill shipped a 74,880-char SKILL.md (plus a
946KB folder), and invoking it injected ~156k tokens in one tool call,
exhausting the context window. These tests prove the validator catches
that failure class (oversized SKILL.md) and that the restructured skill
now passes.

Run with:  python -m pytest skills/skill-creator/tests/
"""

import sys
from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent / "scripts"
sys.path.insert(0, str(SCRIPTS_DIR))

from quick_validate import DEFAULT_MAX_TOKENS, validate_skill, validate_skill_detailed  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parent.parent.parent.parent


def _old_style_skill(tmp_path):
    """Reconstruct the pre-fix claude-api failure shape: a monolithic
    SKILL.md far over the spec's token budget, with bundled reference docs."""
    skill_dir = tmp_path / "claude-api"
    skill_dir.mkdir()
    body = "# Building LLM-Powered Applications with Claude\n\n"
    # Inline reference content the way the old skill did — models table,
    # thinking/effort table, provider clients, server tools, pitfalls.
    body += "## Current Models (cached)\n\n| Model | Model ID | Context |\n|---|---|---|\n"
    for i in range(60):
        body += f"| Claude Model {i} | `claude-model-{i}` | 1M |\n"
    body += "\n## Thinking & Effort\n\n" + ("| Model | Thinking | Effort |\n|---|---|---|\n")
    for i in range(40):
        body += f"| Model {i} | adaptive | low/high |\n"
    body += "\n## Provider Clients\n\n"
    for i in range(40):
        body += f"| Lang {i} | `AnthropicLang{i}()` |\n"
    body += "\n## Server Tools\n\n" + ("tool row\n" * 50)
    body += "\n## Common Pitfalls\n\n" + ("- pitfall detail\n" * 60)
    while len(body) < (DEFAULT_MAX_TOKENS * 4):  # ~4x the budget, like 74KB
        body += "- more reference content to inflate the payload\n"
    frontmatter = (
        "---\n"
        "name: claude-api\n"
        "description: Reference for the Claude API. Use whenever the prompt names "
        "Claude, Opus, Sonnet, Haiku, or Anthropic in any form.\n"
        "---\n\n"
    )
    (skill_dir / "SKILL.md").write_text(frontmatter + body, encoding="utf-8")
    # A bundled reference doc, mirroring the 946KB folder.
    (skill_dir / "shared").mkdir()
    (skill_dir / "shared" / "model-migration.md").write_text(
        "x" * 200_000, encoding="utf-8"
    )
    return skill_dir


@pytest.fixture(scope="module")
def repo_claude_api():
    """The real, restructured claude-api skill in this checkout."""
    skill = REPO_ROOT / "skills" / "claude-api"
    if not (skill / "SKILL.md").exists():
        pytest.skip("claude-api skill not found in checkout")
    return skill


def test_old_style_skill_fails_strict(tmp_path):
    skill_dir = _old_style_skill(tmp_path)
    assert not validate_skill(skill_dir, strict=True)[0]


def test_old_style_skill_exceeds_token_budget(tmp_path):
    skill_dir = _old_style_skill(tmp_path)
    result = validate_skill_detailed(skill_dir)
    tokens = result.metrics["skill_md_tokens"]
    assert tokens > DEFAULT_MAX_TOKENS


def test_old_style_skill_exceeds_line_budget(tmp_path):
    skill_dir = _old_style_skill(tmp_path)
    result = validate_skill_detailed(skill_dir)
    assert result.metrics["skill_md_lines"] > 500


def test_restructured_claude_api_passes_strict(repo_claude_api):
    valid, message = validate_skill(repo_claude_api, strict=True)
    assert valid, message


def test_restructured_claude_api_within_token_budget(repo_claude_api):
    result = validate_skill_detailed(repo_claude_api)
    tokens = result.metrics["skill_md_tokens"]
    assert tokens <= DEFAULT_MAX_TOKENS, (
        f"SKILL.md is ~{tokens} tokens; keep the index under {DEFAULT_MAX_TOKENS} "
        "and push detail into references/"
    )


def test_restructured_claude_api_within_line_budget(repo_claude_api):
    result = validate_skill_detailed(repo_claude_api)
    assert result.metrics["skill_md_lines"] <= 500


def test_restructured_claude_api_reference_index_intact(repo_claude_api):
    """Every file the index points at must exist — a broken index is a
    broken skill (the progressive-disclosure contract)."""
    result = validate_skill_detailed(repo_claude_api)
    errors = [f for f in result.findings if f.level == "error"]
    assert not errors, errors
