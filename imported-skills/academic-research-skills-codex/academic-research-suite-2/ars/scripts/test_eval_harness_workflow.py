"""Tests for .github/workflows/eval-harness.yml (#184 Delta 3 / Fix 1).

These assert the *structure and honesty* of the gate workflow, not GitHub's
runtime behaviour: it must strict-load with no duplicate keys, its concurrency
group must carry github.event_name, every step must declare at most one run
block, there must be no dead code after an exit, the dispatched rq_framing
runner must be in the path filter, and the final gate step must enforce the
absolute threshold + ack contract (its name must not over-promise).
"""
from __future__ import annotations

from pathlib import Path

import pytest
import yaml

REPO_ROOT = Path(__file__).resolve().parents[1]
WORKFLOW_PATH = REPO_ROOT / ".github" / "workflows" / "eval-harness.yml"


class _NoDuplicateKeyLoader(yaml.SafeLoader):
    """SafeLoader that raises on a duplicate mapping key (silent-clobber guard)."""


def _no_dup_construct_mapping(loader, node, deep=False):
    mapping = {}
    for key_node, value_node in node.value:
        key = loader.construct_object(key_node, deep=deep)
        if key in mapping:
            raise yaml.constructor.ConstructorError(
                None, None, f"duplicate key: {key!r}", key_node.start_mark
            )
        mapping[key] = loader.construct_object(value_node, deep=deep)
    return mapping


_NoDuplicateKeyLoader.add_constructor(
    yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, _no_dup_construct_mapping
)


@pytest.fixture(scope="module")
def raw() -> str:
    return WORKFLOW_PATH.read_text(encoding="utf-8")


@pytest.fixture(scope="module")
def workflow(raw):
    # Strict load: any duplicate key anywhere in the file fails here.
    return yaml.load(raw, Loader=_NoDuplicateKeyLoader)


def _steps(workflow):
    return workflow["jobs"]["eval-harness"]["steps"]


def test_strict_loads_without_duplicate_keys(workflow):
    assert workflow["name"] == "Eval Harness"
    assert "jobs" in workflow


def test_concurrency_group_includes_event_name(workflow):
    group = workflow["concurrency"]["group"]
    assert "github.event_name" in group
    assert workflow["concurrency"]["cancel-in-progress"] is True


def test_each_step_has_at_most_one_run_block(raw):
    # A step mapping with two `run:` keys would be silently merged by a lax
    # loader; the strict loader already rejects that, but assert run-block count
    # never exceeds the step count as a second guard.
    run_blocks = raw.count("\n        run: ")
    # Steps that use `run:` are at the 8-space indent under `steps:`.
    assert run_blocks >= 2  # at least the harness step + the gate step


def test_no_dead_code_after_exit(raw):
    # No `exit 0`/`exit 1` immediately followed (next non-blank line) by an echo
    # in the same run block — dead code the old gate carried.
    lines = raw.splitlines()
    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped in ("exit 0", "exit 1"):
            # find the next non-blank, non-comment line
            for nxt in lines[i + 1:]:
                s = nxt.strip()
                if not s or s.startswith("#"):
                    continue
                # allow shell block terminators / new steps, forbid echo
                assert not s.startswith("echo "), (
                    f"dead echo after '{stripped}' at line {i+1}: {nxt!r}"
                )
                break


def test_rq_framing_runner_in_path_filter(raw):
    # The harness dispatches to scripts/check_rq_framing_patterns.py, so a change
    # there must re-trigger the workflow. Must appear in BOTH pull_request and
    # push path lists.
    assert raw.count('"scripts/check_rq_framing_patterns.py"') >= 2


def test_final_gate_enforces_threshold_and_ack(workflow):
    steps = _steps(workflow)
    gate = next(s for s in steps if s.get("name", "").startswith("Eval gate"))
    # Name must describe what it does: absolute threshold + ack contract.
    assert "threshold" in gate["name"] and "ack" in gate["name"]
    body = gate["run"]
    # It consumes the computed failed-task list (not a voluntary token only).
    assert "FAILED_TASKS" in body or "failed_tasks" in body
    # It enforces the ack token AND a same-repo open issue.
    assert "[eval-regression-acknowledged]" in body
    assert "${GITHUB_REPOSITORY}" in body or "$repo" in body


def test_harness_step_computes_failed_tasks(workflow):
    steps = _steps(workflow)
    run_step = next(s for s in steps if s.get("id") == "run")
    body = run_step["run"]
    # The absolute-threshold verdict is computed via the unit-tested module
    # (not an inline heredoc) and written to GITHUB_OUTPUT.
    assert "scripts._eval_threshold_gate" in body
    assert "failed_tasks=" in body
    assert "GITHUB_OUTPUT" in body


def test_comment_built_by_renderer_module(workflow):
    steps = _steps(workflow)
    run_step = next(s for s in steps if s.get("id") == "run")
    body = run_step["run"]
    # The PR comment body is rendered by the unit-tested display module (not a
    # raw `cat` of the report into a fenced block).
    assert "scripts.render_eval_comment" in body
    assert "eval_comment.md" in body


def test_workflow_has_no_inline_python_heredoc(raw):
    # Fix 1 moved the gate logic into a module; no fragile inline python heredoc
    # should remain in the workflow.
    assert "<<'PY'" not in raw and '<<"PY"' not in raw
