"""Tests for scripts/check_corpus_consumer_protocol.py.

Each L1-L9 invariant has at least one positive test (passing case) and
one negative test (failing case). The lint is manifest-driven for L3-L6
and closed-set for L8.
"""
from __future__ import annotations

import json
import subprocess
import sys
import textwrap
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
LINT_SCRIPT = REPO_ROOT / "scripts" / "check_corpus_consumer_protocol.py"


def run_lint(cwd: Path) -> subprocess.CompletedProcess:
    """Run the lint script in `cwd`. Returns CompletedProcess."""
    return subprocess.run(
        [sys.executable, str(LINT_SCRIPT)],
        cwd=str(cwd),
        capture_output=True,
        text=True,
    )


@pytest.fixture
def fixture_repo(tmp_path: Path) -> Path:
    """Build a minimal valid v3.6.5 PR-A repo layout under tmp_path.

    Each test mutates exactly one artifact to trigger a specific lint failure.
    The base layout passes all nine invariants.
    """
    # --- manifest (PR-A: bibliography only)
    (tmp_path / "scripts").mkdir()
    manifest = {
        "supported_consumers": [
            {
                "agent_path": "deep-research/agents/bibliography_agent.md",
                "agent_basename": "bibliography_agent",
                "skill": "deep-research",
                "since_version": "v3.6.5",
                "phase": "Phase 1",
            }
        ]
    }
    (tmp_path / "scripts" / "corpus_consumer_manifest.json").write_text(
        json.dumps(manifest, indent=2)
    )

    # --- reference doc with full bibliography block + stub strategist block
    ref_dir = tmp_path / "academic-pipeline" / "references"
    ref_dir.mkdir(parents=True)
    (ref_dir / "literature_corpus_consumers.md").write_text(
        textwrap.dedent(
            """\
            # Consumer Protocol — `literature_corpus[]` Reading

            ## Consumer: bibliography_agent

            ### Iron Rule 1 — Same criteria
            ### Iron Rule 2 — No silent skip
            ### Iron Rule 3 — No corpus mutation
            ### Iron Rule 4 — Graceful fallback on parse failure

            <!-- BAD -->
            ```
            corpus has 5 entries; agent silently skips one with empty abstract.
            ```

            <!-- GOOD -->
            ```
            agent records the skipped entry in PRE-SCREENED skipped sub-section
            with reason "abstract empty after privacy clearing".
            ```

            ## Consumer: literature_strategist_agent

            **Status:** Stub — implementation in PR-B (v3.6.5)
            <!-- LINT_STUB: skip_cross_check -->

            (full content shipped in PR-B)
            """
        )
    )

    # --- bibliography_agent.md with all required prose markers
    agent_dir = tmp_path / "deep-research" / "agents"
    agent_dir.mkdir(parents=True)
    (agent_dir / "bibliography_agent.md").write_text(
        textwrap.dedent(
            """\
            ---
            name: bibliography_agent
            ---

            See `academic-pipeline/references/literature_corpus_consumers.md`.

            ### Step 0: presence detection
            ### Step 1: pre-screen
            ### Step 2: search-fills-gap
            ### Step 3: merge
            ### Step 4: emit report

            case A: ...
            case B: ...
            case B': ...
            case C: ...

            ### Iron Rule 1 — Same criteria
            ### Iron Rule 2 — No silent skip
            ### Iron Rule 3 — No corpus mutation
            ### Iron Rule 4 — Graceful fallback on parse failure

            ```
            PRE-SCREENED FROM USER CORPUS:
            - Adapter: zotero-bbt-export
              # per F4a, per F4b, per F4c documented inline
            - Snapshot date: 2026-04-26
              # per F4d, per F4e, per F4f documented inline
            - Total entries scanned: 87
            - Pre-screening result:
              - Included: 12 entries
                citation_keys:
                  - chen2024ai
              - Excluded by inclusion / exclusion criteria: 5 entries
                citation_keys:
                  - foo2023bar
              - Skipped (criteria cannot be applied): 2 entries
                citation_keys with reasons:
                  - baz2024: missing required tags
            - Zero-hit note (emit per F3 only when Included: 0):
              corpus stale, RQ shifted, or adapter exported unrelated entries.
            - Note: presence in corpus does not imply inclusion;
              same criteria applied to corpus and external sources.
            ```
            Truncation rule: lists exceeding 50 entries truncate to first 20 + last 5 alphabetically with appendix file.
            """
        )
    )

    # --- handoff_schemas.md keeps the deferred caveat (PR-A state)
    shared_dir = tmp_path / "shared"
    shared_dir.mkdir()
    (shared_dir / "handoff_schemas.md").write_text(
        "Schema 9 ... Consumer-side integration deferred to v3.6.5+ ...\n"
    )

    return tmp_path


def test_l1_passes_when_reference_doc_exists(fixture_repo: Path) -> None:
    result = run_lint(fixture_repo)
    assert result.returncode == 0, result.stdout + result.stderr


def test_l1_fails_when_reference_doc_missing(fixture_repo: Path) -> None:
    (
        fixture_repo
        / "academic-pipeline"
        / "references"
        / "literature_corpus_consumers.md"
    ).unlink()
    result = run_lint(fixture_repo)
    assert result.returncode != 0
    assert "L1" in result.stdout or "L1" in result.stderr


def test_l2_passes_with_both_consumer_blocks_stub_marked(fixture_repo: Path) -> None:
    result = run_lint(fixture_repo)
    assert result.returncode == 0, result.stdout + result.stderr


def test_l2_fails_when_stub_marker_missing(fixture_repo: Path) -> None:
    ref = (
        fixture_repo
        / "academic-pipeline"
        / "references"
        / "literature_corpus_consumers.md"
    )
    text = ref.read_text().replace("<!-- LINT_STUB: skip_cross_check -->", "")
    ref.write_text(text)
    result = run_lint(fixture_repo)
    assert result.returncode != 0
    assert "L2" in result.stdout or "L2" in result.stderr


# --- L3: backpointer ---


def test_l3_passes_when_backpointer_present(fixture_repo: Path) -> None:
    result = run_lint(fixture_repo)
    assert result.returncode == 0, result.stdout + result.stderr


def test_l3_fails_when_backpointer_missing(fixture_repo: Path) -> None:
    agent = fixture_repo / "deep-research" / "agents" / "bibliography_agent.md"
    text = agent.read_text().replace(
        "academic-pipeline/references/literature_corpus_consumers.md", ""
    )
    agent.write_text(text)
    result = run_lint(fixture_repo)
    assert result.returncode != 0
    assert "L3" in result.stdout or "L3" in result.stderr


# --- L4: PRE-SCREENED template start ---


def test_l4_passes_when_pre_screened_template_present(fixture_repo: Path) -> None:
    result = run_lint(fixture_repo)
    assert result.returncode == 0, result.stdout + result.stderr


def test_l4_fails_when_pre_screened_template_missing(fixture_repo: Path) -> None:
    agent = fixture_repo / "deep-research" / "agents" / "bibliography_agent.md"
    text = agent.read_text().replace("PRE-SCREENED FROM USER CORPUS:", "")
    agent.write_text(text)
    result = run_lint(fixture_repo)
    assert result.returncode != 0
    assert "L4" in result.stdout or "L4" in result.stderr


# --- L5: four Iron Rule titles ---


def test_l5_passes_with_all_four_iron_rule_titles(fixture_repo: Path) -> None:
    result = run_lint(fixture_repo)
    assert result.returncode == 0, result.stdout + result.stderr


def test_l5_fails_when_iron_rule_title_missing(fixture_repo: Path) -> None:
    agent = fixture_repo / "deep-research" / "agents" / "bibliography_agent.md"
    text = agent.read_text().replace(
        "Iron Rule 4 — Graceful fallback on parse failure", "Iron Rule 4 — TBD"
    )
    agent.write_text(text)
    result = run_lint(fixture_repo)
    assert result.returncode != 0
    assert "L5" in result.stdout or "L5" in result.stderr


# --- L6: Step headings + Step 2 case markers ---


def test_l6_passes_with_all_steps_and_cases(fixture_repo: Path) -> None:
    result = run_lint(fixture_repo)
    assert result.returncode == 0, result.stdout + result.stderr


def test_l6_fails_when_case_marker_missing(fixture_repo: Path) -> None:
    agent = fixture_repo / "deep-research" / "agents" / "bibliography_agent.md"
    text = agent.read_text().replace("case B': ...", "")
    agent.write_text(text)
    result = run_lint(fixture_repo)
    assert result.returncode != 0
    assert "L6" in result.stdout or "L6" in result.stderr


def test_l6_distinguishes_case_b_from_case_b_prime(fixture_repo: Path) -> None:
    """Drop the standalone `case B:` line but keep `case B':`.

    Substring matching would let `case B'` cover for the missing
    `case B`, falsely passing L6. The boundary regex must catch this.
    """
    agent = fixture_repo / "deep-research" / "agents" / "bibliography_agent.md"
    text = agent.read_text().replace("case B: ...\n", "")
    agent.write_text(text)
    result = run_lint(fixture_repo)
    assert result.returncode != 0
    combined = result.stdout + result.stderr
    assert "L6" in combined
    # Failure message must point at the missing "case B" (not "case B'"),
    # which still exists in the fixture text.
    assert "'case B'" in combined


# --- L7: PRE-SCREENED template line markers ---


def test_l7_passes_with_all_nine_line_markers(fixture_repo: Path) -> None:
    result = run_lint(fixture_repo)
    assert result.returncode == 0, result.stdout + result.stderr


def test_l7_fails_when_skipped_marker_missing(fixture_repo: Path) -> None:
    agent = fixture_repo / "deep-research" / "agents" / "bibliography_agent.md"
    text = agent.read_text().replace(
        "Skipped (criteria cannot be applied):", "Removed:"
    )
    agent.write_text(text)
    result = run_lint(fixture_repo)
    assert result.returncode != 0
    assert "L7" in result.stdout or "L7" in result.stderr


def test_l7_fails_when_citation_keys_marker_missing(fixture_repo: Path) -> None:
    """Spec §5.2 L7: PRE-SCREENED template must contain citation_keys marker.

    If the agent drops the citation_keys lines while keeping the counts,
    the reproducibility surface no longer says which corpus entries
    were screened. L7 catches this.
    """
    agent = fixture_repo / "deep-research" / "agents" / "bibliography_agent.md"
    text = agent.read_text()
    # Drop both citation_keys variants from inside the fenced template.
    # Keep the trailing truncation-rule prose mention.
    new_text = text.replace(
        "    citation_keys:\n      - chen2024ai\n", "", 1
    )
    new_text = new_text.replace(
        "    citation_keys:\n      - foo2023bar\n", "", 1
    )
    new_text = new_text.replace(
        "    citation_keys with reasons:\n      - baz2024: missing required tags\n",
        "",
        1,
    )
    assert new_text != text
    agent.write_text(new_text)
    result = run_lint(fixture_repo)
    assert result.returncode != 0
    combined = result.stdout + result.stderr
    assert "L7" in combined
    assert "citation_keys" in combined


def test_l7_fails_when_f4_inline_anchors_missing(fixture_repo: Path) -> None:
    """Cross-model codex round-3 caught: L7 only checked coarse line
    prefixes (Adapter:, Snapshot date:), so silently dropping the F4a-c
    / F4d-f inline-comment guidance from the canonical template would
    not fail CI.

    Regression: drop the F4 inline anchors from the template body and
    assert L7 fails.
    """
    agent = fixture_repo / "deep-research" / "agents" / "bibliography_agent.md"
    text = agent.read_text()
    new_text = text.replace("# per F4a, per F4b, per F4c documented inline\n", "", 1)
    new_text = new_text.replace("# per F4d, per F4e, per F4f documented inline\n", "", 1)
    assert new_text != text
    agent.write_text(new_text)
    result = run_lint(fixture_repo)
    assert result.returncode != 0
    combined = result.stdout + result.stderr
    assert "L7" in combined
    assert "F4" in combined or "per F4" in combined


def test_l7_fails_when_zero_hit_anchor_missing(fixture_repo: Path) -> None:
    """L7 must require the F3 zero-hit conditional template line.
    Without it, a future PR could drop the zero-hit reproducibility
    surface from the template and CI would still pass.
    """
    agent = fixture_repo / "deep-research" / "agents" / "bibliography_agent.md"
    text = agent.read_text()
    new_text = text.replace(
        "- Zero-hit note (emit per F3 only when Included: 0):", "- Removed:"
    )
    assert new_text != text
    agent.write_text(new_text)
    result = run_lint(fixture_repo)
    assert result.returncode != 0
    combined = result.stdout + result.stderr
    assert "L7" in combined
    assert "Zero-hit" in combined or "F3" in combined


def test_l7_marker_check_is_scoped_to_fenced_template(fixture_repo: Path) -> None:
    """Marker checks must run against the PRE-SCREENED block body only.

    Codex review round-3 caught: an agent file that mentions a marker
    string in surrounding prose (e.g., \"citation_keys\" inside the
    truncation rule sentence) would mask a deletion of the marker line
    inside the actual template, causing L7 to falsely pass.

    Regression: drop the citation_keys lines from the template body but
    keep them mentioned in the surrounding prose; the lint must still
    fail L7.
    """
    agent = fixture_repo / "deep-research" / "agents" / "bibliography_agent.md"
    text = agent.read_text()
    # Drop citation_keys lines from inside the fenced template.
    new_text = text.replace(
        "    citation_keys:\n      - chen2024ai\n", "", 1
    )
    new_text = new_text.replace(
        "    citation_keys:\n      - foo2023bar\n", "", 1
    )
    new_text = new_text.replace(
        "    citation_keys with reasons:\n      - baz2024: missing required tags\n",
        "",
        1,
    )
    # Append a sentence outside the fenced block that mentions the marker —
    # this is what would have falsely satisfied a full-file substring check.
    new_text = new_text + "\nNote: each citation_keys list participates in the truncation rule.\n"
    agent.write_text(new_text)
    result = run_lint(fixture_repo)
    assert result.returncode != 0
    combined = result.stdout + result.stderr
    assert "L7" in combined
    assert "citation_keys" in combined


def test_l7_fails_when_truncation_prose_missing(fixture_repo: Path) -> None:
    """Spec §5.2 L7: PRE-SCREENED template must include 'truncation rule' prose."""
    agent = fixture_repo / "deep-research" / "agents" / "bibliography_agent.md"
    text = agent.read_text()
    # Remove the truncation prose. Use a lowercase replace to catch both casings.
    new_text = text.replace("Truncation rule:", "Removed:")
    assert new_text != text, "fixture must contain 'Truncation rule:' line for this test"
    agent.write_text(new_text)
    result = run_lint(fixture_repo)
    assert result.returncode != 0
    assert "L7" in result.stdout or "L7" in result.stderr


# --- L8: caveat state vs manifest closed-set match ---


def test_l8_passes_pr_a_with_caveat_remaining(fixture_repo: Path) -> None:
    """PR-A state: manifest = {bibliography_agent}, caveat MUST remain."""
    result = run_lint(fixture_repo)
    assert result.returncode == 0, result.stdout + result.stderr


def test_l8_fails_pr_a_when_caveat_retired_prematurely(fixture_repo: Path) -> None:
    """PR-A must NOT retire the deferred caveat."""
    schemas = fixture_repo / "shared" / "handoff_schemas.md"
    text = schemas.read_text().replace("Consumer-side integration deferred to v3.6.5+", "")
    schemas.write_text(text)
    result = run_lint(fixture_repo)
    assert result.returncode != 0
    assert "L8" in result.stdout or "L8" in result.stderr


def test_l8_passes_pr_b_with_caveat_retired_and_backpointer(fixture_repo: Path) -> None:
    """PR-B state: manifest = both consumers, caveat retired, backpointer present."""
    # Promote manifest to PR-B
    manifest = json.loads(
        (fixture_repo / "scripts" / "corpus_consumer_manifest.json").read_text()
    )
    manifest["supported_consumers"].append(
        {
            "agent_path": "academic-paper/agents/literature_strategist_agent.md",
            "agent_basename": "literature_strategist_agent",
            "skill": "academic-paper",
            "since_version": "v3.6.5",
            "phase": "Phase 1",
        }
    )
    (fixture_repo / "scripts" / "corpus_consumer_manifest.json").write_text(
        json.dumps(manifest, indent=2)
    )

    # Promote stub block to full content (remove LINT_STUB marker + Status line)
    ref = fixture_repo / "academic-pipeline" / "references" / "literature_corpus_consumers.md"
    text = ref.read_text()
    text = text.replace("<!-- LINT_STUB: skip_cross_check -->", "")
    text = text.replace(
        "**Status:** Stub — implementation in PR-B (v3.6.5)",
        "**Status:** Shipped (v3.6.5)",
    )
    ref.write_text(text)

    # Create the second consumer agent file by cloning bibliography_agent.md content
    strat_dir = fixture_repo / "academic-paper" / "agents"
    strat_dir.mkdir(parents=True)
    biblio_text = (
        fixture_repo / "deep-research" / "agents" / "bibliography_agent.md"
    ).read_text()
    (strat_dir / "literature_strategist_agent.md").write_text(
        biblio_text.replace(
            "name: bibliography_agent", "name: literature_strategist_agent"
        )
    )

    # Retire the caveat in handoff_schemas + add backpointer
    schemas = fixture_repo / "shared" / "handoff_schemas.md"
    text2 = schemas.read_text()
    text2 = text2.replace(
        "Consumer-side integration deferred to v3.6.5+",
        "See `academic-pipeline/references/literature_corpus_consumers.md`",
    )
    schemas.write_text(text2)

    result = run_lint(fixture_repo)
    assert result.returncode == 0, result.stdout + result.stderr


def test_l8_fails_invalid_third_state_strategist_only(fixture_repo: Path) -> None:
    """Manifest with only literature_strategist_agent must fail L8."""
    manifest = {
        "supported_consumers": [
            {
                "agent_path": "academic-paper/agents/literature_strategist_agent.md",
                "agent_basename": "literature_strategist_agent",
                "skill": "academic-paper",
                "since_version": "v3.6.5",
                "phase": "Phase 1",
            }
        ]
    }
    (fixture_repo / "scripts" / "corpus_consumer_manifest.json").write_text(
        json.dumps(manifest, indent=2)
    )
    result = run_lint(fixture_repo)
    assert result.returncode != 0
    assert "L8" in result.stdout or "L8" in result.stderr


def test_l8_fails_duplicate_basename_with_different_path(fixture_repo: Path) -> None:
    """Cross-model codex review caught: L8 used to compare frozenset of
    basenames only. A future manifest could stash a second bibliography_agent
    entry pointing at a different agent_path; frozenset would collapse the
    duplicate and L8 would falsely treat it as PR-A.

    Regression: insert a duplicate basename with a different path and assert
    L8 fails with a duplicate-basename message.
    """
    manifest = json.loads(
        (fixture_repo / "scripts" / "corpus_consumer_manifest.json").read_text()
    )
    manifest["supported_consumers"].append(
        {
            "agent_path": "fake/agents/shadow_bibliography_agent.md",
            "agent_basename": "bibliography_agent",
            "skill": "academic-paper",
            "since_version": "v3.6.5",
            "phase": "Phase 1",
        }
    )
    (fixture_repo / "scripts" / "corpus_consumer_manifest.json").write_text(
        json.dumps(manifest, indent=2)
    )
    result = run_lint(fixture_repo)
    assert result.returncode != 0
    combined = result.stdout + result.stderr
    assert "L8" in combined
    assert "duplicate" in combined.lower()


def test_l8_fails_when_path_diverges_from_canonical(fixture_repo: Path) -> None:
    """L8 must compare the full (basename, path) tuple, not just basename.

    A manifest with the right basename but a moved/renamed agent_path
    is no longer the canonical PR-A state. Lint must catch this even
    when basenames alone would still match PR_A_SET.
    """
    manifest = {
        "supported_consumers": [
            {
                "agent_path": "deep-research/agents/MOVED_bibliography_agent.md",
                "agent_basename": "bibliography_agent",
                "skill": "deep-research",
                "since_version": "v3.6.5",
                "phase": "Phase 1",
            }
        ]
    }
    (fixture_repo / "scripts" / "corpus_consumer_manifest.json").write_text(
        json.dumps(manifest, indent=2)
    )
    result = run_lint(fixture_repo)
    assert result.returncode != 0
    combined = result.stdout + result.stderr
    assert "L8" in combined
    # Either a "does not match a known release state" message OR a
    # related path-driven failure is acceptable; the contract is just
    # "lint must fail" for non-canonical paths.


def test_l8_fails_invalid_third_state_extra_unknown(fixture_repo: Path) -> None:
    """Manifest with an unknown extra consumer must fail L8."""
    manifest = json.loads(
        (fixture_repo / "scripts" / "corpus_consumer_manifest.json").read_text()
    )
    manifest["supported_consumers"].append(
        {
            "agent_path": "fake/agents/citation_compliance_agent.md",
            "agent_basename": "citation_compliance_agent",
            "skill": "academic-paper",
            "since_version": "v3.6.5",
            "phase": "Phase 5a",
        }
    )
    (fixture_repo / "scripts" / "corpus_consumer_manifest.json").write_text(
        json.dumps(manifest, indent=2)
    )
    result = run_lint(fixture_repo)
    assert result.returncode != 0
    assert "L8" in result.stdout or "L8" in result.stderr


# --- L9: BAD/GOOD example pair ---


def test_l9_passes_when_bad_good_pair_present(fixture_repo: Path) -> None:
    result = run_lint(fixture_repo)
    assert result.returncode == 0, result.stdout + result.stderr


def test_l9_fails_when_good_marker_missing(fixture_repo: Path) -> None:
    ref = fixture_repo / "academic-pipeline" / "references" / "literature_corpus_consumers.md"
    text = ref.read_text().replace("<!-- GOOD -->", "")
    ref.write_text(text)
    result = run_lint(fixture_repo)
    assert result.returncode != 0
    assert "L9" in result.stdout or "L9" in result.stderr


# --- Integration: lint runs against the real repo state ---


def test_integration_lint_passes_against_real_repo() -> None:
    """Guard against real-repo drift: lint must pass against REPO_ROOT.

    Wired into CI by spec-consistency.yml. Any future commit that
    breaks an L1-L9 invariant against the live repo state fails here
    AND in CI's `Validate corpus consumer protocol` step.
    """
    result = run_lint(REPO_ROOT)
    assert result.returncode == 0, (
        f"Lint failed against real repo:\n"
        f"STDOUT:\n{result.stdout}\n"
        f"STDERR:\n{result.stderr}"
    )
