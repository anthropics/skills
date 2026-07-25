#!/usr/bin/env python3
"""#390 Slice B revision-mode patch-adoption lint (#424).

Block-scoped string checks per repo convention (check_394 pattern) on the
prompt surfaces that carry the patch protocol, plus schema example
validation. Spec: docs/design/2026-06-10-390-diff-patch-revision-mode-
spec.md (§0 Slice B amendment + §3.2-§3.6 + §8.5).

Invariants:
  1. draft_writer_agent.md carries the patch-output discipline block:
     patch-not-full-draft, sidecar emission path, copy-hashes-never-compute,
     the pre-drafting escalation tag, the <!--block: prohibition, the
     retry-once rule, and the provisional-response role boundary.
  2. pipeline_orchestrator_agent.md carries the sequencing block with the
     five steps IN ORDER (anchorize → dispatch → apply → finalizer →
     Schema 8 completion), the no-rewrite window, both escalation trigger
     layers, the MANDATORY checkpoint, full_reemission_escalated
     provenance, never-auto-fallback, and the 0.6 threshold.
  3. academic-paper/SKILL.md: mode-table revision row says patch document;
     the Revision Mode Patch Protocol section exists with the honest
     boundary sentence and the protocol-doc pointer.
  4. Schema 8 (shared/handoff_schemas.md): ResponseItem carries
     change_block_ids, populated by the orchestrator, never by the writer.
  5. revision_patch_protocol.md ships the exact Mode B commands
     (anchorize / apply / --acknowledge-structural), exit codes, the
     apply-report-as-re-review-input rule, and the marker lifecycle.
  6. Marker rules exist at both consumers: formatter_agent.md ARS Marker
     Stripping (all three kinds, after-gates ordering, working drafts
     keep markers) and word_count_conventions.md strip-before-count.
  7. Threshold value lock: DEFAULT_TOUCHED_RATIO_THRESHOLD == 0.6 in
     ars_apply_revision_patch.py, the argparse --touched-ratio-threshold
     default IS that constant (AST, so a regression to None/literal is
     caught even when the constant still reads 0.6), and the spec §0
     amendment records the same decisions the prose cites.
  8. The spec §3.2 example patch validates against
     revision_patch.schema.json (schema example validation, §8.5).
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

import jsonschema

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(REPO_ROOT / "scripts"))

from _skill_lint import check_section_literals, h2_section_body
from ars_apply_revision_patch import DEFAULT_TOUCHED_RATIO_THRESHOLD

WRITER = REPO_ROOT / "academic-paper/agents/draft_writer_agent.md"
ORCHESTRATOR = REPO_ROOT / "academic-pipeline/agents/pipeline_orchestrator_agent.md"
PAPER_SKILL = (
    REPO_ROOT / "academic-paper/WORKFLOW.md"
    if (REPO_ROOT / "academic-paper/WORKFLOW.md").is_file()
    else REPO_ROOT / "academic-paper/SKILL.md"
)
SCHEMAS = REPO_ROOT / "shared/handoff_schemas.md"
PROTOCOL = REPO_ROOT / "academic-paper/references/revision_patch_protocol.md"
FORMATTER = REPO_ROOT / "academic-paper/agents/formatter_agent.md"
WORD_COUNT = REPO_ROOT / "shared/references/word_count_conventions.md"
SPEC = REPO_ROOT / "docs/design/2026-06-10-390-diff-patch-revision-mode-spec.md"
PATCH_SCHEMA = REPO_ROOT / "shared/contracts/patch/revision_patch.schema.json"
APPLY_SCRIPT = REPO_ROOT / "scripts/ars_apply_revision_patch.py"

WRITER_HEADING = "## Patch-Document Revision Emission (#390)"
ORCH_HEADING = "## Revision-Round Patch Sequencing (#390)"
SKILL_HEADING = "## Revision Mode Patch Protocol (#390)"
FMT_HEADING = "## ARS Marker Stripping (#390)"
AMENDMENT_HEADING = "## §0 Slice B amendment (2026-06-11, #424)"
ESCALATION_TAG = "[PATCH-ESCALATION-REQUIRED:"


def check_writer(text: str) -> list[str]:
    """Invariant 1."""
    return check_section_literals(1, text, WRITER_HEADING, "writer", {
        "patch-not-full-draft": "NOT a re-emitted complete paper",
        "schema path": "shared/contracts/patch/revision_patch.schema.json",
        "sidecar emission path": "phase6_*/revision_patch_round<N>.json",
        "hash copy discipline": "Copy hashes, never compute them.",
        "escalation tag": ESCALATION_TAG + " layer=pre_drafting",
        "block-marker prohibition": "MUST NOT contain `<!--block:` markers",
        "retry-once": "Do not patch the patch",
        "role boundary": "emit **provisional** Schema 8 response items",
    })


def check_orchestrator(text: str) -> list[str]:
    """Invariant 2."""
    fails = check_section_literals(2, text, ORCH_HEADING, "orchestrator", {
        "no-rewrite window": "nothing may rewrite the draft between steps 1 and 3",
        "layer-1 trigger": ESCALATION_TAG,
        "layer-2 trigger": "refused_structural",
        "checkpoint": "MANDATORY CHECKPOINT",
        "escalated provenance": "mode: full_reemission_escalated",
        "no auto-fallback": "NEVER auto-fallback to full re-emission",
        "retry-once": "ONE patch re-emission",
        "Schema 8 completion": "change_block_ids",
        "budget surface": "preserved_ratio",
        "threshold value": "0.6",
        "re-anchorize generation": "new ID generation",
    })
    section = h2_section_body(text, ORCH_HEADING)
    if section is not None:
        steps = [
            "**Anchorize (manifest refresh):**",
            "**Dispatch the writer**",
            "**Apply:**",
            "**Finalizer pass:**",
            "**Complete Schema 8 mechanical fields**",
        ]
        positions = [section.find(s) for s in steps]
        if -1 in positions:
            fails.append(
                "invariant 2: orchestrator sequencing lost step "
                f"{steps[positions.index(-1)]!r}")
        elif positions != sorted(positions):
            fails.append(
                "invariant 2: orchestrator sequencing steps are out of the "
                "normative order (anchorize → dispatch → apply → finalizer "
                "→ Schema 8 completion)")
    return fails


def check_paper_skill(text: str) -> list[str]:
    """Invariant 3."""
    fails = check_section_literals(3, text, SKILL_HEADING, "SKILL.md", {
        "protocol doc pointer": "references/revision_patch_protocol.md",
        "escalated provenance": "full_reemission_escalated",
        "honest boundary": "does not make the revision itself better",
        "item 9 boundary": "Item 9 boundary",
    })
    row = next(
        (line for line in text.splitlines()
         if line.lstrip().startswith("| `revision` |")), None)
    if row is None:
        fails.append("invariant 3: mode table lost the `revision` row")
    elif "Patch document" not in row:
        fails.append(
            "invariant 3: mode-table revision row no longer names the "
            "patch document deliverable")
    return fails


def check_schema8(text: str) -> list[str]:
    """Invariant 4."""
    return check_section_literals(
        4, text, "## Schema 8: Response to Reviewers", "Schema 8", {
            "field row": "`change_block_ids`",
            "producer split": "never by the writer",
            "consumer cross-check": "apply report",
        })


def check_protocol_doc(text: str | None) -> list[str]:
    """Invariant 5."""
    if text is None:
        return [f"invariant 5: protocol doc missing ({PROTOCOL})"]
    literals = {
        "anchorize command": "python scripts/ars_anchorize_draft.py",
        "apply command": "python scripts/ars_apply_revision_patch.py",
        "acknowledge flag": "--acknowledge-structural",
        "new-artifact rule": "MUST be a new file",
        "exit codes": "`2` Phase 1 rejection",
        "re-review input": "required input to re-review",
        "threshold value": "0.6",
        "marker lifecycle": "## Marker lifecycle",
        "honest claim": "cannot be silently distorted",
    }
    return [
        f"invariant 5: protocol doc lost the {name} literal ({lit!r})"
        for name, lit in literals.items() if lit not in text
    ]


def check_marker_rules(formatter_text: str, word_count_text: str) -> list[str]:
    """Invariant 6."""
    fails = check_section_literals(
        6, formatter_text, FMT_HEADING, "formatter", {
            "block marker": "<!--block:",
            "ref marker": "<!--ref:",
            "anchor marker": "<!--anchor:",
            "ordering": "ONLY AFTER every marker-dependent gate",
            "working-draft preservation": "keep their markers untouched",
        })
    if "### HTML-comment markers" not in word_count_text:
        fails.append(
            "invariant 6: word_count_conventions lost the HTML-comment "
            "markers section")
    if "Strip every `<!--...-->` comment before computing" not in word_count_text:
        fails.append(
            "invariant 6: word_count_conventions lost the strip-before-"
            "count rule")
    return fails


def _cli_default_is_the_constant(apply_src: str) -> bool:
    """True iff the apply script's --touched-ratio-threshold argparse arg
    has `default=DEFAULT_TOUCHED_RATIO_THRESHOLD`. AST, not string match,
    so a regression to `default=None` or a re-hardcoded literal is caught
    even though the constant itself still equals 0.6."""
    import ast
    tree = ast.parse(apply_src)
    for node in ast.walk(tree):
        if not (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr == "add_argument"):
            continue
        if not (node.args and isinstance(node.args[0], ast.Constant)
                and node.args[0].value == "--touched-ratio-threshold"):
            continue
        for kw in node.keywords:
            if kw.arg == "default":
                return (isinstance(kw.value, ast.Name)
                        and kw.value.id == "DEFAULT_TOUCHED_RATIO_THRESHOLD")
    return False


def check_threshold_lock(spec_text: str, apply_src: str) -> list[str]:
    """Invariant 7."""
    fails: list[str] = []
    if DEFAULT_TOUCHED_RATIO_THRESHOLD != 0.6:
        fails.append(
            "invariant 7: DEFAULT_TOUCHED_RATIO_THRESHOLD is "
            f"{DEFAULT_TOUCHED_RATIO_THRESHOLD!r}, the recorded #424 ship "
            "decision is 0.6 — changing it requires a new spec amendment "
            "AND updating every 0.6 prose citation this lint guards")
    if not _cli_default_is_the_constant(apply_src):
        fails.append(
            "invariant 7: the --touched-ratio-threshold argparse default is "
            "not `DEFAULT_TOUCHED_RATIO_THRESHOLD` — a regression to None or "
            "a re-hardcoded literal would disable/desync the ship-decision "
            "default while the constant still reads 0.6")
    fails.extend(check_section_literals(
        7, spec_text, AMENDMENT_HEADING, "spec amendment", {
            "threshold decision": "0.6",
            "exemption decision": "heading-anchor exemption",
            "emission decision": "sidecar file",
        }))
    return fails


def spec_example_patch(spec_text: str) -> dict | None:
    """First ```json block of spec §3.2, parsed."""
    section = spec_text.split("### 3.2 Patch document", 1)
    if len(section) < 2:
        return None
    m = re.search(r"```json\n(.*?)```", section[1], re.DOTALL)
    if m is None:
        return None
    return json.loads(m.group(1))


def check_spec_example(spec_text: str, schema: dict) -> list[str]:
    """Invariant 8."""
    example = spec_example_patch(spec_text)
    if example is None:
        return ["invariant 8: spec §3.2 example patch JSON block not found"]
    try:
        jsonschema.validate(example, schema)
    except jsonschema.ValidationError as exc:
        return [f"invariant 8: spec §3.2 example no longer validates "
                f"against revision_patch.schema.json: {exc.message}"]
    return []


def main() -> int:
    failures: list[str] = []
    failures += check_writer(WRITER.read_text(encoding="utf-8"))
    failures += check_orchestrator(ORCHESTRATOR.read_text(encoding="utf-8"))
    failures += check_paper_skill(PAPER_SKILL.read_text(encoding="utf-8"))
    failures += check_schema8(SCHEMAS.read_text(encoding="utf-8"))
    failures += check_protocol_doc(
        PROTOCOL.read_text(encoding="utf-8") if PROTOCOL.exists() else None)
    failures += check_marker_rules(
        FORMATTER.read_text(encoding="utf-8"),
        WORD_COUNT.read_text(encoding="utf-8"))
    spec_text = SPEC.read_text(encoding="utf-8")
    failures += check_threshold_lock(
        spec_text, APPLY_SCRIPT.read_text(encoding="utf-8"))
    failures += check_spec_example(
        spec_text, json.loads(PATCH_SCHEMA.read_text(encoding="utf-8")))

    if failures:
        print("check_390_revision_patch_discipline: FAIL")
        for failure in failures:
            print(f"  - {failure}")
        return 1
    print("check_390_revision_patch_discipline: OK (8 invariants)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
