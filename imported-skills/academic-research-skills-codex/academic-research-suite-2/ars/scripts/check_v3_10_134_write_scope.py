#!/usr/bin/env python3
"""Static lint for the ARS #134 Slice 1 write-scope guard — three-way name cross-check.

Spec: docs/design/2026-06-01-ars-134-conductor-rescope-deterministic-write-guard-spec.md (§3.4)
Classification: docs/design/2026-05-18-ars-v3.9.2-agent-phase-classification.md

THE FAIL-OPEN GUARD. The write-scope hook keys on the subagent's `agent_type`, which
equals the agent's frontmatter `name`. If the manifest key, the classification-table
Bucket A roster, and the on-disk frontmatter `name` ever drift apart (a rename, a
manifest typo, a table edit), the hook silently FAILS OPEN for that agent — it would
treat the agent as "not in the manifest" and allow every write. This lint catches that
drift before it can happen, mirroring check_v3_9_2_phase_boundary.py's 23/16 split.

Three invariants:

  I1 — Roster size. The Bucket A roster is exactly 23 agents (16 B/C/D exempt = 39
       records / 38 unique names per the classification table; the manifest covers the
       23 Bucket A names only).

  I2 — Three-way name set equality. The set of:
         (a) Bucket A agent file paths (the classification-table roster, single-sourced
             here as BUCKET_A_AGENT_FILES — identical to check_v3_9_2_phase_boundary.py),
         (b) manifest keys (scripts/ars_phase_scope_manifest.json -> agents),
         (c) on-disk frontmatter `name` fields read from each (a) file,
       must be IDENTICAL. Any element in one but not the others is a fail-open risk.

  I3 — Bucket B/C/D exclusion. None of the 16 exempt agents' frontmatter `name` may
       appear as a manifest key (a Bucket B/C/D agent in the manifest would impose a
       single-phase fence on a legitimately multi-phase agent).

  I4 — Manifest shape. Every manifest entry carries bucket == "A", a non-empty
       allowed_write_globs list, and a phase label.

Exit codes: 0 on pass, 1 on any failure.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
MANIFEST_PATH = REPO_ROOT / "scripts" / "ars_phase_scope_manifest.json"

# Single-sourced Bucket A roster (the classification-table Bucket A rows). IDENTICAL to
# check_v3_9_2_phase_boundary.py's BUCKET_A_AGENTS — kept in lockstep by I1 (count) +
# the symmetry of the two lints. If v3.9.x adds/removes a Bucket A agent, BOTH lists move.
BUCKET_A_AGENT_FILES = [
    # deep-research/agents/ (10)
    "deep-research/agents/research_question_agent.md",
    "deep-research/agents/research_architect_agent.md",
    "deep-research/agents/bibliography_agent.md",
    "deep-research/agents/source_verification_agent.md",
    "deep-research/agents/synthesis_agent.md",
    "deep-research/agents/timeline_extraction_agent.md",
    "deep-research/agents/editor_in_chief_agent.md",
    "deep-research/agents/ethics_review_agent.md",
    "deep-research/agents/risk_of_bias_agent.md",
    "deep-research/agents/meta_analysis_agent.md",
    # academic-paper/agents/ (7)
    "academic-paper/agents/literature_strategist_agent.md",
    "academic-paper/agents/structure_architect_agent.md",
    "academic-paper/agents/draft_writer_agent.md",
    "academic-paper/agents/citation_compliance_agent.md",
    "academic-paper/agents/abstract_bilingual_agent.md",
    "academic-paper/agents/peer_reviewer_agent.md",
    "academic-paper/agents/formatter_agent.md",
    # academic-paper-reviewer/agents/ (6)
    "academic-paper-reviewer/agents/eic_agent.md",
    "academic-paper-reviewer/agents/methodology_reviewer_agent.md",
    "academic-paper-reviewer/agents/domain_reviewer_agent.md",
    "academic-paper-reviewer/agents/perspective_reviewer_agent.md",
    "academic-paper-reviewer/agents/devils_advocate_reviewer_agent.md",
    "academic-paper-reviewer/agents/editorial_synthesizer_agent.md",
]

# The 16 Bucket B/C/D agents that MUST NOT appear in the manifest.
BUCKET_BCD_AGENT_FILES = [
    "deep-research/agents/devils_advocate_agent.md",
    "deep-research/agents/report_compiler_agent.md",
    "academic-paper/agents/argument_builder_agent.md",
    "academic-paper/agents/visualization_agent.md",
    "deep-research/agents/socratic_mentor_agent.md",
    "academic-paper/agents/socratic_mentor_agent.md",
    "deep-research/agents/monitoring_agent.md",
    "academic-paper/agents/revision_coach_agent.md",
    "academic-pipeline/agents/integrity_verification_agent.md",
    "academic-pipeline/agents/collaboration_depth_agent.md",
    "academic-pipeline/agents/claim_ref_alignment_audit_agent.md",
    "shared/agents/compliance_agent.md",
    "academic-paper/agents/intake_agent.md",
    "academic-pipeline/agents/pipeline_orchestrator_agent.md",
    "academic-pipeline/agents/state_tracker_agent.md",
    "academic-paper-reviewer/agents/field_analyst_agent.md",
]

_NAME_RE = re.compile(r"^name:\s*(.+?)\s*$", re.MULTILINE)
# Line-anchored fence so a literal `---` inside a description value can't split the
# block early (^---$ on its own line, tolerating trailing whitespace).
_FENCE_RE = re.compile(r"^---[ \t]*$", re.MULTILINE)


def read_frontmatter_name(rel_path: str) -> str | None:
    """Read the frontmatter `name:` field from the first YAML block of an agent file.

    Deliberately NOT `_skill_lint.parse_frontmatter`: this lint needs the precise line-
    anchored two-fence semantics below (a `---` inside a description value must NOT split the
    block, and a `name:` in prose must NOT masquerade as the binding — a review finding), and a
    missing/broken fence pair must surface as a drift (return None) rather than being parsed
    leniently. Keeping it stdlib-only also avoids coupling this fail-open guard to the
    skill-lint module / its pyyaml dependency. The block is flat key:value, so a regex suffices.
    """
    path = REPO_ROOT / rel_path
    if not path.exists():
        return None
    text = path.read_text(encoding="utf-8")
    fences = list(_FENCE_RE.finditer(text))
    if len(fences) < 2:
        # No well-formed frontmatter fence pair. Return None (fail loud upstream) rather
        # than scanning the body — a `name:` in prose must NOT masquerade as the binding
        # (review finding). A missing/broken frontmatter is itself a drift the lint reports.
        return None
    block = text[fences[0].end():fences[1].start()]
    m = _NAME_RE.search(block)
    return m.group(1).strip().strip('"').strip("'") if m else None


def load_manifest() -> dict:
    return json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))


def load_manifest_keys() -> set[str]:
    return set(load_manifest().get("agents", {}).keys())


def run_checks() -> list[str]:
    errors: list[str] = []

    # I1 — roster size
    if len(BUCKET_A_AGENT_FILES) != 23:
        errors.append(
            f"I1: BUCKET_A_AGENT_FILES has {len(BUCKET_A_AGENT_FILES)} entries, expected 23 "
            "(classification doc: A=23). Update in lockstep with check_v3_9_2_phase_boundary.py."
        )
    if len(BUCKET_BCD_AGENT_FILES) != 16:
        errors.append(
            f"I1: BUCKET_BCD_AGENT_FILES has {len(BUCKET_BCD_AGENT_FILES)} entries, expected 16."
        )

    # I5 — roster exhaustiveness (NON-VACUOUS guard). Glob the actual filesystem for every
    # agent definition; assert the two hard-coded rosters together cover ALL of them. A new
    # agent file added without updating the rosters + manifest would otherwise be silently
    # treated as unconstrained (fail-open) by the hook — this catches that at lint time.
    #
    # `**/agents/*.md` (not `*/agents/*.md`) so an agent dir nested deeper than one level is
    # also covered — a one-level glob would silently miss a future `skill/sub/agents/x.md`
    # and reopen the fail-open hole (caught in review). Two real-layout subtleties
    # this must handle WITHOUT false-positives:
    #   * The plugin-root `agents/` MIRROR dir (Claude Code plugin convention) holds real
    #     byte-identical COPIES of per-skill agent files — copies since #413 (relative
    #     symlinks broke Windows checkouts / zip installs); check_agents_mirror_sync.py
    #     pins the byte-equality. A mirror file introduces no new agent name: map it BY
    #     NAME to its `deep-research/agents/...` source and check THAT against the roster.
    #     A name with no rostered source still falls through to undeclared — the mapping
    #     is not an allowlist for anything dropped into `agents/`. LOAD-BEARING
    #     assumption: every mirror sources from `deep-research/agents/<same name>`. If a
    #     mirror of an agent living elsewhere (e.g. `academic-paper/agents/`) is ever
    #     added, this rule and the MIRRORS roster in check_agents_mirror_sync.py would
    #     silently disagree — extend BOTH in lockstep (deliberately re-derived here, not
    #     imported: one-lint-one-invariant; the disagreement today fails CLOSED, pinned
    #     by the non-deep-research-source negative test).
    #   * Anything else compares on the CANONICAL (resolved) workspace-relative path: a
    #     leftover symlink resolves to its rostered target (the pre-#413 shape, kept for
    #     generality), while a genuinely NEW standalone .md at any depth resolves to
    #     itself, is absent from the roster, and is flagged. That is exactly the
    #     fail-open case we want to catch.
    declared = set(BUCKET_A_AGENT_FILES) | set(BUCKET_BCD_AGENT_FILES)
    undeclared = []
    for md in REPO_ROOT.glob("**/agents/*.md"):
        if ".git" in md.parts:
            continue
        # .as_posix() so the comparison uses `/` on every OS (the rosters use `/`).
        rel = md.relative_to(REPO_ROOT).as_posix()
        if rel.startswith("experiment-agent/"):
            continue  # Codex package vendors experiment-agent as a separate skill.
        if rel in declared:
            continue  # directly rostered — skip the alias mapping (the common case)
        # Not directly rostered: map the two alias shapes documented above before
        # deciding it is undeclared.
        if rel.startswith("agents/") and rel.count("/") == 1:
            # Plugin-root mirror (#413) — DIRECT children only. A nested
            # agents/sub/agents/x.md is NOT a mirror (codex P2: remapping it
            # would fail open when its name collides with a rostered agent);
            # it falls through to the resolve path and flags as undeclared.
            canon = f"deep-research/agents/{md.name}"
        else:
            try:
                canon = md.resolve().relative_to(REPO_ROOT).as_posix()
            except ValueError:
                canon = rel  # resolves outside the repo (unexpected) — compare on rel only
        if canon not in declared:
            undeclared.append(rel)
    undeclared = sorted(set(undeclared))
    missing = sorted(f for f in declared if not (REPO_ROOT / f).exists())
    if undeclared:
        errors.append(
            f"I5: agent file(s) {undeclared} exist on disk but are in NEITHER roster — the "
            "hook would fail OPEN for any new Bucket A agent among them. Add to the correct "
            "roster (+ the manifest if Bucket A)."
        )
    if missing:
        errors.append(
            f"I5: roster lists file(s) {missing} that no longer exist on disk — stale entry."
        )

    # Read on-disk names for the Bucket A roster.
    ondisk_names: set[str] = set()
    for rel in BUCKET_A_AGENT_FILES:
        nm = read_frontmatter_name(rel)
        if nm is None:
            errors.append(f"I2: could not read frontmatter `name:` from {rel}")
        else:
            ondisk_names.add(nm)

    manifest_keys = load_manifest_keys()

    # I2 — three-way set equality (on-disk names vs manifest keys)
    # (the classification-table roster is represented by BUCKET_A_AGENT_FILES; on-disk
    #  names ARE the (a)↔(c) bridge, manifest_keys is (b).)
    if ondisk_names != manifest_keys:
        only_disk = sorted(ondisk_names - manifest_keys)
        only_manifest = sorted(manifest_keys - ondisk_names)
        if only_disk:
            errors.append(
                f"I2: agent frontmatter name(s) {only_disk} have NO manifest entry — the "
                "hook would fail OPEN for them (treat as unconstrained)."
            )
        if only_manifest:
            errors.append(
                f"I2: manifest key(s) {only_manifest} match NO Bucket A agent frontmatter "
                "name — a typo/rename; the hook would never enforce them."
            )

    # I3 — Bucket B/C/D exclusion
    bcd_names: set[str] = set()
    for rel in BUCKET_BCD_AGENT_FILES:
        nm = read_frontmatter_name(rel)
        if nm:
            bcd_names.add(nm)
    leaked = sorted(bcd_names & manifest_keys)
    if leaked:
        errors.append(
            f"I3: Bucket B/C/D agent name(s) {leaked} appear as manifest keys — a single-phase "
            "fence on a legitimately multi-phase/orthogonal agent. Remove from manifest."
        )

    # I4 — manifest entry shape
    manifest = load_manifest()
    for key, entry in manifest.get("agents", {}).items():
        if entry.get("bucket") != "A":
            errors.append(f"I4: manifest entry {key!r} has bucket={entry.get('bucket')!r}, expected 'A'.")
        globs = entry.get("allowed_write_globs")
        if not isinstance(globs, list) or not globs:
            errors.append(f"I4: manifest entry {key!r} has empty/invalid allowed_write_globs.")
        if not entry.get("phase"):
            errors.append(f"I4: manifest entry {key!r} missing a phase label.")

    return errors


def main() -> int:
    errors = run_checks()
    if errors:
        print("FAIL — ARS #134 write-scope three-way name cross-check:")
        for e in errors:
            print(f"  - {e}")
        return 1
    print(
        f"PASS — {len(BUCKET_A_AGENT_FILES)} Bucket A agents: classification roster == "
        f"manifest keys == on-disk frontmatter names; {len(BUCKET_BCD_AGENT_FILES)} B/C/D "
        "exempt and absent from manifest."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
