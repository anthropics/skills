{skill_fallback_guide}

You are a quality engineer continuing a phase-by-phase quality playbook run. Phase 1 (exploration) is already complete.

Read these files to get context:
1. quality/EXPLORATION.md - your Phase 1 findings (requirements, risks, architecture)
2. quality/PROGRESS.md - run metadata and phase status
3. SKILL.md - read the Phase 2 section (from "Phase 2: Generate the Quality Playbook" through the "Checkpoint: Update PROGRESS.md after artifact generation" section). Also read the reference files cited in that section. Resolve SKILL.md and reference files via the documented fallback list above; do NOT assume any single install layout (`.github/skills/`, `.claude/skills/quality-playbook/`, `.cursor/skills/quality-playbook/`, `.continue/skills/quality-playbook/`, or root).

**Field preservation rule (v1.5.2, Lever 2).** When transcribing REQ hypotheses from EXPLORATION.md into `quality/REQUIREMENTS.md` and `quality/requirements_manifest.json`, every `- Pattern: <value>` field present on the source hypothesis MUST appear on the corresponding REQ in both output files. Pattern values are `whitelist | parity | compensation`. Phase 1's Cartesian UC rule (confirmation checklist item 6) requires Pattern tagging for every REQ where both UC gates match; Phase 2 must not silently drop these tags. If a hypothesis lacks Pattern but you believe it should have one (per-site UCs emitted with `UC-N.a`/`UC-N.b` suffixes, multi-file `References` suggesting a parallel structure), add Pattern during Phase 2 — do not omit the field. The Phase 5 cardinality gate cannot enforce coverage on a REQ it doesn't know is pattern-tagged; silent omission is a documented v1.4.5-regression vector.

Execute Phase 2: Generate all quality artifacts. Use the exploration findings in EXPLORATION.md as your source - do not re-explore the codebase from scratch. Generate:
- quality/QUALITY.md (quality constitution)
- quality/CONTRACTS.md (behavioral contracts)
- quality/REQUIREMENTS.md (with REQ-NNN and UC-NN identifiers from EXPLORATION.md)
- quality/COVERAGE_MATRIX.md
- Functional tests (quality/test_functional.*)
- quality/RUN_CODE_REVIEW.md (code review protocol)
- quality/RUN_INTEGRATION_TESTS.md (integration test protocol)
- quality/RUN_SPEC_AUDIT.md (spec audit protocol)
- quality/RUN_TDD_TESTS.md (TDD verification protocol)
- quality/COMPLETENESS_REPORT.md (baseline, without verdict)
- If dispatch/enumeration contracts exist: quality/mechanical/ with verify.sh and extraction artifacts. Run verify.sh immediately and save receipts.

Update PROGRESS.md: mark Phase 2 complete (use the checkbox format `- [x] Phase 2 - Generate` — do NOT switch to a table), update artifact inventory.

IMPORTANT: Do NOT proceed to Phase 3 (code review). Your job is artifact generation only. The next phase will execute the review protocols you generated.
