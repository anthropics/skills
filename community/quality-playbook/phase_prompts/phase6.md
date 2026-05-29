{skill_fallback_guide}

You are a quality engineer doing the verification phase of a quality playbook run. Phases 1-5 are complete.

Read SKILL.md - the Phase 6 section ("Phase 6: Verify"). Resolve SKILL.md via the documented fallback list above; do NOT assume any single install layout. Follow the incremental verification steps (6.1 through 6.5).

Step 6.1: If quality/mechanical/verify.sh exists, run it. Record exit code.
Step 6.2: Run quality_gate.py. Locate it via the same fallback list used for SKILL.md (`quality_gate.py` sits in the same directory as SKILL.md in every install layout — e.g., `quality_gate.py`, `.claude/skills/quality-playbook/quality_gate.py`, `.github/skills/quality_gate.py`, `.cursor/skills/quality-playbook/quality_gate.py`, `.continue/skills/quality-playbook/quality_gate.py`, `.github/skills/quality-playbook/quality_gate.py`). Then run:
  python3 <resolved_quality_gate_path> .
Read the output carefully. For every FAIL result, fix the issue:
- Missing regression-test patches: generate quality/patches/BUG-NNN-regression-test.patch
- Missing inline diffs in writeups: add a ```diff block
- Non-canonical JSON fields: fix tdd-results.json (use 'id' not 'bug_id', etc.)
- Missing files: create them
After fixing all FAILs, run quality_gate.py again. Repeat until 0 FAIL.
Save final output to quality/results/quality-gate.log.

Step 6.3: Run functional tests if a test runner is available.
Step 6.4: File-by-file verification checklist (read one file at a time, check, move on).
Step 6.5: Metadata consistency check.

Append each step's result to quality/results/phase6-verification.log.
Mark Phase 6 complete in PROGRESS.md (use the checkbox format `- [x] Phase 6 - Verify` — do NOT switch to a table).
