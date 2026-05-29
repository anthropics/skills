{skill_fallback_guide}

You are a quality engineer continuing a phase-by-phase quality playbook run. Phases 1-3 are complete.

Read these files to get context:
1. quality/PROGRESS.md - run metadata, phase status, BUG tracker
2. quality/REQUIREMENTS.md - derived requirements
3. quality/BUGS.md - bugs found in Phase 3 (code review)
4. SKILL.md - read the Phase 4 section ("Phase 4: Spec Audit and Triage"). Also read references/spec_audit.md. Resolve SKILL.md and the references/ directory via the documented fallback list above; do NOT assume any single install layout.

Execute Phase 4: Spec Audit + Triage + Layer-2 semantic citation check.

Part A — spec audit:
Run the spec audit per quality/RUN_SPEC_AUDIT.md. Produce:
- Individual auditor reports at quality/spec_audits/YYYY-MM-DD-auditor-N.md (one per auditor)
- Triage synthesis at quality/spec_audits/YYYY-MM-DD-triage.md
- Executable triage probes at quality/spec_audits/triage_probes.sh
- Regression tests and patches for any net-new spec audit bugs
- Update BUGS.md and PROGRESS.md BUG tracker with any new findings

Part B — Layer-2 semantic citation check (v1.5.1):
The gate's invariant #17 (schemas.md §10) requires three Council members to
vote on each Tier 1/2 REQ's citation_excerpt. Execute these steps:

1. Generate per-Council-member prompts:
     python3 -m bin.quality_playbook semantic-check plan .
   This writes one or more prompt files to
   quality/council_semantic_check_prompts/<member>.txt per member in the
   Council roster (bin/council_config.py: claude-opus-4.7, gpt-5.4,
   gemini-2.5-pro). For >15 Tier 1/2 REQs, prompts are split into batches
   of 5 (<member>-batch<N>.txt).
   If no Tier 1/2 REQs exist (Spec Gap run), this step writes an empty
   quality/citation_semantic_check.json directly — skip steps 2-4.

2. For each Council member's prompt file, feed the prompt to that model
   (the same roster that ran Part A) and capture its JSON-array response
   to quality/council_semantic_check_responses/<member>.json. If the
   member was batched, concatenate the per-batch responses into a single
   array in the response file. Every entry must have req_id, verdict
   (supports|overreaches|unclear), and reasoning.

3. Assemble the semantic-check output:
     python3 -m bin.quality_playbook semantic-check assemble . \
       --member claude-opus-4.7 --response quality/council_semantic_check_responses/claude-opus-4.7.json \
       --member gpt-5.4         --response quality/council_semantic_check_responses/gpt-5.4.json \
       --member gemini-2.5-pro  --response quality/council_semantic_check_responses/gemini-2.5-pro.json
   This writes quality/citation_semantic_check.json per schemas.md §9.

4. Verify the output file exists. Phase 6's gate invariant #17 requires
   it on every Tier 1/2 run.

Mark Phase 4 (Spec audit + triage + semantic check) complete in PROGRESS.md (use the checkbox format `- [x] Phase 4 - Spec Audit` — the Phase 5 entry gate looks for that exact substring and will abort if it finds a table row or any other layout).

IMPORTANT: Do NOT proceed to Phase 5 (reconciliation). The next phase will handle reconciliation and TDD.
