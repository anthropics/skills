# audit_artifact_consistency fixtures

Synthetic JSON / YAML / JSONL files for ARS v3.6.7 Phase 6.3 lint tests.

`positive/` — bundles that should produce zero findings.
`negative/` — bundles that should produce at least one finding (rule_id named in the directory).

These fixtures stay independent of the in-memory test fixtures in
`test_check_audit_artifact_consistency.py` so the lint script can be
spot-checked from the CLI without running pytest.

## Invocation contract for spot-checking

The sidecars reference deliverable paths (`chapter_4/synthesis.md`
etc.) that are illustrative — the bundle files do **not** exist in the
ARS repo checkout. To spot-check a fixture from the CLI, pass
`--repo-root` pointing at the fixture directory itself so B3's live-
disk verification short-circuits at the synthetic-fixture safe-skip
(no `.git/` marker → B3 Step 2 returns without flagging missing files,
matching the convention used by B4 git-resolution).

```bash
# positive fixtures: rc=0
python scripts/check_audit_artifact_consistency.py \
  --mode persisted \
  --output-dir scripts/fixtures/audit_artifact_consistency/positive/persisted_minor \
  --run-id 2026-04-30T15-22-04Z-d8f3 \
  --repo-root scripts/fixtures/audit_artifact_consistency/positive/persisted_minor

python scripts/check_audit_artifact_consistency.py \
  --mode proposal \
  --output-dir scripts/fixtures/audit_artifact_consistency/positive/proposal_pass \
  --run-id 2026-04-30T15-22-04Z-d8f3 \
  --repo-root scripts/fixtures/audit_artifact_consistency/positive/proposal_pass

# negative fixtures: rc=1 with the rule_id named in the dir
# (a1_pass_with_p1 is a proposal-shaped entry — the violation is the A1
# cross-field rule, not lifecycle arm. Use --mode proposal so the lint
# doesn't first flag the proposal shape under persisted arm enforcement.)
python scripts/check_audit_artifact_consistency.py \
  --mode proposal \
  --output-dir scripts/fixtures/audit_artifact_consistency/negative/a1_pass_with_p1 \
  --run-id 2026-04-30T15-22-04Z-d8f3 \
  --repo-root scripts/fixtures/audit_artifact_consistency/negative/a1_pass_with_p1

# a7_orphan_completion is jsonl-stream mode (single file fixture)
python scripts/check_audit_artifact_consistency.py \
  --mode jsonl-stream \
  --jsonl scripts/fixtures/audit_artifact_consistency/negative/a7_orphan_completion/2026-04-30T15-22-04Z-d8f3.jsonl
```

The default `--repo-root` (the actual ARS checkout containing `.git`)
will exercise B3's live-disk gate against the real repo, which the
synthetic fixtures' sidecar paths do not satisfy. This is intentional
— `--repo-root` is the dial that toggles "lint against real repo state"
vs "spot-check fixture self-consistency".
