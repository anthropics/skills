---
name: rootnode-critic-gate
description: >-
  Independent re-derivation gate for proposed changes during autonomous
  execution. Evaluates a change (code diff, config edit, engine evolution,
  schema change) against the work's authority matrix and a 4-check
  protocol: invariant compliance, scope authorization, detection
  narrowness, and regression risk. Returns structured JSON with pass/fail
  per check, an overall verdict (APPROVE / REQUEST_CHANGES / REJECT), and
  blockers. Profile-driven thresholds (strict for unattended runs, lenient
  for desk supervision). Use when an autonomous agent proposes an engine
  change, when reviewing a Claude Code-authored modification before merge,
  or when an unattended profile requires independent re-derivation.
  Trigger on: "review/approve this proposed change," "critic-gate this,"
  "is this change safe," "is this safe to merge," "should I let this
  land," "run the critic." Do NOT use for handoff-readiness checks (use
  rootnode-handoff-trigger-check), general code review, or design-time
  correctness. Authority matrix required.
license: Apache-2.0
metadata:
  author: rootnode
  version: "1.0.2"
  original-source: "root.node design 2026 — distilled from production engine evolution patterns"
  companion-files: "schema/profile.schema.json, profiles/lenient.json, profiles/strict.json, profiles/balanced.json, references/checks-detailed.md, references/severity-coverage.md, references/troubleshooting.md"
  changelog: "1.0.2 (2026-05-05): Activation precision tuning. Trigger list rebalanced — 'review this proposed change' + 'approve this diff' consolidated to 'review/approve this proposed change' (saves char budget); 'should this land' replaced with 'should I let this land' (1st-person symptom phrasing); 'is this safe to merge' added as new symptom trigger (merge framing covers user-vocabulary surface that change/diff framing misses). Description grew 996 → 1014 chars (10-char headroom remaining). No methodology, schema, or workflow changes; behavior identical to 1.0.1 once activated. 1.0.1 (2026-05-01): Structural patch to align with rootnode authoring convention. Added references/ folder with three on-demand-loaded files (checks-detailed, severity-coverage, troubleshooting). SKILL.md body slimmed via content extraction; behavior identical to 1.0. Deployment target: Claude Code (CC) side of CP/CC split."
  discipline_post: phase-30
---

# Critic Gate

Independent re-derivation of proposed changes during autonomous execution. Returns a structured verdict before any change lands. The load-bearing safety mechanism for autonomous engine evolution — without it, multi-cycle drift is guaranteed.

The premise: **the agent that proposes a change cannot be the agent that approves it.** When Claude Code is iterating on an engine, every proposed change has an author who has reasoned themselves into the change's necessity. That author's judgment is exactly what the change is grounded in — making them an unreliable evaluator of the change's safety. The critic gate runs on a fresh evaluator with no commitment to the change, applying narrow, named checks against the work's invariants.

This Skill is the rootnode runtime layer's analog to a "Critic Agent" role — an independent re-derivation pass over proposed changes. Generalized for portability: the authority matrix is supplied as input, not baked in.

## Important

**The critic does not re-derive the diagnosis.** It does not verify that the bug exists or that the proposed fix would solve it. Those are the change author's responsibility. The critic checks one thing: **would applying this change violate any invariant, exceed any authorization, or introduce regression risk that wasn't accepted in the work's design?** The diagnosis can be wrong; that's a verification problem, not a critic problem.

**Authority matrix is mandatory input.** The critic cannot evaluate compliance against rules it doesn't have. If no authority matrix is provided in `work_context`, the gate halts with `evidence_not_provided` rather than fabricating rules. This is the most common failure mode to design against.

**Structured JSON output is the deliverable.** Same shape as `rootnode-handoff-trigger-check` (if available; the shape is documented inline below regardless). An orchestrator should be able to parse the verdict and act on it without an LLM round-trip.

**Three verdicts, not two.** Unlike handoff-trigger-check (PASS/FAIL), critic gate has three: APPROVE (proceed), REQUEST_CHANGES (specific issues to address; change author re-proposes), REJECT (proposed change violates non-negotiable constraints; do not re-propose without scope-authorization escalation). The middle verdict matters — most real critic findings are fixable, not fatal.

**Profile thresholds calibrate strictness.** Same profile pattern as handoff-trigger-check. Sleeping profiles run all checks at strictest thresholds; desk profiles allow REQUEST_CHANGES on minor findings to be auto-approved if the change author resolves them in the same turn.

**Severity coverage requirement.** Every severity (`info`, `minor`, `major`, `blocker`) must be routed by the profile to exactly one of `auto_approve_on`, `request_changes_threshold`, or `reject_on`. Unrouted severities create ambiguous runtime behavior. The Skill validates coverage on profile load and rejects misconfigured profiles before any change is evaluated. See `references/severity-coverage.md` for the full routing rules and example profile patterns.

---

## The 4 Checks — Overview

Each check evaluates pass/fail/conditional with evidence and findings. The profile determines how findings combine into the verdict. Per-check pass evidence requirements, full REQUEST_CHANGES finding language, REJECT finding language, edge cases, and worked examples are in `references/checks-detailed.md`.

### 1. Invariant Compliance

The proposed change does not modify any element protected by the authority matrix. Pass requires that every tier of the matrix has been examined against the change diff and no protected content is touched (or only authorized tiers are touched). REQUEST_CHANGES findings handle inadvertent tier crossings the author can re-scope; REJECT findings handle deliberate invariant violations that require scope-authorization escalation.

### 2. Scope Authorization

The proposed change falls within the in-scope authorization for autonomous iteration. Pass requires the change's category appears in the in-scope list (or in-scope-with-notification list with proper surfacing). REQUEST_CHANGES findings handle in-scope changes missing required surfacing; REJECT findings handle out-of-scope categories that the Critic has no authority to approve.

### 3. Detection Narrowness

For changes that add new code paths gated by detection criteria (the additive-evolution pattern): the detection criterion is narrow enough that the new path only fires on the target failure shape, not on existing-passing cases. Pass requires specific detection (named pattern, named field, named state) plus regression-sweep evidence. REQUEST_CHANGES findings handle overly-broad detection the author can tighten; REJECT findings handle detection so broad the change is effectively non-additive.

This check is **skipped** for changes that are not additive-evolution pattern (recorded as `pass: null, skipped: true, reason: "not_additive_evolution"`).

### 4. Regression Risk

The change has acceptable regression risk given the work's verification surface and the active profile's risk tolerance. Pass requires documented verification gates (test suite, regression sweep, smoke tests as appropriate) all clean and no unmodified-but-affected downstream contracts. REQUEST_CHANGES findings handle incomplete verification the author can complete; REJECT findings handle deferred-fix patterns or broken verification surfaces.

---

## Workflow

When invoked:

**Step 1 — Receive inputs.** The Skill expects three inputs:
- `profile`: A profile config matching the included schema. Names verdict thresholds, behavior on REQUEST_CHANGES, and skip rules.
- `work_context`: Must include the authority matrix (full text or path), the in-scope/out-of-scope authorization lists, and the proposed change (diff or change description with affected files/sections named).
- `change_metadata`: Author identity, diagnosis statement, claimed verification, and category (engine_fix / additive_evolution / refactor / test_addition / config_change / other).

**Step 2 — Validate inputs.** If authority matrix is missing, halt with `evidence_not_provided` and surface to caller. If the change diff is too vague to evaluate (no specific files/sections named), halt with `evidence_too_vague` and request specifics.

**Step 3 — Run the 4 checks in order.** Each check produces pass / fail / conditional / skipped with evidence and findings. Findings include severity (info / minor / major / blocker) and concrete language describing what's wrong.

**Step 4 — Apply profile threshold to determine verdict:**
- **APPROVE** — all checks pass with no findings, OR all findings are info-severity only AND profile permits info-only auto-approval
- **REQUEST_CHANGES** — at least one check has minor or major findings, but no blockers AND no REJECT-class findings. Author can re-propose after addressing findings.
- **REJECT** — at least one blocker-severity finding, OR any finding marked REJECT-class regardless of severity (invariant violation, out-of-scope, etc.). Author cannot re-propose without scope-authorization escalation.

**Step 5 — Generate verdict.** Produce structured JSON output (see Output Format). Include per-check results, all findings with severity, recommended actions per finding, and a `requires_human_escalation` boolean for any REJECT-class outcome.

**Step 6 — Return.** Output the JSON. If verbose mode, append a 3-5 sentence human-readable summary explaining the verdict and naming the most critical findings.

---

## Output Format

```json
{
  "verdict": "APPROVE | REQUEST_CHANGES | REJECT",
  "profile_applied": "profile-name-from-input",
  "checked_at": "ISO-8601 timestamp",
  "change_id": "identifier from change_metadata",
  "checks": {
    "invariant_compliance": {
      "pass": true,
      "evidence": "Change touches only Tier 3 UI chrome per authority matrix; no Tier 1 or Tier 2 modifications detected.",
      "findings": []
    },
    "scope_authorization": {
      "pass": true,
      "evidence": "Change is category 'additive_evolution' which is in-scope per authorization list; surfacing entry present in change_log.",
      "findings": []
    },
    "detection_narrowness": {
      "pass": false,
      "evidence": "New code path gated on 'tables with 2+ rows'; this fires on 47 existing test cases that currently pass.",
      "findings": [
        {
          "severity": "major",
          "category": "REQUEST_CHANGES",
          "description": "Detection criterion too broad; will fire on existing-passing cases.",
          "recommended_action": "Narrow detection to 'tables with synthetic_headers=true AND 2+ rows' to match the specific failure shape."
        }
      ]
    },
    "regression_risk": {
      "pass": true,
      "evidence": "Full test suite re-run (62 cases pass); regression sweep across 27 instances complete; no downstream contract changes.",
      "findings": []
    }
  },
  "all_findings": [
    {
      "severity": "major",
      "category": "REQUEST_CHANGES",
      "check": "detection_narrowness",
      "description": "Detection criterion too broad; will fire on existing-passing cases.",
      "recommended_action": "Narrow detection to 'tables with synthetic_headers=true AND 2+ rows' to match the specific failure shape."
    }
  ],
  "requires_human_escalation": false,
  "summary": "REQUEST_CHANGES: detection narrowness check failed with one major finding. Author should tighten detection criterion as recommended; other checks pass. Re-submit after revision."
}
```

When verdict is APPROVE, `all_findings` is empty (or contains info-only entries) and the summary is a single sentence: "Change approved; all checks pass." When verdict is REJECT, `requires_human_escalation` is true and the summary names the specific REJECT-class finding.

---

## Examples

Three worked examples illustrating how the 4 checks combine into the verdict — strict profile + additive engine fix → APPROVE; lenient profile + refactor with broad detection → REQUEST_CHANGES; any profile + test deletion → REJECT — are in `references/checks-detailed.md` (in the "Worked Examples" section). Consult that file when modeling a new use case against an existing pattern, or when authoring a profile and wanting to see how the routing logic plays out on real changes.

---

## Profile Configuration

The Skill expects a profile config conforming to `schema/profile.schema.json`. Minimum profile structure:

```json
{
  "schema_version": "1.0.0",
  "name": "profile-name",
  "description": "When this profile applies",
  "auto_approve_on": ["info"],
  "request_changes_threshold": ["minor", "major"],
  "reject_on": ["blocker"],
  "skip_checks": [],
  "escalation_required_for_categories": ["invariant_violation", "out_of_scope"]
}
```

Three example profiles ship with the Skill:
- `lenient` — auto-approves on info findings; allows REQUEST_CHANGES auto-resolution if author addresses in same turn
- `balanced` — moderate; auto-approves on info; REQUEST_CHANGES requires explicit author re-submission
- `strict` — auto-approves only on full pass; any major finding becomes REJECT (no auto-resolution available without HITL)

Users author their own profiles for their availability and risk tolerance using `rootnode-profile-builder` (if available), or by hand-editing JSON against `schema/profile.schema.json`. The full severity routing rules — including the coverage requirement that every severity be routed to exactly one outcome, the three example profile patterns explained, and severity classification heuristics — are in `references/severity-coverage.md`.

---

## When to Use This Skill

Use this Skill when:
- An autonomous agent has proposed an engine change, refactor, or non-trivial modification during execution
- A Claude Code session has produced a diff that should be reviewed by a fresh evaluator before merge
- A sleeping/unattended profile requires independent re-derivation per its critic-required configuration
- An orchestrator is gating engine-evolution proposals before applying them to a stable codebase

Do NOT use this Skill when:
- Evaluating whether work is ready to hand off to autonomous execution (use rootnode-handoff-trigger-check)
- General code review feedback or improvement suggestions (different intent — critic is gate, not advisor)
- Design-time correctness checks during chat-based design work (no execution context yet)
- Reviewing changes to documentation only (no engine impact; over-engineered for the task)
- Authority matrix is unavailable or undefined (Skill cannot proceed; surface and halt)

---

## Troubleshooting

Common failure modes and resolution guidance — covering input validation issues (no authority matrix, vague matrix, oversized diff, incomplete metadata), verdict behavior issues (Critic approves something that broke, rejects valid work, findings appear on APPROVE, author argues with verdict), profile authoring issues (unrouted severities, no fitting standard pattern), and inter-gate coordination (detection narrowness on non-additive changes, Critic vs handoff-gate verdict disagreement, broken verification surface) — are in `references/troubleshooting.md`. Consult that file when the gate's behavior in production doesn't match expectations.
