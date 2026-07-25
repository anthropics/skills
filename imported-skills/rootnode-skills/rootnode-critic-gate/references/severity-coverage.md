# Severity Coverage and Profile Routing

The full reference for severity classification (`info`, `minor`, `major`, `blocker`), routing rules across profile fields (`auto_approve_on`, `request_changes_threshold`, `reject_on`), and the coverage requirement that every severity must be routed to exactly one outcome. Use this when authoring a profile, debugging unexpected verdict behavior, or when validation rejects a profile for unrouted severities.

**When to consult this file:** When authoring a new profile and deciding how to route each severity, when a profile validation error names "unrouted severities" and you need to fix the routing, when a profile produces unexpected verdicts and you suspect severity routing is the cause, or when classifying a new finding's severity is ambiguous.

---

## Table of Contents

1. [The Four Severity Levels](#the-four-severity-levels)
2. [The Coverage Requirement](#the-coverage-requirement)
3. [Routing Rules](#routing-rules)
4. [Profile Authoring Patterns](#profile-authoring-patterns)
5. [Severity Classification Heuristics](#severity-classification-heuristics)

---

## The Four Severity Levels

Findings produced by the Critic Gate's 4 checks are classified into one of four severities. The classification is the check's responsibility; the routing to verdict is the profile's responsibility.

### info

Observational findings that the change author or downstream readers should know about, but that do not block any verdict.

**Examples:**
- "Change adds a new code path; consider adding a unit test in a follow-up to lock the new behavior."
- "Verification gap: existing test suite does not exercise the affected code path. Change passes regression risk by default but the gap is tracked."
- "Authority matrix Tier 3 free-design touch is intentional and appropriate; documented for audit trail."

**Default routing:** `auto_approve_on: ["info"]` — info findings never block.

**Anti-pattern:** Using `info` for findings that *should* block but the author wants to suppress. If a finding is genuinely worth surfacing, classify it accurately and let the profile decide what to do with it.

### minor

Findings that the change author can address with a small adjustment in the same iteration cycle. Typically: missing surfacing, incomplete documentation, narrow technical issues.

**Examples:**
- "Cross-cutting refactor is in-scope-with-notification but the change_log entry is missing. Add the notification."
- "Detection criterion is correctly narrow but the supporting comment in code is vague. Tighten the comment to name the specific failure shape."
- "Verification: integration regression sweep was run but its output wasn't captured in the change metadata. Add the sweep result."

**Default routing:** `request_changes_threshold: ["minor", "major"]` — minor findings produce REQUEST_CHANGES.

**Lenient profile variant:** `auto_approve_on: ["info", "minor"]` — minor findings are tracked but auto-approved when the change author can resolve them in the same turn.

### major

Findings that meaningfully affect change safety and require deliberate adjustment. Typically: detection that's too broad, verification that's incomplete in ways the change demands, scope creep that's substantive.

**Examples:**
- "Detection criterion 'any table with 2+ rows' will fire on 47 existing-passing cases; narrow to '[specific form]' to match the actual failure shape."
- "Test suite passes but integration regression sweep was not run; the change touches a file exercised across all 27 instances; sweep is required."
- "Refactor change is substantively larger than its surfacing entry suggests; notification entry should be expanded to reflect actual blast radius."

**Default routing:** `request_changes_threshold: ["minor", "major"]` — major findings produce REQUEST_CHANGES.

**Strict profile variant:** `reject_on: ["major", "blocker"]` — strict profiles treat major findings as REJECT-class. The change author cannot iterate to APPROVE without a fresh submission addressing the finding. This is the right setting for unattended runs where iteration cycles aren't observable in real-time.

### blocker

Non-negotiable findings that violate invariants or scope authorization. The Critic Gate has no authority to grant exceptions; only human scope-authorization can override.

**Examples:**
- "Change deliberately modifies Tier 1 protected content with no escalation. §19.2 violation regardless of intent."
- "Change category 'test_deletion' is in the explicit out-of-scope list. Critic Gate cannot grant exceptions to the authorization list."
- "Verification surface itself is broken (test suite fails to run). Cannot evaluate regression risk against a broken verification surface."

**Default routing:** `reject_on: ["blocker"]` — blockers produce REJECT, regardless of profile.

**No profile may permit auto-approval of blockers.** A profile with `auto_approve_on: ["blocker"]` is invalid and rejected by profile validation. This is the one routing rule that's not configurable.

---

## The Coverage Requirement

Every severity (info / minor / major / blocker) must be routed by the profile to exactly one of `auto_approve_on`, `request_changes_threshold`, or `reject_on`. The Skill validates coverage on profile load and rejects misconfigured profiles before any change is evaluated.

**Why coverage is mandatory:** Unrouted severities create ambiguous runtime behavior. If a finding is classified as `minor` but the profile names neither `minor` in `auto_approve_on`, `request_changes_threshold`, nor `reject_on`, the Skill has no defined behavior for that finding. Rather than guess, the Skill rejects the profile.

**Validation message format:** When a profile is misconfigured, the rejection names which severities are unrouted:

```
Profile validation failed: unrouted severities [minor, major]
Each severity must appear in exactly one of:
  - auto_approve_on
  - request_changes_threshold
  - reject_on
Current routing:
  auto_approve_on: ["info"]
  request_changes_threshold: []
  reject_on: ["blocker"]
Fix: add "minor" and "major" to one of the three routing fields.
```

**Why "exactly one" not "at least one":** Routing a severity to multiple outcomes (e.g., both `request_changes_threshold` and `reject_on`) creates the same ambiguity as not routing it at all. Pick one outcome per severity. If you want REQUEST_CHANGES for some `major` findings and REJECT for others, the right answer is to refine the severity classification (split into `major` and `critical`), not to route a single severity to multiple outcomes.

---

## Routing Rules

The three routing fields produce three verdicts:

### auto_approve_on

Severities in this list do not block APPROVE. Findings of these severities still appear in the verdict's `findings` array (audit trail), but they do not push the verdict away from APPROVE.

**Always include `info` here.** Info findings are observational by design; routing them to `request_changes_threshold` makes the gate noisy without adding safety.

**Lenient profiles may include `minor` here.** This is the auto-resolution pattern: minor findings surface but don't block, on the theory that the author will see them and address in the same cycle.

**Never include `blocker` here.** Profile validation rejects this configuration.

### request_changes_threshold

Severities in this list produce REQUEST_CHANGES verdict. The change author can re-propose after addressing the findings; no human escalation required.

**Default profile setting:** `["minor", "major"]`. This is the most common configuration — both severities are author-fixable.

**Strict profile variant:** `["minor"]` only. Major findings are escalated via `reject_on`.

**Lenient profile variant:** `[]` (empty). Minor and major are routed to `auto_approve_on` instead, on the assumption that real-time human supervision catches anything serious.

### reject_on

Severities in this list produce REJECT verdict. `requires_human_escalation` is true; the change author cannot re-propose without scope-authorization decision.

**Always include `blocker` here.** This is the one mandatory routing.

**Strict profile variant:** `["major", "blocker"]`. Major findings escalate to REJECT, treating "needs deliberate adjustment" as "needs human authorization for unattended runs."

---

## Profile Authoring Patterns

The three example profiles shipped with the Skill demonstrate three coherent severity routing patterns:

### Strict pattern (sleeping / unattended runs)

```json
{
  "auto_approve_on": ["info"],
  "request_changes_threshold": ["minor"],
  "reject_on": ["major", "blocker"]
}
```

Major findings escalate to REJECT because no human is available to evaluate "should this be auto-fixed?" mid-run. The conservative routing prevents work from continuing when something substantive is wrong.

### Balanced pattern (default)

```json
{
  "auto_approve_on": ["info"],
  "request_changes_threshold": ["minor", "major"],
  "reject_on": ["blocker"]
}
```

The neutral configuration. Author can iterate on minor and major findings; only blockers escalate to human authorization. Suitable for desk supervision where the human is available but not actively monitoring every change.

### Lenient pattern (real-time pairing)

```json
{
  "auto_approve_on": ["info", "minor"],
  "request_changes_threshold": ["major"],
  "reject_on": ["blocker"]
}
```

Minor findings auto-approve under the assumption that real-time human pairing catches anything that needs adjustment. Major findings still require explicit re-submission; blockers still escalate. Use only when human is actively supervising every change.

---

## Severity Classification Heuristics

When a finding's severity classification is ambiguous, these heuristics help.

### Heuristic 1: Is it observational?

If the finding is "the change has property X, which the author/reader should know about" without implying any required action, it's **info**.

### Heuristic 2: Can the change author fix it in the same iteration?

If the finding is "address X and re-submit" and the fix is small and self-contained, it's **minor**.

### Heuristic 3: Does it require deliberate re-design?

If the finding is "address X" but the fix requires re-thinking the change's structure (broader detection, additional verification, expanded scope), it's **major**.

### Heuristic 4: Does it violate non-negotiable constraints?

If the finding is "the change cannot proceed without scope-authorization escalation" — invariant violation, out-of-scope category, broken verification surface — it's **blocker**, regardless of size.

### Avoiding severity inflation

Tempting failure mode: classifying every finding as `major` because it feels important. This degrades the gate's signal-to-noise ratio. The honest classifications are:

- Most findings should be `minor` (small adjustments).
- Some findings are `major` (require re-design).
- A few findings are `info` (observational only).
- Rare findings are `blocker` (non-negotiable).

If your gate is producing `major` findings on every change, the threshold is mis-calibrated. Re-evaluate the classifications.

### Avoiding severity deflation

Opposite failure mode: classifying findings as `info` to suppress them. This produces verdicts that look clean but mask real issues. The test: if a finding is genuinely observational and would be appropriate to log without taking action, it's `info`. If it's "the author needs to do something," it's at least `minor`.
