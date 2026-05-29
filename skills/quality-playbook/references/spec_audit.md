# Council of Three Spec Audit Protocol (File 5)

This is a static analysis protocol — AI models read the code and compare it to specifications. No code is executed. It catches a different class of problem than testing: spec-code divergence, undocumented features, phantom specs, and missing implementations.

## Why Three Models?

Different AI models have different blind spots — they're confident about different things and miss different things. Cross-referencing three independent reviews catches defects that any single model would miss.

## Template

```markdown
# Spec Audit Protocol: [Project Name]

## The Definitive Audit Prompt

Give this prompt identically to three independent AI tools (e.g., Claude, GPT, Gemini).

---

**Context files to read:**
1. [List all spec/intent documents with paths]
2. [Architecture docs]
3. [Design decision records]

**Task:** Act as the Tester. Read the actual code in [source directories] and compare it against the specifications listed above.

**Requirement confidence tiers:**
Requirements are tagged with `[Req: tier — source]`. Weight your findings by tier:
- **formal** — written by humans in a spec document. Authoritative. Divergence is a real finding.
- **user-confirmed** — stated by the user but not in a formal doc. Treat as authoritative unless contradicted by other evidence.
- **inferred** — deduced from code behavior. Lower confidence. Report divergence as NEEDS REVIEW, not as a definitive defect.

**Rules:**
- ONLY list defects. Do not summarize what matches.
- For EVERY defect, cite specific file and line number(s).
  If you cannot cite a line number, do not include the finding.
- Before claiming missing, grep the codebase.
- Before claiming exists, read the actual function body.
- Classify each finding: MISSING / DIVERGENT / UNDOCUMENTED / PHANTOM
- For findings against inferred requirements, add: NEEDS REVIEW

**Defect classifications:**
- **MISSING** — Spec requires it, code doesn't implement it
- **DIVERGENT** — Both spec and code address it, but they disagree
- **UNDOCUMENTED** — Code does it, spec doesn't mention it
- **PHANTOM** — Spec describes it, but it's actually implemented differently than described

**Project-specific scrutiny areas:**

[5–10 specific questions that force the auditor to read the most critical code. Target:]

1. [The most fragile module — force the auditor to read specific functions]
2. [External data handling — validation, normalization, error recovery]
3. [Assumptions that might not hold — field presence, value ranges, format consistency]
4. [Features that cross module boundaries]
5. [The gap between documentation and implementation]
6. [Specific edge cases from the QUALITY.md scenarios]

**Output format:**

### [filename.ext]
- **Line NNN:** [MISSING / DIVERGENT / UNDOCUMENTED / PHANTOM] [Req: tier — source] Description.
  Spec says: [quote or reference]. Code does: [what actually happens].
  *(Include the `[Req: tier — source]` tag so findings can be traced back to their requirement and confidence level.)*

---

## Pre-audit docs validation (required triage section)

The triage report must include a `## Pre-audit docs validation` section regardless of whether `reference_docs/` exists. This section documents what the auditors used as their factual baseline.

**If `reference_docs/` exists:** Spot-check the gathered docs for factual accuracy before running the audit. Stale or incorrect docs can skew audit confidence — a model that reads "the library handles X by doing Y" in the docs will rate a divergent finding higher even if the docs are wrong.

**Quick validation procedure (5 minutes max):**
1. Pick 2–3 factual claims from `reference_docs/` that describe specific runtime behavior (e.g., "invalid input raises ValueError", "field X defaults to Y", "format Z is not supported").
2. Grep the source code for the cited behavior. Does the code match the docs?
3. If any claim is wrong, note it in the triage header: "reference_docs/ contains N known inaccuracies: [list]. Findings that rely on these claims are downgraded to NEEDS REVIEW."

**Spot-check claims about code contents must extract, not assert.** When the spec audit prompt or pre-validation includes claims like "function X handles constant Y at line Z," the triage must read the cited lines and report what they actually contain. Do not confirm a claim by checking that the function exists or that the constant is defined somewhere — confirm it by showing the exact text at the cited lines. Format each spot-check result as:

```
Claim: "vring_transport_features() preserves VIRTIO_F_RING_RESET at line 3527"
Actual line 3527: `default:`
Result: CLAIM IS FALSE — line 3527 is the default branch, not a RING_RESET case label
```

Spot-check claims derived from generated requirements or gathered docs (rather than from the code) are **hypotheses to test**, not facts to confirm. This rule prevents the contamination chain observed in v1.3.17 where a false spot-check claim was accepted as "accurate" without reading the actual lines, causing three auditors to inherit a hallucinated code-presence claim.

**If `reference_docs/` does not exist:** State this explicitly: "No supplemental docs provided. Auditors relied on in-repo specs and code only." This confirms the absence is intentional, not an oversight.

This section fires in every triage, not just when docs are present. In v1.3.5 cross-repo testing, it only fired in 1/8 repos because it was conditional — making it required ensures the audit trail always documents the factual baseline.

## Running the Audit

1. Give the identical prompt to three AI tools
2. Each auditor works independently — no cross-contamination
3. Collect all three reports

## Triage Process

After all three models report, merge findings.

**Log the effective council size.** If a model did not return a usable report (timeout, empty output, refusal), record this in the triage header:

```
## Council Status
- Model A: Fresh report received (YYYY-MM-DD)
- Model B: Fresh report received (YYYY-MM-DD)
- Model C: TIMEOUT — no usable report. Effective council: 2/3.
```

When the effective council is 2/3, downgrade the confidence tier: "All three" becomes impossible, "Two of three" becomes the ceiling. When the effective council is 1/3, all findings are "Needs verification" regardless of how confident that single model is. Do not silently substitute stale reports from prior runs — if a model didn't produce a fresh report for this run, it didn't participate.

| Confidence | Found By | Action |
|------------|----------|--------|
| Highest | All three | Almost certainly real — fix or update spec |
| High | Two of three | Likely real — verify and fix |
| Needs verification | One only | Could be real or hallucinated — deploy verification probe |

**When the effective council is 2/3 or less:** Distinguish single-auditor findings from multi-auditor findings explicitly in the triage. With a 2/3 council, a finding from both present auditors has "High" confidence. A finding from only one present auditor has "Needs verification" — it cannot be promoted to confirmed BUG without a verification probe, because the missing auditor might have contradicted it. Do not treat all findings as equivalent just because the council is incomplete.

In the triage summary table, add a column for auditor agreement: "2/2 present", "1/2 present", etc. This makes the confidence tier visible and auditable.

**Incomplete council gate for enumeration/dispatch checks.** If the effective council is less than 3/3 and the run includes whitelist/enumeration/dispatch-function checks (claims about which constants a function handles), the audit may not conclude "no confirmed defects" for those checks without executed mechanical proof. Check whether `quality/mechanical/<function>_cases.txt` exists for each relevant function. If it does and shows the constant is present, the claim is confirmed. If it does and shows the constant is absent, the claim is false regardless of what any auditor wrote. If no mechanical artifact exists, generate one before closing the enumeration check. This rule exists because v1.3.18 had an effective council of 1/3, and the single model's triage fabricated line contents for enumeration claims — a mechanical artifact would have caught the contradiction.

### The Verification Probe

When models disagree on factual claims, deploy a read-only probe: give one model the disputed claim and ask it to read the code and report ground truth. Never resolve factual disputes by majority vote — the majority can be wrong about what code actually does.

**Verification probes must produce executable evidence.** Prose reasoning is not sufficient for either confirmations or rejections. Every verification probe must produce a test assertion that mechanically proves the determination:

**For rejections** (finding is false positive): Write an assertion that PASSES, proving the auditor's claim is wrong:
```python
# Rejection proof: function X does check for null at line 247
assert "if (ptr == NULL)" in source_of("X"), "X has null check at line 247"
```
If you cannot write a passing assertion, **do not reject the finding**. The inability to produce mechanical proof is itself evidence that the finding may be real.

**For confirmations** (finding is a real bug): Write an assertion that FAILS (expected-failure), proving the bug exists:
```python
# Confirmation proof: RING_RESET is not a case label in the whitelist
assert "case VIRTIO_F_RING_RESET:" in source_of("vring_transport_features"), \
    "RING_RESET should be in the switch but is not — cleared by default at line 3527"
```

**Every assertion must cite an exact line number** for the evidence it references. Not "lines 3527-3528" but "line 3527: `default:`" — showing what the line actually contains.

**Why this rule exists:** In v1.3.16 virtio testing, the triage received a correct minority finding that VIRTIO_F_RING_RESET was missing from a switch/case whitelist. The triage performed a verification probe that claimed lines 3527-3528 "explicitly preserve VIRTIO_F_RING_RESET" — but those lines contained the `default:` branch. The probe hallucinated compliance. Had it been required to write `assert "case VIRTIO_F_RING_RESET:" in source`, the assertion would have failed, exposing the hallucination. Requiring executable evidence makes hallucinated rejections self-defeating.

### Categorize Each Confirmed Finding

- **Spec bug** — Spec is wrong, code is fine → update spec
- **Design decision** — Human judgment needed → discuss and decide
- **Real code bug** — Fix in small batches by subsystem
- **Documentation gap** — Feature exists but undocumented → update docs
- **Missing test** — Code is correct but no test verifies it → add to the functional test file
- **Inferred requirement wrong** — The inferred requirement doesn't match actual intent → remove or correct it in QUALITY.md

That last category is the bridge between the spec audit and the test suite. Every confirmed finding not already covered by a test should become one.

### Legacy and historical scripts

Scripts documented as "historical," "deprecated," or "not part of current workflow" are sometimes downgraded during triage on the theory that they don't affect current operations. This is correct when the script genuinely never runs. But if the script's bug has already materialized in canonical artifacts — duplicate entries in a published file, stale data in a checked-in cache, incorrect mappings that downstream tools consume — the bug is not historical. It's a live defect in the repository's published state.

**Rule: If a legacy script's bug is already visible in canonical artifacts, promote it to confirmed BUG regardless of the script's status.** The script may be historical, but the damage it left behind is current. The regression test should target the artifact (the duplicate entry, the stale mapping), not the script — because the artifact is what users encounter.

This rule exists because v1.3.5 bootstrap runs on QPB found duplicate changelog entries and stale cache mappings produced by a "historical" script. Both triages downgraded the findings because the script was historical. But the duplicate entries were already in the published library, visible to every user.

### Cross-artifact consistency check

After triage, compare the spec audit findings against the code review findings from `quality/code_reviews/`. If the code review and spec audit disagree on the same factual claim (one says a bug is real, the other calls it a false positive), flag the disagreement and deploy a verification probe. The code review and spec audit use different methods (structural reading vs. spec comparison), so disagreements are informative, not errors. But a factual contradiction about what the code actually does needs to be resolved before either report is trusted.

## Detecting partial sessions and carried-over artifacts

### Partial session detection

A session that terminates early (timeout, context exhaustion, crash) may generate scaffolding (directory structure, empty templates) without producing the actual review or audit content. The retry mechanism in the run script can regenerate scaffolding but cannot recover the analytical work.

**After any session completes, check for partial results:**
1. If `quality/code_reviews/` exists but contains no `.md` files with actual findings (or only contains template headers with no BUG/VIOLATED/INCONSISTENT entries), the code review did not run. Mark this as FAILED in PROGRESS.md, not as "complete with no findings."
2. If `quality/spec_audits/` exists but contains no triage summary, the spec audit did not run.
3. If `quality/test_regression.*` exists but contains only imports and no test functions, regression tests were not written.

A partial session is not a "clean run with no findings" — it's a failed run that needs to be re-executed. PROGRESS.md should record this clearly: "Phase 6: FAILED — code review session terminated before producing findings. Re-run required."

### Provenance headers on carried-over artifacts

When a new playbook run finds existing artifacts from a previous run (after archiving), or when artifacts survive from a failed session, they must carry provenance headers so readers know their origin.

**If any artifact was NOT generated fresh in the current run**, add a provenance header:

```markdown
<!-- PROVENANCE: This file was carried over from a previous run ([date]).
     It was NOT regenerated by the current v1.3.5 run.
     Treat findings as potentially stale — verify against current source before acting. -->
```

This prevents the failure mode observed in v1.3.4 where express and zod silently preserved v1.3.3 code reviews and spec audits without marking them as archival. Users reading those artifacts assumed they were fresh v1.3.4 results.

## Fix Execution Rules

- Group fixes by subsystem, not by defect number
- Never one mega-prompt for all fixes
- Each batch: implement, test, have all three reviewers verify the diff
- At least two auditors must confirm fixes pass before marking complete

## Output

Save audit reports to `quality/spec_audits/YYYY-MM-DD-[model].md`
Save triage summary to `quality/spec_audits/YYYY-MM-DD-triage.md`
```

## The Four Guardrails (Critical for All Auditors)

Some models confidently claim features are missing without checking code. These four rules embedded in the audit prompt materially improve output quality by reducing vague and hallucinated findings:

1. **Mandatory line numbers** — If you cannot cite a line number, do not include the finding. This eliminates vague claims.
2. **Grep before claiming missing** — Before saying a feature is absent, search the codebase. It may be in a different file.
3. **Read function bodies, not just signatures** — Don't assume a function works correctly based on its name.
4. **Classify defect type** — Forces structured thinking (MISSING/DIVERGENT/UNDOCUMENTED/PHANTOM) instead of vague "this looks wrong."

These guardrails are already embedded in the template above. They matter most for models that tend toward confident but unchecked claims.

## Model Selection Notes

Different models have different audit strengths. In practice:

- **Architecture-focused models** (e.g., Claude) tend to find the most issues with fewest false positives, excelling at silent data loss, cross-function data flow, and state machine bugs.
- **Edge-case focused models** (e.g., GPT-based tools) tend to catch boundary conditions other models miss (zero-length inputs, file collisions, off-by-one errors) and serve as effective verification cross-checkers.
- **Models that need structure** (e.g., some Gemini variants) may perform poorly on open-ended audit prompts but respond dramatically to the four guardrails above.

The specific models that excel will change over time. The principle holds: use multiple models with different strengths, and always include the four guardrails.

### Minimum model capability

The audit protocol requires reading function bodies, citing line numbers, grepping before claiming missing, and classifying defect types. Lightweight or speed-optimized models (Haiku-class, GPT-4o-mini-class) are not suitable as auditors. They tend to skim rather than read, skip the grep step, and produce shallow or empty reports ("No defects found") on codebases where stronger models find real bugs. Use models with strong code-reading ability for all three auditor slots. A weak auditor doesn't just miss findings — it reduces the Council from three independent perspectives to two.

## Tips for Writing Scrutiny Areas

The scrutiny areas are the most important part of the prompt. Generic questions like "check if the code matches the spec" produce generic answers. Specific questions that name functions, files, and edge cases produce specific findings.

Good scrutiny areas:
- "Read `process_input()` in `pipeline.py` lines 45–120. The spec says it should handle missing fields by substituting defaults. Does it? Which fields have defaults and which silently produce null?"
- "The architecture doc says Module A passes validated data to Module B. Read both modules. Is there any path where unvalidated data reaches Module B?"

Bad scrutiny areas:
- "Check if the code is correct"
- "Look for bugs"
- "Verify the implementation matches the spec"
