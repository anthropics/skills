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

## Running the Audit

1. Give the identical prompt to three AI tools
2. Each auditor works independently — no cross-contamination
3. Collect all three reports

## Triage Process

After all three models report, merge findings:

| Confidence | Found By | Action |
|------------|----------|--------|
| Highest | All three | Almost certainly real — fix or update spec |
| High | Two of three | Likely real — verify and fix |
| Needs verification | One only | Could be real or hallucinated — deploy verification probe |

### The Verification Probe

When models disagree on factual claims, deploy a read-only probe: give one model the disputed claim and ask it to read the code and report ground truth. Never resolve factual disputes by majority vote — the majority can be wrong about what code actually does.

### Categorize Each Confirmed Finding

- **Spec bug** — Spec is wrong, code is fine → update spec
- **Design decision** — Human judgment needed → discuss and decide
- **Real code bug** — Fix in small batches by subsystem
- **Documentation gap** — Feature exists but undocumented → update docs
- **Missing test** — Code is correct but no test verifies it → add to the functional test file
- **Inferred requirement wrong** — The inferred requirement doesn't match actual intent → remove or correct it in QUALITY.md

That last category is the bridge between the spec audit and the test suite. Every confirmed finding not already covered by a test should become one.

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

## Tips for Writing Scrutiny Areas

The scrutiny areas are the most important part of the prompt. Generic questions like "check if the code matches the spec" produce generic answers. Specific questions that name functions, files, and edge cases produce specific findings.

Good scrutiny areas:
- "Read `process_input()` in `pipeline.py` lines 45–120. The spec says it should handle missing fields by substituting defaults. Does it? Which fields have defaults and which silently produce null?"
- "The architecture doc says Module A passes validated data to Module B. Read both modules. Is there any path where unvalidated data reaches Module B?"

Bad scrutiny areas:
- "Check if the code is correct"
- "Look for bugs"
- "Verify the implementation matches the spec"
