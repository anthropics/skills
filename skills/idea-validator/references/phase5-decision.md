# Phase 5 — Go / No-Go Decision Memo

## Goal
Synthesize all four phases into a clear, ruthless verdict.
This is the document the builder reads before opening their IDE.

---

## 5.1 Synthesis Inputs

Pull the following from previous phases:
- Phase 1: Problem acuity score, strongest failure mode, persona fit
- Phase 2: Competitor gap, market signal strength, red flags
- Phase 3: Prototype feasibility, pass condition likelihood
- Phase 4: Top technical risk, spike recommendation

---

## 5.2 Scoring Rubric

Score each dimension 1–5:

| Dimension | Score | Weight | Notes |
|-----------|-------|--------|-------|
| Problem Acuity (how badly does it hurt?) | /5 | 25% | From Phase 1 |
| Market Demand Signal (evidence people pay) | /5 | 25% | From Phase 2 |
| Competitive Differentiation | /5 | 20% | From Phase 2 |
| Technical Feasibility | /5 | 15% | From Phase 4 |
| Prototype Testability (can we validate fast?) | /5 | 15% | From Phase 3 |

**Weighted Score = sum(score × weight)**

Interpretation:
- 4.0–5.0 → **GO** — strong signal across all dimensions
- 3.0–3.9 → **CONDITIONAL GO** — viable but one key condition must be true
- 2.0–2.9 → **HIGH RISK** — proceed only if builder has unique advantage
- < 2.0 → **NO-GO** — fundamental flaw, pivot recommended

---

## 5.3 Verdict Block

Format this as a clear, prominent block:

```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
VERDICT: [GO / CONDITIONAL GO / NO-GO]
CONFIDENCE: [X]/10
WEIGHTED SCORE: [X.X]/5.0
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 5.4 Single Biggest Unvalidated Assumption

Name the one thing, if wrong, that kills this idea.
Be specific. Not "product-market fit" — but e.g.:
"Users will trust AI-generated interview answers enough to practice with them instead of a human coach."

This is the thing to validate before writing production code.

---

## 5.5 Verdict-Specific Guidance

### If GO:
- **Build this first**: [the one feature that delivers the core value, nothing else]
- **Ignore until after first 10 paying users**: [list of scope traps]
- **First distribution channel**: [where to find the first 10 users specifically]

### If CONDITIONAL GO:
- **The condition**: [exact statement of what must be true]
- **How to test the condition**: [specific action, < 1 week]
- **If condition is met**: proceed to Phase 4 spike
- **If condition fails**: [pivot direction]

### If NO-GO:
- **The core flaw**: [one sentence, no softening]
- **Why this can't be patched**: [brief explanation]
- **Pivot option**: [adjacent idea that avoids the flaw, if one exists]

---

## 5.6 Validation Checklist (Appendix)

Generate a checklist of open vs. closed items:

```markdown
## Validation Checklist

### ✅ Validated
- [ ] Problem exists (from Phase 1)
- [ ] Competitors identified (from Phase 2)
- [ ] Differentiation articulated (from Phase 2)
- [ ] Tech stack de-risked (from Phase 4)

### ⚠️ Still Open (must validate before scaling)
- [ ] [Specific assumption from Phase 1 still open]
- [ ] [Pricing hypothesis untested]
- [ ] [Retention assumption unverified]

### 🚫 Out of Scope (validate after first revenue)
- [ ] Enterprise sales motion
- [ ] Mobile app
- [ ] Internationalization
```

---

## Tone Guidance for Phase 5

- Write like a trusted technical co-founder, not a consultant
- No hedge words: "potentially", "might", "could" — state things directly
- If the score is bad, say so clearly — false encouragement costs the builder months
- If the score is good, be specific about why — vague positivity is useless
