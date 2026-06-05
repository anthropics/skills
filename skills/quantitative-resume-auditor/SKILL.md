<!--
SPDX-License-Identifier: Apache-2.0
Copyright 2026 Dr. Adriano De Souza
-->

---
name: quantitative-resume-auditor
description: Audits any resume using Python to compute metric density (M/B ratio). Benchmarks against a 3.0 Gold Standard. Triggers on resume audit, density check, impact scoring, or JD gap analysis.
---

# Quantitative Resume Auditor

This skill transforms qualitative resume reviews into high-precision computational audits producing a fixed Metric Density Score calculated by Python.

**Core formula:** Density = Total Numeric Metrics (M) / Total Bullet Points (B)

A score of 3.0+ means the resume is data-dense. Works on any resume — any length, profession, or career stage.

See REFERENCE.md for benchmarks and JD coverage framework.

---

## Instructions for Claude

### Step 1 — Data Extraction

Count three variables precisely from the resume:

| Variable | Definition |
|----------|------------|
| B | Total bullet points |
| M | Total numeric metrics (numbers, %, $, ratios) |
| Q | Bullets with at least one metric |

Count M by category: Percentages, Currency, Headcount, Years, Score gains, Efficiency, Volume.

### Step 2 — Python Computation

Run using Claude's code execution tool:

```python
def run_resume_audit(M, B, Q):
    if B == 0:
        return {"Error": "No bullet points detected."}
    density = round(M / B, 2)
    rate = min(round((Q / B) * 100, 1), 100.0)
    if density >= 3.0:
        status, rec = "GOLD STANDARD", "Maintain density. Focus on JD gaps."
    elif density >= 1.5:
        status, rec = "COMPETITIVE", "Add 1-2 metrics to the 5 weakest bullets."
    else:
        status, rec = "QUALITATIVE", "Rewrite responsibilities as accomplishments."
    return {"Total Metrics (M)": M, "Bullet Points (B)": B,
            "Quantified Bullets (Q)": Q, "Density": f"{density}/bullet",
            "Rate": f"{rate}%", "Status": status, "Recommendation": rec}

M, B, Q = 0, 0, 0  # Claude replaces with actual counts
for k, v in run_resume_audit(M, B, Q).items():
    print(f"{k}: {v}")
```

### Step 3 — Report Format

1. **Audit Scoreboard** — table with M, B, Q, Density, Rate, Status
2. **Category Breakdown** — per-category metric counts
3. **Gap Analysis** — JD coverage map (if JD provided) or weakest bullet list

---

## When to Use

- Resume audit, score, density check, or impact analysis
- "Is my resume quantitative enough?"
- JD gap analysis or coverage map
- Career coaching on resume strength

## Example Prompts

- "Audit this resume for data density."
- "Score my resume against the 3.0 benchmark."
- "Run a gap analysis — here is my resume and the job description."

## Notes

- **Dynamic:** No fixed target — counts whatever is in the document.
- **Requires code execution** enabled in Claude.
- **3.0 benchmark** is a professional heuristic. See REFERENCE.md.
- **Any profession:** education, business, healthcare, tech, government, nonprofit.
