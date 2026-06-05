<!--
SPDX-License-Identifier: Apache-2.0
Copyright 2026 Dr. Fabiano de Souza
-->

---
name: quantitative-resume-auditor
description: Audits any resume using Python to compute metric density (M/B ratio). Benchmarks against a 3.0 Gold Standard. Triggers on resume audit, density check, impact scoring, or JD gap analysis.
---

# Quantitative Resume Auditor

**Author:** Dr. Fabiano de Souza

This skill turns a resume review from a subjective opinion into a calculated score.
It counts every numeric data point, runs Python to compute a Metric Density ratio,
and tells the user exactly which bullets are pulling the score down.

**Formula:** `Density = Total Numeric Metrics (M) / Total Bullet Points (B)`

A score of 3.0 or above is the target. The skill works on any resume regardless of
length, profession, or career stage. All counts are dynamic — no fixed target number.

See `REFERENCE.md` for benchmark definitions, metric categories, and JD coverage framework.

---

## Instructions for Claude

### Step 1 — Data Extraction

Read the full resume and count these three variables. Do not estimate.

| Variable | Definition |
|----------|------------|
| B | Total bullet points (every accomplishment statement) |
| M | Total numeric metrics (every number, %, $, ratio, or time reference) |
| Q | Bullets that contain at least one metric |

List the M count broken down by category so the total is verifiable:
- Percentages (gains, rates, lifts, completion %)
- Currency (budgets, grants, revenue, cost savings)
- Headcount / scale (people, students, sites, partners)
- Years / time (years of experience, program durations, dates)
- Score gains (test score improvements, rating increases)
- Efficiency (time saved, processing reductions, cycle improvements)
- Volume / output (publications, certifications, projects, transactions)

### Step 2 — Python Computation

Run the following code using Claude's code execution tool.
Do not do this math in plain text.

```python
def run_resume_audit(M, B, Q):
    if B == 0:
        return {"Error": "No bullet points found. Please provide a resume."}

    density = round(M / B, 2)
    # Cap at 100% — a bullet with six metrics still counts as one quantified bullet
    rate = min(round((Q / B) * 100, 1), 100.0)

    if density >= 3.0:
        status = "GOLD STANDARD"
        rec = "Density is strong. Shift focus to job description coverage gaps."
    elif density >= 1.5:
        status = "COMPETITIVE"
        rec = "Find the five weakest bullets and add one or two metrics to each."
    else:
        status = "QUALITATIVE"
        rec = "Rewrite responsibility statements as accomplishment statements."

    return {
        "Total Metrics (M)":      M,
        "Bullet Points (B)":      B,
        "Quantified Bullets (Q)": Q,
        "Density Score":          f"{density} metrics/bullet",
        "Quantification Rate":    f"{rate}%",
        "Status":                 status,
        "Recommendation":         rec
    }

# Replace with actual counts from the resume
M, B, Q = 0, 0, 0

for k, v in run_resume_audit(M, B, Q).items():
    print(f"{k}: {v}")
```

### Step 3 — Report Format

Deliver three sections:

**1. Audit Scoreboard**
A table with M, B, Q, Density Score, Quantification Rate, and Status.

**2. Category Breakdown**
List the count per category so the M total is independently verifiable.
Example: `Percentages: 34 | Currency: 5 | Headcount: 8 | Years: 30`

**3. Gap Analysis**

If a job description is provided: map each JD responsibility area to resume
bullets that provide quantified evidence. Calculate coverage per area and
flag uncovered items by risk level (see `REFERENCE.md` Section 5).

If no job description is provided: list the three to five bullets with the
lowest metric count and suggest what specific data the user could add.

---

## When to Use This Skill

Trigger when the user:

- Uploads a resume and asks for an audit, score, or density check
- Asks "Is my resume quantitative enough?" or similar
- Asks whether their resume matches a job description
- Requests a JD gap analysis or coverage map
- Wants to benchmark their resume before applying for a role

---

## Example Prompts

```
"Audit this resume for data density."
"Score my resume against the 3.0 benchmark."
"Run a gap analysis — here is my resume and the job description."
"Which bullets are weakest and what numbers should I add?"
```

---

## Notes

- **Dynamic counts.** The skill counts whatever is in the document.
  There is no minimum or maximum target — density scales with the resume.
- **Code execution required.** Enable it in Claude settings before using this skill.
- **The 3.0 benchmark is a professional heuristic**, not a published HR standard.
  It was developed through analysis of executive and leadership resumes.
  See `REFERENCE.md` for full definitions.
- **Works across professions** — education, business, healthcare, technology,
  government, and nonprofit roles all use quantifiable accomplishments.
