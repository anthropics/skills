<!--
SPDX-License-Identifier: Apache-2.0
Copyright 2026 Dr. Fabiano de Souza
-->

---
name: quantitative-resume-auditor
description: Audits resumes with Python: metric density (M/B ratio) vs. 3.0 Gold Standard. With a JD: token coverage, knockout flags, False-Miss audit. Triggers on resume audit, density check, or JD gap analysis.
---

# Quantitative Resume Auditor

**Author:** Dr. Fabiano de Souza

This skill turns a resume review from a subjective opinion into a calculated score.
It counts every numeric data point, runs Python to compute a Metric Density ratio,
and tells the user exactly which bullets are pulling the score down.

**Formula:** `Density = Total Numeric Metrics (M) / Total Bullet Points (B)`

A score of 3.0 or above is the target. The skill works on any resume regardless of
length, profession, or career stage. All counts are dynamic — no fixed target number.

When a job description is also provided, the skill runs a second pass: JD token
coverage, knockout flag check, and a False-Miss Audit that distinguishes real gaps
from synonym differences.

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
import re

def tokenize(text):
    """Lowercase, strip punctuation, return content words (4+ chars)."""
    words = re.findall(r'\b[a-zA-Z]{4,}\b', text.lower())
    # Remove common stopwords that add noise to coverage
    stopwords = {
        'that', 'with', 'this', 'from', 'have', 'been', 'will', 'their',
        'they', 'what', 'when', 'your', 'which', 'also', 'into', 'more',
        'about', 'than', 'were', 'each', 'such', 'over', 'other', 'these'
    }
    return [w for w in words if w not in stopwords]


def run_resume_audit(M, B, Q, resume_text="", jd_text=""):
    """
    Core audit function.
    M, B, Q  — counts Claude extracted manually in Step 1.
    resume_text, jd_text — full plain text of each document (optional).
    When both texts are provided, JD coverage and gap analysis run automatically.
    """
    if B == 0:
        return {"Error": "No bullet points found. Please provide a resume."}

    density = round(M / B, 2)
    # Cap at 100% — a bullet with multiple metrics still counts as one quantified bullet
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

    result = {
        "Total Metrics (M)":      M,
        "Bullet Points (B)":      B,
        "Quantified Bullets (Q)": Q,
        "Density Score":          f"{density} metrics/bullet",
        "Quantification Rate":    f"{rate}%",
        "Status":                 status,
        "Recommendation":         rec
    }

    # --- JD pass: only runs when both texts are supplied ---
    if resume_text and jd_text:
        resume_tokens = set(tokenize(resume_text))
        jd_tokens     = set(tokenize(jd_text))

        if jd_tokens:
            covered = jd_tokens & resume_tokens
            missing = jd_tokens - resume_tokens
            coverage = round(len(covered) / len(jd_tokens) * 100, 1)

            # Coverage interpretation — heuristic bands, not published benchmarks
            if coverage >= 35:
                cov_note = "Strong vocabulary alignment with JD."
            elif coverage >= 20:
                cov_note = "Moderate alignment. Review missing terms below."
            else:
                cov_note = "Low alignment. Resume may not match recruiter search terms."

            result["JD Token Coverage"]      = f"{coverage}% ({len(covered)}/{len(jd_tokens)} JD terms)"
            result["Coverage Note"]          = cov_note
            result["Potentially Missing"]    = sorted(missing)[:20]  # top 20 for review

    return result


# Replace these values with actual counts and text from the documents
M           = 0    # total numeric metrics counted
B           = 0    # total bullet points counted
Q           = 0    # bullets containing at least one metric
resume_text = ""   # paste full resume text here
jd_text     = ""   # paste full JD text here (leave empty if no JD)

result = run_resume_audit(M, B, Q, resume_text, jd_text)
for k, v in result.items():
    if isinstance(v, list):
        print(f"{k}:")
        for item in v:
            print(f"  - {item}")
    else:
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

*If a job description is provided*, run three checks in order:

**A. Knockout Flag**
Before any overlap analysis, scan the JD for hard requirements — mandatory
certifications, licenses, degree requirements, or lines using "must have,"
"required," or "minimum." For each one, check whether the resume provides
direct evidence. Flag any that are missing as HIGH RISK — these are the
SPDX-License-Identifier: Apache-2.0
Copyright 2026 Dr. Fabiano de Souza
-->

---
name: quantitative-resume-auditor
description: Audits resumes with Python: metric density (M/B ratio) vs. 3.0 Gold Standard. With a JD: token coverage, knockout flags, False-Miss audit. Triggers on resume audit, density check, or JD gap analysis.
---

# Quantitative Resume Auditor

**Author:** Dr. Fabiano de Souza

This skill turns a resume review from a subjective opinion into a calculated score.
It counts every numeric data point, runs Python to compute a Metric Density ratio,
and tells the user exactly which bullets are pulling the score down.

**Formula:** `Density = Total Numeric Metrics (M) / Total Bullet Points (B)`

A score of 3.0 or above is the target. The skill works on any resume regardless of
length, profession, or career stage. All counts are dynamic — no fixed target number.

When a job description is also provided, the skill runs a second pass: JD token
coverage, knockout flag check, and a False-Miss Audit that distinguishes real gaps
from synonym differences.

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
import re

def tokenize(text):
    """Lowercase, strip punctuation, return content words (4+ chars)."""
    words = re.findall(r'\b[a-zA-Z]{4,}\b', text.lower())
    stopwords = {
        'that', 'with', 'this', 'from', 'have', 'been', 'will', 'their',
        'they', 'what', 'when', 'your', 'which', 'also', 'into', 'more',
        'about', 'than', 'were', 'each', 'such', 'over', 'other', 'these'
    }
    return [w for w in words if w not in stopwords]


def run_resume_audit(M, B, Q, resume_text="", jd_text=""):
    if B == 0:
        return {"Error": "No bullet points found. Please provide a resume."}

    density = round(M / B, 2)
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

    result = {
        "Total Metrics (M)":      M,
        "Bullet Points (B)":      B,
        "Quantified Bullets (Q)": Q,
        "Density Score":          f"{density} metrics/bullet",
        "Quantification Rate":    f"{rate}%",
        "Status":                 status,
        "Recommendation":         rec
    }

    if resume_text and jd_text:
        resume_tokens = set(tokenize(resume_text))
        jd_tokens     = set(tokenize(jd_text))

        if jd_tokens:
            covered  = jd_tokens & resume_tokens
            missing  = jd_tokens - resume_tokens
            coverage = round(len(covered) / len(jd_tokens) * 100, 1)

            if coverage >= 35:
                cov_note = "Strong vocabulary alignment with JD."
            elif coverage >= 20:
                cov_note = "Moderate alignment. Review missing terms below."
            else:
                cov_note = "Low alignment. Resume may not match recruiter search terms."

            result["JD Token Coverage"]   = f"{coverage}% ({len(covered)}/{len(jd_tokens)} JD terms)"
            result["Coverage Note"]       = cov_note
            result["Potentially Missing"] = sorted(missing)[:20]

    return result


M           = 0
B           = 0
Q           = 0
resume_text = ""
jd_text     = ""

result = run_resume_audit(M, B, Q, resume_text, jd_text)
for k, v in result.items():
    if isinstance(v, list):
        print(f"{k}:")
        for item in v:
            print(f"  - {item}")
    else:
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

*If a job description is provided*, run three checks in order:

**A. Knockout Flag**
Scan the JD for hard requirements — mandatory certifications, licenses,
degree requirements, or lines using "must have," "required," or "minimum."
For each one, check whether the resume provides direct evidence. Flag any
that are missing as HIGH RISK — these are the documented auto-filter
triggers, more consequential than any keyword score.
Example: "Valid teaching license — not evidenced in resume."

**B. JD Token Coverage**
Report the coverage % from the Python output. For each term in
"Potentially Missing," apply a False-Miss Audit before calling it a real gap:
- Covered by a synonym? (e.g., "AI" covers "artificial")
- Morphological variant present? (e.g., "communicated" covers "communicate")
- Inferrable title or role equivalent?
Mark SYNONYM/COVERED if yes. Only flag as a real gap if genuinely absent.

**C. Coverage Map**
Map each JD responsibility area to resume bullets with quantified evidence.
Flag uncovered items by risk level (see `REFERENCE.md` Section 5):
High / Medium / Low.

*If no job description is provided:* list the three to five bullets with the
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
"Do I meet the hard requirements in this job posting?"
```

---

## Notes

- **Dynamic counts.** The skill counts whatever is in the document.
  There is no minimum or maximum target — density scales with the resume.
- **Code execution required.** Enable it in Claude settings before using this skill.
- **The 3.0 benchmark is a professional heuristic**, not a published HR standard.
  It was developed through analysis of executive and leadership resumes.
  See `REFERENCE.md` for full definitions.
- **JD token coverage thresholds are heuristics**, not externally validated benchmarks.
  Use them to compare one draft against another, not as absolute pass/fail scores.
  Modern ATS platforms (Workday, Greenhouse, Lever) use semantic matching and
  ontology graphs — not literal keyword counts — to rank candidates.
- **Knockout flags take priority** over all overlap metrics. A missing required
  certification eliminates a candidate regardless of coverage score.
- **False-Miss Audit prevents over-editing.** Do not add a term to the resume
  if the concept is already covered by a synonym or equivalent phrase.
- **Works across professions** — education, business, healthcare, technology,
  government, and nonprofit roles all use quantifiable accomplishments.
