---
name: quantitative-resume-auditor
description: Audits resumes with Python: metric density (M/B ratio) vs. 3.0 Gold Standard. With a JD: token coverage, knockout flags, False-Miss audit. Triggers on resume audit, density check, or JD gap analysis.
---

<!--
SPDX-License-Identifier: Apache-2.0
Copyright 2026 Dr. Fabiano de Souza
-->

# Quantitative Resume Auditor

**Author:** Dr. Fabiano de Souza

This skill turns a resume review from a subjective opinion into a calculated score. It counts every numeric data point, runs Python to compute a Metric Density ratio, and tells the user exactly which bullets are pulling the score down.

## Quick Reference: Metric Density Formula

```
Metric Density = Total Counted Metrics (M) / Total Bullet Points (B)
Target: 3.0 or higher
```

## Audit Process

### Step 1 - Metric Extraction & Categorization (M)

Count every instance of a quantitative data point in the resume text. Every unique metric counts toward `M`. Categorize each into one of four buckets:

1. **Percentages & Rates**: e.g., `45%`, `3x`, `12% YoY`, `200% growth`
2. **Currency & Financials**: e.g., `$1.2M`, `$500K budget`, `$50B AUM`
3. **Headcount & Scale**: e.g., `12 engineers`, `3 cross-functional teams`, `500+ users`
4. **Time & Duration**: e.g., `6 months`, `3-year roadmap`, `24-hour turnaround`

*Rule:* If a bullet contains multiple numbers, count each valid distinct metric toward `M`. Dates (e.g., `2021-2023`) do NOT count as metrics.

### Step 2 - Bullet Counting (B)

Count the total number of bullet points (`B`) across all work experience entries.

Compute:
- `Metric Density = M / B`
- `Quantification Rate = (Bullets with at least 1 metric / B) * 100%`

**Density Benchmarks:**
- `< 1.0`: Weak - highly subjective, narrative-heavy. Needs immediate quantification.
- `1.0 - 2.9`: Moderate - some data, but many bullets lack impact proof.
- `>= 3.0`: Gold Standard - dense, evidence-based, competitive for top-tier roles.

### Step 3 - Report Format

Deliver three sections:

**1. Audit Scoreboard**
A table with M, B, Q, Density Score, Quantification Rate, and Status.

**2. Category Breakdown**
List the count per category so the M total is independently verifiable.
Example: `Percentages: 34 | Currency: 5 | Headcount: 8 | Years: 30`

**3. Gap Analysis**

*If a job description is provided*, run three checks in order:

**A. Knockout Flag**
Before any overlap analysis, scan the JD for hard requirements - mandatory certifications, licenses, degree requirements, or lines using "must have," "required," or "minimum." For each one, check whether the resume provides direct evidence. Flag any that are missing as HIGH RISK - these are the documented auto-filter triggers, more consequential than any keyword score.
Example: "Valid teaching license - not evidenced in resume."

**B. JD Token Coverage**
Extract hard skill tokens, tools, methodologies, and key domain phrases from the JD. Measure the percentage present in the resume. Categorize gaps into:
- **Direct Misses**: Required skill completely absent from resume.
- **Weak Mentions**: Mentioned once in passing without context or metric proof.

**C. False-Miss Audit**
Compare resume bullet wording against JD phrasing to identify matches missed by naive ATS parsers due to synonym or phrasing differences (e.g., `Python scripting` vs. `automated data pipelines in Python`).

```python
def audit_resume(metrics_count, bullets_count, bullets_with_metrics):
    density = metrics_count / bullets_count if bullets_count > 0 else 0
    quant_rate = (bullets_with_metrics / bullets_count * 100) if bullets_count > 0 else 0
    
    if density >= 3.0:
        status = "Gold Standard"
    elif density >= 1.0:
        status = "Moderate"
    else:
        status = "Weak"
        
    return {
        "density": round(density, 2),
        "quantification_rate": f"{round(quant_rate, 1)}%",
        "status": status
    }
```
