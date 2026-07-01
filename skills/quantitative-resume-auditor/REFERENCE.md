<!--
SPDX-License-Identifier: Apache-2.0
Copyright 2026 Dr. Fabiano de Souza
-->

# Quantitative Resume Auditor — Reference

This file defines the benchmarks, metric categories, and JD coverage framework
used during the audit. Claude loads it during benchmarking and gap analysis.

---

## 1. Density Benchmark Levels

These thresholds come from analysis of executive and leadership resumes across
education, business, healthcare, and technology. They are not a published
HR industry standard — treat them as a calibrated professional heuristic.

| Level | Score | What It Looks Like | Practical Risk |
|-------|-------|--------------------|----------------|
| Qualitative | below 1.5 | Bullet points describe duties, not results. Few or no numbers. | Likely screened out before a human reads it. |
| Competitive | 1.5 to 2.9 | Some metrics present — budgets, team sizes, rates. Results are there but not consistent. | Gets past screening but may not stand out in a competitive pool. |
| Gold Standard | 3.0 and above | Multiple metrics per bullet covering result, scale, and context. | Credible on paper. Interviewers can build questions directly from the data. |

---

## 2. Metric Categories

Count each category separately so the M total can be checked independently.

| Category | What to Count | Examples |
|----------|--------------|----------|
| Percentages | Gains, rates, lifts, completion rates, reductions | "Increased proficiency by 25%", "35% efficiency lift" |
| Currency / Financial | Budgets, grants, revenue, cost savings, funding | "$8M grant", "reduced costs by $400K" |
| Headcount / Scale | People trained, students served, sites managed, partners | "Trained 5,000 educators", "supervised 15 staff" |
| Years / Time | Years of experience, program durations, project timelines | "25 years", "3-year program", "launched in 2019" |
| Score Gains | Test score improvements, rating increases, rankings | "+12 points on state assessment" |
| Efficiency | Processing time reductions, speed improvements | "35% reduction in data processing time" |
| Volume / Output | Publications, certifications, projects, transactions | "47 publications", "230 certified" |
| Ratio / Rates | Compliance, engagement, satisfaction, accuracy | "100% compliance", "95% completion rate" |

---

## 3. The Impact Formula

A well-written accomplishment bullet follows this structure:

    [Action verb]  +  [Quantified result]  +  [Scale or context]  +  [Method or tool]

Example: Led a cross-functional team of 50 to grow annual revenue by 22% ($4M)
across 12 international sites by redesigning the incentive structure.

That one bullet contains four metrics: 50 people, 22%, $4M, 12 sites.

Rule of thumb: A bullet with no metrics is a duty statement, not an
accomplishment statement. Ask the user: How much? How many? Over what time?
With what budget?

---

## 4. JD Coverage Framework

When a job description is provided, map resume evidence to these domains.
Adjust the domain names to match the specific JD language.

| Domain | Resume Evidence to Look For |
|--------|-----------------------------|  
| Academic / Program Outcomes | Proficiency gains, mastery rates, completion rates, grade improvements |
| Operational Leadership | Efficiency gains, cost reductions, compliance rates, project timelines |
| People Leadership | Staff supervised, capacity built, retention rates, training delivered |
| Governance / Authorization | Policies adopted, compliance rates, board reporting, funding managed |
| Community / Culture | Partnerships established, stakeholder engagement, participation rates |
| Funding / Resources | Dollars secured or managed, grants won, ROI demonstrated |
| Research / Innovation | Publications, programs founded, frameworks designed, awards received |

Scoring: Count how many JD requirements have at least one quantified bullet
as evidence. Coverage % = evidenced requirements / total requirements x 100.

---

## 5. Gap Risk Classification

Use this table when flagging uncovered JD requirements.

| Risk Level | Meaning | Where to Address It |
|------------|---------|---------------------|
| High | A stated core responsibility with no evidence in the resume | Prepare a specific quantified story for the interview |
| Medium | Partially evidenced, or can be inferred from nearby bullets | Cover letter or leadership statement |
| Low | Soft skills, cultural fit, or location-specific requirements | Verbal in the interview |

---

## 6. Score Interpretation Notes

Density above 5.0 — Common in academic CVs and research-heavy resumes.
Appropriate for scientific roles. For general leadership positions, consider
whether the density is helping or overwhelming the reader.

Quantification rate above 100% — This is a calculation artifact. One bullet
can contain six metrics but is only counted once in Q. The script caps this at 100%.

Short resumes with fewer than 15 bullets — Density scores are more volatile
with small B values. Note the limited sample size in the report.

Career stage context:
- Early career: 1.0 to 2.0 (fewer measurable outcomes is normal)
- Mid-career: 2.0 to 3.5
- Executive or senior leadership: 3.0 to 6.0 and above
