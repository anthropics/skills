# Engineering Hiring Funnel — The Decision: "Where is our hiring funnel leaking, and what do we fix?"

This reference answers exactly one decision: **at which stage is our hiring funnel underperforming, what's the typical fix, and how much top-of-funnel volume do we need?**

Pair with `scripts/eng_hiring_funnel_calculator.py` for automation.

## The Trap

> "We can't find good engineers."

Almost always wrong as stated. The actual problem is:
- Top-of-funnel volume is too low (sourcing channel limited)
- A specific stage is over-filtering (criteria too strict, or wrong criteria)
- A specific stage is under-filtering (people advance who shouldn't, wasting later stages)
- Offer-to-accept rate is poor (comp, close discipline, or speed)

Diagnose specifically; don't recruit a different recruiter.

## The 7-Stage Funnel

| Stage | What happens | Healthy conversion |
|---|---|---|
| Applied | Candidate submits resume | (top of funnel) |
| Sourcer screen | Sourcer reviews resume + does initial qualifying call | 30-50% |
| Recruiter screen | Recruiter does 30-min call (basic fit, motivation, comp expectations) | 50-70% |
| Hiring manager screen | 30-min call with the engineering hiring manager (team fit, level check) | 60-80% |
| Technical interview | 60-90 min technical assessment (live coding, system design, or take-home) | 70-85% |
| Onsite (full loop) | 4-6 interviews covering technical depth + behavioral + team fit | 30-50% |
| Offer extended | Final go decision; offer letter generated | 25-40% |
| Offer accepted | Candidate accepts and signs | 70-90% |

**End-to-end conversion:** multiplying healthy ranges gives roughly 0.5-3% conversion from Applied to Accepted, depending on stage and role level.

**To hire N engineers, you need roughly N / (end-to-end conversion) candidates at top of funnel.** Example: 4 hires × 1% end-to-end = 400 candidates needed.

## Common Leakage Points

### Leakage at applied → sourcer screen (< 30%)

**Diagnosis:** top-of-funnel volume is too noisy, OR resume quality is low.

**Fixes:**
- Diversify sourcing channels (cap inbound at 50%; the rest via direct sourcing + referrals + community)
- Tighten the job description (specific must-haves; remove generic language)
- If volume is low, broaden the JD (remove unnecessary "must-have"s)

### Leakage at sourcer → recruiter (< 50%)

**Diagnosis:** sourcer is over-filtering OR not calibrated with the recruiter.

**Fixes:**
- Recruiter and sourcer review rejected candidates weekly for first month
- Document explicit ICP rubric (must-haves vs nice-to-haves)
- Sourcer attends first 5 recruiter screens to calibrate

### Leakage at recruiter → hiring manager (< 60%)

**Diagnosis:** recruiter and hiring manager disagree on criteria, OR the recruiter is selling the role poorly.

**Fixes:**
- Hiring manager attends first 5 recruiter screens
- Document explicit advance-vs-reject criteria
- Recruiter selling skills training (motivation, comp expectations, narrative)

### Leakage at hiring manager → technical (< 70%)

**Diagnosis:** hiring manager screen too lenient OR technical bar is being applied at the wrong stage.

**Fixes:**
- Define explicit advance criteria for the hiring manager call
- Cap hiring manager screen at 30 min; technical bar comes next
- Hiring manager rejects on team fit + level, not technical depth

### Leakage at technical → onsite (< 30%)

**Diagnosis:** technical bar too high for the level, OR interview is filtering for wrong skills.

**Fixes:**
- Calibrate technical interviewers; rotate to avoid one strict gatekeeper
- Match interview style to the job (algorithms for SWE, system design for senior, integration work for full-stack roles)
- Use a clear rubric; require independent scoring before debrief

### Leakage at onsite → offer (< 25%)

**Diagnosis:** onsite results are inconsistent (anchoring bias from first interviewer), OR the loop is too long (interviewer fatigue).

**Fixes:**
- Structured rubrics; independent scoring before debrief
- Limit loops to 4-5 interviews max
- Designate a hiring manager facilitator for the debrief

### Leakage at offer → accept (< 70%)

**Diagnosis:** comp is below market, close discipline is weak, or offer letter is too slow.

**Fixes:**
- Run `cs-chro-advisor`'s `comp_benchmarker.py` to check competitiveness
- VPE / hiring manager personally calls candidates to close (within 24h of offer)
- Same-day or next-day offer letter delivery

## Pipeline Volume Math

To hit a hiring target, work backwards from end-to-end conversion:

**Pipeline volume needed = hiring target / end-to-end conversion rate**

Example: 4 hires per quarter at 1% end-to-end conversion = 400 candidates at top of funnel per quarter ≈ 130 per month ≈ 30 per week.

If sourcing isn't delivering 30 candidates per week, the hiring plan is unrealistic. Diagnose sourcing channels:

- Inbound (job board, careers page) — 30-50% of pipeline typical
- Outbound (direct sourcing) — 30-50%
- Referrals — 10-30% (and highest conversion!)
- Recruiting agencies — 0-20% (variable quality, premium cost)
- Community / events — 5-15% (slow but very high quality)

**Diversify.** A single-channel pipeline is fragile.

## Time-to-Fill Discipline

Median time-to-fill in B2B SaaS: 45-70 days for engineering roles (longer for senior + specialized).

**Where time accumulates:**

- Sourcing: 14-21 days (until you find a good candidate)
- Screen + first round: 7-14 days
- Technical + onsite: 7-14 days
- Offer + close: 7-14 days

**If you're > 90 days, the candidate has competing offers and you've lost speed advantage.** Focus on speed where possible without sacrificing rigor:
- Schedule next-stage interviews while previous-stage feedback is fresh
- Offer letters within 24 hours of "yes" decision
- Background checks and reference checks in parallel with offer

## Technical Interview Design

The technical bar is where most teams over-engineer.

**Principle:** test what the engineer will actually do on the job.

- **SWE roles:** mix of system design + practical coding (not LeetCode-hard algorithms; mid-difficulty data structures with clean code emphasis)
- **Senior / staff:** more system design + architecture; less coding velocity
- **Full-stack / product engineer:** integration work, debugging, working with messy real-world code
- **ML engineer:** model deployment + production debugging, NOT research-level ML theory
- **Platform engineer:** infra design, debugging distributed systems

**Anti-pattern:** asking SWE candidates to design Twitter from scratch. They won't, and the test doesn't predict job performance.

## Cost-per-Hire

Includes recruiter time, hiring manager time, agency fees, signing bonuses, and ramp time.

**B2B SaaS baseline:** $20K-50K per engineer hire, with senior + specialized roles approaching $80K (especially if using executive search firms).

**Reduce by:**
- Referral program (cheapest source, highest conversion)
- Strong careers page + employer brand (inbound costs less)
- Internal mobility (no recruiting cost; high success rate)

## When This Reference Doesn't Help

- **Comp benchmarking specifics.** See `c-level-advisor/skills/chro-advisor/scripts/comp_benchmarker.py`.
- **Leveling ladders.** See `c-level-advisor/skills/chro-advisor/references/leveling_ladders.md`.
- **ATS tooling selection (Greenhouse / Lever / Ashby / etc.).** Tactical.
- **Diversity + inclusion in hiring.** Important; not covered here; standard HR best practice.
- **Visa / immigration logistics.** Specialist legal territory.

This reference is about diagnosing funnel performance and choosing fixes, not about HR mechanics.

---

**Source authorities (non-exhaustive):**

- LinkedIn Talent Insights — annual benchmarks for tech hiring funnels by region + role
- Atlassian Recruiting Operations blog — public conversion rate data + interview design patterns
- Levels.fyi + Pave — comp benchmarks that affect offer-to-accept rates
- Lou Adler — "Hire With Your Head" (3rd ed., 2007) — behavioral interview design
- Adler, Bock — "Work Rules!" (Google) — structured interview research
- Carnegie Mellon / Booth research on interview validity — coding tests + structured rubrics outperform unstructured interviews
- Annual SHRM surveys on time-to-fill and cost-per-hire benchmarks
