# Use Case Scoring Guide

Use this rubric to score each use case consistently across all 7 dimensions.
Each dimension is scored 1–5. Be calibrated — a 5 should be rare.

---

## 1. Business Impact (Weight: 25%)

How significantly does this use case move a business-critical metric?

| Score | Criteria |
|---|---|
| 5 | Directly moves a top-line metric (revenue, core conversion, critical retention). Order-of-magnitude improvement plausible. Exec-level visibility. |
| 4 | Moves an important operational metric (cost per unit, support volume, processing time). Clear ROI calculation possible. |
| 3 | Improves a secondary metric (user satisfaction, feature adoption, internal productivity). Business case requires some assumptions. |
| 2 | Nice-to-have enhancement. Hard to attribute directly to a business outcome. |
| 1 | Unclear or speculative business value. "AI for AI's sake." |

---

## 2. Data Feasibility (Weight: 20%)

Is the required data available, sufficient, and accessible today?

| Score | Criteria |
|---|---|
| 5 | Data exists, is clean, is accessible via API or SQL, has sufficient volume and history, and is already being used for analytics. |
| 4 | Data exists and is mostly clean but requires some pipeline work to make accessible. Minor quality issues. |
| 3 | Data exists but has significant quality issues, requires labeling effort, or is siloed and requires cross-team coordination. |
| 2 | Data partially exists. Major gaps — missing labels, insufficient history, or significant engineering work needed to surface it. |
| 1 | Data doesn't exist yet, would need to be created, or is inaccessible due to governance/legal constraints. |

---

## 3. Technical Feasibility (Weight: 15%)

Can the AI component be built and integrated given the current architecture and constraints?

| Score | Criteria |
|---|---|
| 5 | Solved problem — standard ML/AI approach, fits the infrastructure, latency requirements are achievable, no novel research needed. |
| 4 | Well-understood approach, minor infrastructure gaps to address. Some engineering work but no unknowns. |
| 3 | Requires non-trivial infrastructure changes or involves some technical uncertainty. Achievable but not straightforward. |
| 2 | Significant technical unknowns. May require research, new infrastructure, or approaches that haven't been validated at this team's scale. |
| 1 | Technically immature, requires GPU compute not available, latency requirements cannot be met, or integration would require breaking architectural changes. |

---

## 4. Org Readiness (Weight: 15%)

Can the team actually build, ship, and maintain this?

| Score | Criteria |
|---|---|
| 5 | Team has shipped AI features before, has dedicated ML/AI engineers, has MLOps tooling, and leadership is committed. |
| 4 | Team has some AI experience, can augment with contractors or APIs, has basic monitoring capabilities. |
| 3 | Team is capable but stretched. Would need upskilling, a new hire, or significant external support. |
| 2 | Team has no AI experience. Success depends on learning on the job or significant external dependency. |
| 1 | Org is actively resistant, has no AI talent, no tooling, and no leadership mandate. |

---

## 5. Risk Level (Weight: 10%) — INVERTED (lower risk = higher score)

What is the consequence and likelihood of AI failure?

| Score | Criteria |
|---|---|
| 5 | Low risk. Errors are invisible or inconsequential. No regulatory exposure. Easily reversible. User is not harmed by a wrong output. |
| 4 | Manageable risk. Errors are visible but low-stakes. Minor regulatory considerations. Easily correctable. |
| 3 | Moderate risk. Errors could cause user frustration or minor financial impact. Some regulatory scrutiny possible. Requires monitoring. |
| 2 | High risk. Errors could cause significant financial, reputational, or legal harm. Requires human-in-the-loop. Compliance review needed. |
| 1 | Critical risk. AI failure could cause safety issues, major regulatory violations, or irreversible harm to users or business. Requires extensive safeguards before deployment. |

---

## 6. Time to Value (Weight: 10%)

How quickly can this use case generate measurable value?

| Score | Criteria |
|---|---|
| 5 | Prototype in ≤2 weeks, production-ready in ≤2 months. Simple integration, existing data, well-understood approach. |
| 4 | Prototype in 1 month, production in 3–4 months. Moderate integration complexity. |
| 3 | Prototype in 6–8 weeks, production in 5–6 months. Some infrastructure or data prep needed. |
| 2 | Prototype in 3+ months, production in 9–12 months. Significant work before any signal of value. |
| 1 | Long-horizon investment. Value may not be realized for 12+ months. High execution risk. |

---

## 7. Novelty / Competitive Moat (Weight: 5%)

Does this create differentiation, or is it commodity AI?

| Score | Criteria |
|---|---|
| 5 | Unique to this product — requires proprietary data or proprietary workflow. Would take competitors 12+ months to replicate meaningfully. |
| 4 | Differentiated in implementation even if the concept isn't novel. Proprietary data creates a defensible edge. |
| 3 | Moderately differentiated. Competitors could replicate in 6–12 months with effort. |
| 2 | Low differentiation. Several competitors already offer equivalent capability. Table stakes in 12–18 months. |
| 1 | Pure commodity. Available off-the-shelf from multiple vendors. No moat created. |

---

## Composite Score Calculation

```
Score = (Impact × 0.25) + (Data × 0.20) + (Tech × 0.15) + (Org × 0.15) 
      + (Risk × 0.10) + (TTV × 0.10) + (Moat × 0.05)
```

**Interpretation:**
- **4.0–5.0**: Green light. High priority. Activate immediately.
- **3.0–3.9**: Conditional. Address the lowest-scoring dimension before proceeding.
- **2.0–2.9**: Deferred. Needs a prerequisite to be resolved first.
- **1.0–1.9**: Not now. Revisit in 12+ months or deprioritize.

---

## Readiness Tier Quick Reference

| Tier | Overall Score Across Axes | Recommended Sourcing |
|---|---|---|
| Tier 1 | Data ≤ 2 AND/OR Org ≤ 2 | API Wrap only. No custom training. |
| Tier 2 | Data 3, Org 3, Tooling 3 | RAG, fine-tuning, prompt engineering |
| Tier 3 | Data 4+, Org 4+, Tooling 4+ | Full spectrum including custom model training |