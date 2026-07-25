# Pipeline Management Framework

Best practices for pipeline management including stage definitions, conversion benchmarks, velocity optimization, and inspection cadence.

---

## Pipeline Stage Definitions

A well-defined pipeline requires clear, observable exit criteria at each stage. Subjective stages lead to inaccurate forecasting and unreliable conversion data.

### Recommended Stage Model (B2B SaaS)

| Stage | Name | Exit Criteria | Probability | Typical Duration |
|-------|------|--------------|-------------|-----------------|
| S0 | Lead | Contact identified, initial interest signal | 5% | 0-7 days |
| S1 | Discovery | Pain identified, budget confirmed, stakeholder engaged | 10% | 7-14 days |
| S2 | Qualification | MEDDPICC criteria met, mutual action plan created | 20% | 14-21 days |
| S3 | Proposal | Solution presented, pricing delivered, champion confirmed | 40% | 7-14 days |
| S4 | Negotiation | Commercial terms discussed, legal engaged, verbal commitment | 60% | 7-21 days |
| S5 | Commit | Contract redlined, signature timeline confirmed | 80% | 3-7 days |
| S6 | Closed Won | Signed contract received | 100% | -- |
| SL | Closed Lost | Deal disposition recorded with loss reason | 0% | -- |

### Stage Exit Criteria Best Practices

**Discovery (S1) Exit Criteria:**
- Pain point articulated by prospect (not assumed by rep)
- Budget range discussed (even if informal)
- Decision-making process understood
- Next meeting scheduled with clear agenda

**Qualification (S2) Exit Criteria:**
- MEDDPICC or BANT qualification framework completed
- Economic buyer identified (not just champion)
- Compelling event or timeline identified
- Mutual action plan (MAP) shared and agreed upon
- Technical requirements understood

**Proposal (S3) Exit Criteria:**
- Solution demo completed and well-received
- Pricing proposal delivered
- Champion validated proposal internally
- Competitive landscape understood
- No unresolved technical blockers

**Negotiation (S4) Exit Criteria:**
- Commercial terms discussed (not just pricing, but payment terms, SLA, etc.)
- Legal review initiated
- Security/procurement review started
- Verbal agreement on core terms
- Close date confirmed within 30 days

**Commit (S5) Exit Criteria:**
- Final contract sent for signature
- All legal redlines resolved
- Procurement approval obtained
- Signature expected within 7 business days

---

## Conversion Benchmarks by Segment

### SMB (ACV <$25K)

| Transition | Benchmark | Top Quartile |
|-----------|-----------|--------------|
| Lead to Discovery | 20-30% | 35%+ |
| Discovery to Qualification | 40-50% | 55%+ |
| Qualification to Proposal | 50-60% | 65%+ |
| Proposal to Negotiation | 55-65% | 70%+ |
| Negotiation to Close | 65-75% | 80%+ |
| Overall Win Rate | 20-30% | 35%+ |
| Avg Cycle Length | 14-30 days | <14 days |

### Mid-Market (ACV $25K-$100K)

| Transition | Benchmark | Top Quartile |
|-----------|-----------|--------------|
| Lead to Discovery | 15-25% | 30%+ |
| Discovery to Qualification | 35-45% | 50%+ |
| Qualification to Proposal | 45-55% | 60%+ |
| Proposal to Negotiation | 50-60% | 65%+ |
| Negotiation to Close | 60-70% | 75%+ |
| Overall Win Rate | 15-25% | 30%+ |
| Avg Cycle Length | 30-60 days | <30 days |

### Enterprise (ACV >$100K)

| Transition | Benchmark | Top Quartile |
|-----------|-----------|--------------|
| Lead to Discovery | 10-20% | 25%+ |
| Discovery to Qualification | 30-40% | 45%+ |
| Qualification to Proposal | 40-50% | 55%+ |
| Proposal to Negotiation | 45-55% | 60%+ |
| Negotiation to Close | 55-65% | 70%+ |
| Overall Win Rate | 10-20% | 25%+ |
| Avg Cycle Length | 60-120 days | <60 days |

---

## Sales Velocity Optimization

Sales velocity = (# Opportunities x Avg Deal Size x Win Rate) / Avg Cycle Days

Each component is an optimization lever:

### Lever 1: Increase Opportunity Volume

**Strategies:**
- Invest in inbound marketing (content, SEO, paid)
- Scale outbound SDR capacity
- Develop partner/channel sourcing
- Launch product-led growth (PLG) motion
- Implement customer referral programs

**Measurement:** Pipeline created ($) per week/month, by source

### Lever 2: Increase Average Deal Size

**Strategies:**
- Multi-product bundling and packaging
- Usage-based pricing with growth triggers
- Land-and-expand with defined expansion playbooks
- Move upmarket with enterprise features
- Value-based pricing tied to customer outcomes

**Measurement:** ACV trend by quarter, by segment

### Lever 3: Increase Win Rate

**Strategies:**
- Implement MEDDPICC qualification rigor
- Build competitive battle cards and train on them
- Create multi-threaded relationships (not single-threaded)
- Develop ROI/business case tools
- Invest in sales engineering and demo quality
- Win/loss analysis with structured debriefs

**Measurement:** Win rate by stage entry, by competitor, by rep

### Lever 4: Decrease Sales Cycle Length

**Strategies:**
- Pre-qualify harder at S1/S2 to remove slow deals
- Mutual action plans with milestone dates
- Champion enablement (arm champions with internal selling materials)
- Parallel processing (legal/security review concurrent with evaluation)
- Standardized contracts and pre-approved terms
- Executive sponsor engagement for stuck deals

**Measurement:** Days in each stage, cycle length trend, stage-specific bottlenecks

---

## Pipeline Inspection Cadence

### Daily (Rep Level)

**Focus:** Deal-level activity and next steps

**Questions:**
- What is the next step for each deal in S3+?
- Are any deals missing next steps or scheduled meetings?
- Which deals have not been updated in >3 days?

### Weekly (Manager/Team Level)

**Focus:** Pipeline health and forecast accuracy

**Review Format (45-60 minutes):**

1. **Coverage Check (10 min)**
   - Current pipeline vs. quota -- is coverage >3x?
   - Pipeline created this week vs. target
   - Net pipeline change (created minus closed minus lost)

2. **Deal Inspection (25 min)**
   - Walk top 10 deals by value in S3+
   - MEDDPICC validation for each commit deal
   - Identify deals at risk (aging, single-threaded, no next step)

3. **Forecast Call (10 min)**
   - Commit, best case, and pipeline forecast
   - Changes from last week's forecast (what moved and why)
   - Gaps to plan and remediation

4. **Action Items (5 min)**
   - Deals needing executive engagement
   - Pipeline generation actions for next week
   - Coaching priorities

### Monthly (Leadership Level)

**Focus:** Pipeline trends, velocity, and efficiency

**Review Areas:**
- Month-over-month pipeline growth trend
- Conversion rate trends by stage
- Sales velocity trend (improving or declining?)
- Forecast accuracy (MAPE) for the month
- Rep performance distribution (quartile analysis)
- Pipeline source mix health

### Quarterly (Executive/Board Level)

**Focus:** GTM efficiency and strategic pipeline

**Review Areas:**
- Pipeline coverage for next 2-3 quarters
- LTV:CAC and Magic Number trends
- Sales efficiency ratio trends
- Market segment performance comparison
- New market/product pipeline contribution
- Competitive win/loss trends

---

## Pipeline Hygiene

### Deal Hygiene Standards

1. **Close date accuracy:** Close dates must be based on buyer commitment, not rep hope. Any deal pushed more than twice should be flagged for re-qualification.

2. **Stage accuracy:** Deals must meet exit criteria to be in a stage. No deal should be in Proposal (S3) without a pricing deliverable sent.

3. **Amount accuracy:** Deal amounts must reflect the current proposal, not aspirational upsell. Variance between deal value and proposal should be <10%.

4. **Contact coverage:** Deals >$50K should have 3+ contacts associated. Enterprise deals should have economic buyer, champion, and technical evaluator.

5. **Activity recency:** No deal should go 7+ days without logged activity. Deals without recent activity signal stalling.

### Pipeline Cleanup Triggers

Run cleanup when:
- Pipeline-to-quota ratio drops below 2.5x
- Forecast accuracy (MAPE) exceeds 20%
- More than 15% of pipeline is >90 days old
- Average deal age exceeds 1.5x normal cycle time

### Cleanup Process

1. Flag all deals with close date in the past
2. Flag all deals with no activity in 14+ days
3. Flag all deals pushed 3+ times
4. Rep self-assessment: keep, push, or close for each flagged deal
5. Manager review and disposition
6. Update CRM and recalculate metrics

---

## Pipeline Risk Indicators

### Concentration Risk

**Definition:** Over-reliance on a small number of large deals.

**Thresholds:**
- Single deal >40% of pipeline = HIGH risk
- Single deal >25% of pipeline = MEDIUM risk
- Top 3 deals >70% of pipeline = HIGH risk

**Mitigation:** Diversify pipeline across segments, deal sizes, and sources. Increase deal count even if average deal size decreases.

### Stage Imbalance Risk

**Definition:** Pipeline is concentrated in early or late stages with gaps in between.

**Healthy Distribution:**
- Discovery/Qualification: 50-60% of pipeline value
- Proposal: 20-25% of pipeline value
- Negotiation/Commit: 15-20% of pipeline value

**Warning Signs:**
- >70% in early stages = insufficient progression
- >50% in late stages = insufficient pipeline generation
- Empty stages = broken funnel mechanics

### Temporal Risk

**Definition:** Pipeline is concentrated in a single quarter or lacks coverage for future quarters.

**Standard:** Maintain 3x coverage for current quarter and 1.5x for next quarter.

### Source Risk

**Definition:** Pipeline is overly dependent on a single source (e.g., 80% outbound, 0% inbound).

**Healthy Mix (varies by stage):**
- Inbound/Marketing: 30-40%
- Outbound/SDR: 30-40%
- Partner/Channel: 10-20%
- Expansion/Customer: 10-20%
