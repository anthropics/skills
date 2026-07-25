# Product Management Frameworks

Comprehensive reference for prioritization, discovery, and measurement frameworks.

---

## Table of Contents

- [Prioritization Frameworks](#prioritization-frameworks)
  - [RICE Framework](#rice-framework)
  - [Value vs Effort Matrix](#value-vs-effort-matrix)
  - [MoSCoW Method](#moscow-method)
  - [ICE Scoring](#ice-scoring)
  - [Kano Model](#kano-model)
- [Discovery Frameworks](#discovery-frameworks)
  - [Customer Interview Guide](#customer-interview-guide)
  - [Hypothesis Template](#hypothesis-template)
  - [Opportunity Solution Tree](#opportunity-solution-tree)
  - [Jobs to Be Done](#jobs-to-be-done)
- [Metrics Frameworks](#metrics-frameworks)
  - [North Star Metric](#north-star-metric-framework)
  - [HEART Framework](#heart-framework)
  - [Funnel Analysis](#funnel-analysis-template)
  - [Feature Success Metrics](#feature-success-metrics)
- [Strategic Frameworks](#strategic-frameworks)
  - [Product Vision Template](#product-vision-template)
  - [Competitive Analysis](#competitive-analysis-framework)
  - [Go-to-Market Checklist](#go-to-market-checklist)

---

## Prioritization Frameworks

### RICE Framework

**Formula:**
```
RICE Score = (Reach × Impact × Confidence) / Effort
```

**Components:**

| Component | Description | Values |
|-----------|-------------|--------|
| **Reach** | Users affected per quarter | Numeric count (e.g., 5000) |
| **Impact** | Effect on each user | massive=3x, high=2x, medium=1x, low=0.5x, minimal=0.25x |
| **Confidence** | Certainty in estimates | high=100%, medium=80%, low=50% |
| **Effort** | Person-months required | xl=13, l=8, m=5, s=3, xs=1 |

**Example Calculation:**
```
Feature: Mobile Push Notifications
Reach: 10,000 users
Impact: massive (3x)
Confidence: medium (80%)
Effort: medium (5 person-months)

RICE = (10,000 × 3 × 0.8) / 5 = 4,800
```

**Interpretation Guidelines:**
- **1000+**: High priority - strong candidates for next quarter
- **500-999**: Medium priority - consider for roadmap
- **100-499**: Low priority - keep in backlog
- **<100**: Deprioritize - requires new data to reconsider

**When to Use RICE:**
- Quarterly roadmap planning
- Comparing features across different product areas
- Communicating priorities to stakeholders
- Resolving prioritization debates with data

**RICE Limitations:**
- Requires reasonable estimates (garbage in, garbage out)
- Doesn't account for dependencies
- May undervalue platform investments
- Reach estimates can be gaming-prone

---

### Value vs Effort Matrix

```
                  Low Effort          High Effort
                +--------------+------------------+
   High Value   |  QUICK WINS  |    BIG BETS      |
                |  [Do First]  |   [Strategic]    |
                +--------------+------------------+
   Low Value    |   FILL-INS   |   TIME SINKS     |
                |   [Maybe]    |    [Avoid]       |
                +--------------+------------------+
```

**Quadrant Definitions:**

| Quadrant | Characteristics | Action |
|----------|-----------------|--------|
| **Quick Wins** | High impact, low effort | Prioritize immediately |
| **Big Bets** | High impact, high effort | Plan strategically, validate ROI |
| **Fill-Ins** | Low impact, low effort | Use to fill sprint gaps |
| **Time Sinks** | Low impact, high effort | Avoid unless required |

**Portfolio Balance:**
- Ideal mix: 40% Quick Wins, 30% Big Bets, 20% Fill-Ins, 10% Buffer
- Review balance quarterly
- Adjust based on team morale and strategic goals

---

### MoSCoW Method

| Category | Definition | Sprint Allocation |
|----------|------------|-------------------|
| **Must Have** | Critical for launch; product fails without it | 60% of capacity |
| **Should Have** | Important but workarounds exist | 20% of capacity |
| **Could Have** | Desirable enhancements | 10% of capacity |
| **Won't Have** | Explicitly out of scope (this release) | 0% - documented |

**Decision Criteria for "Must Have":**
- Regulatory/legal requirement
- Core user job cannot be completed without it
- Explicitly promised to customers
- Security or data integrity requirement

**Common Mistakes:**
- Everything becomes "Must Have" (scope creep)
- Not documenting "Won't Have" items
- Treating "Should Have" as optional (they're important)
- Forgetting to revisit for next release

---

### ICE Scoring

**Formula:**
```
ICE Score = (Impact + Confidence + Ease) / 3
```

| Component | Scale | Description |
|-----------|-------|-------------|
| **Impact** | 1-10 | Expected effect on key metric |
| **Confidence** | 1-10 | How sure are you about impact? |
| **Ease** | 1-10 | How easy to implement? |

**When to Use ICE vs RICE:**
- ICE: Early-stage exploration, quick estimates
- RICE: Quarterly planning, cross-team prioritization

---

### Kano Model

Categories of feature satisfaction:

| Type | Absent | Present | Priority |
|------|--------|---------|----------|
| **Basic (Must-Be)** | Dissatisfied | Neutral | High - table stakes |
| **Performance (Linear)** | Neutral | Satisfied proportionally | Medium - differentiation |
| **Excitement (Delighter)** | Neutral | Very satisfied | Strategic - competitive edge |
| **Indifferent** | Neutral | Neutral | Low - skip unless cheap |
| **Reverse** | Satisfied | Dissatisfied | Avoid - remove if exists |

**Feature Classification Questions:**
1. How would you feel if the product HAS this feature?
2. How would you feel if the product DOES NOT have this feature?

---

## Discovery Frameworks

### Customer Interview Guide

**Structure (35 minutes total):**

```
1. CONTEXT QUESTIONS (5 min)
   └── Build rapport, understand role

2. PROBLEM EXPLORATION (15 min)
   └── Dig into pain points

3. SOLUTION VALIDATION (10 min)
   └── Test concepts if applicable

4. WRAP-UP (5 min)
   └── Referrals, follow-up
```

**Detailed Script:**

#### Phase 1: Context (5 min)
```
"Thanks for taking the time. Before we dive in..."

- What's your role and how long have you been in it?
- Walk me through a typical day/week.
- What tools do you use for [relevant task]?
```

#### Phase 2: Problem Exploration (15 min)
```
"I'd love to understand the challenges you face with [area]..."

- What's the hardest part about [task]?
- Can you tell me about the last time you struggled with this?
- What did you do? What happened?
- How often does this happen?
- What does it cost you (time, money, frustration)?
- What have you tried to solve it?
- Why didn't those solutions work?
```

#### Phase 3: Solution Validation (10 min)
```
"Based on what you've shared, I'd like to get your reaction to an idea..."

[Show prototype/concept - keep it rough to invite honest feedback]

- What's your initial reaction?
- How does this compare to what you do today?
- What would prevent you from using this?
- How much would this be worth to you?
- Who else would need to approve this purchase?
```

#### Phase 4: Wrap-up (5 min)
```
"This has been incredibly helpful..."

- Anything else I should have asked?
- Who else should I talk to about this?
- Can I follow up if I have more questions?
```

**Interview Best Practices:**
- Never ask "would you use this?" (people lie about future behavior)
- Ask about past behavior: "Tell me about the last time..."
- Embrace silence - count to 7 before filling gaps
- Watch for emotional reactions (pain = opportunity)
- Record with permission; take minimal notes during

---

### Hypothesis Template

**Format:**
```
We believe that [building this feature/making this change]
For [target user segment]
Will [achieve this measurable outcome]

We'll know we're right when [specific metric moves by X%]

We'll know we're wrong when [falsification criteria]
```

**Example:**
```
We believe that adding saved payment methods
For returning customers
Will increase checkout completion rate

We'll know we're right when checkout completion increases by 15%

We'll know we're wrong when completion rate stays flat after 2 weeks
or saved payment adoption is < 20%
```

**Hypothesis Quality Checklist:**
- [ ] Specific user segment defined
- [ ] Measurable outcome (number, not "better")
- [ ] Timeframe for measurement
- [ ] Clear falsification criteria
- [ ] Based on evidence (interviews, data)

---

### Opportunity Solution Tree

**Structure:**
```
[DESIRED OUTCOME]
        │
        ├── Opportunity 1: [User problem/need]
        │   ├── Solution A
        │   ├── Solution B
        │   └── Experiment: [Test to validate]
        │
        ├── Opportunity 2: [User problem/need]
        │   ├── Solution C
        │   └── Solution D
        │
        └── Opportunity 3: [User problem/need]
            └── Solution E
```

**Example:**
```
[Increase monthly active users by 20%]
        │
        ├── Users forget to return
        │   ├── Weekly email digest
        │   ├── Mobile push notifications
        │   └── Test: A/B email frequency
        │
        ├── New users don't find value quickly
        │   ├── Improved onboarding wizard
        │   └── Personalized first experience
        │
        └── Users churn after free trial
            ├── Extended trial for engaged users
            └── Friction audit of upgrade flow
```

**Process:**
1. Start with measurable outcome (not solution)
2. Map opportunities from user research
3. Generate multiple solutions per opportunity
4. Design small experiments to validate
5. Prioritize based on learning potential

---

### Jobs to Be Done

**JTBD Statement Format:**
```
When [situation/trigger]
I want to [motivation/job]
So I can [expected outcome]
```

**Example:**
```
When I'm running late for a meeting
I want to notify attendees quickly
So I can set appropriate expectations and reduce anxiety
```

**Force Diagram:**
```
                    ┌─────────────────┐
     Push from      │                 │     Pull toward
     current ──────>│    SWITCH       │<────── new
     solution       │    DECISION     │       solution
                    │                 │
                    └─────────────────┘
                           ^   ^
                           |   |
              Anxiety of   |   |   Habit of
              change ──────┘   └────── status quo
```

**Interview Questions for JTBD:**
- When did you first realize you needed something like this?
- What were you using before? Why did you switch?
- What almost prevented you from switching?
- What would make you go back to the old way?

---

## Metrics Frameworks

### North Star Metric Framework

**Criteria for a Good NSM:**
1. **Measures value delivery**: Captures what users get from product
2. **Leading indicator**: Predicts business success
3. **Actionable**: Teams can influence it
4. **Measurable**: Trackable on regular cadence

**Examples by Business Type:**

| Business | North Star Metric | Why |
|----------|-------------------|-----|
| Spotify | Time spent listening | Measures engagement value |
| Airbnb | Nights booked | Core transaction metric |
| Slack | Messages sent in channels | Team collaboration value |
| Dropbox | Files stored/synced | Storage utility delivered |
| Netflix | Hours watched | Entertainment value |

**Supporting Metrics Structure:**
```
[NORTH STAR METRIC]
        │
        ├── Breadth: How many users?
        ├── Depth: How engaged are they?
        └── Frequency: How often do they engage?
```

---

### HEART Framework

| Metric | Definition | Example Signals |
|--------|------------|-----------------|
| **Happiness** | Subjective satisfaction | NPS, CSAT, survey scores |
| **Engagement** | Depth of involvement | Session length, actions/session |
| **Adoption** | New user behavior | Signups, feature activation |
| **Retention** | Continued usage | D7/D30 retention, churn rate |
| **Task Success** | Efficiency & effectiveness | Completion rate, time-on-task, errors |

**Goals-Signals-Metrics Process:**
1. **Goal**: What user behavior indicates success?
2. **Signal**: How would success manifest in data?
3. **Metric**: How do we measure the signal?

**Example:**
```
Feature: New checkout flow

Goal: Users complete purchases faster
Signal: Reduced time in checkout, fewer drop-offs
Metrics:
  - Median checkout time (target: <2 min)
  - Checkout completion rate (target: 85%)
  - Error rate (target: <2%)
```

---

### Funnel Analysis Template

**Standard Funnel:**
```
Acquisition → Activation → Retention → Revenue → Referral
    │             │            │           │          │
    │             │            │           │          │
  How do      First        Come back    Pay for    Tell
  they find   "aha"        regularly     value     others
  you?        moment
```

**Metrics per Stage:**

| Stage | Key Metrics | Typical Benchmark |
|-------|-------------|-------------------|
| **Acquisition** | Visitors, CAC, channel mix | Varies by channel |
| **Activation** | Signup rate, onboarding completion | 20-30% visitor→signup |
| **Retention** | D1/D7/D30 retention, churn | D1: 40%, D7: 20%, D30: 10% |
| **Revenue** | Conversion rate, ARPU, LTV | 2-5% free→paid |
| **Referral** | NPS, viral coefficient, referrals/user | NPS > 50 is excellent |

**Analysis Framework:**
1. Map current conversion rates at each stage
2. Identify biggest drop-off point
3. Qualitative research: Why are users leaving?
4. Hypothesis: What would improve conversion?
5. Test and measure

---

### Feature Success Metrics

| Metric | Definition | Target Range |
|--------|------------|--------------|
| **Adoption** | % users who try feature | 30-50% within 30 days |
| **Activation** | % who complete core action | 60-80% of adopters |
| **Frequency** | Uses per user per time | Weekly for engagement features |
| **Depth** | % of feature capability used | 50%+ of core functionality |
| **Retention** | Continued usage over time | 70%+ at 30 days |
| **Satisfaction** | Feature-specific NPS/rating | NPS > 30, Rating > 4.0 |

**Measurement Cadence:**
- **Week 1**: Adoption and initial activation
- **Week 4**: Retention and depth
- **Week 8**: Long-term satisfaction and business impact

---

## Strategic Frameworks

### Product Vision Template

**Format:**
```
FOR [target customer]
WHO [statement of need or opportunity]
THE [product name] IS A [product category]
THAT [key benefit, compelling reason to use]
UNLIKE [primary competitive alternative]
OUR PRODUCT [statement of primary differentiation]
```

**Example:**
```
FOR busy professionals
WHO need to stay informed without information overload
Briefme IS A personalized news digest
THAT delivers only relevant stories in 5 minutes
UNLIKE traditional news apps that require active browsing
OUR PRODUCT learns your interests and filters automatically
```

---

### Competitive Analysis Framework

| Dimension | Us | Competitor A | Competitor B |
|-----------|----|--------------|--------------|
| **Target User** | | | |
| **Core Value Prop** | | | |
| **Pricing** | | | |
| **Key Features** | | | |
| **Strengths** | | | |
| **Weaknesses** | | | |
| **Market Position** | | | |

**Strategic Questions:**
1. Where do we have parity? (table stakes)
2. Where do we differentiate? (competitive advantage)
3. Where are we behind? (gaps to close or ignore)
4. What can only we do? (unique capabilities)

---

### Go-to-Market Checklist

**Pre-Launch (4 weeks before):**
- [ ] Success metrics defined and instrumented
- [ ] Launch/rollback criteria established
- [ ] Support documentation ready
- [ ] Sales enablement materials complete
- [ ] Marketing assets prepared
- [ ] Beta feedback incorporated

**Launch Week:**
- [ ] Staged rollout plan (1% → 10% → 50% → 100%)
- [ ] Monitoring dashboards live
- [ ] On-call rotation scheduled
- [ ] Communications ready (in-app, email, blog)
- [ ] Support team briefed

**Post-Launch (2 weeks after):**
- [ ] Metrics review vs. targets
- [ ] User feedback synthesized
- [ ] Bug/issue triage complete
- [ ] Iteration plan defined
- [ ] Stakeholder update sent

---

## Framework Selection Guide

| Situation | Recommended Framework |
|-----------|----------------------|
| Quarterly roadmap planning | RICE + Portfolio Matrix |
| Sprint-level prioritization | MoSCoW |
| Quick feature comparison | ICE |
| Understanding user satisfaction | Kano |
| User research synthesis | JTBD + Opportunity Tree |
| Feature experiment design | Hypothesis Template |
| Success measurement | HEART + Feature Metrics |
| Strategy communication | North Star + Vision |

---

*Last Updated: January 2025*
