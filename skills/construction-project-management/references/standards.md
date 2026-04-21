# Construction Project Management Standards & Reference

## Project Management Frameworks

### PMBOK (Project Management Body of Knowledge)

Standard framework covering:

- **Integration**: Coordinate all aspects of project
- **Scope**: Define and control what's included
- **Schedule**: Plan and control timeline
- **Cost**: Estimate and control budget
- **Quality**: Plan and monitor deliverables
- **Resource**: Plan and manage team
- **Communication**: Share information effectively
- **Risk**: Identify and manage uncertainties
- **Procurement**: Acquire external resources
- **Stakeholder**: Engage and manage stakeholders

### Construction-Specific Standards

**BS 6046 (UK Standard)**

- Project phases and governance
- Roles and responsibilities
- Document management
- Change control procedures

**RIBA Stages (Architect's Plan of Work)**

- Stage 0: Strategic Definition
- Stage 1: Preparation & Brief
- Stage 2: Concept Design
- Stage 3: Spatial Coordination
- Stage 4: Technical Design
- Stage 5: Manufacturing & Construction
- Stage 6: Handover
- Stage 7: Use

## Work Breakdown Structure (WBS) Hierarchy

### Level 1: Project (Overall)

Total project scope and budget

### Level 2: Phase (Major segments)

```
Phase 1: Mobilization & Site Setup
Phase 2: Groundwork & Foundations
Phase 3: Structural Works
Phase 4: MEP Systems
Phase 5: Finishes
Phase 6: Testing & Handover
```

### Level 3: Package (Activity groups)

```
Groundwork Package:
  - Excavation
  - Foundation Design & Procurement
  - Foundation Construction
  - Backfill & Site Preparation
```

### Level 4: Activity (Specific tasks)

```
Foundation Construction:
  - Excavate Foundation Trenches
  - Place Reinforcement
  - Pour Concrete
  - Strip Formwork
  - Cure & Test
```

### Level 5: Task (Operational details - optional)

Fine-grained breakdown for resource planning and tracking

## Duration Estimation

### Typical Construction Activities

| Activity | Typical Duration | Basis | Notes |
|----------|-----------------|-------|-------|
| Mobilization | 1-2 weeks | Fixed | Site setup, safety induction |
| Excavation | 1-4 weeks | Per 1,000 m³ | Depends on soil type, equipment |
| Foundation | 2-4 weeks | Per 100 m | Excavation + concrete + curing |
| Structural concrete | 0.5-1 week | Per 200 m² | Formwork + pour + curing |
| Structural steel | 2-3 weeks | Per 100 tonnes | Fabrication + delivery + erection |
| Masonry | 0.5-1 week | Per 100 m² | Blockwork or brickwork |
| Mechanical & Electrical rough-in | 3-4 weeks | Per floor | Main installation phase |
| Plumbing rough-in | 2-3 weeks | Per floor | Piping & drainage |
| Internal finishes | 1-2 weeks | Per floor | Plastering, flooring |
| Painting | 0.5-1 week | Per 100 m² | Interior + exterior |
| Fit-out & commissioning | 2-4 weeks | Variable | Testing & handover |

### Estimation Methods

**1. Analogous (Historical Data)**

- Use data from similar past projects
- Quick but less accurate
- Good for early planning

**2. Parametric (Metrics-Based)**

- Break into units: hours per m², m³, etc.
- Example: Painting = 0.8 hours/m²
- More accurate than analogous

**3. Three-Point Estimate**

- Optimistic (O): Best case if everything goes well
- Most Likely (M): Realistic scenario
- Pessimistic (P): Worst case with problems
- **Expected duration** = (O + 4M + P) / 6
- Better accounts for uncertainty

**Example:**

```
Foundation duration:
  Optimistic: 10 days (perfect conditions)
  Most Likely: 14 days (normal conditions)
  Pessimistic: 21 days (weather delays, rework)
  Expected: (10 + 4×14 + 21) / 6 = 14.8 days
```

## Schedule Dependencies

### Finish-to-Start (FS) - Most common

```
Activity A: ───────
Activity B:        ───────
Result: B starts only after A finishes
```

### Start-to-Start (SS) - Overlapping work

```
Activity A: ───────
Activity B: ───────
Result: B starts at same time as A (concurrent work)
```

### Finish-to-Finish (FF) - Concurrent ending

```
Activity A: ───────
Activity B:    ──────
Result: B finishes when A finishes
```

### Lead/Lag - Time gaps

```
A: ─────────
B:       ────────────
Result: B starts 2 weeks after A finishes (lag) 
Or: B starts before A finishes (lead/overlap)
```

### Critical Path Calculation

**Forward Pass** (Calculate earliest times):

- ES (Early Start) = max(finish times of predecessors)
- EF (Early Finish) = ES + Duration

**Backward Pass** (Calculate latest times):

- LF (Late Finish) = min(start times of successors)
- LS (Late Start) = LF - Duration

**Slack/Float** = LS - ES (or LF - EF)

- **Zero slack** = Critical path (no delays allowed)
- **Positive slack** = Non-critical (can be delayed)

## Risk Categories & Examples

### Technical Risks

- Design complexity
- Soil/ground conditions unknown
- Structural issues discovered
- Quality defects requiring rework
- Building code violations

### Schedule Risks

- Weather delays (rain, frost, wind)
- Approval/permit delays
- Supply chain disruptions
- Resource unavailability
- Supplier delays
- Dependent activities delayed

### Resource Risks

- Key person leaves
- Labor disputes/strikes
- Skill shortages in market
- Inefficiency/low productivity
- Subcontractor failure
- Equipment breakdown

### Cost Risks

- Material price inflation
- Waste & rework costs
- Scope creep (extra work)
- Productivity loss
- Retention/warranty claims
- Currency fluctuations

### External Risks

- Regulatory changes
- Site access issues
- Neighbor disputes
- Utility disruptions
- Environmental issues
- Force majeure (pandemic, war, natural disaster)

## Risk Probability & Impact Scales

### Probability Scale

```
Low (1):    <25% chance
Medium (2): 25-50% chance
High (3):   >50% chance
```

Or numeric 1-10:

```
1-3:   Low
4-7:   Medium
8-10:  High
```

### Impact Scale

```
Low (1):    Minimal effect on project (< 5% cost/schedule)
Medium (2): Moderate effect (5-15% cost/schedule)
High (3):   Major effect (> 15% cost/schedule)
```

### Risk Matrix Priority

```
          Probability
Impact    Low  Med  High
  High     🟡   🔴   🔴
  Med      🟢   🟡   🔴
  Low      🟢   🟢   🟡

🔴 = High priority (must mitigate)
🟡 = Medium priority (monitor & plan)
🟢 = Low priority (accept, monitor)
```

## Resource Planning

### Typical Construction Team

| Role | Quantity | Typical Duration | Skills |
|------|----------|------------------|--------|
| Project Manager | 1 | Full project | Leadership, planning, coordination |
| Site Manager | 1 | 80% of project | Daily operations, quality, safety |
| Site Supervisor | 1-2 | Active phases | Direct crew management |
| Safety Officer | 1 | Full project | Health & safety compliance |
| Quality Inspector | 1 | Active phases | Quality assurance, testing |
| Health & Safety Rep | 1 | Full project | Safety procedures, incidents |
| Estimator/Planner | 0.5-1 | Front 20%, back 20% | Cost, scheduling |
| Administrative | 0.5-1 | Full project | Paperwork, logistics |
| Skilled Trades | Variable | Active phases | Excavation, concrete, electrical, plumbing, etc. |
| Laborers | Variable | Active phases | General construction work |

### Resource Leveling Techniques

1. **Delay non-critical activities** (use float available)
2. **Split activities** into phases over time
3. **Adjust crew sizes** (hire/reduce as needed)
4. **Overlap phases** differently to balance load
5. **Use subcontractors** for peak demand periods
6. **Cross-train staff** for flexibility

## Earned Value Management

### Three Key Metrics

**Planned Value (PV) or Budgeted Cost of Work Scheduled**

- Budget allocated to work planned for the period
- "How much work should have been done?"

**Earned Value (EV) or Budgeted Cost of Work Performed**

- Budget allocated to completed work
- "How much work was actually done?"

**Actual Cost (AC) or Actual Cost of Work Performed**

- Actual spending to date
- "How much did it actually cost?"

### Performance Indicators

**Schedule Performance Index (SPI) = EV / PV**

- SPI = 1.0 → On schedule
- SPI > 1.0 → Ahead of schedule
- SPI < 1.0 → Behind schedule
- Example: SPI = 0.85 means 85% progress on only 85/0.85 = 100% of planned time (⚠️ behind)

**Cost Performance Index (CPI) = EV / AC**

- CPI = 1.0 → On budget
- CPI > 1.0 → Under budget (spending less)
- CPI < 1.0 → Over budget (spending more)
- Example: CPI = 0.95 means earning 95% value for 100% actual spend (⚠️ over budget)

**Variance at Completion (VAC) = BAC - (BAC / CPI)**

- BAC = Budget at Completion (original budget)
- Projected cost overrun/underrun
- Example: BAC = £1M, CPI = 0.95 → VAC = 1M - (1M/0.95) = -£52k (projected overrun)

### Forecasting

**Estimate at Completion (EAC)**

- If current cost rate continues: EAC = BAC / CPI
- If only current problems remain: EAC = AC + (BAC - EV)

**Schedule Forecast**

- Current schedule duration: D
- Adjusted for SPI: D / SPI
- Example: D = 52 weeks, SPI = 0.95 → Forecast 52 / 0.95 = 54.7 weeks (3-week delay)

## Status Report Template

**Header:**

- Project name
- Reporting period (Week XX of YY)
- Report date & prepared by
- Overall status (On Track / At Risk / Off Track)

**Executive Summary:**

- Schedule status (% complete, ahead/behind)
- Budget status (spent to date, % of budget)
- Quality status (defects, rework)
- Safety status (incidents, near-misses)

**Key Metrics (if tracking):**

- Schedule Performance Index (SPI)
- Cost Performance Index (CPI)
- Planned vs. Actual completion dates

**Phase Progress:**

- Current phase name & % complete
- Next phase start date
- Major milestones achieved this period
- Milestones due next period

**Issues:**

- What went wrong?
- Impact (schedule/cost/quality)?
- Root cause?
- Corrective action?
- Owner & target resolution date?

**Risks:**

- Any new risks?
- Status of existing risks
- Any risks escalating?
- Mitigations in progress?

**Resource Status:**

- Current team size vs. planned
- Key positions vacant/at risk?
- Subcontractor status
- Equipment status

**Upcoming Work:**

- What's due next week?
- Any approvals needed?
- Procurement activities?
- External dependencies?

**Action Items:**

- What needs to be done?
- Who's responsible?
- Target completion date?

## Common Project Health Indicators

| Indicator | Green (OK) | Yellow (At Risk) | Red (Critical) |
|-----------|-----------|-----------------|----------------|
| Schedule | SPI ≥ 0.95 | 0.85 ≤ SPI < 0.95 | SPI < 0.85 |
| Budget | CPI ≥ 0.95 | 0.85 ≤ CPI < 0.95 | CPI < 0.85 |
| Safety | 0 incidents | 1 incident | 2+ incidents |
| Quality | 0-2% defects | 3-5% defects | >5% defects |
| Resources | On target | 1-2 gaps | 3+ gaps |
| Risks | Managed | 1-2 escalating | 3+ high-risk |
| Issues | Resolved | 1-2 open | 3+ open issues |

## Key Acronyms

| Acronym | Meaning | Use |
|---------|---------|-----|
| WBS | Work Breakdown Structure | Project decomposition |
| FS/SS/FF | Finish-to-Start / Start-to-Start / Finish-to-Finish | Dependencies |
| ES/EF | Early Start / Early Finish | Forward pass calculation |
| LS/LF | Late Start / Late Finish | Backward pass calculation |
| PV | Planned Value | Budgeted work for period |
| EV | Earned Value | Budget for completed work |
| AC | Actual Cost | Actual spending |
| SPI | Schedule Performance Index | Schedule efficiency |
| CPI | Cost Performance Index | Cost efficiency |
| VAC | Variance at Completion | Projected cost over/under run |
| BAC | Budget at Completion | Total project budget |
| EAC | Estimate at Completion | Forecast final cost |
| KPI | Key Performance Indicator | Project health metrics |
| NCR | Non-Conformance Report | Quality issue |
| LTI | Lost Time Injury | Safety incident |
| FAC | Forecast at Completion | Projected final schedule/cost |
