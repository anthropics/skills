---
name: construction-project-management
description: Comprehensive construction project management planning and reporting. Use this skill whenever users need to create project schedules and Gantt charts, develop risk registers and mitigation plans, allocate resources and manage team capacity, track project progress with earned value analysis, generate status reports and dashboards, manage dependencies and critical path, identify milestones and deliverables, or perform variance analysis and forecasting for construction projects.
compatibility: "Python 3.7+, pandas/openpyxl for Excel (optional), CSV/Markdown for lightweight output"
---

# Construction Project Management Skill

Comprehensive project management support for construction projects. Create schedules, manage risks, allocate resources, track progress, and generate executive reports. This skill helps structure project plans from specifications, organize work into phases, identify dependencies, assess risks, and monitor project health through multiple reporting formats.

## Quick Start

When given construction project information (scope, specifications, timeline, team, constraints), your goal is to:

1. **Structure** the project into phases and work breakdown
2. **Schedule** activities with durations, dependencies, and critical path
3. **Identify** risks and develop mitigation strategies
4. **Allocate** resources efficiently and highlight conflicts
5. **Generate** multiple outputs: timelines, risk registers, resource plans, status reports

## Project Dimensions

Construction projects have four key dimensions to manage:

### 1. **Time Management**
- Work Breakdown Structure (WBS)
- Activity sequencing & dependencies
- Duration estimation
- Critical path analysis
- Milestone identification
- Schedule optimization

### 2. **Risk Management**
- Risk identification (technical, resource, schedule, cost)
- Risk assessment (probability × impact)
- Mitigation strategies
- Contingency planning
- Risk monitoring

### 3. **Resource Management**
- Team composition & roles
- Skill requirements
- Resource allocation & leveling
- Capacity planning
- Conflict identification

### 4. **Progress Tracking**
- Planned vs. actual
- Earned value metrics
- Variance analysis
- Forecasting & corrective actions
- Status reporting

## Methodology

### Phase 1: Project Analysis

When given project information, extract:

**Project Scope:**
- Building type, location, scale
- Key deliverables
- Contract value & duration
- Client/stakeholder requirements
- Constraints (weather, logistics, access)

**Work Breakdown:**
- Major phases (Design, Procurement, Mobilization, Construction, Handover)
- Key activities per phase
- Interdependencies
- Critical items

### Phase 2: Schedule Development

**1. Create Work Breakdown Structure (WBS)**

Organize work hierarchically:
```
Level 1: Phase (e.g., "Groundwork", "Structures")
Level 2: Activity (e.g., "Excavation", "Concrete Works")
Level 3: Task (e.g., "Bulk Excavation", "Trench Preparation")
```

**2. Estimate Durations**

For each activity:
- Research typical duration (based on scope)
- List crew/equipment
- Identify dependencies
- Add buffers for uncertainties

**Duration estimation examples:**
- Excavation: ~2-4 weeks (depends on area, soil type, equipment)
- Foundation concrete: ~1-2 weeks (curing time)
- Structural concrete slabs: ~2-3 weeks per floor
- Masonry: ~0.5-1 weeks per 100 m²
- MEP rough-in: ~3-4 weeks per floor
- Finishes: ~2-3 weeks per floor

**3. Define Dependencies**

Types of dependencies:
- **Finish-to-Start (FS)**: Activity B starts after Activity A finishes
- **Start-to-Start (SS)**: Activities start together
- **Finish-to-Finish (FF)**: Activities finish together
- **Leads/Lags**: Overlaps or gaps between activities

Example:
```
Excavation (10d) FS → Foundation concrete (14d) FS → Structural works (45d)
```

**4. Calculate Critical Path**

The longest path determines project duration.

Steps:
1. Calculate forward pass (earliest start/finish times)
2. Calculate backward pass (latest start/finish times)
3. Identify activities with zero slack/float
4. Flag activities that can't be delayed

### Phase 3: Risk Assessment

**1. Risk Identification**

Common construction risks by category:

| Category | Examples |
|----------|----------|
| **Technical** | Design changes, soil conditions, structural complexity |
| **Schedule** | Delay in approvals, adverse weather, resource unavailability |
| **Resource** | Key person dependency, skill shortage, labor disputes |
| **Cost** | Material price increases, rework, productivity loss |
| **External** | Regulatory changes, site access issues, utilities disruption |

**2. Risk Scoring**

For each risk:
- **Probability** (High/Medium/Low or 1-10)
- **Impact** (High/Medium/Low or 1-10)
- **Risk Score** = Probability × Impact
- **Priority** = High scores addressed first

**3. Mitigation Strategies**

For each high-priority risk:
- **Avoid**: Eliminate the risk entirely
- **Mitigate**: Reduce probability or impact
- **Transfer**: Shift to third party (insurance)
- **Accept**: Plan for contingency

Example:
```
Risk: Concrete delays due to poor weather
Probability: Medium (40%)
Impact: High (adds 2 weeks)
Score: Medium
Mitigation: Use covered areas, weather monitoring, accelerate schedule buffer
Contingency: Retain 2-week float in critical activities
```

### Phase 4: Resource Planning

**1. Resource Requirements**

Identify all resources needed:
- **Personnel**: Roles, quantities, duration, skills
- **Equipment**: Machinery, tools, duration
- **Materials**: Major items with procurement lead time
- **Subcontractors**: Specialty trades, dependencies

**2. Resource Allocation**

For each phase/activity:
```
Groundwork Phase:
  - Excavation crew (5 laborers): Weeks 1-3
  - Equipment operator (1): Weeks 1-3
  - Concrete team (8 crew): Weeks 3-5
  - Supervisor (1): Weeks 1-8
```

**3. Capacity Management**

Check for:
- **Resource conflicts**: Same resource assigned to multiple activities
- **Overallocation**: Resource usage >100% in any week
- **Underutilization**: Resource idle periods
- **Skill gaps**: Required skills not available

**4. Resource Leveling**

Strategies to balance resource utilization:
- Delay non-critical activities
- Split activities into phases
- Adjust crew sizes
- Hire/contract additional resources
- Use alternative methods

### Phase 5: Progress Tracking

**1. Baseline Establishment**

Before work starts:
- Finalize schedule
- Approve budget & resources
- Set performance targets
- Define earned value milestones

**2. Status Collection**

During execution:
- Weekly/monthly status updates
- % completion per activity
- Actual vs. planned duration
- Issues & change requests
- Resource actuals

**3. Earned Value Analysis**

Calculate three metrics:

- **PV (Planned Value)**: Budget for planned work
- **EV (Earned Value)**: Budget for completed work
- **AC (Actual Cost)**: Actual spending

Key performance indicators:
- **SPI (Schedule Performance Index)** = EV / PV
  - >1.0 = Ahead of schedule
  - <1.0 = Behind schedule
- **CPI (Cost Performance Index)** = EV / AC
  - >1.0 = Under budget
  - <1.0 = Over budget
- **Variance at Completion (VAC)** = BAC - (BAC / CPI)
  - Projected cost overrun/underrun

**4. Corrective Actions**

When behind schedule or over budget:
- Identify root cause
- Propose corrective action
- Assess impact on remaining schedule
- Update forecast
- Implement & monitor

## Output Generation

### Output 1: Project Schedule (Gantt Chart)

Format options:

**CSV Format** (for importing to tools):
```
ID | Task | Duration | Start | Finish | Predecessor | Resource | % Complete
1 | Mobilization | 5d | Week 1 | Week 1 | - | PM | 100%
2 | Excavation | 10d | Week 2 | Week 3 | 1 | Crew-A | 50%
3 | Foundation | 14d | Week 4 | Week 5 | 2 | Crew-B | 0%
```

**Markdown Timeline** (visual):
```
## Project Schedule

### Phase 1: Mobilization (Week 1-2)
- [####----] Mobilization & Site Setup (5 days)
- [#####---] Safety Induction (3 days)

### Phase 2: Groundwork (Week 3-6)
- [#########---] Excavation (10 days, Dependent on Mob)
- [---##########] Foundation (14 days, Dependent on Excavation)
```

**Key information to include:**
- Activity name & ID
- Start/end dates
- Duration
- Dependencies (predecessors)
- Resource assignment
- Status (% complete if tracking)
- Critical path highlighted
- Milestones marked

### Output 2: Risk Register

**Structure:**
```
ID | Risk | Category | Probability | Impact | Score | Mitigation | Owner | Status
1 | Wet weather delays | Schedule | Medium | High | 9 | Covered areas, buffer | PM | Active
2 | Key staff departure | Resource | Low | High | 6 | Cross-training, retention | HR | Active
3 | Soil conditions differ | Technical | Medium | Medium | 6 | Geotechnical testing, contingency | Eng | Monitoring
```

**For each risk include:**
- Unique ID
- Clear description
- Category (Technical/Schedule/Resource/Cost/External)
- Probability (1-10 or High/Med/Low)
- Impact (1-10 or High/Med/Low)
- Risk score = Probability × Impact
- Mitigation strategy
- Owner/responsible party
- Current status

### Output 3: Resource Allocation Chart

**Resource Histogram** (weekly resource usage):
```
## Labor Resource Plan

Week 1-2:   Project Manager:    [#####]
            Excavation Crew:    [##########]
            Safety Officer:     [##]

Week 3-4:   Project Manager:    [#####]
            Concrete Team:      [##########]
            Equipment Op:       [####]
```

**Resource Conflict Report:**
```
Conflicts Found:
1. Safety Officer: Over-allocated Week 3 (100% + 20%)
   Recommendation: Hire additional safety support

2. Concrete Team: Conflicting assignments Week 4-5
   Recommendation: Stagger Foundation & Structural phases by 1 week
```

**For each resource include:**
- Name/role
- Weekly allocation (%)
- Conflicts identified
- Recommendations for resolution

### Output 4: Status Report

**Executive Summary:**
```
## Project Status - Week 12 of 52

**Overall Status**: On Track (Yellow)
**Schedule**: 95% of planned work complete (On track)
**Budget**: £2.1M actual vs £2.0M planned (3% over)
**Quality**: No safety incidents (Target: Zero)

Key Metrics:
- Schedule Performance Index: 0.98 (Acceptable)
- Cost Performance Index: 1.03 (Good)
- Current Phase: Structural Works (60% complete)
```

**Detailed Breakdown:**
```
Phase Summary:
1. Mobilization: Complete ✓
2. Groundwork: Complete ✓
3. Structural Works: In Progress (60%)
4. MEP Systems: Not Started (Starts Week 20)
5. Finishes: Not Started
6. Handover: Not Started

Issues:
- Concrete delivery delayed 2 days (resolved)
- Additional soil stabilization required (impacts budget +2%)

Risks:
- Weather forecast: Heavy rain expected Week 14 (Mitigation: accelerate exterior work)

Next Week Actions:
- Pour Slab B (Critical path)
- Finalize MEP design (prevent downstream delays)
- Approve Finish materials
```

### Output 5: Project Dashboard

**One-page summary:**
```
## Project Dashboard - [Project Name]

Timeline Progress:
[████░░░░░░░░] Week 12 of 52 (23% complete)

Key Metrics:
┌─────────────────────────────────┐
│ Schedule: On Track       (98%)   │
│ Budget:   3% Over        (103%)  │
│ Quality:  Excellent      (0 NCR) │
│ Safety:   Excellent      (0 LTI) │
└─────────────────────────────────┘

Next Milestones:
▸ Foundation Complete: Week 6 (On track)
▸ Structural Start: Week 7 (On track)
▸ MEP Rough-in: Week 18 (At risk)
▸ Practical Completion: Week 50 (Projected)

Top Risks:
1. Weather delays (Mitigation active)
2. MEP design approval (Schedule risk)
3. Labor availability (Confirmed through Week 20)

Resource Status:
- Team: Fully staffed ✓
- Equipment: All operational ✓
- Subcontractors: 3 of 4 on-site

Last Updated: 2026-04-21
```

## Best Practices

### Schedule Development
- **WBS first**: Break down work logically before scheduling
- **Realistic durations**: Use historical data, add contingency
- **Clear dependencies**: Understand true constraints vs. self-imposed
- **Resource-loaded**: Factor in availability when setting dates
- **Buffer strategically**: Add contingency time to critical activities
- **Regular updates**: Revise as conditions change

### Risk Management
- **Identify early**: Front-load risk identification in planning phase
- **Score objectively**: Use consistent probability/impact scales
- **Prioritize**: Focus on high-impact items, not everything
- **Assign owners**: Each risk needs responsible party
- **Monitor actively**: Track risk status weekly/monthly
- **Escalate appropriately**: High-risk items need visibility

### Resource Planning
- **Balance**: Avoid peaks that cause fatigue or gaps
- **Skills-based**: Match skills to requirements, identify gaps
- **Efficiency**: Minimize idle time, plan cross-training
- **Constraints**: Factor in skill shortages, unions, availability
- **Forecasting**: Project resource needs 4-6 weeks ahead

### Progress Tracking
- **Timely data**: Collect status at consistent intervals
- **Earned value**: Use objective, verified metrics
- **Variance analysis**: Investigate all variances >5%
- **Root cause**: Don't just report problems, understand why
- **Proactive**: Forecast impact early, don't wait for issues
- **Communication**: Share status visibly, involve stakeholders

### Reporting
- **Tiered**: Executive summary for leadership, detail for team
- **Visual**: Charts are better than tables for status
- **Trend**: Show direction (improving/worsening)
- **Actionable**: Include recommended actions, not just facts
- **Consistent**: Same format, same timing for comparability

## Common Pitfalls

❌ **Schedule too optimistic**: Don't account for uncertainties  
✅ DO: Use 3-point estimate (Optimistic, Most Likely, Pessimistic)

❌ **Dependencies missing**: Independent activities assumed sequential  
✅ DO: Clearly map what really depends on what

❌ **Resource conflicts ignored**: Same person assigned to multiple tasks  
✅ DO: Resource-level the schedule, resolve conflicts early

❌ **Risks identified but not managed**: Risk register created then forgotten  
✅ DO: Review risks weekly, update status, implement mitigations

❌ **Budget and schedule separate**: Cost and time not integrated  
✅ DO: Use earned value to track both dimensions together

❌ **Reactive reporting**: Only report problems after they occur  
✅ DO: Forecast problems, report trends, be proactive

## Handling Incomplete Information

When project details are partial:

✅ **DO:**
- State clearly what you're assuming
- Use industry standard durations as baseline
- Mark areas needing more detail
- Provide ranges (e.g., 8-12 weeks) when uncertain
- Flag high-uncertainty items

❌ **DON'T:**
- Make wild guesses at timelines
- Ignore resource constraints
- Assume everything is on critical path
- Create overly precise dates without basis
- Miss dependencies because info is incomplete

## Quality Checklist

Before delivering PM outputs, verify:
- [ ] Work is organized logically (WBS structure sound)
- [ ] Durations are realistic (based on scope & resources)
- [ ] Dependencies are accurate (no missing constraints)
- [ ] Critical path identified and documented
- [ ] Major risks identified and assessed
- [ ] Resources allocated without major conflicts
- [ ] Status metrics are clear and meaningful
- [ ] Outputs are in requested formats
- [ ] Assumptions documented
- [ ] Next steps/actions identified

## Integration with Other Skills

This PM skill works well with:
- **bill-of-quantities**: Translate BoQ items into project activities
- **Organizational alignment**: Align resources with PMO governance
- **Risk management**: Deep dive on specific high-priority risks
- **Budget development**: Schedule + resources → cost estimate
