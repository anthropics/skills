# Construction Project Management Skill - Development Guide

## Overview

The **construction-project-management** skill provides comprehensive project planning, tracking, and reporting for construction projects. It covers scheduling, risk management, resource allocation, and progress tracking with multiple output formats.

## Directory Structure

```
/Users/user/Documents/GitHub/skills/skills/construction-project-management/
├── SKILL.md                           # Main skill definition (500+ lines)
├── LICENSE.txt                        # MIT License
├── DEVELOPMENT.md                     # This file
├── QUICK_REFERENCE.md                 # Quick lookup guide
│
├── references/
│   └── standards.md                   # PM standards, frameworks, calculations
│
├── evals/
│   └── evals.json                     # 3 test cases (simple, medium, status)
│
├── scripts/
│   └── generate_sample_pm_outputs.py  # Generate sample outputs
│
└── [workspace for iteration results]
```

## What This Skill Does

### Input

Construction project details:

- Scope & deliverables
- Timeline & constraints
- Team & resources
- Budget & costs
- Known risks

### Output (5 Formats)

1. **Project Schedule** - Gantt timeline with dependencies, critical path
2. **Risk Register** - Identified risks with probability, impact, mitigation
3. **Resource Allocation** - Team planning, capacity, conflicts
4. **Status Reports** - Weekly/monthly tracking with earned value metrics
5. **Project Dashboard** - One-page executive summary

### Key Capabilities

✅ Work Breakdown Structure (WBS)  
✅ Activity sequencing & dependencies  
✅ Duration estimation  
✅ Critical path analysis  
✅ Risk identification & scoring  
✅ Resource leveling  
✅ Earned value management (SPI, CPI, VAC)  
✅ Schedule forecasting  
✅ Cost forecasting  
✅ Progress tracking & variance analysis  
✅ Executive reporting  

## Test Cases

### Eval 1: Simple Renovation (Easy)

**Scope**: 2,000 m² office renovation, 12 weeks, £500k  
**Tests**: Basic WBS, simple schedule, standard risk register, resource plan  
**Expected**: 15-20 activities, 12-week timeline, 5-8 risks, clear critical path

### Eval 2: Multi-Storey Construction (Medium-Hard)

**Scope**: 4-storey mixed-use building, 78 weeks, £8.5M  
**Tests**: Complex WBS, 30+ activities, critical path, resource conflicts, risk matrix  
**Expected**: 30-40 detailed activities, 78-week schedule, 15+ risks, professional reporting

### Eval 3: Mid-Project Status (Hard - Analysis)

**Scope**: Project at Week 25 of 52, analyze delays & overruns  
**Tests**: Earned value analysis, variance calculation, forecasting, corrective actions  
**Expected**: SPI/CPI calculations, VAC/EAC projections, issues identified, recovery plan

## Key Concepts

### Project Dimensions

| Dimension | Focus | Key Metrics |
|-----------|-------|-------------|
| **Time** | Schedule activities, dependencies, critical path | SPI, schedule variance, completion forecast |
| **Risk** | Identify threats, assess probability/impact | Risk score, mitigation strategies |
| **Resource** | Team composition, allocation, conflicts | Utilization %, capacity gaps |
| **Progress** | Track vs. plan, earned value, forecasts | CPI, SPI, VAC, EAC |

### Methodologies

**Work Breakdown Structure (WBS)**

- Hierarchical decomposition (Project → Phase → Activity → Task)
- Organized by work scope (not organizational structure)
- Each element unique and complete

**Critical Path Method (CPM)**

- Forward pass: Calculate earliest times
- Backward pass: Calculate latest times
- Float/slack identifies critical activities
- Zero-delay flexibility on critical path

**Earned Value Management (EVM)**

- Combines schedule, cost, and scope
- PV = Planned value | EV = Earned value | AC = Actual cost
- SPI = EV/PV (schedule efficiency)
- CPI = EV/AC (cost efficiency)
- Enables forecasting (EAC, VAC)

**Risk Management**

- Identify, assess (probability × impact), mitigate
- Risk register tracks status
- High-priority risks actively managed
- Contingency planning

### Duration Estimation

| Method | Accuracy | Time | Use Case |
|--------|----------|------|----------|
| Analogous | 50-75% | Quick | Early planning, limited data |
| Parametric | 75-85% | Moderate | Bulk activities, historical data available |
| Three-Point | 80-95% | More time | Critical activities, uncertainty high |

### Status Metrics

| Metric | Formula | Interpretation |
|--------|---------|-----------------|
| **SPI** | EV / PV | >1 ahead, <1 behind schedule |
| **CPI** | EV / AC | >1 under budget, <1 over budget |
| **VAC** | BAC - (BAC/CPI) | Projected cost over/under |
| **EAC** | BAC / CPI | Forecast final cost |

## Output Formats

### 1. Project Schedule (CSV/Markdown)

```csv
ID, Activity, Duration, Start, Finish, Predecessor, Resource, Critical Path
1, Mobilization, 5d, Week 1, Week 1, -, Site Mgr, Yes
2, Excavation, 10d, Week 2, Week 3, 1, Crew-A, Yes
3, Foundation, 14d, Week 4, Week 5, 2, Crew-B, Yes
```

### 2. Risk Register (Table)

```
ID | Risk | Category | Probability | Impact | Score | Mitigation | Owner | Status
1 | Weather delay | Schedule | High | High | 9 | Contingency buffer | Site Mgr | Active
2 | Labor shortage | Resource | Medium | High | 6 | Early hiring | HR | Monitoring
```

### 3. Resource Histogram (ASCII)

```
Week 1-2:   PM: [#####] 
           Crew: [##########]
Week 3-4:   PM: [#####]
           Crew: [########]
```

### 4. Status Report (Markdown)

```
Overall Status: AT RISK
- Schedule: 92% progress (SPI 0.92, 1 week behind)
- Budget: 97% efficiency (CPI 0.97, 3% over)
- Safety: Excellent (0 incidents)
- Quality: Good (99.8% pass rate)
```

### 5. Dashboard (One-page summary)

```
Timeline: [████░░░░] Week 12 of 52 (23%)
Schedule: On Track (98%)
Budget: 3% Over (103%)
Safety: Excellent (0 LTI)
```

## Sample Outputs

Run the helper script to see examples:

```bash
cd /Users/user/Documents/GitHub/skills/skills/construction-project-management
python scripts/generate_sample_pm_outputs.py
cat sample_outputs/sample_schedule.csv
cat sample_outputs/sample_risk_register.md
cat sample_outputs/sample_status_report.md
```

This shows:

- CSV schedule format with dependencies
- Risk register with probability/impact scoring
- Comprehensive status report with earned value metrics

## Reference Materials

**standards.md** includes:

- PMBOK framework overview
- Construction-specific standards (BS6046, RIBA)
- WBS hierarchy & examples
- Duration estimation techniques
- Dependency types & critical path
- Risk categories & assessment
- Resource planning guidance
- Earned value calculations
- Status report templates
- Health indicators

## Quality Checklist

Before delivering PM outputs, verify:

- [ ] WBS is logically organized & complete
- [ ] Durations realistic (based on scope, resources, past projects)
- [ ] Dependencies accurate (true constraints, not self-imposed)
- [ ] Critical path identified & marked
- [ ] Major risks identified (5-10 minimum for complex projects)
- [ ] Risk scores calculated consistently
- [ ] Resources allocated without conflicts
- [ ] Metrics (SPI, CPI, etc.) calculated correctly if tracking
- [ ] Outputs match requested formats
- [ ] Assumptions documented
- [ ] Next steps/actions identified

## Evaluation Workflow

### Phase 1: Run Tests

- Run eval 1 (simple) - tests basic capability
- Run eval 2 (complex) - tests advanced capability
- Run eval 3 (status) - tests analysis & forecasting

### Phase 2: Review Outputs

**Quantitative**:

- Activity count vs. expected
- Schedule reasonableness (weeks per phase)
- Critical path clearly identified
- Risk scores (probability × impact)
- Earned value metrics (if tracking)

**Qualitative**:

- WBS logical & hierarchical
- Dependencies accurate
- Descriptions clear & complete
- Risk mitigations actionable
- Assumptions documented
- Format matches expectations

### Phase 3: Iterate

Based on feedback:

- Refine estimation methodology
- Improve risk assessment guidance
- Enhance resource planning
- Add missing output formats
- Clarify ambiguous sections

## Common Issues & Improvements

### Issue: Activities too vague

**Solution**: Add more detail in descriptions, specify "who" and "what"

### Issue: Durations unrealistic

**Solution**: Reference industry standards, use three-point estimation

### Issue: Dependencies missing

**Solution**: Ask "What must be done before this?" and "What can't start until this is done?"

### Issue: Risk register incomplete

**Solution**: Ask "What could go wrong?" for each phase, use risk categories as checklist

### Issue: Resource conflicts unresolved

**Solution**: Explicitly show % allocation per week, recommend leveling strategies

## Integration Points

Works well with:

- **bill-of-quantities skill**: Translate BoQ items into project activities
- **Cost management**: Schedule + Resources = Cost estimate
- **Risk management**: Deep-dive specific high-priority risks
- **Quality management**: Link activities to quality gates
- **Change management**: Impact of scope changes on schedule/cost/risk

## Key Metrics to Track

| Phase | Key Metrics | Target | Warning |
|-------|-----------|--------|---------|
| Planning | Activity count, CPM float | Reasonable values | Unrealistic dates |
| Execution | SPI, CPI | ≥0.95 | <0.90 |
| Reporting | Variance %, risks escalating | <5%, stable | >10%, increasing |

## Skill Status

| Task | Status |
|------|--------|
| Skill definition | ✅ Complete (500+ lines) |
| Test cases | ✅ Complete (3 evals) |
| Reference materials | ✅ Complete (comprehensive) |
| Sample outputs | ✅ Complete (3 formats) |
| Ready for evaluation | ✅ Ready |

## Next Steps

1. **Review SKILL.md** - Understand project methodology
2. **Check references/standards.md** - Learn PM concepts
3. **Run sample generator** - See expected output formats
4. **Review test cases** - Understand evaluation scenarios
5. **Run evaluations** - Test with skill-creator framework
6. **Iterate based on results** - Improve based on feedback

---

**Skill Name**: construction-project-management  
**Version**: 1.0  
**Created**: 2026-04-21  
**Status**: Draft - Ready for Initial Evaluation
