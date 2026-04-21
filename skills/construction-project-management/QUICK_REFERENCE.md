# Construction Project Management Skill - Quick Reference

## 📍 Location

```
/Users/user/Documents/GitHub/skills/skills/construction-project-management/
```

## 📚 Quick Links

| Resource | Purpose | Command |
|----------|---------|---------|
| SKILL.md | Core skill definition | `cat SKILL.md \| head -100` |
| DEVELOPMENT.md | Setup & eval guide | `cat DEVELOPMENT.md` |
| references/standards.md | PM standards & concepts | `cat references/standards.md \| head -80` |
| evals/evals.json | 3 test cases | `cat evals/evals.json` |
| Sample outputs | Expected format | `python scripts/generate_sample_pm_outputs.py` |

## 🎯 What It Does

| Input | Process | Output |
|-------|---------|--------|
| Project scope, timeline, team, risks, constraints | Structure → Schedule → Risk → Resource → Track | Schedule, Risk register, Resource plan, Status report, Dashboard |

## 📊 Key Concepts

### Work Breakdown Structure (WBS)

```
Project
├── Phase 1: Mobilization
├── Phase 2: Groundwork
├── Phase 3: Structural
├── Phase 4: MEP
├── Phase 5: Finishes
└── Phase 6: Handover
```

### Critical Path

**Longest sequence of dependent activities** = Project duration  
Any delay on critical path = Project delay

### Earned Value Metrics

```
SPI = EV / PV  (Schedule efficiency)
CPI = EV / AC  (Cost efficiency)
```
>
- >1.0 = Good (ahead/under budget)
- <1.0 = Bad (behind/over budget)

### Risk Scoring

```
Risk Score = Probability × Impact

High   = Score 7-9  (Immediate action)
Medium = Score 4-6  (Plan mitigation)
Low    = Score 1-3  (Monitor)
```

## 🚀 Quick Commands

### View the skill

```bash
cat /Users/user/Documents/GitHub/skills/skills/construction-project-management/SKILL.md | head -150
```

### Generate sample outputs

```bash
cd /Users/user/Documents/GitHub/skills/skills/construction-project-management
python scripts/generate_sample_pm_outputs.py
cat sample_outputs/sample_schedule.csv
cat sample_outputs/sample_risk_register.md
cat sample_outputs/sample_status_report.md
```

### View test cases

```bash
cat /Users/user/Documents/GitHub/skills/skills/construction-project-management/evals/evals.json | python -m json.tool | head -80
```

### Read standards reference

```bash
cat /Users/user/Documents/GitHub/skills/skills/construction-project-management/references/standards.md | head -100
```

## 📋 Test Cases

| Eval | Complexity | Project Type | Size | Expected Output |
|------|-----------|--------------|------|-----------------|
| 1 | Easy | Renovation | 12 weeks | 15-20 activities, simple schedule |
| 2 | Medium-Hard | Multi-storey | 78 weeks | 30-40 activities, complex dependencies |
| 3 | Hard | Status analysis | Week 25 of 52 | Earned value, forecasts, corrective actions |

## 📐 Output Formats

**1. Schedule (CSV)**

```
ID | Activity | Duration | Predecessor | Critical Path
1 | Mobilization | 5d | - | Yes
2 | Excavation | 10d | 1 | Yes
3 | Foundation | 14d | 2 | Yes
```

**2. Risk Register (Table)**

```
| Risk | Probability | Impact | Score | Mitigation |
|------|-------------|--------|-------|-----------|
| Weather delays | 60% | High | 9 | Buffer schedule |
| Labor shortage | 40% | Medium | 5 | Early hiring |
```

**3. Resource Histogram (ASCII)**

```
Week 1-2:  PM: [#####] Crew: [##########]
Week 3-4:  PM: [#####] Crew: [########]
```

**4. Status Report (Markdown)**

```
Schedule: 92% (SPI 0.92 - behind)
Budget: 103% (CPI 0.97 - over)
Safety: 0 incidents (excellent)
```

**5. Dashboard (Summary)**

```
Timeline: [████░░░] Week 8 of 12 (67%)
Status: At Risk (Yellow)
Next Milestone: Structural complete Week 10
```

## ✅ Quality Checklist

Before delivery:

- [ ] WBS logically organized
- [ ] Durations realistic (use standards or 3-point estimate)
- [ ] Dependencies accurate & minimal
- [ ] Critical path clearly marked
- [ ] 5-15 risks identified & scored
- [ ] Resources allocated w/ conflicts resolved
- [ ] Status metrics (SPI, CPI) calculated correctly
- [ ] Outputs in requested format(s)
- [ ] Assumptions documented
- [ ] Next steps identified

## 🔄 Evaluation Workflow

```
Create ✅ → Test ✅ → Evaluate ⏳ → Iterate ⏳ → Deploy ⏳
```

**Phase 1**: Run test cases (with-skill vs baseline)  
**Phase 2**: Review outputs (qualitative + quantitative)  
**Phase 3**: Gather feedback (what worked, what didn't)  
**Phase 4**: Iterate (refine SKILL.md based on results)  

## 💡 Key Formulas

| Metric | Formula | Interpretation |
|--------|---------|-----------------|
| **SPI** | EV ÷ PV | <1.0 = Behind schedule |
| **CPI** | EV ÷ AC | <1.0 = Over budget |
| **VAC** | BAC - (BAC ÷ CPI) | Projected cost variance |
| **EAC** | BAC ÷ CPI | Forecast final cost |
| **Duration** | (O + 4M + P) ÷ 6 | Three-point estimate |

## 📊 Health Status Indicators

| Indicator | Green ✓ | Yellow ⚠️ | Red 🔴 |
|-----------|---------|-----------|--------|
| Schedule (SPI) | ≥0.95 | 0.85-0.95 | <0.85 |
| Budget (CPI) | ≥0.95 | 0.85-0.95 | <0.85 |
| Safety (LTI) | 0 incidents | 1 incident | 2+ incidents |
| Quality | <1% defects | 1-3% defects | >3% defects |
| Risks | Stable | 1-2 escalating | 3+ escalating |

## 🎓 Learning Path

1. **Understand project dimensions** - Time, Risk, Resource, Progress
2. **Learn WBS decomposition** - Break work logically
3. **Master critical path** - Identify what can't delay
4. **Calculate earned value** - SPI, CPI, VAC, EAC
5. **Assess & mitigate risks** - Probability, impact, strategies
6. **Resource plan & level** - Allocation, conflicts, capacity
7. **Track & report** - Weekly status, variance, forecasts

## 📚 Standards Referenced

- **PMBOK**: 10 knowledge areas
- **BS6046**: UK project governance
- **RIBA**: Architect's work stages
- **Construction industry standards**: Duration norms, resource ratios

## 🔗 Integrations

Works with:

- **bill-of-quantities**: BoQ items → Activities in schedule
- **Cost management**: Schedule + Resources = Budget
- **Risk management**: Deep-dive on high-priority risks
- **Quality management**: Quality gates in schedule
- **Change management**: Impact assessment on schedule/cost/risk

## 📞 Quick Troubleshooting

**Schedule looks unrealistic?**
→ Use industry standards from references/standards.md

**Risk register incomplete?**
→ Review all 5 risk categories; use as checklist

**Resource conflicts?**
→ Show % allocation per week; recommend leveling

**Earned value metrics off?**
→ Verify: SPI = EV÷PV, CPI = EV÷AC

---

**Status**: ✅ Draft Complete - Ready for Evaluation  
**Version**: 1.0  
**Created**: 2026-04-21
