#!/usr/bin/env python3
"""
Helper script to generate sample project management outputs.
Demonstrates expected format and structure for PM planning documents.
"""

import json
from datetime import datetime, timedelta

def generate_sample_schedule_csv(output_path):
    """Generate a sample project schedule in CSV format."""
    
    schedule_data = [
        # Header
        ["ID", "Activity", "Duration", "Start", "Finish", "Predecessor", "Resource", "Critical Path"],
        [],
        # Phase 1: Mobilization
        ["1", "Mobilization & Site Setup", "5d", "Week 1", "Week 1", "-", "Site Manager + 3 crew", "Yes"],
        ["2", "Safety Induction", "3d", "Week 1", "Week 1", "1", "All staff", "Yes"],
        ["3", "Temporary Site Facilities", "5d", "Week 1", "Week 1", "1", "Contractor", "No"],
        [],
        # Phase 2: Groundwork
        ["4", "Excavation & Bulk Earthworks", "10d", "Week 2", "Week 3", "2", "Excavation crew (6 people)", "Yes"],
        ["5", "Temporary Dewatering (if needed)", "5d", "Week 2", "Week 2", "1", "Specialist (1)", "No"],
        ["6", "Foundation Trenches", "7d", "Week 3", "Week 3", "4", "Crew (5 people)", "Yes"],
        ["7", "Reinforcement Placement", "5d", "Week 3", "Week 4", "6", "Reinforcement crew (4 people)", "Yes"],
        ["8", "Foundation Concrete Pour", "7d", "Week 4", "Week 4", "7", "Concrete crew (8 people)", "Yes"],
        ["9", "Foundation Curing & Testing", "7d", "Week 5", "Week 5", "8", "QA Inspector (1)", "Yes"],
        [],
        # Phase 3: Structural
        ["10", "Structural Design Approval", "3d", "Week 1", "Week 1", "-", "Engineer (0.5)", "No"],
        ["11", "Structural Steel Procurement", "14d", "Week 2", "Week 4", "10", "Procurement (1)", "No"],
        ["12", "Structural Steel Erection - Level 1", "5d", "Week 5", "Week 5", "11,9", "Steel crew (6)", "Yes"],
        ["13", "Concrete Slab - Level 1", "10d", "Week 5", "Week 6", "12", "Concrete crew (8)", "Yes"],
        ["14", "Structural Steel Erection - Level 2", "5d", "Week 6", "Week 6", "13", "Steel crew (6)", "Yes"],
        ["15", "Concrete Slab - Level 2", "10d", "Week 6", "Week 7", "14", "Concrete crew (8)", "Yes"],
        ["16", "Structural Steel Erection - Level 3", "5d", "Week 7", "Week 7", "15", "Steel crew (6)", "Yes"],
        ["17", "Concrete Slab - Level 3", "10d", "Week 7", "Week 8", "16", "Concrete crew (8)", "Yes"],
        ["18", "Structural Testing & Inspection", "5d", "Week 8", "Week 8", "17", "Engineer + Inspector (1.5)", "No"],
        [],
        # Phase 4: MEP Rough-In (concurrent with finishes)
        ["19", "MEP Design Approval", "5d", "Week 5", "Week 5", "10", "MEP Engineer (0.5)", "No"],
        ["20", "Electrical Main Distribution", "7d", "Week 8", "Week 8", "19,17", "Electrical crew (4)", "No"],
        ["21", "Plumbing Main Lines", "7d", "Week 8", "Week 8", "19,17", "Plumbing crew (4)", "No"],
        ["22", "HVAC Ductwork & Equipment", "7d", "Week 8", "Week 9", "19,17", "HVAC crew (3)", "No"],
        ["23", "MEP Testing & Inspection", "5d", "Week 9", "Week 9", "20,21,22", "MEP Inspector (1)", "No"],
        [],
        # Phase 5: Internal Finishes
        ["24", "Plastering & Drywall", "8d", "Week 9", "Week 10", "18", "Plaster crew (4)", "No"],
        ["25", "Painting", "6d", "Week 10", "Week 10", "24", "Painting crew (3)", "No"],
        ["26", "Flooring Installation", "7d", "Week 10", "Week 11", "24", "Flooring crew (4)", "No"],
        ["27", "Door & Window Installation", "5d", "Week 9", "Week 9", "18", "Carpentry crew (3)", "No"],
        ["28", "Electrical Outlet & Fixture Install", "6d", "Week 11", "Week 11", "25,26,27", "Electrical crew (4)", "No"],
        ["29", "Plumbing Fixture Installation", "6d", "Week 11", "Week 12", "25,26,27", "Plumbing crew (4)", "No"],
        [],
        # Phase 6: Handover
        ["30", "Snagging & Remedials", "5d", "Week 12", "Week 12", "29", "All trades", "No"],
        ["31", "Final Testing & Commissioning", "3d", "Week 12", "Week 12", "30", "All consultants", "No"],
        ["32", "Site Clearance", "2d", "Week 12", "Week 12", "31", "Site crew (2)", "No"],
        ["33", "Handover & Keys", "1d", "Week 12", "Week 12", "32", "Project Manager", "No"],
    ]
    
    with open(output_path, 'w') as f:
        for row in schedule_data:
            f.write(','.join(row) + '\n')
    
    print(f"✓ Sample schedule CSV generated: {output_path}")

def generate_sample_risk_register(output_path):
    """Generate a sample risk register."""
    
    risk_register = """# Risk Register - Sample Project

## Summary
- Total Risks Identified: 12
- High Priority (Red): 3
- Medium Priority (Yellow): 5
- Low Priority (Green): 4

## Detailed Risk Register

| ID | Risk Description | Category | Probability | Impact | Score | Priority | Mitigation Strategy | Owner | Status |
|----|------------------|----------|-------------|--------|-------|----------|-------------------|-------|--------|
| R1 | Adverse weather delays excavation & foundation | Schedule | 60% | High | 9 | 🔴 High | Accelerate schedule buffer, use covers for concrete | Site Mgr | Active |
| R2 | Unforeseen soil conditions (contamination/instability) | Technical | 30% | High | 6 | 🔴 High | Geotechnical investigation, contingency in budget | Engineer | Monitoring |
| R3 | Structural steel supplier delays delivery | Supply Chain | 40% | Medium | 8 | 🔴 High | Dual sourcing, early order, expedite fees budgeted | Procurement | At Risk |
| R4 | Key project manager leaves mid-project | Resource | 20% | High | 6 | 🟡 Medium | Cross-train assistant PM, retention bonus | HR | Monitoring |
| R5 | Concrete quality issues requiring rework | Quality | 25% | Medium | 5 | 🟡 Medium | Independent testing, quality control procedures | QA | Active |
| R6 | MEP design approval delays (Client indecision) | Schedule | 50% | Medium | 7 | 🟡 Medium | Early client engagement, design workshops | PM | At Risk |
| R7 | Material cost inflation (steel, concrete) | Cost | 60% | Low | 3 | 🟢 Low | Fixed-price contracts where possible, hedging | Finance | Monitoring |
| R8 | Labor shortages in skilled trades | Resource | 40% | Medium | 5 | 🟡 Medium | Early subcontractor engagement, wage incentives | Site Mgr | Active |
| R9 | Site access/traffic management issues | External | 30% | Low | 3 | 🟢 Low | Traffic management plan, early coordination with council | PM | Monitoring |
| R10 | Noise complaints from neighbors | External | 35% | Low | 4 | 🟢 Low | Noise mitigation measures, communication plan | Site Mgr | Monitoring |
| R11 | Electrical/utility disruptions | External | 15% | High | 5 | 🟡 Medium | Pre-coordination with utilities, contingency plans | Engineer | Monitoring |
| R12 | Change orders from Client scope creep | Scope | 55% | Medium | 8 | 🔴 High | Clear scope documentation, formal change process | PM | Active |

## Risk Action Items

### R1 - Weather Delays (Priority: HIGH)
- **Action**: Install temporary covers for foundation concrete
- **Owner**: Site Manager
- **Target Completion**: Week 3
- **Status**: In Progress

### R3 - Steel Supplier Delays (Priority: HIGH)
- **Action**: Contact alternate supplier, confirm capacity
- **Owner**: Procurement
- **Target Completion**: Week 1 (URGENT)
- **Status**: Open

### R12 - Scope Creep (Priority: HIGH)
- **Action**: Implement formal change request process, get Client sign-off on scope
- **Owner**: Project Manager
- **Target Completion**: Week 1
- **Status**: In Progress

## Risk Trends
- ✓ Geotechnical risk decreasing (investigation complete)
- ✓ Weather risk seasonal (high in winter months)
- ⚠️ Supply chain risks increasing (material delays observed)
- ⚠️ Client decision-making slow (design approval delays)

"""
    
    with open(output_path, 'w') as f:
        f.write(risk_register)
    
    print(f"✓ Sample risk register generated: {output_path}")

def generate_sample_status_report(output_path):
    """Generate a sample project status report."""
    
    status_report = """# Project Status Report - Week 8

**Project**: 3-Storey Commercial Building  
**Reporting Period**: Week 8 of 12  
**Report Date**: 2026-04-21  
**Prepared By**: Project Manager  
**Overall Status**: ⚠️ AT RISK

---

## Executive Summary

Project is currently **1-2 weeks behind schedule** due to foundation concrete delays from adverse weather. Budget is tracking **3% over** due to additional soil stabilization requirements. Quality is good with no major defects. Safety performance excellent (zero incidents).

### Key Metrics
- **Schedule Performance Index (SPI)**: 0.92 (Target: ≥0.95)
- **Cost Performance Index (CPI)**: 0.97 (Target: ≥0.95)
- **Project Health**: 🟡 At Risk
- **Safety Record**: ✓ Excellent (0 incidents)

---

## Schedule Status

### Current Progress
- **Target Completion**: Week 12 (June 15)
- **Forecast Completion**: Week 14 (June 29)  
- **Projected Delay**: 2 weeks ⚠️
- **Overall Progress**: 67% of planned work complete (Week 8 of 12 baseline)

### Phase Breakdown

| Phase | Status | % Complete | Comments |
|-------|--------|-----------|----------|
| Mobilization | ✓ Complete | 100% | Finished Week 1 |
| Groundwork | ✓ Complete | 100% | Finished Week 6 (1 week late due to weather) |
| **Structural** | 🟡 In Progress | 65% | On track (2 of 3 slabs poured) |
| MEP Rough-In | ⏳ Starting | 0% | Scheduled to start Week 8 ✓ |
| Finishes | ⏳ Pending | 0% | Scheduled Week 10 |
| Handover | ⏳ Pending | 0% | Scheduled Week 12 |

### Key Milestones

| Milestone | Planned | Actual/Forecast | Status |
|-----------|---------|-----------------|--------|
| Mobilization Complete | Week 1 | Week 1 | ✓ On time |
| Groundwork Complete | Week 6 | Week 6 | ✓ On time* |
| Structural Complete | Week 8 | Week 10 | ⚠️ 2 weeks late |
| MEP Rough-In Complete | Week 10 | Week 11 | ⚠️ 1 week late |
| Finishes Complete | Week 11 | Week 12 | ⚠️ 1 week late |
| **Final Handover** | **Week 12** | **Week 14** | **⚠️ 2 weeks late** |

*Groundwork was 1 week late internally but caught up through accelerated structural works

---

## Budget Status

### Spending to Date
- **Planned Value (PV)**: £1,800,000 (budgeted for work through Week 8)
- **Earned Value (EV)**: £1,750,000 (value of completed work)
- **Actual Cost (AC)**: £1,803,000 (actual spending)
- **Remaining Budget**: £1,400,000 of original £3,200,000
- **Forecast Total Cost**: £3,296,000 (3.0% over)

### Cost Variance
- **Cost Variance (CV)**: -£53,000 (over budget by 3%)
- **CPI**: 0.97 (97¢ earned per £1 spent)

### Cost Drivers (Overruns)
- Soil stabilization work: +£75,000 (unforeseen)
- Concrete waste/rework: +£35,000
- Extended equipment rental (delay-related): +£28,000
- Offset by productivity gains: -£85,000

---

## Quality Status

### Defects & Rework
- **Minor defects found**: 3 (all cosmetic)
- **Rework required**: None to date
- **Pass rate**: 99.8%
- **Quality target**: ✓ Excellent

### Inspections This Week
- Foundation concrete testing: ✓ All samples passed
- Structural steel connections: ✓ Approved
- MEP design review: ✓ Approved

---

## Safety Status

### Safety Record
- **Lost Time Injuries**: 0 ✓
- **Near Misses**: 1 (ladder incident, corrected)
- **Incidents**: 0
- **Safety Target**: Zero LTI ✓

### Safety Activities This Week
- Daily toolbox talks (Monday-Friday)
- Site safety audit performed
- PPE compliance check: 100%
- Safety training: 4 workers completed CSCS card upgrade

---

## Resources Status

### Current Staffing
- **Project Manager**: 1 (Full time)
- **Site Manager**: 1 (Full time)
- **Supervisors**: 2 (Full time)
- **Safety Officer**: 1 (Full time)
- **Skilled Trades**: 18 (peaked from plan of 16)
- **Laborers**: 12 (as planned)
- **Subcontractors**: 2 active (Excavation ✓ complete, Structural ✓ on-site)

### Resource Issues
- ⚠️ Concrete finisher resigned (1 of 3) - replaced, no delay impact
- ✓ MEP subcontractor confirmed mobilization Week 8
- ✓ No other resource constraints identified

### Forecast Resource Needs
- Peak demand: Week 9-10 (structural + MEP + finishes concurrent)
- Team size: 28 people (manageable)
- Subcontractors: MEP team arriving Week 8, finishes team Week 10

---

## Issues & Risks

### Active Issues

| Issue | Impact | Action | Owner | Target Close |
|-------|--------|--------|-------|---------------|
| Weather delayed foundation concrete 1 week | Schedule +1 week | Accelerate structural phase | Site Mgr | Week 8 ✓ |
| Soil stabilization costs £75k more | Budget +£75k | Claim against contingency | Finance | Week 8 |
| Client MEP approval slow | Schedule risk | Weekly design meetings | PM | Week 7 ✓ |

### Top Risks (for next 4 weeks)

1. **🔴 Weather delays structural work (HIGH)**
   - Current status: Forecast improving, Week 9-10 looks clear
   - Mitigation: Temporary covers in place, accelerate schedule

2. **🟡 MEP design changes (MEDIUM)**
   - Current status: Design approved, but Client may request changes
   - Mitigation: Formal change request process, contingency budget allocated

3. **🟡 Finish material deliveries (MEDIUM)**
   - Current status: Flooring material on order (8-week lead time)
   - Mitigation: Expedited shipping arranged, cost absorbed

---

## Next Period (Week 9) Focus

### Immediate Priorities
1. ✓ Complete Structural Slab 2 (on schedule)
2. ✓ Pour Structural Slab 3 (on schedule)
3. ✓ MEP rough-in commencement (on schedule)
4. → Review weather forecast, prepare contingencies
5. → Finalize finishes procurement orders

### Approvals Needed
- [ ] Client sign-off on MEP rough routing (due Week 8)
- [ ] Final finishes selections (due Week 8)
- [ ] Change order for soil stabilization work (due Week 8)

### Key Meetings
- Client project review: Thursday, Week 8
- Health & safety committee: Monday, Week 9
- Subcontractor coordination: Tuesday, Week 9
- Weekly team huddle: Friday, Week 9

---

## Corrective Actions in Progress

1. **Schedule Recovery**: Accelerate structural phase to recover 1-week delay
   - Owner: Site Manager
   - Status: In progress (on track to recover 0.5 weeks by Week 10)

2. **Budget Control**: Implement weekly cost monitoring
   - Owner: Finance
   - Status: New system implemented, shows daily variances

3. **Risk Management**: Increased weather monitoring
   - Owner: Site Manager
   - Status: Weather contingencies in place

---

## Financial Summary

| Category | Budget | Spent | Remaining | Forecast | Variance |
|----------|--------|-------|-----------|-----------|----------|
| Labor | £1,200,000 | £810,000 | £390,000 | £1,240,000 | +£40,000 |
| Materials | £1,500,000 | £750,000 | £750,000 | £1,520,000 | +£20,000 |
| Equipment | £300,000 | £180,000 | £120,000 | £316,000 | +£16,000 |
| Contingency | £200,000 | £63,000 | £137,000 | £220,000 | +£20,000 |
| **TOTAL** | **£3,200,000** | **£1,803,000** | **£1,397,000** | **£3,296,000** | **+£96,000** |

---

## Recommendations

### Immediate (This Week)
1. **Approve corrective actions** for schedule recovery
2. **Authorize change order** for soil stabilization (£75k)
3. **Confirm MEP subcontractor** mobilization

### Short-term (Next 2 Weeks)
1. **Implement weekly cost tracking** to control variance
2. **Finalize finishes selections** to avoid delays
3. **Prepare contingency plans** for remaining risks

### Strategic
1. **Review final completion date** - currently forecasting Week 14 vs. planned Week 12
2. **Assess impact on Client occupancy** - handover delay implications?
3. **Plan acceleration options** - additional resources, parallel work phases?

---

## Sign-off

**Project Manager**: _________________________ Date: _________

**Client Representative**: __________________ Date: _________

**Prepared By**: [Name], Project Manager  
**Report Date**: 2026-04-21  
**Next Report**: 2026-04-28

"""
    
    with open(output_path, 'w') as f:
        f.write(status_report)
    
    print(f"✓ Sample status report generated: {output_path}")

def main():
    """Generate all sample outputs."""
    import os
    
    output_dir = "sample_outputs"
    os.makedirs(output_dir, exist_ok=True)
    
    schedule_path = os.path.join(output_dir, "sample_schedule.csv")
    risk_path = os.path.join(output_dir, "sample_risk_register.md")
    status_path = os.path.join(output_dir, "sample_status_report.md")
    
    generate_sample_schedule_csv(schedule_path)
    generate_sample_risk_register(risk_path)
    generate_sample_status_report(status_path)
    
    print("\n✓ Sample PM outputs generated successfully!")
    print(f"  Schedule: {schedule_path}")
    print(f"  Risk Register: {risk_path}")
    print(f"  Status Report: {status_path}")

if __name__ == "__main__":
    main()
