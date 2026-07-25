# risk-management-specialist reference

## Risk Assessment Templates

### Hazard Analysis Worksheet

```
HAZARD ANALYSIS WORKSHEET

Product: [Device Name]
Document: HA-[Product]-[Rev]
Analyst: [Name]
Date: [Date]

| ID | Hazard | Hazardous Situation | Harm | P | S | Initial Risk | Control | Residual P | Residual S | Final Risk |
|----|--------|---------------------|------|---|---|--------------|---------|------------|------------|------------|
| H-001 | [Hazard] | [Situation] | [Harm] | [1-5] | [1-5] | [Level] | [Control ref] | [1-5] | [1-5] | [Level] |
```

### FMEA Worksheet

```
FMEA WORKSHEET

Product: [Device Name]
Subsystem: [Subsystem]
Analyst: [Name]
Date: [Date]

| ID | Item | Function | Failure Mode | Effect | S | Cause | O | Control | D | RPN | Action |
|----|------|----------|--------------|--------|---|-------|---|---------|---|-----|--------|
| FM-001 | [Item] | [Function] | [Mode] | [Effect] | [1-10] | [Cause] | [1-10] | [Detection] | [1-10] | [S×O×D] | [Action] |

RPN Action Thresholds:
>200: Critical - Immediate action
100-200: High - Action plan required
50-100: Medium - Consider action
<50: Low - Monitor
```

### Risk Management Report Summary

```
RISK MANAGEMENT REPORT

Product: [Device Name]
Date: [Date]
Revision: [X.X]

SUMMARY:
- Total hazards identified: [N]
- Risk controls implemented: [N]
- Residual risks: [N] Low, [N] Medium, [N] High
- Overall conclusion: [Acceptable / Not Acceptable]

RISK DISTRIBUTION:
| Risk Level | Before Control | After Control |
|------------|----------------|---------------|
| Unacceptable | [N] | 0 |
| High | [N] | [N] |
| Medium | [N] | [N] |
| Low | [N] | [N] |

CONTROLS IMPLEMENTED:
- Inherent safety: [N]
- Protective measures: [N]
- Information for safety: [N]

OVERALL RESIDUAL RISK: [Acceptable / Reduced as far as possible (AFAP) demonstrated]
BENEFIT-RISK CONCLUSION: [If applicable]

APPROVAL:
Risk Management Lead: _____________ Date: _______
Quality Assurance: _____________ Date: _______
```

---
