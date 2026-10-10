# Organizational overhead and team cost (Steps 7 + 8)

## Step 7: Developers don't code 40 hours/week

Developers do not code 40 hours per week. Convert total engineering hours to calendar time using efficiency:

| Company type | Coding efficiency | Focused coding hrs/week |
|---|---|---|
| Solo / founder | 65 – 75% | 26 – 30 |
| Lean startup | 55 – 65% | 22 – 26 |
| Growth company | 45 – 55% | 18 – 22 |
| Enterprise | 35 – 45% | 14 – 18 |
| Large bureaucracy | 25 – 35% | 10 – 14 |

```
calendar_weeks  = Total_Eng_Hours / (40 × efficiency)
calendar_months = calendar_weeks / 4.33
```

Report across all five company types.

---

## Step 8: Full team cost (engineering isn't shipped alone)

Role ratios (fraction of engineering hours) and typical rates:

| Role | Ratio | Typical Rate |
|---|---|---|
| Product Management | 0.25 – 0.40 | $125 – 200/hr |
| UX / UI Design | 0.20 – 0.35 | $100 – 175/hr |
| Engineering Management | 0.12 – 0.20 | $150 – 225/hr |
| QA / Testing | 0.15 – 0.25 | $75 – 125/hr |
| Project / Program Mgmt | 0.08 – 0.15 | $100 – 150/hr |
| Technical Writing | 0.05 – 0.10 | $75 – 125/hr |
| DevOps / Platform | 0.10 – 0.20 | $125 – 200/hr |

## Team composition by stage (approx. engineering-cost multipliers)

| Stage | Multiplier | Staffed roles |
|---|---|---|
| Solo / founder | 1.0× | Engineering only |
| Lean startup | ~1.45× | Eng + light PM/design/DevOps |
| Growth company | ~2.2× | Core team, no program mgmt |
| Enterprise | ~2.65× | All roles |

Compute full-team cost at engineering P50 for each stage.
