---
name: "scrum-master"
description: "Advanced Scrum Master skill for data-driven agile team analysis and coaching. Use when the user asks about sprint planning, velocity tracking, retrospectives, standup facilitation, backlog grooming, story points, burndown charts, blocker resolution, or agile team health. Runs Python scripts to analyse sprint JSON exports from Jira or similar tools: velocity_analyzer.py for Monte Carlo sprint forecasting, sprint_health_scorer.py for multi-dimension health scoring, and retrospective_analyzer.py for action-item and theme tracking. Produces confidence-interval forecasts, health grade reports, and improvement-velocity trends for high-performing Scrum teams."
license: MIT
metadata:
  version: 2.0.0
  author: Alireza Rezvani
  category: project-management
  domain: agile-development
  updated: 2026-02-15
  python-tools: velocity_analyzer.py, sprint_health_scorer.py, retrospective_analyzer.py
  tech-stack: scrum, agile-coaching, team-dynamics, data-analysis
---

# Scrum Master Expert

Data-driven Scrum Master skill combining sprint analytics, probabilistic forecasting, and team development coaching. The unique value is in the three Python analysis scripts and their workflows — refer to `references/` and `assets/` for deeper framework detail.

---

## Table of Contents

- [Analysis Tools & Usage](#analysis-tools-usage)
- [Input Requirements](#input-requirements)
- [Sprint Execution Workflows](#sprint-execution-workflows)
- [Team Development Workflow](#team-development-workflow)
- [Key Metrics & Targets](#key-metrics-targets)
- [Limitations](#limitations)

---

## Analysis Tools & Usage

### 1. Velocity Analyzer (`scripts/velocity_analyzer.py`)

Runs rolling averages, linear-regression trend detection, and Monte Carlo simulation over sprint history.

```bash
# Text report
python velocity_analyzer.py sprint_data.json --format text

# JSON output for downstream processing
python velocity_analyzer.py sprint_data.json --format json > analysis.json
```

**Outputs**: velocity trend (improving/stable/declining), coefficient of variation, 6-sprint Monte Carlo forecast at 50 / 70 / 85 / 95% confidence intervals, anomaly flags with root-cause suggestions.

**Validation**: If fewer than 3 sprints are present in the input, stop and prompt the user: *"Velocity analysis needs at least 3 sprints. Please provide additional sprint data."* 6+ sprints are recommended for statistically significant Monte Carlo results.

---

### 2. Sprint Health Scorer (`scripts/sprint_health_scorer.py`)

Scores team health across 6 weighted dimensions, producing an overall 0–100 grade.

| Dimension | Weight | Target |
|---|---|---|
| Commitment Reliability | 25% | >85% sprint goals met |
| Scope Stability | 20% | <15% mid-sprint changes |
| Blocker Resolution | 15% | <3 days average |
| Ceremony Engagement | 15% | >90% participation |
| Story Completion Distribution | 15% | High ratio of fully done stories |
| Velocity Predictability | 10% | CV <20% |

```bash
python sprint_health_scorer.py sprint_data.json --format text
```

**Outputs**: overall health score + grade, per-dimension scores with recommendations, sprint-over-sprint trend, intervention priority matrix.

**Validation**: Requires 2+ sprints with ceremony and story-completion data. If data is missing, report which dimensions cannot be scored and ask the user to supply the gaps.

---

### 3. Retrospective Analyzer (`scripts/retrospective_analyzer.py`)

Tracks action-item completion, recurring themes, sentiment trends, and team maturity progression.

```bash
python retrospective_analyzer.py sprint_data.json --format text
```

**Outputs**: action-item completion rate by priority/owner, recurring-theme persistence scores, team maturity level (forming/storming/norming/performing), improvement-velocity trend.

**Validation**: Requires 3+ retrospectives with action-item tracking. With fewer, note the limitation and offer partial theme analysis only.

---

## Input Requirements

All scripts accept JSON following the schema in `assets/sample_sprint_data.json`:

```json
{
  "team_info": { "name": "string", "size": "number", "scrum_master": "string" },
  "sprints": [
    {
      "sprint_number": "number",
      "planned_points": "number",
      "completed_points": "number",
      "stories": [...],
      "blockers": [...],
      "ceremonies": {...}
    }
  ],
  "retrospectives": [
    {
      "sprint_number": "number",
      "went_well": ["string"],
      "to_improve": ["string"],
      "action_items": [...]
    }
  ]
}
```

Jira and similar tools can export sprint data; map exported fields to this schema before running the scripts. See `assets/sample_sprint_data.json` for a complete 6-sprint example and `assets/expected_output.json` for corresponding expected results (velocity avg 20.2 pts, CV 12.7%, health score 78.3/100, action-item completion 46.7%).

---

## Sprint Execution Workflows

### Sprint Planning

1. Run velocity analysis: `python velocity_analyzer.py sprint_data.json --format text`
2. Use the 70% confidence interval as the recommended commitment ceiling for the sprint backlog.
3. Review the health scorer's Commitment Reliability and Scope Stability scores to calibrate negotiation with the Product Owner.
4. If Monte Carlo output shows high volatility (CV >20%), surface this to stakeholders with range estimates rather than single-point forecasts.
5. Document capacity assumptions (leave, dependencies) for retrospective comparison.

### Daily Standup

1. Track participation and help-seeking patterns — feed ceremony data into `sprint_health_scorer.py` at sprint end.
2. Log each blocker with date opened; resolution time feeds the Blocker Resolution dimension.
3. If a blocker is unresolved after 2 days, escalate proactively and note in sprint data.

### Sprint Review

1. Present velocity trend and health score alongside the demo to give stakeholders delivery context.
2. Capture scope-change requests raised during review; record as scope-change events in sprint data for next scoring cycle.

### Sprint Retrospective

1. Run all three scripts before the session:
   ```bash
   python sprint_health_scorer.py sprint_data.json --format text > health.txt
   python retrospective_analyzer.py sprint_data.json --format text > retro.txt
   ```
2. Open with the health score and top-flagged dimensions to focus discussion.
3. Use the retrospective analyzer's action-item completion rate to determine how many new action items the team can realistically absorb (target: ≤3 if completion rate <60%).
4. Assign each action item an owner and measurable success criterion before closing the session.
5. Record new action items in `sprint_data.json` for tracking in the next cycle.

---

## Team Development Workflow

### Assessment

```bash
python sprint_health_scorer.py team_data.json > health_assessment.txt
python retrospective_analyzer.py team_data.json > retro_insights.txt
```

- Map retrospective analyzer maturity output to the appropriate development stage.
- Supplement with an anonymous psychological safety pulse survey (Edmondson 7-point scale) and individual 1:1 observations.
- If maturity output is `forming` or `storming`, prioritise safety and conflict-facilitation interventions before process optimisation.

### Intervention

Apply stage-specific facilitation (details in `references/team-dynamics-framework.md`):

| Stage | Focus |
|---|---|
| Forming | Structure, process education, trust building |
| Storming | Conflict facilitation, psychological safety maintenance |
| Norming | Autonomy building, process ownership transfer |
| Performing | Challenge introduction, innovation support |

### Progress Measurement

- **Sprint cadence**: re-run health scorer; target overall score improvement of ≥5 points per quarter.
- **Monthly**: psychological safety pulse survey; target >4.0/5.0.
- **Quarterly**: full maturity re-assessment via retrospective analyzer.
- If scores plateau or regress for 2 consecutive sprints, escalate intervention strategy (see `references/team-dynamics-framework.md`).

---

## Key Metrics & Targets

| Metric | Target |
|---|---|
| Overall Health Score | >80/100 |
| Psychological Safety Index | >4.0/5.0 |
| Velocity CV (predictability) | <20% |
| Commitment Reliability | >85% |
| Scope Stability | <15% mid-sprint changes |
| Blocker Resolution Time | <3 days |
| Ceremony Engagement | >90% |
| Retrospective Action Completion | >70% |

---

## Limitations

- **Sample size**: fewer than 6 sprints reduces Monte Carlo confidence; always state confidence intervals, not point estimates.
- **Data completeness**: missing ceremony or story-completion fields suppress affected scoring dimensions — report gaps explicitly.
- **Context sensitivity**: script recommendations must be interpreted alongside organisational and team context not captured in JSON data.
- **Quantitative bias**: metrics do not replace qualitative observation; combine scores with direct team interaction.
- **Team size**: techniques are optimised for 5–9 member teams; larger groups may require adaptation.
- **External factors**: cross-team dependencies and organisational constraints are not fully modelled by single-team metrics.

---

## Related Skills

- **Agile Product Owner** (`product-team/agile-product-owner/`) — User stories and backlog feed sprint planning
- **Senior PM** (`project-management/senior-pm/`) — Portfolio health context informs sprint priorities

---

*For deep framework references see `references/velocity-forecasting-guide.md` and `references/team-dynamics-framework.md`. For template assets see `assets/sprint_report_template.md` and `assets/team_health_check_template.md`.*
