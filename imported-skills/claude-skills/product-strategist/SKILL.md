---
name: "product-strategist"
description: Strategic product leadership toolkit for Head of Product covering OKR cascade generation, quarterly planning, competitive landscape analysis, product vision documents, and team scaling proposals. Use when creating quarterly OKR documents, defining product goals or KPIs, building product roadmaps, running competitive analysis, drafting team structure or hiring plans, aligning product strategy across engineering and design, or generating cascaded goal hierarchies from company to team level.
---

# Product Strategist

Strategic toolkit for Head of Product to drive vision, alignment, and organizational excellence.

---

## Core Capabilities

| Capability | Description | Tool |
|------------|-------------|------|
| **OKR Cascade** | Generate aligned OKRs from company to team level | `okr_cascade_generator.py` |
| **Alignment Scoring** | Measure vertical and horizontal alignment | Built into generator |
| **Strategy Templates** | 5 pre-built strategy types | Growth, Retention, Revenue, Innovation, Operational |
| **Team Configuration** | Customize for your org structure | `--teams` flag |

---

## Quick Start

```bash
# Growth strategy with default teams
python scripts/okr_cascade_generator.py growth

# Retention strategy with custom teams
python scripts/okr_cascade_generator.py retention --teams "Engineering,Design,Data"

# Revenue strategy with 40% product contribution
python scripts/okr_cascade_generator.py revenue --contribution 0.4

# Export as JSON for integration
python scripts/okr_cascade_generator.py growth --json > okrs.json
```

---

## Workflow: Quarterly Strategic Planning

### Step 1: Define Strategic Focus

| Strategy | When to Use |
|----------|-------------|
| **Growth** | Scaling user base, market expansion |
| **Retention** | Reducing churn, improving LTV |
| **Revenue** | Increasing ARPU, new monetization |
| **Innovation** | Market differentiation, new capabilities |
| **Operational** | Improving efficiency, scaling operations |

See `references/strategy_types.md` for detailed guidance.

### Step 2: Gather Input Metrics

```json
{
  "current": 100000,      // Current MAU
  "target": 150000,       // Target MAU
  "current_nps": 40,      // Current NPS
  "target_nps": 60        // Target NPS
}
```

### Step 3: Configure Teams & Run Generator

```bash
# Default teams
python scripts/okr_cascade_generator.py growth

# Custom org structure with contribution percentage
python scripts/okr_cascade_generator.py growth \
  --teams "Core,Platform,Mobile,AI" \
  --contribution 0.3
```

### Step 4: Review Alignment Scores

| Score | Target | Action if Below |
|-------|--------|-----------------|
| Vertical Alignment | >90% | Ensure all objectives link to parent |
| Horizontal Alignment | >75% | Check for team coordination gaps |
| Coverage | >80% | Validate all company OKRs are addressed |
| Balance | >80% | Redistribute if one team is overloaded |
| **Overall** | **>80%** | <60% needs restructuring |

### Step 5: Refine, Validate, and Export

Before finalizing:

- [ ] Review generated objectives with stakeholders
- [ ] Adjust team assignments based on capacity
- [ ] Validate contribution percentages are realistic
- [ ] Ensure no conflicting objectives across teams
- [ ] Set up tracking cadence (bi-weekly check-ins)

```bash
# Export JSON for tools like Lattice, Ally, Workboard
python scripts/okr_cascade_generator.py growth --json > q1_okrs.json
```

---

## OKR Cascade Generator

### Usage

```bash
python scripts/okr_cascade_generator.py [strategy] [options]
```

**Strategies:** `growth` | `retention` | `revenue` | `innovation` | `operational`

### Configuration Options

| Option | Description | Default |
|--------|-------------|---------|
| `--teams`, `-t` | Comma-separated team names | Growth,Platform,Mobile,Data |
| `--contribution`, `-c` | Product contribution to company OKRs (0-1) | 0.3 (30%) |
| `--json`, `-j` | Output as JSON instead of dashboard | False |
| `--metrics`, `-m` | Metrics as JSON string | Sample metrics |

### Output Examples

#### Dashboard Output (`growth` strategy)

```
============================================================
OKR CASCADE DASHBOARD
Quarter: Q1 2025  |  Strategy: GROWTH
Teams: Growth, Platform, Mobile, Data  |  Product Contribution: 30%
============================================================

🏢 COMPANY OKRS
📌 CO-1: Accelerate user acquisition and market expansion
   └─ CO-1-KR1: Increase MAU from 100,000 to 150,000
   └─ CO-1-KR2: Achieve 50% MoM growth rate
   └─ CO-1-KR3: Expand to 3 new markets

📌 CO-2: Achieve product-market fit in new segments
📌 CO-3: Build sustainable growth engine

🚀 PRODUCT OKRS
📌 PO-1: Build viral product features and market expansion
   ↳ Supports: CO-1
   └─ PO-1-KR1: Increase product MAU to 45,000
   └─ PO-1-KR2: Achieve 45% feature adoption rate

👥 TEAM OKRS
Growth Team:
  📌 GRO-1: Build viral product features through acquisition and activation
     └─ GRO-1-KR1: Increase product MAU to 11,250
     └─ GRO-1-KR2: Achieve 11.25% feature adoption rate

🎯 ALIGNMENT SCORES
✓ Vertical Alignment: 100.0%
! Horizontal Alignment: 75.0%
✓ Coverage: 100.0%  |  ✓ Balance: 97.5%  |  ✓ Overall: 94.0%
✅ Overall alignment is GOOD (≥80%)
```

#### JSON Output (`retention --json`, truncated)

```json
{
  "quarter": "Q1 2025",
  "strategy": "retention",
  "company": {
    "objectives": [
      {
        "id": "CO-1",
        "title": "Create lasting customer value and loyalty",
        "key_results": [
          { "id": "CO-1-KR1", "title": "Improve retention from 70% to 85%", "current": 70, "target": 85 }
        ]
      }
    ]
  },
  "product": { "contribution": 0.3, "objectives": ["..."] },
  "teams": ["..."],
  "alignment_scores": {
    "vertical_alignment": 100.0, "horizontal_alignment": 75.0,
    "coverage": 100.0, "balance": 97.5, "overall": 94.0
  }
}
```

See `references/examples/sample_growth_okrs.json` for a complete example.

---

## Reference Documents

| Document | Description |
|----------|-------------|
| `references/okr_framework.md` | OKR methodology, writing guidelines, alignment scoring |
| `references/strategy_types.md` | Detailed breakdown of all 5 strategy types with examples |
| `references/examples/sample_growth_okrs.json` | Complete sample output for growth strategy |

---

## Best Practices

### OKR Cascade

- Limit to 3-5 objectives per level, each with 3-5 key results
- Key results must be measurable with current and target values
- Validate parent-child relationships before finalizing

### Alignment Scoring

- Target >80% overall alignment; investigate any score below 60%
- Balance scores ensure no team is overloaded
- Horizontal alignment prevents conflicting goals across teams

### Team Configuration

- Configure teams to match your actual org structure
- Adjust contribution percentages based on team size
- Platform/Infrastructure teams often support all objectives
- Specialized teams (ML, Data) may only support relevant objectives

## Related Skills

- **Senior PM** (`project-management/senior-pm/`) — Portfolio management and risk analysis inform strategic planning
- **Competitive Teardown** (`product-team/competitive-teardown/`) — Competitive intelligence feeds product strategy
