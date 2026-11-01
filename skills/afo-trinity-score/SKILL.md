---
name: trinity-score-calculator
description: Calculate the 5-Pillar Trinity Score (眞善美孝永) with weighted philosophy alignment. Core evaluation system for AFO Kingdom decisions.
license: MIT
compatibility:
  - claude-code
  - codex
  - cursor
metadata:
  version: "2.0.0"
  category: analysis-evaluation
  author: AFO Kingdom
  philosophy_weights:
    truth: 35
    goodness: 35
    beauty: 20
    serenity: 8
    eternity: 2
allowed-tools:
  - mcp__afo-ultimate-mcp__calculate_trinity_score
  - mcp__trinity-score-mcp__calculate
---

# Trinity Score Calculator (眞善美孝永)

The Trinity Score is the core philosophy alignment metric for the AFO Kingdom, evaluating decisions and actions against the 5 pillars of wisdom.

## Philosophy Pillars

| Pillar | Korean | Weight | Description |
|--------|--------|--------|-------------|
| Truth (眞) | 진 | 35% | Technical accuracy, verifiability, factual correctness |
| Goodness (善) | 선 | 35% | Ethical soundness, stability, no harm to systems |
| Beauty (美) | 미 | 20% | Clear structure, elegant design, UX clarity |
| Serenity (孝) | 효 | 8% | Frictionless operation, low cognitive load |
| Eternity (永) | 영 | 2% | Long-term sustainability, reproducibility |

## Usage

Calculate a Trinity Score by providing base scores for each pillar:

```json
{
  "truth_base": 95,
  "goodness_base": 90,
  "beauty_base": 85,
  "risk_score": 5,
  "friction": 3,
  "eternity_base": 88
}
```

## Decision Thresholds

- **AUTO_RUN**: Trinity Score ≥ 90 AND Risk Score ≤ 10
- **ASK_COMMANDER**: Trinity Score 70-89 OR Risk Score 11-30
- **BLOCK**: Trinity Score < 70 OR Risk Score > 30

## Integration

This skill integrates with:
- Chancellor Graph for decision routing
- MCP Tool Bridge for external validations
- All AFO skills for philosophy alignment tracking

## Example Output

```json
{
  "trinity_score": 0.92,
  "balance_status": "balanced",
  "decision": "AUTO_RUN",
  "pillar_scores": {
    "truth": 0.95,
    "goodness": 0.90,
    "beauty": 0.85,
    "filial_serenity": 0.88,
    "eternity": 0.90
  }
}
```
