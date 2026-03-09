# FAF AI-Readiness Tier System

The Michelin Star rating for AI context quality.

## Tiers

| Tier | Score | Meaning |
|------|-------|---------|
| Big Orange | 105% | Michelin Star - Perfect + bonus |
| Trophy | 100% | Perfect compliance |
| Gold | 99%+ | Exceptional |
| Silver | 95%+ | Excellent |
| Bronze | 85%+ | Production ready |
| Green | 70%+ | Solid foundation |
| Yellow | 55%+ | Needs improvement |
| Red | <55% | Major gaps |
| White | 0% | No context |

## Scoring

### Core (40 pts)
- `faf_version`: 5 pts
- `project.name`: 10 pts
- `project.description` (>20 chars): 15 pts
- `project.stack`: 10 pts

### Context (30 pts)
- `context.architecture`: 10 pts
- `context.key_files` (3+): 10 pts
- `context.conventions` (2+): 10 pts

### AI Guidance (20 pts)
- `ai_guidance.priorities`: 8 pts
- `ai_guidance.avoid`: 7 pts
- `ai_guidance.testing`: 5 pts

### Bonus (15 pts max)
- Deployment section: +5 pts
- Integrations: +5 pts
- Under 200 lines: +3 pts
- Doc cross-refs: +2 pts

## Philosophy

> AI-Readiness is not documentation. It's the minimum context that changes AI behavior.

**Target: Bronze (85%+)** - where AI collaboration becomes productive.
