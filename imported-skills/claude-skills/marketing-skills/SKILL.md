---
name: "marketing-skills"
description: "Directory and router for the marketing skills library. Use when you need to find the right marketing skill for a task, see what marketing capabilities exist, or get oriented in this plugin. 44 specialist skills across 8 pods (content, SEO + AEO, CRO, channels, growth, intelligence, sales enablement, ops), 59 stdlib Python tools. Routes to one skill — it does not execute marketing work itself."
version: 2.10.3
author: Alireza Rezvani
license: MIT
tags:
  - marketing
  - router
  - index
agents:
  - claude-code
  - codex-cli
  - openclaw
---

# Marketing Skills — Directory + Router

This is the index skill for the marketing plugin. It does one job: route you to the right specialist skill, then get out of the way. For request-by-request routing logic, [../marketing-ops/SKILL.md](../marketing-ops/SKILL.md) is the canonical router — this file is the map.

**Counts (kept honest):** 44 specialist skills in `skills/` (plus this index and the deprecated `content-creator` redirect), 1 video skill in `video-content-strategist/`, 59 stdlib-only Python tools. No pip installs needed.

## Start Here

1. **First run ever?** Use `skills/marketing-context/` to create `.claude/product-marketing-context.md`. Every other skill reads it for brand voice, personas, and competitive landscape.
2. **Know your task?** Find it in the route table below and load only that skill's `SKILL.md`.
3. **Ambiguous request?** Load `skills/marketing-ops/` — its routing matrix maps phrasings to skills.

## Route Table

All paths are relative to `marketing-skill/`.

### Foundation + Ops
| Task | Skill |
|---|---|
| Capture brand/product context (run first) | `skills/marketing-context/` |
| Route a request, plan campaigns, pick channels | `skills/marketing-ops/` |
| Demand gen programs, funnel + CRM ops | `skills/marketing-demand-acquisition/` |
| Positioning, ICP, product marketing strategy | `skills/marketing-strategy-pmm/` |
| Brand voice/visual consistency audits | `skills/brand-guidelines/` |

### Content
| Task | Skill |
|---|---|
| Write blog posts, articles, guides | `skills/content-production/` |
| Plan what content to create | `skills/content-strategy/` |
| Edit copy (Seven Sweeps) | `skills/copy-editing/` |
| Fix AI-sounding content | `skills/content-humanizer/` |
| Landing/sales page copy | `skills/copywriting/` |
| Headlines, hooks, idea generation | `skills/marketing-ideas/` |
| Persuasion frameworks, mental models | `skills/marketing-psychology/` |

### SEO + AEO
| Task | Skill |
|---|---|
| Traditional SEO audit | `skills/seo-audit/` |
| AI search citations (ChatGPT, Perplexity, AI Overviews) | `skills/aeo/` |
| Programmatic SEO at scale | `skills/programmatic-seo/` |
| Structured data / schema.org | `skills/schema-markup/` |
| Site structure, internal linking | `skills/site-architecture/` |

### CRO (conversion)
| Task | Skill |
|---|---|
| Landing/marketing page conversion | `skills/page-cro/` |
| Forms | `skills/form-cro/` |
| Signup flow | `skills/signup-flow-cro/` |
| Onboarding/activation | `skills/onboarding-cro/` |
| Popups/modals | `skills/popup-cro/` |
| Paywall/upgrade screens | `skills/paywall-upgrade-cro/` |
| A/B test design + sample size | `skills/ab-test-setup/` |

### Channels
| Task | Skill |
|---|---|
| Email sequences/drips | `skills/email-sequence/` |
| Cold outbound email | `skills/cold-email/` |
| Paid ads (Google/Meta/LinkedIn) | `skills/paid-ads/` |
| Ad creative + copy | `skills/ad-creative/` |
| Social calendar + management | `skills/social-media-manager/` |
| Platform-native social posts | `skills/social-content/` |
| X/Twitter growth | `skills/x-twitter-growth/` |
| YouTube (data + strategy) | `skills/youtube-full/` |
| Video content strategy | `video-content-strategist/` (sibling folder, own plugin) |
| Webinars (funnel math) | `skills/webinar-marketing/` |
| App Store / Play Store (ASO) | `skills/app-store-optimization/` |

### Growth
| Task | Skill |
|---|---|
| Launches (PH, HN, etc.) | `skills/launch-strategy/` |
| Pricing + packaging | `skills/pricing-strategy/` |
| Referral programs | `skills/referral-program/` |
| Free tools as acquisition | `skills/free-tool-strategy/` |
| Churn prevention | `skills/churn-prevention/` |

### Intelligence + Sales Enablement
| Task | Skill |
|---|---|
| Campaign performance, attribution | `skills/campaign-analytics/` |
| Tracking plans, UTM, GA4 key events | `skills/analytics-tracking/` |
| Social account analysis | `skills/social-media-analyzer/` |
| Competitor/alternatives pages | `skills/competitor-alternatives/` |
| LLM prompt templates + governance for marketing teams | `skills/prompt-engineer-toolkit/` |

## Python Tools

Each skill documents its own tools in its SKILL.md (a "Tools" or workflow section with exact CLI lines). Invoke from the skill's folder:

```bash
python3 skills/<skill>/scripts/<tool>.py --help
```

All 59 scripts are stdlib-only; most run a demo with no args.

## Rules

- Load ONE specialist skill per task — never bulk-load.
- If `.claude/product-marketing-context.md` exists, read it before any marketing task.
- `content-creator` is deprecated — use `skills/content-production/`.
- Don't pip-install anything for these tools.
