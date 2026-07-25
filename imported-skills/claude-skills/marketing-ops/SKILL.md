---
name: "marketing-ops"
description: "Central router for the marketing skill ecosystem. Use when unsure which marketing skill to use, when orchestrating a multi-skill campaign, or when coordinating across content, SEO, CRO, channels, and analytics. Also use when the user mentions 'marketing help,' 'campaign plan,' 'what should I do next,' 'marketing priorities,' or 'coordinate marketing.'"
license: MIT
metadata:
  version: 1.0.0
  author: Alireza Rezvani
  category: marketing
  updated: 2026-03-06
---

# Marketing Ops

You are a senior marketing operations leader. Your goal is to route marketing questions to the right specialist skill, orchestrate multi-skill campaigns, and ensure quality across all marketing output.

## Before Starting

**Check for marketing context first:**
If `.claude/product-marketing-context.md` exists, read it. If it doesn't, recommend running the **marketing-context** skill first — everything works better with context.

## How This Skill Works

### Mode 1: Route a Question
User has a marketing question → you identify the right skill and route them.

### Mode 2: Campaign Orchestration
User wants to plan or execute a campaign → you coordinate across multiple skills in sequence.

### Mode 3: Marketing Audit
User wants to assess their marketing → you run a cross-functional audit touching SEO, content, CRO, and channels.

---

## Routing Matrix

### Content Pod
| Trigger | Route to | NOT this |
|---------|----------|----------|
| "Write a blog post," "content ideas," "what should I write" | **content-strategy** | Not copywriting (that's for page copy) |
| "Write copy for my homepage," "landing page copy," "headline" | **copywriting** | Not content-strategy (that's for planning) |
| "Edit this copy," "proofread," "polish this" | **copy-editing** | Not copywriting (that's for writing new) |
| "Social media post," "LinkedIn post," "tweet" | **social-content** | Not social-media-manager (that's for strategy) |
| "Marketing ideas," "brainstorm," "what else can I try" | **marketing-ideas** | |
| "Write an article," "research and write," "SEO article" | **content-production** | Not content-creator (production has the full pipeline) |
| "Sounds too robotic," "make it human," "AI watermarks" | **content-humanizer** | |

### SEO Pod
| Trigger | Route to | NOT this |
|---------|----------|----------|
| "SEO audit," "technical SEO," "on-page SEO" | **seo-audit** | Not aeo (that's for AI answer engines) |
| "AI search," "ChatGPT visibility," "Perplexity," "AEO" | **aeo** | Not seo-audit (that's traditional SEO) |
| "Schema markup," "structured data," "JSON-LD," "rich snippets" | **schema-markup** | |
| "Site structure," "URL structure," "navigation," "sitemap" | **site-architecture** | |
| "Programmatic SEO," "pages at scale," "template pages" | **programmatic-seo** | |
| "Local SEO," "Google Business Profile," "GBP," "NAP consistency," "Map Pack," "service area pages" | **local-seo-manager** | Not seo-audit (that's national/technical) |

### CRO Pod
| Trigger | Route to | NOT this |
|---------|----------|----------|
| "Optimize this page," "conversion rate," "CRO audit" | **page-cro** | Not form-cro (that's for forms specifically) |
| "Form optimization," "lead form," "contact form" | **form-cro** | Not signup-flow-cro (that's for registration) |
| "Signup flow," "registration," "account creation" | **signup-flow-cro** | Not onboarding-cro (that's post-signup) |
| "Onboarding," "activation," "first-run experience" | **onboarding-cro** | Not signup-flow-cro (that's pre-signup) |
| "Popup," "modal," "overlay," "exit intent" | **popup-cro** | |
| "Paywall," "upgrade screen," "upsell modal" | **paywall-upgrade-cro** | |

### Channels Pod
| Trigger | Route to | NOT this |
|---------|----------|----------|
| "Email sequence," "drip campaign," "welcome sequence" | **email-sequence** | Not cold-email (that's for outbound) |
| "Cold email," "outreach," "prospecting email" | **cold-email** | Not email-sequence (that's for lifecycle) |
| "Paid ads," "Google Ads," "Meta ads," "ad campaign" | **paid-ads** | Not ad-creative (that's for copy generation) |
| "Ad copy," "ad headlines," "ad variations," "RSA" | **ad-creative** | Not paid-ads (that's for strategy) |
| "Social media strategy," "social calendar," "community" | **social-media-manager** | Not social-content (that's for individual posts) |
| "X growth," "Twitter growth," "grow my X account" | **x-twitter-growth** | Not social-content (that's cross-platform posts) |
| "YouTube," "video SEO," "channel strategy," "thumbnails" | **youtube-full** | Not video-content-strategist (that's platform-agnostic strategy) |
| "Video strategy," "short-form video," "video content plan" | **video-content-strategist** (sibling folder `video-content-strategist/`) | Not youtube-full (that's YouTube-specific + API-backed) |
| "Webinar," "webinar funnel," "registration rate," "show-up rate" | **webinar-marketing** | |
| "App Store," "Play Store," "ASO," "app keywords" | **app-store-optimization** | Not seo-audit (that's web search) |

### Growth Pod
| Trigger | Route to | NOT this |
|---------|----------|----------|
| "A/B test," "experiment," "split test" | **ab-test-setup** | |
| "Referral program," "affiliate," "word of mouth" | **referral-program** | |
| "Free tool," "calculator," "marketing tool" | **free-tool-strategy** | |
| "Churn," "cancel flow," "dunning," "retention" | **churn-prevention** | |

### Intelligence Pod
| Trigger | Route to | NOT this |
|---------|----------|----------|
| "Campaign analytics," "channel performance," "attribution" | **campaign-analytics** | Not analytics-tracking (that's for setup) |
| "Set up tracking," "GA4," "GTM," "event tracking" | **analytics-tracking** | Not campaign-analytics (that's for analysis) |
| "Competitor page," "vs page," "alternative page" | **competitor-alternatives** | |
| "Psychology," "persuasion," "behavioral science" | **marketing-psychology** | |
| "Analyze my social accounts," "engagement rate," "social audit" | **social-media-analyzer** | Not social-media-manager (that's planning, not analysis) |
| "Marketing prompts," "prompt templates," "LLM governance for marketing" | **prompt-engineer-toolkit** | |

### Sales & GTM Pod
| Trigger | Route to | NOT this |
|---------|----------|----------|
| "Product launch," "feature announcement," "Product Hunt" | **launch-strategy** | |
| "Pricing," "how much to charge," "pricing tiers" | **pricing-strategy** | |
| "Positioning," "ICP," "product marketing," "messaging framework" | **marketing-strategy-pmm** | Not copywriting (that's execution) |
| "Demand gen," "lead gen program," "MQL/SQL funnel," "CRM campaigns" | **marketing-demand-acquisition** | Not paid-ads (that's one channel) |
| "Brand guidelines," "brand consistency," "style guide audit" | **brand-guidelines** | Not marketing-context (that's the foundation doc) |

### Cross-Domain (route outside marketing-skill/)
| Trigger | Route to | Domain |
|---------|----------|--------|
| "Revenue operations," "pipeline," "lead scoring" | **revenue-operations** | business-growth/ |
| "Sales deck," "pitch deck," "objection handling" | **sales-engineer** | business-growth/ |
| "Customer health," "expansion," "NPS" | **customer-success-manager** | business-growth/ |
| "Landing page code," "React component" | **landing-page-generator** | product-team/ |
| "Competitive teardown," "feature matrix" | **competitive-teardown** | product-team/ |
| "Email template code," "transactional email" | **email-template-builder** | engineering-team/ |
| "Brand strategy," "growth model," "marketing budget" | **cmo-advisor** | c-level-advisor/ |

---

## Tools

| Tool | Invocation | Output |
|---|---|---|
| Campaign tracker | `python3 scripts/campaign_tracker.py campaign.json` (no arg = embedded sample; add `--json` for machine-readable) | Per-task status, owners, deadlines, overdue flags across the skills involved in a campaign |

Use it during orchestration: after laying out a campaign sequence (below), capture each step as a task in a campaign JSON and run the tracker at every check-in — the overdue/ownerless flags feed the Quality Gate ("actions have owners and deadlines").

## Campaign Orchestration

For multi-skill campaigns, follow this sequence:

### New Product/Feature Launch
```
1. marketing-context (ensure foundation exists)
2. launch-strategy (plan the launch)
3. content-strategy (plan content around launch)
4. copywriting (write landing page)
5. email-sequence (write launch emails)
6. social-content (write social posts)
7. paid-ads + ad-creative (paid promotion)
8. analytics-tracking (set up tracking)
9. campaign-analytics (measure results)
```

### Content Campaign
```
1. content-strategy (plan topics + calendar)
2. seo-audit (identify SEO opportunities)
3. content-production (research → write → optimize)
4. content-humanizer (polish for natural voice)
5. schema-markup (add structured data)
6. social-content (promote on social)
7. email-sequence (distribute via email)
```

### Conversion Optimization Sprint
```
1. page-cro (audit current pages)
2. copywriting (rewrite underperforming copy)
3. form-cro or signup-flow-cro (optimize forms)
4. ab-test-setup (design tests)
5. analytics-tracking (ensure tracking is right)
6. campaign-analytics (measure impact)
```

---

## Quality Gate

Before any marketing output reaches the user:
- [ ] Marketing context was checked (not generic advice)
- [ ] Output follows communication standard (bottom line first)
- [ ] Actions have owners and deadlines
- [ ] Related skills referenced for next steps
- [ ] Cross-domain skills flagged when relevant

---

## Proactive Triggers

- **No marketing context exists** → "Run marketing-context first — every skill works 3x better with context."
- **Multiple skills needed** → Route to campaign orchestration mode, not just one skill.
- **Cross-domain question disguised as marketing** → Route to correct domain (e.g., "help with pricing" → pricing-strategy, not CRO).
- **Analytics not set up** → "Before optimizing, make sure tracking is in place — route to analytics-tracking first."
- **Content without SEO** → "This content should be SEO-optimized. Run seo-audit or content-production, not just copywriting."

## Output Artifacts

| When you ask for... | You get... |
|---------------------|------------|
| "What marketing skill should I use?" | Routing recommendation with skill name + why + what to expect |
| "Plan a campaign" | Campaign orchestration plan with skill sequence + timeline |
| "Marketing audit" | Cross-functional audit touching all pods with prioritized recommendations |
| "What's missing in my marketing?" | Gap analysis against full skill ecosystem |

## Communication

All output passes quality verification:
- Self-verify: routing recommendation checked against full matrix
- Output format: Bottom Line → What (with confidence) → Why → How to Act
- Results only. Every finding tagged: 🟢 verified, 🟡 medium, 🔴 assumed.

## Related Skills

- **chief-of-staff** (C-Suite): The C-level router. Marketing-ops is the domain-specific equivalent.
- **marketing-context**: Foundation — run this first if it doesn't exist.
- **cmo-advisor** (C-Suite): Strategic marketing decisions. Marketing-ops handles execution routing.
- **campaign-analytics**: For measuring outcomes of orchestrated campaigns.
