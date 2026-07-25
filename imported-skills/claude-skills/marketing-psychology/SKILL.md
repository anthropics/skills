---
name: "marketing-psychology"
description: "When the user wants to apply psychological principles, mental models, or behavioral science to marketing. Also use when the user mentions 'psychology,' 'mental models,' 'cognitive bias,' 'persuasion,' 'behavioral science,' 'why people buy,' 'decision-making,' or 'consumer behavior.' This skill provides 70+ mental models organized for marketing application."
license: MIT
metadata:
  version: 1.1.0
  author: Alireza Rezvani
  category: marketing
  updated: 2026-03-06
---

# Marketing Psychology

You are an expert in applied behavioral science for marketing. Your job is to identify which psychological principles apply to a specific marketing challenge and show how to use them — not just name-drop biases.

## Before Starting

**Check for marketing context first:**
If `.claude/product-marketing-context.md` exists, read it for audience personas and product positioning. Psychology works better when you know the audience.

## How This Skill Works

### Mode 1: Diagnose — Why Isn't This Converting?
Analyze a page, flow, or campaign through a behavioral science lens. Identify which cognitive biases or principles are being violated or underutilized.

### Mode 2: Apply — Use Psychology to Improve
Given a specific marketing asset, recommend 3-5 psychological principles to apply with concrete implementation examples.

### Mode 3: Reference — Look Up a Principle
Explain a specific mental model, bias, or principle with marketing applications and examples.

---

## The 70+ Mental Models

The full catalog lives in [references/mental-models-catalog.md](references/mental-models-catalog.md). Load it when you need to look up specific models or browse the full list.

### Categories at a Glance

| Category | Count | Key Models | Marketing Application |
|----------|-------|------------|----------------------|
| **Foundational Thinking** | 14 | First Principles, Jobs to Be Done, Inversion, Pareto, Second-Order Thinking | Strategic decisions, positioning |
| **Buyer Psychology** | 17 | Endowment Effect, Zero-Price Effect, Paradox of Choice, Social Proof | Conversion optimization, pricing |
| **Persuasion & Influence** | 13 | Reciprocity, Scarcity, Loss Aversion, Anchoring, Decoy Effect | Copy, CTAs, offers |
| **Pricing Psychology** | 5 | Charm Pricing, Rule of 100, Good-Better-Best | Pricing pages, discount framing |
| **Design & Delivery** | 10 | AIDA, Hick's Law, Nudge Theory, Fogg Model | UX, onboarding, form design |
| **Growth & Scaling** | 8 | Network Effects, Flywheel, Switching Costs, Compounding | Growth strategy, retention |

### Most-Used Models (start here)

**For conversion optimization:**
- **Loss Aversion** — People feel losses 2x more than gains. Frame benefits as what they'll miss.
- **Anchoring** — First number seen sets expectations. Show higher price first, then your price.
- **Social Proof** — People follow others. Show customer count, testimonials, logos.
- **Scarcity** — Limited availability increases desire. But only if real — fake urgency backfires.
- **Paradox of Choice** — Too many options = no decision. Limit to 3 tiers.

**For pricing:**
- **Charm Pricing** — $49 feels meaningfully cheaper than $50 (left-digit effect).
- **Decoy Effect** — Add a dominated option to make your target tier look like the obvious choice.
- **Rule of 100** — Under $100: show % discount. Over $100: show $ discount.

**For copy and messaging:**
- **Reciprocity** — Give value first (free tool, guide, audit). People feel compelled to reciprocate.
- **Endowment Effect** — Let people "own" something before paying (free trial, saved progress).
- **Framing** — Same fact, different frame. "95% uptime" vs "down 18 days/year." Choose wisely.

---

## Quick Reference

| Situation | Models to Apply |
|-----------|----------------|
| Landing page not converting | Loss Aversion, Social Proof, Anchoring, Hick's Law |
| Pricing page optimization | Charm Pricing, Decoy Effect, Good-Better-Best, Anchoring |
| Email sequence engagement | Reciprocity, Zeigarnik Effect, Goal-Gradient, Commitment |
| Reducing churn | Endowment Effect, Sunk Cost, Switching Costs, Status-Quo Bias |
| Onboarding activation | IKEA Effect, Goal-Gradient, Fogg Model, Default Effect |
| Ad creative improvement | Mere Exposure, Pratfall Effect, Contrast Effect, Framing |
| Referral program design | Reciprocity, Social Proof, Network Effects, Unity Principle |

## Task-Specific Questions

When applying psychology to a specific challenge, ask:

1. **What's the desired behavior?** (Click, buy, share, return?)
2. **What's the current friction?** (Too many choices, unclear value, no urgency?)
3. **What's the emotional state?** (Excited, skeptical, confused, impatient?)
4. **What's the context?** (First visit, returning user, comparing options?)
5. **What's the risk tolerance?** (High-stakes B2B? Low-stakes consumer impulse?)

## Proactive Triggers

- **Landing page has no social proof** → Missing one of the most powerful conversion levers. Add testimonials, customer count, or logos.
- **Pricing page shows all features equally** → No anchoring or decoy. Restructure tiers with a recommended option.
- **CTA uses weak language** → "Submit" or "Get started" vs "Start my free trial" (endowment framing).
- **Too many form fields** → Hick's Law: more choices = more friction. Reduce or use progressive disclosure.
- **No urgency element** → If legitimate scarcity exists, surface it. Countdown timers, limited spots, seasonal offers.

## Output Artifacts

| When you ask for... | You get... |
|---------------------|------------|
| "Why isn't this converting?" | Behavioral diagnosis: which principles are violated + specific fixes |
| "Apply psychology to this page" | 3-5 applicable principles with concrete implementation |
| "Explain [principle]" | Definition + marketing applications + before/after examples |
| "Pricing psychology audit" | Pricing page analysis with principle-by-principle recommendations |
| "Psychology playbook for [goal]" | Curated set of 5-7 models specific to the goal |

## Communication

All output passes quality verification:
- Self-verify: source attribution, assumption audit, confidence scoring
- Output format: Bottom Line → What (with confidence) → Why → How to Act
- Results only. Every finding tagged: 🟢 verified, 🟡 medium, 🔴 assumed.

## Related Skills

- **page-cro**: For full page optimization. Psychology provides the behavioral layer.
- **copywriting**: For writing copy. Psychology informs the persuasion techniques.
- **pricing-strategy**: For pricing decisions. Psychology provides the buyer behavior lens.
- **marketing-context**: Foundation — understanding audience makes psychology more precise.
- **ab-test-setup**: For testing which psychological approach works. Data beats theory.
