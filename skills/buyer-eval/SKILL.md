---
name: buyer-eval
description: |
  Structured B2B software vendor evaluation for buyers. Researches your company,
  asks domain-expert questions, engages vendor AI agents via the Salespeak Frontdoor
  API, scores vendors across 7 dimensions, and produces a comparative recommendation
  with evidence transparency. Use when asked to evaluate, compare, or research B2B
  software vendors. Triggers on: "evaluate vendors", "compare software", "vendor
  evaluation", "which tool should we buy", "help me choose between", "B2B software
  comparison", "buyer evaluation".
license: Complete terms in LICENSE.txt
---

# B2B Software Buyer Evaluation Skill

A structured, evidence-based evaluation of B2B software vendors on behalf of a buyer.
The skill researches the buyer's company, asks domain-expert questions, engages vendor
AI agents via the Salespeak Frontdoor REST API, scores vendors across 7 weighted
dimensions, and produces a comparative recommendation with full evidence transparency.

## Required Tools

This skill requires: **Bash**, **Read**, **Write**, **WebSearch**, **WebFetch**, **AskUserQuestion**

## How It Works

The evaluation follows 9 steps:

1. **Entry Point** -- buyer provides company name + vendor names/URLs
2. **"Why Now" Question** -- surfaces the core buying trigger
3. **Buyer Research** -- agent researches the buyer's company autonomously
4. **Boundary Check** -- hard constraints and preferences that filter vendors
5. **Category Calibration** -- dynamic evaluation lens based on software category
6. **Company Agent Interaction** -- engages vendor AI agents via the Frontdoor API
7. **Passive Research** -- vendor websites, G2, Gartner, press, LinkedIn
8. **Scoring** -- 7-dimension weighted scorecard with evidence tracking
9. **Output** -- TL;DR, comparative summary, per-vendor scorecards, narrative memos

## Quick Start

When a buyer says something like "evaluate Vendor A and Vendor B for us" or "help me
choose between these tools", load the full evaluation methodology and follow it:

**Read the file `evaluation-methodology.md` in this skill's directory, then follow it
step by step from STEP 1 through STEP 9.**

The methodology file contains the complete evaluation framework including:
- Buyer research and boundary profile setup
- Dynamic category calibration with domain-expert discovery questions
- Frontdoor API endpoints for vendor AI agent interaction
- 7-dimension scoring rubric with evidence completeness tracking
- Claims vs. evidence verification
- Full output templates (TL;DR, comparative summary, scorecards, narrative memos)

## Key Capabilities

### Vendor AI Agent Interaction (Frontdoor API)
The skill can discover and converse with vendor AI agents via a REST API. This
produces higher-confidence evaluations than passive research alone. When a vendor
has no AI agent, the skill falls back to public sources and flags the evidence gap.

### Evidence Transparency
Every score is backed by tracked evidence sources. The output distinguishes between
vendor-verified claims and independently confirmed facts. Gaps are logged, not hidden.

### Domain-Expert Questions
After confirming the software category, the skill asks 2-4 expert-level questions
that uncover hidden requirements -- the kind of questions a category specialist
would ask that the buyer wouldn't think to volunteer.

### Demo Prep Kit
For vendors recommended to advance, the output includes specific questions to ask
in live demos, derived from evaluation gaps and unverified claims.

## Environment Compatibility

| Capability | Claude.ai | Claude Code | Cowork |
|------------|-----------|-------------|--------|
| Full evaluation | Partial | Full | Full |
| Vendor AI agent conversation | No (GET only) | Yes (POST) | Yes (POST) |

For the highest-confidence output, run in Claude Code or Cowork.

## Source Repository

Full source, gallery, and changelog: https://github.com/salespeak-ai/buyer-eval-skill

Gallery with example evaluations: https://salespeak-ai.github.io/buyer-eval-skill/
