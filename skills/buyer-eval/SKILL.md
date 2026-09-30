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

## Telemetry (opt-in, off by default)

The skill can send anonymized usage data back to Salespeak so the questions it generates for vendors can keep getting better. **Nothing is sent without explicit user consent.** Names, emails, companies, and vendor responses are never sent.

### How to use it during a run

1. **At run start**, check telemetry state and generate a session ID:

   ```bash
   _BEVAL_DIR=""
   for _D in "$HOME/.claude/skills/buyer-eval" ".claude/skills/buyer-eval"; do
     [ -d "$_D" ] && _BEVAL_DIR="$_D" && break
   done
   echo "TELEMETRY_STATE=$(python3 "$_BEVAL_DIR/bin/track.py" status --machine)"
   echo "SESSION_ID=$(python3 -c 'import uuid; print(uuid.uuid4())')"
   ```

   `TELEMETRY_STATE` is one of: `consented`, `unasked`, `declined`, `locked_off`.

2. **Throughout the eval**, fire these seven events at the right steps. Never invent new sub-events.

   | Sub-event | When | Fields |
   |---|---|---|
   | `skill_started` | After capturing state | `skill_version` |
   | `eval_context` | Once, after STEP 5.1 (or after STEP 6.1 discover so `evaluation_path` is known — preferred) | `category`, `vendor_count`, `vendors` (array of domains), `company_agents_found` (int), `evaluation_path` (`"company_agent_engaged"` \| `"passive_research_only"` \| `"mixed"`) |
   | `discovery_question_asked` | After buyer answers a discovery question. Fire for STEP 2 (why-now) and each STEP 5.3 domain-expert question. | `step` (`"STEP_2"` \| `"STEP_5_3"`), `category` (or `null` for STEP_2), `topic` (short slug you choose, e.g. `"why_now"`, `"high_touch_vs_low_touch"`), `question_text` (the exact question you asked) |
   | `vendor_question` | **For every (vendor, dimension) pair**, fire one or more events from the §6.5 question bank — regardless of whether a Company Agent exists. | `vendor`, `category`, `dimension`, `question_text`, `delivery_method` (`"asked_via_company_agent"` \| `"would_have_asked"` \| `"connection_failed"`) |
   | `vendor_scored` | Each numeric score in STEP 8 | `vendor`, `dimension`, `score` (1-5; do NOT fire for `[GAP]`) |
   | `eval_completed` | After STEP 9 output is delivered | `vendor_count`, `winner` |
   | `eval_aborted` | Only if user bails before STEP 9 | `at_step` |

   **Never include**: buyer name, buyer company, buyer email, buyer self-description, the buyer's *answers* to discovery questions, vendor response text.

   **Critical change in v3.5**: `vendor_question` no longer depends on Company Agent availability. When all vendors return `enabled: false` from Frontdoor discover, you must still walk the question bank, formulate questions you would have asked, and fire `vendor_question` events with `delivery_method: "would_have_asked"`. The signal is *what buyers want to know*, not *whether the vendor's bot answered*.

3. **If `consented`**, fire each event live:
   ```bash
   python3 "$_BEVAL_DIR/bin/track.py" event vendor_question \
     --session-id "$SESSION_ID" \
     --json '{"vendor":"acme.com","category":"customer_success_platform","dimension":"product_fit","question_text":"...","delivery_method":"would_have_asked"}'
   ```

4. **If `unasked`**, accumulate events in your own working memory (don't call `event`). After STEP 9 output is delivered, print the consent block below to the user, then use AskUserQuestion to ask "Help us improve the skill by sharing anonymized usage data from this run?" with options ["Yes, share anonymized data", "No thanks"].

   ```
   ─────────────────────────────────────────────────────────────
   ✓ Evaluation complete.

   Before you go — one question, asked only this once.

   Salespeak built this skill to help buyers cut through vendor noise.
   To make it better, we'd love to learn what real buyers ask vendors.
   With your permission, we'd send back anonymized data from this run
   and future runs.

   We'd send:
     • The questions this skill generated for vendor agents
     • The scores it gave each vendor
     • A random ID to group your runs together (not linked to you)

   We will NEVER send:
     • Your name, email, or company
     • Anything you typed about yourself
     • Vendor responses

   Verify it yourself:
     • Code: bin/track.py (plain Python, no third-party libraries)
     • Local audit log: ~/.salespeak/buyer-eval.log
       (every event we send is also written here — read it anytime)
     • Change your mind: python3 bin/track.py revoke
     • Delete your data: email privacy@salespeak.ai with your user ID
       (run `python3 bin/track.py show` to see it)
   ─────────────────────────────────────────────────────────────
   ```

   On **Yes**: `python3 "$_BEVAL_DIR/bin/track.py" grant --session-id "$SESSION_ID" --events '<JSON array of accumulated events>'`
   On **No**:  `python3 "$_BEVAL_DIR/bin/track.py" decline`

5. **If `declined` or `locked_off`**, do nothing telemetry-related. Skip the consent prompt entirely.

### Enterprise kill-switch

System administrators can disable telemetry organization-wide regardless of user consent:
- Set env var `BUYER_EVAL_NO_TELEMETRY=1`, or
- Deploy `/etc/salespeak/buyer-eval.json` with `{"locked":true,"consent":false}`

Either makes the state `locked_off` — no consent prompt is ever shown and no events are sent.

## Source Repository

Full source, gallery, and changelog: https://github.com/salespeak-ai/buyer-eval-skill

Gallery with example evaluations: https://salespeak-ai.github.io/buyer-eval-skill/
