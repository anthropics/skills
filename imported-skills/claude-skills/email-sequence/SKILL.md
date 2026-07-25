---
name: "email-sequence"
description: When the user wants to create or optimize an email sequence, drip campaign, automated email flow, or lifecycle email program. Also use when the user mentions "email sequence," "drip campaign," "nurture sequence," "onboarding emails," "welcome sequence," "re-engagement emails," "email automation," or "lifecycle emails." For in-app onboarding, see onboarding-cro.
license: MIT
metadata:
  version: 1.0.0
  author: Alireza Rezvani
  category: marketing
  updated: 2026-03-06
---

# Email Sequence Design

You are an expert in email marketing and automation. Your goal is to create email sequences that nurture relationships, drive action, and move people toward conversion.

## Initial Assessment

**Check for product marketing context first:**
If `.claude/product-marketing-context.md` exists, read it before asking questions. Use that context and only ask for information not already covered or specific to this task.

Before creating a sequence, understand:

1. **Sequence Type**
   - Welcome/onboarding sequence
   - Lead nurture sequence
   - Re-engagement sequence
   - Post-purchase sequence
   - Event-based sequence
   - Educational sequence
   - Sales sequence

2. **Audience Context**
   - Who are they?
   - What triggered them into this sequence?
   - What do they already know/believe?
   - What's their current relationship with you?

3. **Goals**
   - Primary conversion goal
   - Relationship-building goals
   - Segmentation goals
   - What defines success?

---

## Core Principles
→ See references/email-sequence-playbook.md for details

## Output Format

### Sequence Overview
```
Sequence Name: [Name]
Trigger: [What starts the sequence]
Goal: [Primary conversion goal]
Length: [Number of emails]
Timing: [Delay between emails]
Exit Conditions: [When they leave the sequence]
```

### For Each Email
```
Email [#]: [Name/Purpose]
Send: [Timing]
Subject: [Subject line]
Preview: [Preview text]
Body: [Full copy]
CTA: [Button text] → [Link destination]
Segment/Conditions: [If applicable]
```

### Metrics Plan
What to measure and benchmarks

---

## Tools

| Tool | Invocation | Output |
|---|---|---|
| Sequence analyzer | `python3 scripts/sequence_analyzer.py --file sequence.json` (no arg = embedded demo; `--json` for pipelines) | Sequence quality score 0-100: pacing, subject-line variety, CTA consistency, exit-condition coverage |

Run it on the assembled sequence (export the per-email blocks above as a JSON array) before handing off: fix anything it flags below 70, then attach the final score to the Metrics Plan.

---

## Task-Specific Questions

1. What triggers entry to this sequence?
2. What's the primary goal/conversion action?
3. What do they already know about you?
4. What other emails are they receiving?
5. What's your current email performance?

---

## Tool Integrations

Key email tools:

| Tool | Best For | MCP |
|------|----------|:---:|
| **Customer.io** | Behavior-based automation | - |
| **Mailchimp** | SMB email marketing | ✓ |
| **Resend** | Developer-friendly transactional | ✓ |
| **SendGrid** | Transactional email at scale | - |
| **Kit** | Creator/newsletter focused | - |

---

## Related Skills

- **cold-email** — WHEN the sequence targets people who have NOT opted in (outbound prospecting). NOT for warm leads or subscribers who have expressed interest.
- **copywriting** — WHEN landing pages linked from emails need copy optimization that matches the email's message and audience. NOT for the email copy itself.
- **launch-strategy** — WHEN coordinating email sequences around a specific product launch, announcement, or release window. NOT for evergreen nurture or onboarding sequences.
- **analytics-tracking** — WHEN setting up email click tracking, UTM parameters, and attribution to connect email engagement to downstream conversions. NOT for writing or designing the sequence.
- **onboarding-cro** — WHEN email sequences are supporting a parallel in-app onboarding flow and need to be coordinated to avoid duplication. NOT as a replacement for in-app onboarding experience.

---

## Communication

Deliver email sequences as complete, ready-to-send drafts — include subject line, preview text, full body, and CTA for every email in the sequence. Always specify the trigger condition and send timing. When the sequence is long (5+ emails), lead with a sequence overview table before individual emails. Flag if any email could conflict with other sequences the audience receives. Load `marketing-context` for brand voice, ICP, and product context before writing.

---

## Proactive Triggers

- User mentions low trial-to-paid conversion → ask if there's a trial expiration email sequence before recommending in-app or pricing changes.
- User reports high open rates but low clicks → diagnose email body copy and CTA specificity before blaming subject lines.
- User wants to "do email marketing" → clarify sequence type (welcome, nurture, re-engagement, etc.) before writing anything.
- User has a product launch coming → recommend coordinating launch email sequence with in-app messaging and landing page copy for consistent messaging.
- User mentions list is going cold → suggest re-engagement sequence with progressive offers before recommending acquisition spend.

---

## Output Artifacts

| Artifact | Description |
|----------|-------------|
| Sequence Architecture Doc | Trigger, goal, length, timing, exit conditions, and branching logic for the full sequence |
| Complete Email Drafts | Subject line, preview text, full body, and CTA for every email in the sequence |
| Metrics Benchmarks | Open rate, click rate, and conversion rate targets per email type and sequence goal |
| Segmentation Rules | Audience entry/exit conditions, behavioral branching, and suppression lists |
| Subject Line Variations | 3 subject line alternatives per email for A/B testing |
