# Triage Decision Framework — TAKE IT / WORTH / PASS / FLAG

This reference answers exactly one decision: **for each decision-required email, which of the 4 recommendation categories does it land in, and what draft tone matches each?**

Pair with `evaluation-framework.md` (the user's specific TAKE-IT / PASS signals from setup S4).

## The Four Categories

| Category | When | Draft tone | User effort |
|---|---|---|---|
| **TAKE IT** | All TAKE-IT signals match | Engaged + concrete next step | Read + send (or edit lightly) |
| **WORTH CONSIDERING** | Partial TAKE-IT match | Curious + 1-2 clarifying questions | Reply with judgment |
| **PASS** | Any PASS signal matches | Polite decline + brief reason | Skim + send |
| **FLAG FOR REVIEW** | Unusual / ambiguous / VIP edge case | NO DRAFT — user decides shape | Compose from scratch |

## Decision Flow

```
For each opportunity email:
  1. Is sender in VIP list?       → TAKE IT (bypass other checks)
  2. Any PASS signal matches?     → PASS
  3. All TAKE-IT signals match?   → TAKE IT
  4. Partial TAKE-IT match?       → WORTH CONSIDERING
  5. Unusual / unfamiliar shape?  → FLAG FOR REVIEW
```

The decision tree comes from the user's setup-time answers (S4.Q2 deal-breakers → PASS signals; S4.Q3 attractors → TAKE-IT signals; S4.Q6 VIPs → bypass list).

## Draft Tone Per Category

### TAKE IT — engaged + concrete next step

The TAKE-IT draft:
- Acknowledges what's interesting
- Names the concrete next step ("happy to do a 30-min call this week")
- Includes any pricing / availability information immediately (if `rate-card.md` exists)
- Voice register from `email-patterns.md` (no register escalation just because TAKE-IT)

**Anti-pattern:** TAKE-IT draft that hedges or asks questions. If the criteria match, commit.

### WORTH CONSIDERING — curious + 1-2 clarifying questions

The WORTH draft:
- Acknowledges interest tentatively
- Asks 1-2 specific questions that resolve the ambiguity
- Does NOT commit to next step until questions answered
- Avoids "I'll think about it" — no faux-deliberation language

**Anti-pattern:** WORTH draft with 5+ clarifying questions. If you need that much info, escalate to FLAG.

### PASS — polite decline + brief reason

The PASS draft:
- Polite, brief
- Specific reason (not just "not a fit"): "the timeline doesn't match our current capacity" / "the budget is below my standard rate"
- No false promises ("circle back next quarter" only if true)
- No apology ladder ("so sorry, really wish we could")

**Anti-pattern:** PASS draft that hedges or invites back-and-forth ("happy to revisit if budget changes!"). Decline cleanly.

### FLAG FOR REVIEW — no draft, surface fully

For FLAG cases, the skill produces:
- A detailed card in Section 5 of the report (sender, subject, category, why flagged, context)
- **NO draft body** — user decides response shape themselves

When to flag:
- Sender is famous / public figure (PR risk on default tone)
- Email contains threat / legal language
- Request is outside the framework's coverage (new offering type, unusual ask)
- Conflicting signals (VIP sender + PASS criteria)
- Anything that would benefit from user voice rather than templated voice

## Non-Opportunity Decisions

The framework above is for opportunity emails (pitches, proposals, collab asks). Other email types use simpler heuristics from `email-taxonomy.md`:

| Category from taxonomy | Default action |
|---|---|
| Active Conversations | Draft reply matching thread tone |
| Action Required | Draft reply OR flag if action unclear |
| Financial | NEVER draft (always FLAG — financial decisions are user's) |
| Important / Personal | Draft if pattern is clear; FLAG otherwise |
| Informational | Skip drafting (FYI emails don't need replies) |
| Ignore / Low Priority | Skip entirely (don't even read thread) |

## When `evaluation-framework.md` Doesn't Exist

If the user didn't set up an evaluation framework (no opportunities in their inbox), **skip Step 5 entirely**. Opportunity emails (if they appear unexpectedly) get classified as Action Required (per taxonomy) and the skill drafts a generic acknowledgment + FLAG for review.

The skill does NOT invent a framework on the fly. The framework is the user's commitment device; inventing one violates KB-as-source-of-truth.

## VIP Override Discipline

VIP senders bypass PASS filters but do NOT bypass FLAG logic. A VIP sender sending an unusual request → still FLAG. The VIP bypass is for "this person's emails always get serious consideration even if signals look weak," NOT "this person's emails always get auto-drafted with no judgment."

## Anti-Patterns

- **Auto-drafting FLAG cases.** Defeats the point of flagging.
- **Hedging in PASS drafts.** "Happy to revisit if X changes" with no actual interest = wasted user goodwill.
- **5+ questions in WORTH drafts.** That's not WORTH, that's FLAG.
- **TAKE IT with conditions.** If you need conditions, you're WORTH not TAKE.
- **Ignoring VIP override.** If sender is in VIP list, do not classify as PASS even if signals match.
- **Drafting for Financial emails.** Always FLAG; user must decide.

## Operational Checklist

For each opportunity email:

- [ ] Run signal check against `evaluation-framework.md`
- [ ] VIP check → may force TAKE IT
- [ ] PASS check → if matched, decline draft
- [ ] TAKE-IT check → if all match, engaged draft
- [ ] Partial match → WORTH + clarifying questions draft
- [ ] Unusual / ambiguous → FLAG (no draft, full surface in report)
- [ ] Apply `email-patterns.md` voice rules to whatever draft is created
- [ ] Log the recommendation + reasoning to `triage-log/`

## Citations

The 4-category decision framework canon:

1. **David Allen, *Getting Things Done* (Penguin, 2001/2015)** — the 2-minute rule + the categorical clearing taxonomy (Do / Delegate / Defer / Drop). The TAKE IT / WORTH / PASS / FLAG mapping is a closer-to-email-specific evolution.

2. **Merlin Mann, *Inbox Zero* (43folders.com talks, 2007)** — explicit category-based clearing. Inbox Zero's "5 verbs to do with email" (delete, delegate, respond, defer, do) is the conceptual ancestor of triage's 4 categories.

3. **Cal Newport, *A World Without Email* (Portfolio, 2021)** — the case for batch processing email rather than perpetual partial attention. Justifies the recurring-cadence design.

4. **Tiago Forte, *Building a Second Brain* (Atria, 2022)** — CODE framework (Capture / Organize / Distill / Express) applied to information. The triage system is the "Organize" + "Distill" phase for email specifically.

5. **Allen Cooper, *The Inmates Are Running the Asylum* (Sams, 2004)** — persona-driven design. The triage skill's `email-patterns.md` is a per-user persona; the framework's "respect documented preferences" is Cooper's "don't override the user's stated intent."

6. **Daniel Kahneman, *Thinking, Fast and Slow* (FSG, 2011)** — System 1 vs System 2 framing. PASS auto-decline is System 1 (gut filter from setup); FLAG is "this needs System 2 — slow user judgment." The 4-category framework explicitly routes between fast and slow paths.

7. **Atul Gawande, *The Checklist Manifesto* (Metropolitan Books, 2009)** — checklists as commitment devices. `evaluation-framework.md` is the user's checklist; the triage skill enforces it. The discipline of "respect documented preferences" rather than re-deciding each time is Gawande's checklist principle.
