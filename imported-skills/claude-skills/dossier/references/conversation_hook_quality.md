# Conversation Hook Quality — Finding-Tied vs Generic

This reference answers exactly one decision: **what makes a conversation hook (Section 8 of the dossier DOCX) useful enough to justify a meeting prep workflow?**

## The Core Frame

A conversation hook is useful when it:

1. References a **specific recent finding** (timestamped, sourced)
2. Provides **suggested framing** (verbatim phrasing the user can adapt)
3. Connects the finding to **the meeting's purpose** (sales pitch / investment / hire)

A generic hook is useful for nothing. "Ask about their roadmap" doesn't help the user — they already knew they could ask about that.

## The Quality Bar

A hook passes if all three are true:

✅ Specific finding from this dossier (with hyperlink)
✅ Suggested phrasing (1-2 sentences)
✅ Tied to user's hypothesis or meeting purpose

A hook fails if any of:

❌ Generic ("ask about their priorities")
❌ Unsourced ("they're probably hiring")
❌ Untimely (>6 months old finding without explicit recency note)
❌ Speculative ("they might be considering X")
❌ Not actionable in the meeting context

## Side-by-Side Examples

### Sales prep for AI infrastructure company

| ❌ Generic | ✅ Finding-tied |
|---|---|
| "Ask about their AI strategy." | "Mention their recent acquisition of Hugging Face vendor [X] (announced 2 weeks ago via TechCrunch). Suggested framing: *'Saw the [X] acquisition — how does that change your model deployment story?'*" |
| "Talk about pricing." | "Their pricing page was updated last Thursday (their official site). The change adds a per-token usage tier. Suggested framing: *'Noticed the new usage tier — was that customer-driven or competitive response?'*" |
| "Ask about their team." | "Their VP Eng [name] left 3 weeks ago (LinkedIn). Their job board posted a Director of AI Engineering req last Friday. Suggested framing: *'I noticed [name] moved on and you're hiring an AI Eng Director — what's the eng leadership focus shifting toward?'*" |

### Investment diligence on founder

| ❌ Generic | ✅ Finding-tied |
|---|---|
| "Test technical depth." | "She published 3 technical blog posts on her personal site this year (links in Section 1) on distributed systems. Suggested probe: *'Your post on consensus protocols was sharp — what's the actual implementation challenge you're hitting on [their startup]?'*" |
| "Check for red flags." | "Her co-founder left the company 4 months ago — no public statement either side (LinkedIn + her bio update). Suggested probe: *'I noticed [co-founder] is no longer listed — what's the founding-team story now?'*" |
| "Ask about market." | "They raised $5M seed in Feb 2024, now hiring 3 GTM roles (Crunchbase + LinkedIn). Suggested probe: *'You're staffing GTM heavily for a $5M seed — what's the pipeline that justifies that shape?'*" |

## Hook Construction Pattern

```
Hook = Finding + Suggested Framing + Tied-To-Purpose

Where:
  Finding         = specific event, statement, change, or signal (with URL + tier)
  Suggested       = verbatim 1-2 sentence question or comment user can adapt
  Tied-To-Purpose = connection to Q3 purpose + Q4 hypothesis
```

## Anti-Patterns

### "Ask about their values/culture/roadmap/strategy"

These are generic openers, not conversation hooks. The user already knew they could ask about strategy. The hook should surface **specific evidence the user didn't have before**.

### "I suggest mentioning their recent quarter"

If the dossier doesn't cite a specific quarter result, this is speculation. Hooks must be evidence-anchored.

### "They might appreciate hearing about [generic topic]"

The hook should be about the user finding signal, not about the subject's preferences. Frame as: "Here's what the user just learned and can leverage."

### "Hooks tied to private/sensitive findings"

If Q6 (sensitivities) excluded family / medical / political, the hook also can't lean on those even tangentially. Check exclusions before drafting.

### "5+ hooks padding"

3-5 hooks is the sweet spot. More dilutes signal. If only 3 strong hooks emerge from findings, ship 3 — don't pad to 5 with weak ones.

### "Generic LinkedIn-style hook"

"I saw you went to Stanford — I went to Stanford too" — this is networking small-talk, not a substantive hook. Substantive hooks reveal the user did homework.

## Hook Tier (Implicit)

Hooks inherit the source tier of their underlying finding:

| Tier | Hook reliability |
|---|---|
| Primary (SEC, court, official site) | High — user can confidently lead with this |
| Secondary (mainstream news) | Medium — user can lead but acknowledge source |
| Tertiary (blog, forum) | Low — user should treat as soft signal, frame cautiously |

The DOCX tier-tag on each hook lets the user calibrate their conversational confidence.

## Hook Discipline by Purpose (Q3)

| Purpose | Hook flavor |
|---|---|
| Sales pitch | Lead with their recent moves; show you've done homework on their context |
| Investment diligence | Probe contradictions; surface red flags as questions, not accusations |
| Acquisition diligence | Test fit assumptions; ask about org culture + leadership stability |
| Journalism | Get them on the record about specific findings (named source + ask) |
| Interview prep | Show domain knowledge tied to their actual work, not generic praise |
| Competitive intelligence | (not for in-person meeting) — convert hooks to internal team briefing notes |
| Personal vetting | Generally skip hooks; vetting is a one-way information flow |

## Operational Checklist

- [ ] 3-5 hooks (not more, not fewer if findings support it)
- [ ] Each hook references a specific finding from this dossier
- [ ] Each finding has a hyperlink (Phase 4 search result)
- [ ] Each hook has suggested framing (1-2 sentences, verbatim adaptable)
- [ ] Each hook tied to Q3 purpose
- [ ] Each hook tiered (primary / secondary / tertiary based on underlying finding)
- [ ] No hook leans on Q6 excluded topics
- [ ] No hook is purely speculative or generic

## Citations (7 sources)

1. **Dale Carnegie, *How to Win Friends and Influence People* (1936).** The original "show genuine interest" framing. Conversation hooks operationalize this — but require specific evidence, not generic friendliness.

2. **Robert Cialdini, *Influence* (1984, multiple eds.).** Source for the "reciprocity" principle that hooks invoke. When the user signals they've done substantive homework, the subject reciprocates with substantive engagement.

3. **Chris Voss, *Never Split the Difference* (2016).** Source for the "calibrated question" pattern. Voss's "how" / "what" questions tied to specifics outperform generic "yes/no" questions. The dossier's suggested-framing examples follow this pattern.

4. **Daniel Goleman, *Working with Emotional Intelligence* (1998).** Source for the "social awareness" pillar of EI. Hooks operationalize this — surfacing recent specific context shows the user is reading the room.

5. **Patrick Lencioni, *The Five Dysfunctions of a Team* (2002).** Indirect source — Lencioni's "vulnerability-based trust" works because specific shared context creates faster intimacy than generic small-talk.

6. **Carmine Gallo, *Talk Like TED* (2014).** Source for the "lead with the surprising data point" rhetorical pattern. The strongest hooks open with a specific finding the subject didn't expect the user to know.

7. **Edgar Schein, *Humble Inquiry* (2013).** Source for the framing-as-question discipline. Hooks framed as questions ("how does that change your roadmap?") outperform hooks framed as observations ("interesting that you...") because questions invite reciprocal disclosure.
