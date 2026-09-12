---
name: cold-email
description: Write cold emails that actually get responses. Strict 2-4 sentence formula for investors, employers, mentors, partners. Use when drafting outreach emails, investor emails, or any professional cold outreach.
license: Apache-2.0
---


# Cold Email Generator

Write ultra-short, specific, bold cold emails that get responses. Output directly in chat.

## Required Information

Before writing, gather these from user (prompt if missing):

1. **Recipient** — Name, role, company
2. **Your credentials** — Past wins, numbers, notable affiliations (user provides rough draft)
3. **Your ask** — What you want (user provides)
4. **Hook context** — Something recent/specific about recipient (auto-research or user provides)

## The Formula (strict)

Every email follows this structure:

```
Subject: [Short, casual, specific]

Hey [FirstName],

[Specific hook - what prompted this email RIGHT NOW] (1 sentence)

[Your credibility with concrete details] (1 sentence)

[Clear ask with specific time/topic] (1 sentence)

[Name]
```

**Total: 2-4 sentences maximum. No signature block.**

## Email Types (auto-select based on context)

| Type | Key Elements |
|------|--------------|
| **Advice/Mentorship** | Reference their experience, state your situation briefly, ask for specific time |
| **Investor Outreach** | Reference relevant investment, traction with numbers, "would love to tell you more" |
| **Job/Internship** | Reference role/company, one-line achievement, specific skill match |
| **Partnership** | What you do + impressive client/number, specific value prop for them |
| **Paid Consulting** | Offer to pay, reference their specific expertise, clear time ask |

## Subject Line Rules

**Good:** Short, casual, specific
- "Quick question [Name]"
- "[Name] - quick ask"
- "Re: [thing they posted about]"
- Just their first name

**Bad:** Formal, long, generic
- "Seeking Your Valuable Mentorship"
- "Introduction from an Aspiring Entrepreneur"
- Anything with "touching base"

## Voice Rules

### DO
- Be ultra-specific — "I saw your LinkedIn post about your angel group" not "I admire your work"
- Lead with recent context — Reference something from THIS WEEK if possible
- State concrete credentials — Numbers, past wins, notable companies
- Make a clear ask — "20 min call about X" not "pick your brain"
- Write casual — Like texting, not applying to grad school
- Be bold — Not the time for modesty
- Offer value when possible — "Would love to pay you for an hour"

### DON'T
- "I'd love to pick your brain"
- "I hope this email finds you well"
- Generic compliments without specifics
- Long paragraphs about your background
- Vague asks like "get coffee sometime"
- Being overly humble or apologetic
- Professional email signatures
- More than 4 sentences

## Editing Checklist

Before outputting, verify:

- [ ] 2-4 sentences max?
- [ ] Specific and recent hook?
- [ ] Credibility with numbers/names?
- [ ] Crystal clear ask?
- [ ] Casual tone (would send to a friend)?
- [ ] No filler words?
- [ ] No generic phrases?
- [ ] Short casual subject line?
- [ ] No email signature?

## Workflow

1. Check what info user provided
2. Prompt for any missing required info (recipient, credentials, ask)
3. Auto-select email type based on context
4. Research/craft specific hook (recent post, news, mutual connection)
5. Draft email following the formula
6. Edit ruthlessly — cut everything that doesn't add value
7. Output email directly in chat

## Follow-Up Template

If user needs a follow-up (3-5 days after no response):

```
Subject: Re: [original subject]

Hey [Name],

Following up on this - let me know if you're interested!

[Name]
```

**One follow-up max.**

## Detailed Guide

For full examples and advanced tactics, see [references/guide.md](references/guide.md).
