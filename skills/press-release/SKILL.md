---
name: press-release
description: Write professional press releases and crisis communications for organizations, nonprofits, universities, and businesses. Use this skill when the user needs to draft a press release, media advisory, crisis statement, public response, organizational announcement, product launch announcement, event announcement, or any formal media-facing communication. Also trigger when the user mentions PR, public relations, media statement, crisis response, reputation management, or stakeholder communication. Handles both proactive announcements and reactive crisis responses across sectors including higher education, media, tech, nonprofit, and corporate.
license: MIT
author: "Emmanuel Maduneme (https://www.emaduneme.com/)"
compatibility:
  - Claude.ai
  - Claude Code
metadata:
  version: 1.0.0
---

# Press Release & Crisis Communications

## Overview

This skill produces publication-ready press releases and crisis communications that follow AP style, journalistic conventions, and strategic communication best practices. It handles both proactive announcements (launches, hires, partnerships, events) and reactive crisis responses (incidents, controversies, corrections).

## When This Skill Triggers

- User asks to "write a press release" or "draft an announcement"
- User mentions a crisis, controversy, or incident needing a public response
- User needs a media advisory, media alert, or public statement
- User asks about PR strategy or crisis communication planning
- User mentions stakeholder communication during a difficult situation

## Press Release Types

### 1. Standard Announcement
Used for: New hires, product launches, partnerships, awards, events, research findings

### 2. Crisis Response
Used for: Data breaches, safety incidents, public controversies, leadership changes, corrections

### 3. Media Advisory
Used for: Upcoming events, press conferences, availability for interviews

### 4. Opinion/Position Statement
Used for: Policy responses, industry commentary, organizational positions on public issues

## Standard Press Release Structure

```
FOR IMMEDIATE RELEASE
[or EMBARGOED UNTIL: Date, Time, Timezone]

Contact:
[Name]
[Title]
[Email]
[Phone]

HEADLINE: [Active voice, present tense, 8-12 words max]
Subheadline: [Additional context, 12-18 words]

[CITY, STATE] - [Date] - [Opening paragraph: WHO did WHAT, WHEN, WHERE, and WHY.
This paragraph must stand alone as a complete story. Lead with the most
newsworthy element. 2-3 sentences max.]

[Second paragraph: Supporting detail, context, and significance.
Include a data point or specific detail that grounds the announcement. 3-4 sentences.]

[Quote paragraph: Attribution from a senior leader or relevant stakeholder.
The quote should add perspective, not repeat facts from above.
It should sound like something a human would actually say.]

[Third paragraph: Additional details, methodology, timeline, or
background information. Include relevant numbers and context.]

[Optional: Second quote from a partner, collaborator, or external voice.]

[Closing paragraph: Availability information, next steps, links to
additional resources, or call to action.]

###

[Boilerplate: 2-3 sentence description of the organization.
Include mission, key facts, and website URL.]
```

## Crisis Communication Structure

```
STATEMENT FROM [Organization] REGARDING [Situation]

[Date]

[Opening: Acknowledge the situation directly. Do not minimize or deflect.
State what happened in clear, factual terms. 2 sentences.]

[Impact acknowledgment: Who is affected and how.
Express genuine concern using specific, not generic, language. 2 sentences.]

[Action paragraph: What the organization is doing RIGHT NOW to address the situation.
Be specific about steps taken. Include timeline if possible. 3-4 sentences.]

[Accountability: Take responsibility where appropriate.
Do not assign blame externally unless factually warranted. 1-2 sentences.]

[Forward-looking: What will happen next. How affected parties can
get help or information. Specific contact details. 2-3 sentences.]

[Closing: Reaffirm organizational values relevant to the situation.
One sentence, no platitudes.]

Contact for media inquiries:
[Name, Title, Email, Phone]
```

## Writing Rules

### For All Press Releases
1. **AP Style**: Follow AP style for dates, numbers, titles, and abbreviations
2. **Inverted pyramid**: Most important information first
3. **Active voice**: "The university launched..." not "A program was launched by..."
4. **No jargon**: Write for a general audience unless targeting trade media
5. **Quotes sound human**: Avoid corporate-speak in attributed quotes
6. **One page ideal**: 400-600 words for standard releases
7. **Verifiable facts only**: Every claim must be substantiated

### For Crisis Communications
1. **Speed over perfection**: A timely, honest statement beats a perfect late one
2. **Empathy first, logistics second**: Lead with concern for affected people
3. **Be specific**: "We are conducting a full investigation" is better than "We are looking into it"
4. **No speculation**: State what you know, acknowledge what you don't
5. **One spokesperson**: Identify who will handle follow-up inquiries
6. **Update cadence**: Commit to a timeline for follow-up communications

## Tone Calibration by Context

| Context | Tone | Key Priority |
|---------|------|-------------|
| Product/service launch | Enthusiastic, specific | Differentiation and newsworthiness |
| Research finding | Authoritative, accessible | Accuracy and significance |
| Leadership announcement | Warm, forward-looking | Credibility and vision |
| Partnership/collaboration | Balanced, mutual | Equal positioning of partners |
| Crisis (safety) | Empathetic, urgent | Transparency and action |
| Crisis (controversy) | Measured, accountable | Honesty and responsibility |
| Crisis (correction) | Direct, humble | Accuracy and good faith |

## Pre-Publication Checklist

- [ ] Headline is present tense, active voice, under 12 words
- [ ] Opening paragraph answers who, what, when, where, why
- [ ] All quotes are attributed with full name and title
- [ ] AP style applied (dates, numbers, titles, abbreviations)
- [ ] Organization boilerplate is current and accurate
- [ ] Contact information is complete and correct
- [ ] All facts and figures are verified
- [ ] For crisis: legal review recommended before distribution

## Clarifying Questions

1. What is the primary audience? (General public, trade media, stakeholders, internal)
2. Is there an embargo date, or is this for immediate release?
3. Who should be quoted, and what is their exact title?
4. For crisis: What has been confirmed vs. what is still under investigation?
5. What is the desired call to action or next step for the reader?

## Reference Files

- `references/crisis-templates.md` - Pre-approved statement frameworks for common crisis scenarios (user-maintained)
- `references/boilerplates.md` - Organization boilerplate text (user-provided)

> Note: AP style guidance and distribution best practices are built into this skill's process steps and do not require separate reference files.

## Test Cases

1. **University announcement**: New research center launch with faculty quotes
2. **Crisis response**: Data privacy incident at a media organization
3. **Event advisory**: Media advisory for a public panel discussion
4. **Position statement**: Organization response to a policy change affecting their sector
