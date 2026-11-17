---
name: email-drafting
description: Draft professional emails across academic, administrative, networking, and career contexts. Use this skill whenever the user asks to write, draft, compose, or edit an email, Slack message, or professional message of any kind. Also trigger when the user describes a communication situation and needs help with wording, tone, or structure. Covers contexts including job applications, committee correspondence, collaboration requests, conference invitations, student communication, departmental updates, and stakeholder engagement. Adapts tone from formal academic to warm professional based on context and relationship.
license: MIT
author: "Emmanuel Maduneme (https://www.emaduneme.com/)"
compatibility:
  - Claude.ai
  - Claude Code
metadata:
  version: 1.0.0
---

# Professional Email Drafting

## Overview

This skill generates context-appropriate professional emails that balance warmth with professionalism. It reads relationship dynamics, organizational hierarchy, and communication purpose to calibrate tone, length, and formality.

## When This Skill Triggers

- User says "write an email to..." or "draft a message to..."
- User describes a professional situation and asks "how should I word this?"
- User needs to respond to an invitation, request, or professional opportunity
- User asks for help with Slack messages, LinkedIn messages, or other professional communication
- User mentions needing to follow up, decline, accept, or negotiate via written communication

## Context Detection

Before drafting, identify:

1. **Relationship type**: Supervisor, peer, mentee, external contact, stranger
2. **Power dynamic**: Writing up (to authority), laterally (to peers), or down (to students/reports)
3. **Purpose category**:
   - **Request**: Asking for something (letter of support, meeting, information)
   - **Response**: Accepting, declining, or negotiating an invitation/offer
   - **Update**: Providing status information or confirming plans
   - **Introduction**: First contact or cold outreach
   - **Follow-up**: Continuing a prior conversation thread
   - **Difficult**: Delivering bad news, setting boundaries, pushing back
4. **Urgency**: Routine, time-sensitive, or urgent
5. **Channel**: Email, Slack, LinkedIn, text message

## Tone Calibration

| Context | Tone | Length | Sign-off |
|---------|------|--------|----------|
| Department chair / dean | Respectful, concise | Short (3-5 sentences) | Best regards |
| Dissertation committee | Warm professional | Medium | Best / Thank you |
| Peer collaborator | Collegial, direct | Medium | Best / Cheers |
| Conference organizer | Professional, enthusiastic | Medium | Warmest Regards |
| Student / mentee | Supportive, clear | Varies | Best |
| External professional (first contact) | Professional, warm | Short-medium | Warmest Regards |
| Recruiter / hiring manager | Confident, professional | Medium | Warmest Regards |
| Close colleague | Casual professional | Short | Thanks / Best |

## Structure Templates

### Standard Professional Email
```
Subject: [Specific, scannable subject line]

[Greeting],

[Opening: Context or connection point - 1 sentence]

[Body: Purpose and key information - 2-4 sentences]

[Closing: Next step or call to action - 1 sentence]

[Sign-off],
[Name]
```

### Request Email
```
Subject: [What you're requesting] - [Brief context]

[Greeting],

[Brief context for the request - why you're reaching out]

[The specific ask - clear and direct]

[Acknowledge their time / provide deadline if relevant]

[Sign-off],
[Name]
```

### Response to Opportunity
```
Subject: Re: [Original subject] - [Your response]

[Greeting],

[Express genuine appreciation]

[Your answer (accept/decline/negotiate) - state it clearly in the first sentence]

[Brief supporting context if needed]

[Next steps or logistics]

[Sign-off],
[Name]
```

## Writing Rules

1. **Lead with the point.** Don't bury the ask or the answer in paragraph three.
2. **One email, one purpose.** If you need to address multiple topics, flag them upfront.
3. **Respect attention spans.** Most professional emails should be 5-10 sentences max.
4. **Subject lines are scannable.** Include the action or topic, not just "Quick Question."
5. **No filler phrases**: Avoid "I hope this email finds you well" unless writing to someone you haven't contacted in a long time and need a soft opening.
6. **No em dashes.** Use commas, semicolons, or separate sentences.
7. **Match the register.** Don't write a 300-word email when a 3-sentence Slack message will do.

## Difficult Emails Protocol

For emails involving conflict, boundary-setting, or sensitive topics:

1. **Name the situation clearly** but without accusation
2. **State your position** in one direct sentence
3. **Provide reasoning** briefly (not defensively)
4. **Offer a path forward** that respects both parties
5. **Keep it short.** Longer emails in tense situations create more surface area for misinterpretation.

Always ask the user if they want multiple drafts with different strategic approaches (e.g., "firm but warm" vs. "maximally diplomatic").

## Clarifying Questions

Before drafting, ask if not obvious from context:
1. What's your relationship with this person? (How formal should this be?)
2. What outcome do you want from this email?
3. Any specific details or constraints I should know?
4. Is there a deadline or time sensitivity?

## Hard Rules

- **Never assume relationship dynamics.** Ask if unclear.
- **Never include details the user hasn't provided** or approved.
- **Always match the user's preferred sign-off** for the context.
- **Flag potential issues.** If the user's draft might be received poorly, say so before sending.
- **No hollow pleasantries.** Every sentence should carry information or build connection.

## Output

Present the email cleanly. If the user wants to send it directly, offer to format for the message_compose tool with appropriate variants.

## Reference Files

- `references/voice-samples.md` - Approved email examples from the user across contexts
- `references/contacts.md` - Key contacts and relationship context (optional, user-provided)
- `references/signatures.md` - Sign-off preferences by context

## Test Cases

1. **Acceptance email**: Responding to a conference panel invitation
2. **Request email**: Asking a department chair for a letter of support with a Monday deadline
3. **Cold outreach**: Introducing yourself to a potential research collaborator
4. **Difficult email**: Declining an opportunity while maintaining the relationship
