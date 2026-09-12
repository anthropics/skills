---
name: brand-voice
description: Create brand voice guidelines, style guides, and tone documentation for organizations, departments, publications, and personal brands. Use this skill when the user asks to define a brand voice, create style guidelines, document tone and messaging standards, build a writing style guide, or establish communication standards for a team. Also trigger when the user mentions brand identity, messaging framework, voice and tone documentation, editorial standards, or asks how their brand should "sound." Handles everything from one-page voice summaries to comprehensive multi-section style guides. Works for corporate brands, academic departments, nonprofits, media outlets, and personal brands.
license: MIT
author: "Emmanuel Maduneme (https://www.emaduneme.com/)"
compatibility:
  - Claude.ai
  - Claude Code
metadata:
  version: 1.0.0
---

# Brand Voice & Style Guide Generator

## Overview

This skill produces structured brand voice documentation that gives any writer or communicator clear, actionable guidance on how the brand should sound. It moves beyond vague adjectives ("professional, friendly") to provide concrete examples, do/don't comparisons, and context-specific tone adjustments.

## When This Skill Triggers

- User says "help me define my brand voice" or "create a style guide"
- User asks "how should our organization sound?"
- User needs messaging guidelines for a team, publication, or department
- User mentions brand consistency, tone documentation, or editorial standards
- User is onboarding writers or communicators and needs reference documentation

## Process

### Phase 1: Brand Voice Discovery

Gather inputs through interview or analysis:

**1. Mission and Values**
- What does the organization exist to do?
- What 3-5 values guide decision-making?
- What does the organization believe that others in the space might not?

**2. Audience Analysis**
- Who are the primary audiences? (Be specific about demographics, expertise level, needs)
- What emotional state are they in when they encounter your communication?
- What do they need from you? (Information, reassurance, inspiration, tools)

**3. Voice Attributes**
Identify 3-4 core voice attributes. Each should be defined on a spectrum with a "but not" qualifier:

```
[Attribute] but not [extreme]

Examples:
- Authoritative but not condescending
- Warm but not saccharine
- Direct but not blunt
- Conversational but not sloppy
- Confident but not arrogant
- Accessible but not dumbed-down
```

**4. Competitive Differentiation**
- How do similar organizations sound?
- What makes this brand's voice distinctive?
- What tonal territory is unoccupied in the space?

### Phase 2: Style Guide Construction

#### Section 1: Voice Overview (1 page)

A concise summary anyone can reference quickly:
- Brand mission (1 sentence)
- Voice in 3-4 attributes with "but not" qualifiers
- The brand's "personality" described as if it were a person at a dinner party

#### Section 2: Tone Spectrum

Voice stays constant; tone shifts by context. Document tone adjustments for:

| Context | Tone Shift | Example |
|---------|------------|---------|
| Celebrating a win | Enthusiastic, proud | "We're thrilled to announce..." |
| Delivering difficult news | Empathetic, direct | "We need to share something important..." |
| Teaching/educating | Patient, clear | "Here's what you need to know..." |
| Responding to criticism | Measured, accountable | "We hear your concern, and here's what we're doing..." |
| Social media (casual) | Warm, conversational | "Real talk: this changed how we think about..." |
| Formal announcement | Confident, precise | "[Organization] announces the launch of..." |

#### Section 3: Writing Dos and Don'ts

Provide concrete examples for each guideline:

```
DO: "Our research found that solutions-focused news coverage 
    increased readers' willingness to act by 40%."
DON'T: "Our groundbreaking, paradigm-shifting research has 
    conclusively proven beyond any shadow of a doubt..."

DO: "We made a mistake. Here's what happened and what we're 
    doing about it."
DON'T: "Regrettably, circumstances beyond our control led to 
    an unavoidable situation..."
```

#### Section 4: Vocabulary and Terminology

- **Preferred terms**: Words and phrases the brand uses (with definitions if needed)
- **Avoided terms**: Words and phrases that don't fit the brand
- **Industry jargon policy**: When technical terms are acceptable vs. when to use plain language
- **Inclusive language guidelines**: Preferred terminology for referring to people, communities, identities

#### Section 5: Grammar and Mechanics

- **Style base**: AP Style, Chicago, or custom (specify which and document exceptions)
- **Oxford comma**: Yes or no
- **Numbers**: When to spell out vs. use numerals
- **Capitalization**: Title case vs. sentence case for headings
- **Abbreviations**: When to spell out on first reference
- **Special formatting**: How to handle links, CTAs, hashtags

#### Section 6: Platform-Specific Guidelines

For each active platform, document:
- Character/length targets
- Hashtag strategy
- Emoji policy
- Image/visual tone
- Engagement style (how to respond to comments, DMs)

#### Section 7: Templates

Include ready-to-use templates for the most common communication types:
- Social media post (by platform)
- Newsletter introduction
- Press release lead paragraph
- Email announcement
- Event promotion

### Phase 3: Output Formats

**Comprehensive guide (.docx or .md)**: Full multi-section document for teams
**One-pager (.pdf)**: Quick reference card with voice attributes, dos/don'ts, and key terms
**Slide deck (.pptx)**: Presentation format for team training
**Interactive artifact (.jsx)**: Searchable, tabbed reference tool

## Clarifying Questions

1. Does the organization have any existing brand guidelines or documentation?
2. Can you share 3-5 examples of communications you think nail the right tone?
3. Can you share 2-3 examples of communications that felt off-brand?
4. Who will use this guide? (Writers, social media managers, all staff, external partners)
5. What's the scope: full style guide or voice-only documentation?

## Hard Rules

- **Ground every guideline in examples.** Abstract adjectives without examples are useless.
- **Include "but not" qualifiers.** "Friendly" means nothing without boundaries.
- **Make it scannable.** Writers will reference this mid-draft. Walls of text defeat the purpose.
- **Test with real content.** Before finalizing, apply the guide to an actual piece of communication to verify it works.

## Reference Files

- `assets/one-pager-template.md` - Template for the quick-reference card
- `assets/audit-worksheet.md` - Content audit worksheet for voice discovery

> Note: Voice architecture frameworks and AP vs. Chicago style comparisons are covered by Claude's training and do not require separate reference files. The `references/` folder is reserved for user-provided brand materials (existing guidelines, sample communications, terminology lists).

## Test Cases

1. **University research center**: Voice guide for a new Solutions Journalism Research Hub
2. **Nonprofit**: Brand voice for an organization focused on health and environmental advocacy
3. **Personal brand**: Voice documentation for an academic building a public-facing presence
4. **Student publication**: Editorial style guide for a university newspaper
