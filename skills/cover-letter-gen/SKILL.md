---
name: cover-letter-gen
description: Generate tailored, professional cover letters from a job posting and the user's CV/resume. Use this skill whenever the user mentions cover letters, job applications, applying for a position, customizing application materials, or asks to adjust/tailor a letter for a role. Also trigger when the user pastes a job description and mentions wanting to apply, or references their resume/CV in the context of a job opportunity. Handles academic, industry, and hybrid roles across communications, UX research, journalism, and related fields.
license: MIT
author: "Emmanuel Maduneme (https://www.emaduneme.com/)"
compatibility:
  - Claude.ai
  - Claude Code
metadata:
  version: 1.0.0
---

# Cover Letter Generator

## Overview

This skill takes a job posting (pasted or fetched via URL) and the user's CV/resume, then generates a fully customized cover letter that matches the role's requirements to the user's actual experience. It preserves the user's authentic voice and never fabricates credentials.

## When This Skill Triggers

- User says "adjust my cover letter for this role"
- User pastes a job posting and says "I want to apply"
- User mentions "cover letter," "application letter," or "letter of interest"
- User shares a job URL and asks for help with application materials
- User asks to "tailor" or "customize" a letter for a position

## Required Inputs

1. **Job posting** (pasted text or URL to fetch)
2. **User's CV/resume** (uploaded file or stored in `references/resume.md`)

## Optional Inputs

- Specific experiences to emphasize
- Custom opening or closing preferences
- Target tone (e.g., more academic vs. more industry)
- Additional context about the company or team

## Process

### Step 1: Analyze the Job Posting

Extract and categorize:
- **Role title and organization**
- **Required qualifications** (hard requirements vs. preferred)
- **Key responsibilities** (ranked by emphasis in posting)
- **Technical skills or tools mentioned**
- **Cultural signals** (mission language, values, team descriptors)
- **Application-specific instructions** (word limits, specific questions)

### Step 2: Map User Qualifications

Cross-reference the job requirements against the user's CV:
- Identify direct matches (exact skill or experience)
- Identify transferable matches (adjacent experience that maps)
- Flag gaps (requirements the user doesn't meet)
- Rank experiences by relevance to THIS specific role

### Step 3: Select Letter Strategy

Based on the role type, choose the appropriate framing:

**Academic positions**: Lead with research, teaching philosophy, and scholarly contributions. Reference specific departmental strengths and how the user's work complements them.

**Industry/UX roles**: Lead with applied experience, measurable outcomes, and methodological versatility. Emphasize cross-functional collaboration and business impact.

**Hybrid roles** (research + practice): Balance both, leading with whichever the posting emphasizes more heavily.

### Step 4: Draft the Letter

Structure:
1. **Opening paragraph**: State the position, express genuine interest, and deliver a compelling hook that connects the user's unique background to the role
2. **Body paragraph 1**: Strongest qualification match, with specific evidence and outcomes (quantified where possible)
3. **Body paragraph 2**: Secondary qualifications, demonstrating range and versatility
4. **Body paragraph 3** (if needed): Teaching, service, or additional value-adds relevant to the role
5. **Closing**: Restate enthusiasm, reference what excites the user about the specific organization, and include a forward-looking statement

### Step 5: Voice and Style Check

Apply these rules:
- Warm but professional tone
- Declarative sentences; avoid hedging unless strategic
- No cliches ("I am passionate about..." / "I believe I would be a great fit...")
- Show, don't tell: evidence over adjectives
- Keep paragraphs to 4-6 sentences max
- Total length: one page (350-500 words unless specified otherwise)

## Hard Rules

- **NEVER fabricate experiences, publications, or skills** the user does not have
- **NEVER guess** company details. If uncertain, ask or note a placeholder
- **Always use the user's preferred sign-off** (default: "Warmest Regards,")
- **Always ask** before making significant structural changes to the user's established template
- If the user's qualifications don't match a requirement, either omit it or frame adjacent experience honestly. Do not stretch the truth.

## Pre-Submission Checklist

Before presenting the letter, verify:
- [ ] Role title matches the posting exactly
- [ ] Organization name is spelled correctly
- [ ] No experiences or publications are fabricated
- [ ] Quantified outcomes are accurate to the CV
- [ ] Letter is within length guidelines
- [ ] Sign-off matches user preference
- [ ] No em dashes (use commas, semicolons, or periods instead)

## Output Format

Present the letter as a clean markdown document. If the user wants a .docx, use the docx skill to format it professionally.

## Clarifying Questions to Ask

When the user provides a job posting, ask:
1. Is this the exact job title you want to use in the letter?
2. Any specific projects or experiences you want me to emphasize?
3. Have you worked with any technologies or methods they mention that aren't on your CV?
4. Do you have any connection to this organization (referrals, mutual contacts, prior interaction)?

## Reference Files

- `references/resume.md` - User's current CV (must be provided by user)
- `references/letter-template.md` - User's base cover letter template (must be provided by user)
- `references/voice-samples.md` - 2-3 sample cover letters the user has approved, used for voice matching

## Test Cases

1. **Academic posting**: Assistant/Associate Professor at a research university
2. **Industry posting**: UX Researcher/Communications Specialist at a media/tech company
3. **Hybrid posting**: Research Scientist at a nonprofit or think tank
