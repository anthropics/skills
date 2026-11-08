---
name: content-calendar
description: Build content strategies, editorial calendars, and social media plans for organizations, personal brands, and academic departments. Use this skill when the user asks to plan content, create a posting schedule, build an editorial calendar, develop a content strategy, organize social media posts, or plan a content pipeline. Also trigger when the user mentions content pillars, posting frequency, platform strategy, content mix, audience engagement planning, or newsletter scheduling. Handles multi-platform strategies across LinkedIn, X/Twitter, Instagram, TikTok, YouTube, newsletters, blogs, and podcasts. Outputs structured calendars as spreadsheets, markdown documents, or interactive artifacts.
license: MIT
author: "Emmanuel Maduneme (https://www.emaduneme.com/)"
compatibility:
  - Claude.ai
  - Claude Code
metadata:
  version: 1.0.0
---

# Content Strategy & Editorial Calendar

## Overview

This skill helps users develop structured content strategies and produces actionable editorial calendars. It handles the full pipeline from audience analysis and content pillar definition through to daily/weekly posting schedules with specific content prompts.

## When This Skill Triggers

- User says "help me plan my content" or "create a content calendar"
- User asks about posting frequency, content pillars, or platform strategy
- User wants to build a social media presence for a brand, department, or personal profile
- User mentions newsletter planning, blog scheduling, or podcast content pipeline
- User asks "what should I post about?"

## Process

### Phase 1: Strategic Foundation

Before building any calendar, establish:

**1. Audience Definition**
- Who are you trying to reach? (Be specific: not "everyone" but "mid-career journalists exploring AI tools")
- Where do they spend time online?
- What problems do they need solved?
- What content formats do they prefer?

**2. Content Pillars** (3-5 themes)

Content pillars are the recurring topics that define your brand's territory. Each pillar should:
- Connect to your expertise or mission
- Address a specific audience need
- Be broad enough for dozens of posts but narrow enough to be distinctive

Example for an academic in journalism + AI:
- Pillar 1: AI tools for newsrooms (practical tutorials, tool reviews)
- Pillar 2: Research insights (translating academic findings for practitioners)
- Pillar 3: Teaching and pedagogy (classroom experiments, student work)
- Pillar 4: Industry commentary (responding to news about journalism's future)
- Pillar 5: Behind the scenes (personal journey, academic life, career reflections)

**3. Platform Selection**

| Platform | Best For | Posting Frequency | Content Type |
|----------|----------|-------------------|--------------|
| LinkedIn | Professional authority, B2B, academic networking | 3-5x/week | Long-form posts, articles, carousels |
| X/Twitter | Real-time commentary, community engagement | Daily | Short takes, threads, quote tweets |
| Instagram | Visual storytelling, personal brand | 3-5x/week | Reels, carousels, stories |
| TikTok | Discovery, younger audiences, viral potential | 3-7x/week | Short video, trends, educational |
| YouTube | Deep dives, tutorials, long-form | 1-2x/week | Videos 8-20 min, shorts |
| Newsletter | Owned audience, depth, loyalty | 1-2x/week | Long-form, curated, personal |
| Blog/Website | SEO, portfolio, evergreen content | 2-4x/month | Articles, guides, case studies |
| Podcast | Relationship building, thought leadership | 1x/week or biweekly | Interviews, commentary, series |

**4. Content Mix Formula**

A healthy content mix typically follows a ratio:
- **40% Value content**: Teaches, informs, solves problems
- **25% Engagement content**: Asks questions, sparks discussion, shares opinions
- **20% Authority content**: Research, case studies, credentials, media appearances
- **15% Personal content**: Behind the scenes, reflections, celebrations

### Phase 2: Calendar Construction

**Monthly Planning View**
- Map key dates: holidays, industry events, product launches, academic calendar
- Assign content pillars to weeks (rotating or themed)
- Identify "anchor content" (one substantial piece per week that smaller posts support)

**Weekly Planning View**
- Assign specific post types to days
- Include platform, content pillar, format, and a content prompt/brief
- Note which posts can be cross-posted vs. platform-native

**Daily Post Brief**
Each calendar entry should include:
- Date and day of week
- Platform(s)
- Content pillar
- Post type (educational, engagement, authority, personal)
- Content prompt: 1-2 sentence description of what the post covers
- Format: text, image, video, carousel, thread, story
- Call to action (if applicable)
- Hashtags or keywords (if applicable)

### Phase 3: Output Formats

**Spreadsheet (.xlsx)**: Best for teams and ongoing management
- Tab 1: Monthly overview (calendar grid)
- Tab 2: Detailed post briefs (one row per post)
- Tab 3: Content pillar definitions
- Tab 4: Performance tracking columns

**Markdown (.md)**: Best for individual creators
- Weekly sections with daily entries
- Content prompts as checklists

**Interactive artifact (.jsx)**: Best for visual planning
- Calendar view with drag-and-drop
- Color-coded by pillar or platform

## Content Prompt Examples

Good prompts are specific enough to reduce blank-page paralysis but flexible enough to allow creativity:

**Weak**: "Post about AI"
**Strong**: "Share one specific AI tool you used this week in your classroom, what you asked it to do, what worked, and what didn't. Include a screenshot of the output."

**Weak**: "Share research"
**Strong**: "Take one finding from your latest paper and explain it in 3 sentences a journalist could understand. End with 'Why this matters for your newsroom.'"

## Clarifying Questions

1. What platforms are you currently active on, and which do you want to add?
2. How much time per week can you realistically spend on content creation?
3. Do you have existing content (lectures, papers, talks) that can be repurposed?
4. What's the primary goal: visibility, community building, lead generation, or thought leadership?
5. Is this for a personal brand, an organization, or a department?

## Hard Rules

- **Never suggest a posting frequency the user can't sustain.** Consistency beats volume.
- **Always tie content pillars to the user's actual expertise.** Don't suggest topics they can't speak to authentically.
- **Include repurposing strategies.** One piece of anchor content should generate 3-5 derivative posts.
- **Build in flexibility.** Leave 20% of calendar slots for reactive/timely content.

## Reference Files

This skill does not require user-provided reference files. Platform specifications, content formulas (PAS, AIDA, storytelling arc), and posting conventions are built into Claude's training.

> For spreadsheet-format output, use the `xlsx` skill after generating the calendar here.

## Test Cases

1. **Academic personal brand**: Monthly LinkedIn + newsletter calendar for a journalism professor
2. **Organizational launch**: 90-day content plan for a new research center's social media presence
3. **Repurposing pipeline**: Turn a 30-minute conference talk into 2 weeks of multi-platform content
