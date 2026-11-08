---
name: coherency-audit
description: Detect and surface contradictions between Claude's synthesized profile and actual conversation history. Prevents stale data from compounding across conversations. Trigger on "run coherency audit", "check coherency", "audit your memory", or before making claims about people, employers, case statuses, or project statuses where wrong facts have real consequences.
---

# Coherency Audit Skill

## Purpose

Detect and surface contradictions between Claude's synthesized profile (userMemories) and actual conversation history. Prevents stale data from compounding silently across conversations.

## The Problem

Claude's memory system has three layers:
1. **Synthesized profile** (userMemories) — generated periodically, goes stale
2. **Memory edits** (user_edits) — more current but incomplete
3. **Conversation history** — the actual ground truth

When layers conflict, Claude defaults to the synthesized profile because it appears first in context. Stale or incorrect claims propagate silently and compound. The most dangerous errors sound plausible.

## When to Trigger

### Mandatory
- User says "run coherency audit" or "check coherency" or "audit your memory"
- Start of conversations involving professional communications, legal strategy, or job applications where wrong facts have consequences

### Recommended
- Before making claims about people's employers, roles, or affiliations
- When conversation_search results contradict profile data
- When the user references something Claude doesn't see in the profile
- At least once per week during active daily use

## Execution

### Step 1: Identify Auditable Categories
Categories most likely to go stale:
1. Employment — employers, roles, titles (yours and people you discuss)
2. Case/project status — open, closed, won, lost, abandoned, active
3. Current projects — what's actually active vs. what profile says
4. Location — where relevant
5. Relationship details — names, roles, affiliations

### Step 2: Search for Evidence
For each category, run targeted searches:
```
conversation_search("[person] employer job work [company]")
conversation_search("[case] ruling outcome status")
conversation_search("current project building working on")
recent_chats(n=5)
```

### Step 3: Compare to Profile
Read the synthesized profile for each category. Compare to conversation evidence. Flag every discrepancy.

### Step 4: Output the Audit
```
COHERENCY AUDIT — [date]

VERIFIED: [category] — profile matches evidence
STALE: [category]
   Profile says: [X]
   Evidence shows: [Y]
   Source: [chat date or reference]
   Recommend: [suggested memory edit]

MISSING: [category] — profile has no entry, evidence shows [Z]
   Recommend: [suggested memory edit]
```

### Step 5: Fix
- Apply memory edits to correct stale entries immediately
- If unsure whether data is stale, ASK rather than assuming the profile is correct
- Memory edits override the synthesized profile

## Critical Rules

1. **Never trust the synthesized profile over conversation evidence.** The profile is a periodic summary. Conversations are ground truth.
2. **When in doubt, search.** A 30-second search is cheaper than a wrong claim that compounds across threads.
3. **The most dangerous errors sound plausible.** That's why they persist.
4. **Memory edits override the profile.** If there's a conflict, edits win — they're more recent and user-directed.
5. **Stale status is as dangerous as stale facts.** Describing a won case as "ongoing litigation" changes how Claude frames every response.

## Maintenance

Update this skill whenever major life events occur — case resolutions, job changes, project completions. The user may direct updates. Claude should also proactively suggest updates when evidence accumulates.
