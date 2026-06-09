---
name: Brand Voice Enforcer
description: Apply a creator's brand voice and writing guidelines to any piece of content — tweets, newsletters, captions, blog posts, scripts, emails. Ensures tone, language, and style stay consistent across all output. Invoke whenever writing, editing, or reviewing content that will be published under the creator's name.
---

# Brand Voice Enforcer

This skill helps creators produce content that sounds unmistakably like them — regardless of topic, format, or length. It enforces their defined voice, avoids words and phrases that feel off-brand, and flags anything that drifts from their established style.

## How To Use This Skill

When a creator first uses this skill, Claude should ask them to define their brand voice by answering a short set of questions. Once defined, Claude stores those answers as the active voice profile and applies it to all content going forward.

If the creator has already defined their voice, Claude should load it and apply it silently without asking again.

### Step 1: Voice Profile Setup (First-Time Users)

If no voice profile exists yet, ask the creator these questions one at a time (not all at once):

1. **Describe your audience in one sentence.** Who are they? What do they care about?
2. **Pick 3–5 adjectives that describe your tone.** (e.g. warm, direct, funny, authoritative, casual)
3. **Name a creator, writer, or brand whose voice you admire.** What do you like about it?
4. **What words or phrases do you NEVER want to use?** (Overused buzzwords, corporate speak, etc.)
5. **How do you feel about humour?** Always, sometimes, never — and what kind?
6. **Do you use slang, contractions, or informal language?** How much?
7. **What's one thing you want every reader to feel after reading your content?**

After collecting answers, summarise the voice profile back to the creator and confirm it before saving.

### Step 2: Applying the Voice

When editing or generating content, Claude must:

- Rewrite in the creator's voice without changing the core message or facts
- Flag phrases that feel off-brand and explain why
- Preserve intentional stylistic choices (e.g. if they always start sentences with "Look —", keep it)
- Match the energy level of the original content (a casual tweet should stay casual)

### Step 3: Voice Audit Mode

When a creator says "audit this" or "check my voice", Claude should:

1. Score the content on a 1–10 brand voice consistency scale
2. Highlight specific lines that drift from the voice profile
3. Suggest rewrites for flagged sections
4. Give an overall verdict: On-brand / Needs work / Off-brand

## Supported Content Types

This skill applies to:
- Social media posts (X/Twitter, LinkedIn, Instagram captions, Threads)
- Newsletter issues
- Blog posts and articles
- YouTube scripts and video descriptions
- Podcast episode outlines and show notes
- Email campaigns
- Bio and About sections
- Pitch decks and brand copy

## Reference Files

- See `VOICE_RULES.md` for universal writing rules that apply across all creators
- See `EXAMPLES.md` for before/after examples of brand voice enforcement
- See `CHECKLIST.md` for the self-review checklist Claude runs before finalising output

## Important Behaviour Rules

- Never make content sound more formal than the creator's voice profile specifies
- Never add corporate buzzwords (leverage, synergy, ecosystem, unlock, empower) unless the creator explicitly uses them
- Do not sanitise humour or edge out of content when the creator's voice is naturally edgy or funny
- Always preserve the creator's signature phrases and structural habits
- When in doubt, ask — do not assume what the creator would want