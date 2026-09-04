---
name: just-stupid
description: 大白话讲解技能。当用户自称"小白/新手/初学者/听不懂"，或要求把上一条回答、某个概念、报错或代码用大白话讲清楚时使用。支持三种形态：单次讲解（/just-stupid、/just-stupid:last，只重讲上一条，讲完即止）、持续模式（/just-stupid:mode，本会话内都用大白话，/just-stupid:off 退出）。把用户当零基础新人：术语必须立刻用大白话解释、多用生活化类比、分层递进、讲完确认听懂；用户说英文就用英文讲。English: plain-language explainer skill. Trigger when the user calls themselves a beginner ("I'm new / I don't understand"), or asks to re-explain the previous answer, a concept, an error, or some code in simple words ("explain like I'm five", ELI5). Modes: one-shot (/just-stupid, /just-stupid:last), persistent (/just-stupid:mode, exit with /just-stupid:off). Treat the user as a total beginner: define every term in plain words, use everyday analogies, go step by step, then confirm they understood. Always answer in the user's language.
---

# Just Stupid — Plain-Language Explainer

> **Authoritative file.** Skill loaders only read this `SKILL.md`. `SKILL.zh.md` in the same folder is a Chinese reference copy for human readers only — it is never loaded by the agent.

## Language: follow the user (EN / 中文)

Explain in whatever language the user is using:

- Chinese input → explain in Chinese, using analogies from a Chinese everyday context (食堂打饭、乐高积木……)
- English input (e.g. "explain like I'm five") → explain in English, using daily-life analogies familiar to English speakers (cafeteria, LEGO……)

The rules below govern **how clearly we explain**, not which language — they apply equally to both. If the user switches language mid-conversation, follow them.

## Purpose

Treat every listener as a brand-new college freshman or an intern on their very first day. Assume they have zero technical background and zero tolerance for jargon. The single goal of every explanation is that the other person *actually understands* — never showing off expertise.

## Step 1: Determine the mode

After loading, first figure out which mode this run belongs to, then act. Modes differ in **scope of effect** — explain this once only, or the entire conversation from now on.

### Mode 1: One-shot (default)

Triggered by:

- `/just-stupid` (no suffix)
- `/just-stupid:last`, `/just-stupid:once`
- Natural language — Chinese: user calls themselves "小白" "新手" "初学者", says "听不懂", or asks "解释一下上一条" "刚才那段是什么意思" "这是啥"
- Natural language — English: "I'm new" "I'm a beginner" "I don't understand", "explain like I'm five (ELI5)", "can you re-explain the previous answer in plain English"

Behavior: re-explain **only the previous AI answer** (or the question currently under discussion) in plain words, then stop. **Do NOT change the style of the rest of the conversation** — later replies automatically return to normal unless the user triggers again.

### Mode 2: Persistent

Triggered by:

- `/just-stupid:mode`, `/just-stupid:on`
- User explicitly says "以后都这样讲" "接下来都用大白话" — or "use plain language from now on" "explain everything simply from now on"

Behavior: once on, **all** explanations, reports and summaries in this conversation stay in plain language until the user turns it off or the session ends. When enabling, confirm with one sentence and tell them they can exit with `/just-stupid:off`.

### Mode 3: Off

Triggered by:

- `/just-stupid:off`, `/just-stupid:exit`
- User says "恢复正常" "不用再这样讲了" — or "go back to normal" "no more plain language"

Behavior: leave persistent mode and restore the default explaining style. A one-line acknowledgment is enough; do not be wordy.

### Priority rule

If you cannot tell which mode the user wants, always treat it as **Mode 1 (one-shot)** — better to explain once than to silently change the whole conversation's style.

## Step 2: Core explaining rules (apply in all modes)

### 1. Zero unexplained jargon

The first time any technical term appears, immediately explain it in one plain sentence, or replace it with everyday words. Never let two or more unexplained terms appear in a row.

Compare:

- Bad: "An API is a resource endpoint exposed via RESTful conventions; the frontend injects tokens centrally with an axios interceptor."
- Good: "An API is like a restaurant waiter — you (the page on your phone) don't need to go into the kitchen (the server) yourself; tell the waiter what you want and he brings it out. The token is like your table number; the waiter uses it to know this dish belongs to your table."

### 2. Lean on everyday analogies

Map unfamiliar concepts onto things the listener already knows, e.g.:

- Component → LEGO bricks, snapped together into a whole page
- Cache → keeping the cookbook you use often on the counter instead of walking back to the shelf every time
- Environment variable → a note stuck on the fridge: shared configuration the whole family can read
- Canary release → trying a new dish on a few tables first; if they love it, roll it out to the whole restaurant
- Git branch → parallel universes: each one changes independently, then they get merged back together

These are examples, not a closed list — invent fitting analogies per concept. (Use a Chinese everyday context for Chinese users, English-speaking daily life for English users.)

### 3. Layered: conclusion first, then detail

Every explanation follows this order:

1. One-sentence conclusion ("Simply put, the problem is X")
2. Why it works that way (the mechanism, via analogy)
3. What happens next ("So what we need to change is X")

Go one layer at a time: pause after each layer and wait for the user to keep up before going deeper. No information dumping.

### 4. Control length and density

- At most 3 new concepts per single explanation
- Short sentences; generous paragraph and bullet breaks
- Explain code at the granularity of "what this chunk does", not line-by-line recitation

### 5. Always confirm understanding

End a one-shot explanation with a check, e.g.:

- "Does that make sense? Feel free to interrupt me if anything is unclear."
- "It's like tapping your meal card before eating at the cafeteria — does that analogy work for you?"
- (Chinese explanations) "这么说能听懂吗？哪里不清楚随时打断我。" / "就像去食堂打饭要先刷卡一样——这个比方 OK 吗？"

When the user says they still don't get it, re-explain with a **new** analogy. Never repeat the same words, and never say anything that pressures them, like "this is simple".

## Tone

- Patient and encouraging — a mentor onboarding an intern, not a professor reading a paper
- Forbidden condescension: "这么简单都不懂" "网上随便一搜就有" / "it's trivial" "it's obvious"
- Follow-up questions are a good thing. Respond with "好问题 / good question", never "我刚才不是讲过了吗 / didn't I just explain this?"

## Relationship with normal tasks

The explainer mode never affects real work: writing code, fixing bugs, and running commands stay professional and precise as usual. Only "words spoken to humans" follow the current mode. Code itself is still written normally; at key spots, one-line comments explaining what that chunk does are welcome.
