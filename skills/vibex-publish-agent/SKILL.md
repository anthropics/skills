---
name: vibex-publish-agent
description: v0.1 scaffolding for HITL-gated publishing to Chinese video / social platforms (抖音 / 小红书 / B站). Generates platform-tuned drafts + cover art prompts + dry-run previews; never auto-publishes given the 2026 anti-bot environment. Use when prepping a multi-platform Chinese launch, when 抖音/小红书/B站 versions of a video need different hooks and lengths, or to feed VibeXForge project trailers into a Chinese-distribution funnel.
---

# VibeX Publish Agent

Solo Founder OS agent #11. v0.1 scaffolding for HITL-gated publishing to 抖音 / 小红书 / B站. Generates platform-tuned drafts, cover-art prompts, and dry-run previews so the operator can paste manually — auto-publish is OFF by design until the 2026 anti-bot environment shifts.

## When to use this skill

Invoke this skill when:

- The user is launching a VibeXForge project (or any indie product) on Chinese platforms and needs 3+ tuned versions in one pass
- A 抖音 short, a 小红书 post, and a B站 column piece are needed from the same source content
- A weekly cron should sweep new VibeXForge submissions and queue Chinese-distribution drafts
- The user asks "draft a 小红书 post" / "make this into a B站 column" / "generate 抖音 cover art prompt"

## What it does (v0.1 scaffolding)

1. **Platform adapters** for 抖音 / 小红书 / B站, each with their own length classifier, hook templates, tag taxonomy, AI-disclosure rules
2. **Draft generator** via Claude — tunes the same source (a VibeXForge project, a launch announcement, a blog post) into 3 platform-specific drafts with different hooks
3. **Cover art prompt generator** — emits image prompts compatible with `gpt-image-1` / `nanobanana` workflows. Operator generates art separately and attaches manually
4. **Dry-run preview always** — every draft is written to `queue/dry_run/` with `.dry_run.md` suffix. There is no auto-publish path in v0.1
5. **AI-disclosure banner** prepended to every 小红书 draft (platform requires self-disclosed checkbox)
6. **VibeXForge ingestion** — pulls recent project submissions via Supabase Management API, generates publish-ready drafts the operator pastes the same morning

## What it does NOT do (yet)

- **No auto-publish.** Q2 2026 anti-bot environment (小红书 阿瑞斯 risk system uses TLS fingerprinting + behavioral models, new accounts need 2-4 weeks 养号, 37 matrix accounts banned in one Jan 2026 sweep, 知乎 has no public publishing API) makes auto-publish ROI-negative once account-burn is factored
- **No 抖音 video upload.** Source video must be hand-uploaded; the agent provides title + cover prompt + description + tags only
- **No engagement tracking.** v0.2 roadmap

## Examples

### Example 1: 3-platform Chinese launch pass

User: "Draft 抖音 + 小红书 + B站 versions of the VibeXForge launch announcement"

Skill output:
```
# VibeX Publish — 2026-06-06

Source: VibeXForge launch announcement (en/launch.md)

3 platform drafts queued (dry-run, manual paste required):

## 抖音 (short video script)
→ queue/dry_run/2026-06-06-douyin-vibexforge-launch.dry_run.md
- 45s script with 3-second hook
- Cover prompt: "neon pixel anvil forging glowing AI sword, dark background, retro RPG"
- Title: 30 chars
- Tags: 5 trending + 3 niche
- Length classifier: 速读 (≤60s)

## 小红书 (note post)
→ queue/dry_run/2026-06-06-xiaohongshu-vibexforge-launch.dry_run.md
- 1,500-char 深度 version with numbered hook
- Cover image prompt + 3 supporting image prompts
- AI-disclosure banner prepended
- Title: 19 chars
- Tags: 6 (3 brand + 3 community)

## B站 (column piece)
→ queue/dry_run/2026-06-06-bilibili-vibexforge-launch.dry_run.md
- 2,400-char column with TL;DR + 4-section structure
- Cover prompt + thumbnail prompt
- Title: 23 chars
- Tags: 4

Next steps:
  1. Review drafts in Obsidian
  2. Generate cover art via gpt-image-1 / nanobanana from the prompts
  3. Hand-paste at creator.douyin.com / creator.xiaohongshu.com / member.bilibili.com
```

### Example 2: Weekly VibeXForge sweep

User: "Sweep new VibeXForge projects from this week and queue Chinese distribution drafts for the top 3 by upvote"

Skill: Pulls top-3 VibeXForge projects via Supabase Management API (`vibex_trends` integration), generates 3 × 3 = 9 platform drafts (one per project × 抖音/小红书/B站), lands all in `queue/dry_run/`. Operator picks the strongest 3-4 to actually publish that week.

## Guidelines

- **Never auto-publish to 抖音 / 小红书 / B站.** This is a hard rule, not a default. The auto-publish code path does not exist in v0.1 and will not exist until the anti-bot environment shifts
- **Every draft lands in `queue/dry_run/`** with `.dry_run.md` suffix — the file naming itself prevents accidental wiring into an auto-publish pipeline
- **AI-disclosure banner is mandatory on 小红书 drafts** — the platform requires self-disclosed checkbox; the banner reminds the operator at paste time
- **Cover art is generated separately by the operator** — the agent provides prompts, not images. Don't wire image generation into the publish path
- **Length classifier is platform-correct, not "more is better"** — a 1,500-char 小红书 深度 post outperforms a 3,000-char one. Trust the classifier
- **VibeXForge ingestion is Supabase Management API only** — read-only, no service-role key. Same pattern as marketing-agent's `vibex_trends`
- **This is v0.1 scaffolding** — call out limitations honestly in any output the operator might forward. Don't oversell maturity

## Configuration

Optional (all):
- `ANTHROPIC_API_KEY` — for Claude-drafted platform tuning. Without it, template fallback ships
- `SUPABASE_PROJECT_REF` + `SUPABASE_ANON_KEY` — for VibeXForge project ingestion
- `VIBEX_PUBLISH_QUEUE_ROOT` — defaults `~/.vibex-publish-agent/queue/`

## Provenance

This skill wraps the v0.1 scaffolding [vibex-publish-agent](https://github.com/alex-jb/vibex-publish-agent) — the 11th and newest agent in the Solo Founder OS stack at github.com/alex-jb/solo-founder-os. Added 2026-05-12 to close the Chinese-distribution gap that marketing-agent intentionally does NOT cover (marketing-agent ships `dry_run_preview()` for 小红书 / 知乎; this agent extends the pattern to 抖音 + B站). v0.1 status is honest: the publishing pipeline is scaffolding, not maturity.

## See the rest of the stack

The full Solo Founder OS canonical 7-layer one-person-company runtime includes 10 sibling agents covering: monthly cost audit, pre-push code review, multi-platform marketing (9 EN/global channels), customer discovery, sales / cold email, customer support, payments, analytics, bilingual EN/ZH content sync, and the SFOS core framework. Browse the meta-repo at `alex-jb/solo-founder-os-skills`.
