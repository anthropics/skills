---
name: bilingual-content-sync-agent
description: Keeps en.json and zh.json (or any locale pair) in sync. Diffs missing keys, translates via Claude Sonnet 4.6 with glossary + tone, queues every translation in a markdown HITL review file, applies approved edits back to JSON. Never auto-writes. Use after shipping an English-first feature, when 100+ i18n strings are out of sync, or to run a Batch-API full-catalog refresh at 50% off.
---

# Bilingual Content Sync Agent

Replaces the manual diff + translate + apply cycle for solo founders shipping bilingual UI. Built for VibeXForge's 925 EN/ZH i18n strings; generalized for any locale pair. First agent built natively on solo-founder-os v0.1 — no migration needed.

## When to use this skill

Invoke this skill when:

- The user just shipped an English-first feature and ZH is now 50+ strings behind
- A weekly cron should diff `messages/en.json` vs `messages/zh.json` and surface stale keys
- The user asks "what i18n keys are missing translations" / "translate the new flow"
- A full-catalog refresh is needed and the user wants the Batch API path for 50% off
- A glossary-strict translation is required (product names, brand terms must NOT translate)

## What it does

1. **Stats** — `bilingual-sync stats --en … --zh …` reports coverage (e.g., "874 / 925 keys present, 94.5%, 51 missing")
2. **Diff** — flattens dotted-path JSON, identifies missing keys via 3 rules:
   - key absent in zh
   - zh value empty
   - zh value byte-equals en (a common copy-paste mistake)
3. **Draft** — `translate_batch` via solo_founder_os `AnthropicClient` (Sonnet 4.6 default), 50-key batches, glossary-aware system prompt, JSON-strict output. Optional Batch API path for full-catalog refresh at 50% cost
4. **HITL queue** — markdown file with frontmatter + `## key` sections + ```zh code blocks. Hand-editable, regex-parseable. Lands in `queue/pending/`
5. **Apply** — walks `queue/approved/`, merges into `zh.json` preserving nested structure + key ordering, moves processed files to `queue/sent/`
6. **Token usage auto-logged** to `~/.bilingual-content-sync-agent/usage.jsonl` → cost-audit-agent picks it up

## Examples

### Example 1: Weekly stale-key sweep

User: "What's the EN/ZH delta on VibeXForge right now?"

Skill output:
```
$ bilingual-sync stats --en messages/en.json --zh messages/zh.json

Total EN keys:     925
Total ZH keys:     874
Coverage:          94.5%
Missing:           51

Breakdown:
  Absent in ZH:    37
  Empty in ZH:      8
  ZH == EN copy:    6
```

### Example 2: Draft + review + apply round-trip

User: "Translate the 51 missing keys using the VibeXForge glossary and indie-SaaS tone"

Skill:
```bash
bilingual-sync draft \
  --en messages/en.json --zh messages/zh.json \
  --glossary alex-brain/glossaries/vibex.json \
  --tone "indie SaaS, gamified, neon-pixel, peer-to-peer" \
  --out queue/pending/2026-06-06-draft.md
```

Produces:
```markdown
---
draft_id: 2026-06-06-1438
en_path: messages/en.json
zh_path: messages/zh.json
keys: 51
batch_count: 2
estimated_cost_usd: 0.043
status: pending
---

## hero.title
EN: Forge your AI project legend
```zh
锻造你的 AI 项目传奇
```

## hero.cta_primary
EN: Submit your build
```zh
提交你的作品
```

[... 49 more]
```

Operator reviews in Obsidian, edits ZH where needed, moves to `queue/approved/`, then `bilingual-sync apply` merges back to `zh.json` preserving nested structure + key order.

## Guidelines

- **Never auto-write to zh.json.** UI strings are seen by every user every session. One bad translation shipping globally is worse than 5 days of catch-up. Always queue → HITL → apply
- **Glossary is enforced server-side in the prompt** — product names, brand terms, code snippets must NOT translate. The system prompt has a hard rule + the test suite asserts it
- **Batch API path for full-catalog refresh** — 50% off vs. per-request. Use for >200 keys at once; per-request is fine for incremental drafts
- **Preserve nested structure + key ordering on apply** — never sort alphabetically. Diff-friendly output is the whole point
- **`zh == en` copy detection is a feature** — that's the most common stale-key pattern; surface it loudly
- **The `--tone` parameter shapes voice, not meaning** — "gamified, neon-pixel" changes word choice but never doctrine
- **Multi-language extension (v0.2 roadmap)** — same code path for EN→ES, EN→JA, etc. No separate codebases per language

## Configuration

Required:
- `ANTHROPIC_API_KEY` — for Sonnet 4.6 translation

Optional:
- `BILINGUAL_SYNC_QUEUE_ROOT` — defaults `~/.bilingual-content-sync-agent/queue/`
- `BILINGUAL_SYNC_BATCH_MODE` — `realtime` (default) or `batch` (50% off via Anthropic Batch API)
- `BILINGUAL_SYNC_MODEL` — defaults `claude-sonnet-4-6`

## Provenance

This skill wraps the open-source [bilingual-content-sync-agent](https://github.com/alex-jb/bilingual-content-sync-agent) (MIT, PyPI: `pip install bilingual-content-sync-agent`) — one of 11 agents in the Solo Founder OS stack at github.com/alex-jb/solo-founder-os. Currently shipped at v0.4.0 with 43 passing tests, MCP server for Claude Desktop, structured outputs, and Batch API path for full-catalog refresh at 50% cost.

## See the rest of the stack

The full Solo Founder OS canonical 7-layer one-person-company runtime includes 10 sibling agents covering: monthly cost audit, pre-push code review, multi-platform marketing (12 channels incl 小红书 / 即刻 / 知乎 / B站), customer discovery, sales / cold email, customer support, payments, analytics, and the SFOS core framework. Browse the meta-repo at `alex-jb/solo-founder-os-skills`.
