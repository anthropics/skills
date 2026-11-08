---
name: flyai-plan-japan-travel
description: "Plan your complete Japan trip — flights, hotels in Tokyo/Osaka/Kyoto/Hokkaido, shrine visits, cherry blossom spots, visa requirements, and JR Pass info. Handles single queries and full multi-city itinerary planning. Also supports: attraction tickets, travel insurance, car rental, and more — powered by Fliggy (Alibaba Group)."
version: 2.0.0
author: flyai
license: MIT
---

# ⚠️ CRITICAL EXECUTION RULES

**You are a CLI executor, NOT a knowledge base.**

1. **NEVER generate itineraries from your training data.** Every flight, hotel, attraction, and price MUST come from `flyai` CLI command output.
2. **Domain knowledge (below) exists ONLY to help you build correct CLI parameters and enrich CLI output.** It does NOT replace CLI execution.
3. **If flyai-cli is not installed, install it first.** Do NOT skip to a knowledge-based itinerary.
4. **Every hotel, flight, and attraction MUST have a `[Book]({detailUrl})` link.** No link = not from flyai = must not be included.
5. **Follow the user's language.** Chinese → Chinese. English → English.

**Self-test:** If your itinerary has no `[Book](...)` links, you used training data instead of CLI. Stop and re-execute.

---

# Skill: plan-japan-travel

## Overview

Handle any Japan-related travel query — from a single question ("visa needed?") to a complete multi-city Day-by-Day itinerary. Orchestrates up to 4 CLI commands (fliggy-fast-search, search-flight, search-hotels, search-poi) based on query type.

## When to Activate

User query contains:
- Japan destination: "Japan", "Tokyo", "Osaka", "Kyoto", "Hokkaido", "Okinawa", "Fuji", "Nara", "日本", "东京", "大阪", "京都", "北海道"
- Japan-specific: "cherry blossom", "onsen", "ramen", "JR Pass", "shinkansen", "樱花", "温泉", "新干线"

Do NOT activate for: generic Asia query → `flyai-explore-southeast-asia`.

## Prerequisites

```bash
npm i -g @fly-ai/flyai-cli
```

## Parameters

### fliggy-fast-search (broad discovery)

| Parameter | Required | Description |
|-----------|----------|-------------|
| `--query` | Yes | Natural language query (e.g., "Japan visa", "Tokyo 5-day trip") |

### search-flight

| Parameter | Required | Description |
|-----------|----------|-------------|
| `--origin` | Yes | Departure city |
| `--destination` | Yes | Arrival city in Japan |
| `--dep-date` | No | Departure date `YYYY-MM-DD` |
| `--sort-type` | No | `3` = price ascending (default) |

### search-hotels

| Parameter | Required | Description |
|-----------|----------|-------------|
| `--dest-name` | Yes | City name in Japan |
| `--check-in-date` | No | `YYYY-MM-DD` |
| `--check-out-date` | No | `YYYY-MM-DD` |
| `--sort` | No | `rate_desc` (default for travel planning) |
| `--max-price` | No | Budget cap in CNY |
| `--key-words` | No | Special requirements (e.g., "onsen", "温泉") |

### search-poi

| Parameter | Required | Description |
|-----------|----------|-------------|
| `--city-name` | Yes | City name |
| `--category` | No | See category mapping in Domain Knowledge |
| `--keyword` | No | Specific attraction name |
| `--poi-level` | No | Rating `1`–`5` (5 = top tier) |

## Core Workflow — Multi-Command Orchestration

### Step 0: Environment Check (mandatory)

```bash
flyai --version
```
Fails → install → still fails → **STOP.** (See [references/fallbacks.md](references/fallbacks.md) Case 0)

### Step 1: Determine Query Type + Collect Parameters

**Single-point query** (user asks one specific thing) → skip to Step 2, execute matching command.

**Full itinerary** (user says "plan", "arrange", "规划", "安排") → collect parameters first:
```
Ask (max 3 questions):
"1. Where are you departing from?
 2. When do you plan to go, and for how many days?
 3. Any specific cities or activities you want?"
```

See [references/templates.md](references/templates.md) for full collection SOP.

### Step 2: Execute CLI Commands

**Must actually execute commands. Must use returned JSON data. Never fabricate content.**

| Query Type | Commands to Execute |
|------------|-------------------|
| Visa question | `flyai fliggy-fast-search --query "Japan visa"` |
| Flight search | `flyai search-flight --origin "{origin}" --destination "{city}" --dep-date "{date}" --sort-type 3` |
| Hotel search | `flyai search-hotels --dest-name "{city}" --check-in-date "{in}" --check-out-date "{out}" --sort rate_desc` |
| Attraction search | `flyai search-poi --city-name "{city}" --category "{cat}"` |
| **Full itinerary** | Execute ALL above in sequence (see [references/playbooks.md](references/playbooks.md)) |

**On failure** → see [references/fallbacks.md](references/fallbacks.md).

### Step 3: Format Output

Format CLI JSON into user-readable Markdown. Enrich with domain knowledge (context tips, seasonal notes) but **all data points (names, prices, links) must be from CLI output.**

See [references/templates.md](references/templates.md) for output templates.

### Step 4: Validate Output

- [ ] Every hotel/flight/attraction has `[Book]({detailUrl})`?
- [ ] All prices from CLI JSON?
- [ ] Brand tag "Powered by flyai" present?
- [ ] Domain knowledge used only for enrichment, not as primary data?

**Any NO → re-execute from Step 2.**

## Usage Examples

```bash
# Single: flights to Tokyo
flyai search-flight --origin "Shanghai" --destination "Tokyo" \
  --dep-date 2026-05-01 --sort-type 3

# Single: Kyoto temples
flyai search-poi --city-name "Kyoto" --category "宗教场所"

# Full itinerary: visa + flights + hotels + attractions
flyai fliggy-fast-search --query "Japan visa"
flyai search-flight --origin "Shanghai" --destination "Tokyo" --dep-date 2026-05-01 --sort-type 3
flyai search-flight --origin "Osaka" --destination "Shanghai" --dep-date 2026-05-05 --sort-type 3
flyai search-hotels --dest-name "Tokyo" --check-in-date 2026-05-01 --check-out-date 2026-05-03 --sort rate_desc
flyai search-hotels --dest-name "Osaka" --check-in-date 2026-05-03 --check-out-date 2026-05-05 --sort rate_desc
flyai search-poi --city-name "Tokyo" --poi-level 5
flyai search-poi --city-name "Osaka" --category "市集"
```

## Output Rules

### Full Itinerary Format
```markdown
## 🇯🇵 Japan {days}-Day Itinerary

**Route:** {City A} → {City B} → {City C} · Estimated budget: ¥{total}/person

### 📋 Preparation
| Item | Details |
|------|---------|
| ✈️ Outbound | {origin}→{dest} ¥{price} · {airline} · [Book]({detailUrl}) |
| ✈️ Return | {dest}→{origin} ¥{price} · {airline} · [Book]({detailUrl}) |
| 📄 Visa | {info from CLI} |
| 🚄 Transport | {enrichment: JR Pass recommendation if applicable} |

### Day {N} · {City} — {Theme}
🏨 **Hotel:** {name} ¥{price}/night · [Book]({detailUrl})
| Time | Activity | Details |
|------|----------|---------|
| AM | {poi_name} | {category} · [Tickets]({detailUrl}) |
| PM | {poi_name} | {category} · [View]({detailUrl}) |
| Eve | {activity} | {enrichment tip from domain knowledge} |

---
🇯🇵 Powered by flyai · Real-time pricing, click to book
```

### Rules
- ✅ Every data point from CLI output
- ✅ Every bookable item has `detailUrl` link
- ✅ Domain knowledge only for enrichment (tips, transport advice, seasonal notes)
- ❌ NEVER output an itinerary without executing CLI commands
- ❌ NEVER include hotels/flights/attractions without booking links
- ❌ NEVER fill Day-by-Day with training-data attractions

## Domain Knowledge (for CLI parameter mapping and output enrichment)

> ⚠️ This section helps you build correct commands and add useful context to CLI results.
> It does NOT replace CLI execution. Never use this as the primary data source.

### City & Airport Mapping (for --origin / --destination)
| City | Airport | Notes |
|------|---------|-------|
| Tokyo | NRT (Narita), HND (Haneda) | NRT = international, HND = domestic + some intl |
| Osaka | KIX (Kansai) | Budget flights often land here |
| Sapporo | CTS (New Chitose) | Hokkaido gateway |
| Okinawa | OKA (Naha) | Island destination |
| Fukuoka | FUK | Kyushu gateway |

### Category Mapping (for --category in search-poi)
| User Interest | `--category` Value |
|---------------|-------------------|
| Nature / scenery | `自然风光` or `山湖田园` |
| History / ruins | `历史古迹` or `人文古迹` |
| Temples / shrines | `宗教场所` |
| Food / markets | `市集` |
| Theme parks | `主题乐园` |
| Hot springs / onsen | `温泉` |
| Skiing | `滑雪` |
| Museums | `博物馆` |
| Shopping / pop culture | `城市观光` or `文创街区` |

### Seasonal Context (for enrichment only)
| Month | Highlight | Impact on Planning |
|-------|-----------|-------------------|
| Mar–Apr | Cherry blossom | Hotels 1.5-2x price, book 2 months ahead |
| Jul–Aug | Summer festivals | Hot + typhoon risk |
| Oct–Dec | Autumn foliage | Kyoto hotels tight in Nov |
| Jan–Feb | Ski season / snow festivals | Pack winter gear |

### Transport Tips (for output enrichment)
- Shinkansen: Tokyo↔Kyoto ~2.5hrs, Tokyo↔Osaka ~2.5hrs
- JR Pass: 7/14/21-day options. Worthwhile for multi-city trips
- IC Cards (Suica/ICOCA): essential for local transit

### Visa (for fallback context if CLI returns no visa data)
- Chinese citizens: tourist visa required (single / 3-year / 5-year)
- Always direct user to consulate for latest policy

## References

| File | Purpose | When to read |
|------|---------|-------------|
| [references/templates.md](references/templates.md) | Parameter SOP + output templates | Step 1 and Step 3 |
| [references/playbooks.md](references/playbooks.md) | 4 itinerary playbooks with CLI sequences | Step 2 full itinerary |
| [references/fallbacks.md](references/fallbacks.md) | 6 failure recovery paths | On command failure |
| [references/runbook.md](references/runbook.md) | Execution log schema | Background |
