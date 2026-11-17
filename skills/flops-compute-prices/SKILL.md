---
name: flops-compute-prices
description: Look up and cite verifiable GPU/compute rental reference prices (H100, A100, H200, and more; spot, on-demand, or DePIN markets) from the public FLOPS Index — no API key required. Use when the user asks what a GPU or accelerator costs to rent, wants the cheapest option for a given chip, wants to compare spot vs on-demand vs decentralized compute rates, or wants to fact-check / cite a compute price with a source they can independently verify. Keywords: GPU price, H100 cost, A100 rental, compute pricing, spot price, on-demand, DePIN, GPU-hour, accelerator rental, FLOPS index.
---

# FLOPS Compute Prices

Look up **GPU / compute rental reference rates** and cite them with a **verifiable source**, using the public FLOPS Index API. Everything here is key-free.

## When to use this skill
- The user asks what an accelerator costs to rent — "what's an H100 going for?", "cheapest A100 right now?", "on-demand H200 price?".
- The user wants to compare rates across GPUs or across market types (spot / on-demand / DePIN).
- The user states a compute price and wants it fact-checked, or wants a citable price with a link a reader can verify.

## What FLOPS is (and is NOT)
FLOPS publishes **indicative reference levels** for GPU compute, snapped to the most recent 6-hour UTC mark and refreshed every 6 hours. Values are **source-opaque** (no provider identities) and **delayed** on the public surface. A value is **not** a live provider quote, **not** a settlement mark, and **not** investment advice. Always carry that caveat when you cite one. **Never fabricate a number** — if a call fails or returns null, say so.

## Index slugs
`FLOPS-<ACCELERATOR>-<MARKET>` where `<MARKET>` ∈ `SPOT`, `OD` (on-demand), `DEPIN` (decentralized). E.g. `FLOPS-H100-SPOT`, `FLOPS-A100-OD`, `FLOPS-A100-DEPIN`. Don't guess the accelerator list — use the catalog.

## Which endpoint returns what
- **`/v1/price/{slug}`** — the **authoritative** single-index record: full envelope + citation/verify URLs. Use this for any value you will cite.
- **`/v2/catalog/public`** — every index **with its value** in one call; best for scanning/comparing a family. ⚠️ For a given slug, `catalog` may report a slightly different `confidence` / `change_24h` than `/v1/price` (a known backend inconsistency). **When they disagree, `/v1/price` wins** — always confirm a citable value with `/v1/price`.
- **`/v1/search?q=`** — returns matching **slugs + citation URLs only, NO value**. Use it to discover slugs, then call `price`.

## How to use it — price → verify → cite

### 1. Get a price (authoritative)
`GET https://app.flopsindex.com/v1/price/{slug}` — helper: `python scripts/flops.py price FLOPS-H100-SPOT`
Envelope: `value`, `unit` ("USD/GPU-hr"), `as_of`, `delayed`, `confidence` ("HIGH" | "MED" | "LOW" — an ordinal label, never a number), `change_24h` ("UP" | "FLAT" | "DOWN" | null), `data_tier` (e.g. "LIVE" = coverage tier, **not** a freshness claim — the value is still delayed), `verify_url`, `citation_url`, `methodology_url`, `disclaimer`. (Other fields like `permalink`, `upgrade` may appear; list is not exhaustive.)

**`as_of` is a 6-hour UTC bucket label** (00/06/12/18 UTC). The current bucket can read slightly ahead of your wall clock — that's normal bucketing, not stale/future data. Present it as UTC.

### 2. Cheapest for a given chip
Fastest path: `python scripts/flops.py cheapest a100` — fetches `/v1/price` for each of that chip's SPOT/OD/DEPIN slugs and returns the lowest (authoritative), with `market`, an `all_markets` breakdown, and the verify link. Or read `/v2/catalog/public`, filter `FLOPS-<CHIP>-*`, take the min `value`, then confirm the winner with `/v1/price`.

**Two things to get right when reporting the cheapest:**
- **Flag the market class.** The family-min is very often a **DEPIN** (decentralized) rate — a different reliability/risk class than on-demand or spot. Do not present a DePIN number as an apples-to-apples cloud rate; say it's decentralized, and offer the cheapest *conventional* (SPOT/OD) rate alongside. (`cheapest` emits a `market_class_note` when the winner is DePIN.)
- **Cite from a fresh `/v1/price`.** The 6-hour `as_of` bucket can roll between calls, so the envelope inside `cheapest` may carry an older bucket than a `/v1/price` you make seconds later. Re-pull `/v1/price/{winner}` at cite time for the timestamp you print.

### 3. Verify / fact-check a claimed value
`GET https://app.flopsindex.com/v1/verify?index_id={slug}&value={n}` — helper: `python scripts/flops.py verify FLOPS-H100-SPOT 1.50`
Returns `verified`, `actual_value`, `delta_pct`, `tolerance_pct`, `tolerance_abs`.

**Interpreting the result — read this before you narrate a verdict:**
- `delta_pct = (submitted − actual) / actual × 100`. Negative ⇒ the user's number is **below** the reference; positive ⇒ **above**. State the direction explicitly.
- `tolerance_pct` is tiny (±0.5%). Verify is an **exact-match check against the published mark**, NOT a plausibility/fairness test. So `verified:false` means "doesn't match the reference to ~2 decimals," **not** "the user is wrong." Never tell a user their estimate is "wrong" — say it "differs from the FLOPS reference by X% (below/above)".
- If a value fails for the market the user named, **check the sibling markets** (SPOT/OD/DEPIN) before concluding — the gap is often a market mismatch (e.g. a DePIN listing vs a spot rate), and saying so is the fair answer.

### 4. Cite it
Always present the value WITH its `as_of`, the delayed-reference caveat, and the verify + citation URLs. The API's raw `verify_url` has **no** value attached — append `&value={value}` to make it checkable (the `price` and `cheapest` helpers already emit a ready `verify_url_checkable`). Canonical one-liner:

> **$2.33/GPU-hr** — H100 spot reference (`FLOPS-H100-SPOT`) as of 2026-07-16 12:00 UTC; delayed indicative level, not a live quote. Verify: https://app.flopsindex.com/v1/verify?index_id=FLOPS-H100-SPOT&value=2.33 · Source: https://app.flopsindex.com/i/FLOPS-H100-SPOT

## Notes
- **Key-free.** A `FLOPS_API_KEY` (header `X-FLOPS-Api-Key`) upgrades the same calls to real-time full precision, but is never required.
- `change_24h` is often `null` — handle it; not an error.
- Same data is available as MCP tools (`https://app.flopsindex.com/mcp`) and SDKs: `pip install flopsindex`, `npm i @flopsindex/sdk`.
