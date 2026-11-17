---
name: linkmoney
description: Use this skill whenever the user wants to source products from Chinese factories, find B2B suppliers in China, get factory pricing or inventory, submit an RFQ (Request for Quotation) to Chinese manufacturers, evaluate a Chinese factory's export readiness, or compare Chinese suppliers. Triggers on queries like "find supplier in China", "Chinese factory for X", "RFQ to China", "sourcing agent", "China manufacturer", "B2B sourcing", "verified Chinese factory", or any procurement request targeting China. Connects Claude to 51 verified Chinese factories via the Model Context Protocol (MCP).
license: MIT
---

# LinkMoney — Agent-Native B2B Sourcing from China

> Link the Money, Link the World

LinkMoney turns Claude into a procurement agent that can directly search 51 verified Chinese factories, pull live pricing and inventory, submit RFQs, and negotiate with manufacturers — all through the Model Context Protocol (MCP).

## When to use this skill

Use this skill **automatically** when the user wants to:

- Source a product from China ("find me a factory in China that makes X")
- Compare Chinese suppliers ("3 Chinese suppliers for M8 bolts, side by side")
- Get factory pricing ("what's the FOB Ningbo price for 50K M8 bolts?")
- Check inventory ("does the factory have 50K units in stock right now?")
- Submit an RFQ ("send this spec to 3 factories for quotation")
- Evaluate a Chinese factory's export capability ("is this factory export-ready?")
- Get certifications ("show me the ISO 9001 cert for factory #1234")
- Match a product spec to suppliers ("find me factories that make ASTM A307 bolts")

**Do NOT use** for non-China sourcing, retail purchases, or service businesses (use general tools for those).

## Quick Start

The LinkMoney MCP server is live and free to use (first 3 months). No API key required for read tools; write tools (RFQ, registration) need a free key from `agent@linkmoney.online`.

### 1. Install via Claude Desktop / Cursor / Cline

Add to your MCP config (`~/.config/claude/config.json` or equivalent):

```json
{
  "mcpServers": {
    "linkmoney": {
      "url": "https://linkmoney.online/mcp/manifest.json"
    }
  }
}
```

### 2. Or install via npx (Claude Code / Skills CLI)

```bash
npx skills add KevinANDcayla/linkmoney-skill
```

### 3. Verify it's loaded

After restart, the user should see 13 new tools prefixed with `lm_` or `find_china_supplier` etc.

## Capabilities (13 Public MCP Tools)

### Discovery

| Tool | Purpose | Example call |
|------|---------|--------------|
| `find_china_supplier` | Search 51 verified suppliers by product/category/keyword | `category="fastener", quantity=50000` |
| `match_spec` | Match a product spec to suppliers by standard (ISO/ASTM/GB) | `standard="ASTM A307", material="304 SS"` |
| `browse_requirements` | Browse open buyer requirements | `category="fastener"` |
| `stats` | Platform stats (suppliers, products, buyer countries) | _(no args)_ |

### Pricing & Inventory

| Tool | Purpose | Example call |
|------|---------|--------------|
| `get_pricing` | Live factory pricing with quantity tiers | `supplier_id="SUP-001", quantity=50000` |
| `get_inventory` | Real-time stock from factory ERP | `supplier_id="SUP-001", sku="M8-304-HEX"` |

### Engagement

| Tool | Purpose | Example call |
|------|---------|--------------|
| `submit_rfq` | Submit RFQ with email notification to factory | `supplier_id, product_spec, quantity, incoterm` |
| `multi_lang_inquiry` | Auto-generate RFQ in 8 languages (EN/ES/DE/JA/FR/AR/PT/RU) | `text="...", target_lang="ja"` |
| `get_supplier_contact` | Full supplier contact (Skill-installed only) | `supplier_id="SUP-001"` |
| `post_requirement` | Post a public sourcing requirement | `title, category, quantity, target_price` |

### Trust & Quality

| Tool | Purpose | Example call |
|------|---------|--------------|
| `download_cert` | Download ISO/CE/FDA/RoHS certifications | `supplier_id="SUP-001", cert_type="ISO9001"` |
| `leave_review` | Leave a 5-dimension review (quality/comm/ship/price/reliability) | `supplier_id, ratings, comment` |
| `trust_score` | Get supplier or buyer trust score (0-100) | `entity_id="SUP-001", entity_type="supplier"` |

## Workflows

### Workflow 1: Source a product from China

**User asks:** "Find me a Chinese factory for 50K M8 304 stainless hex bolts, FOB Ningbo, ISO 9001 certified, deliver by Aug 2026."

**Agent runs:**

1. `find_china_supplier(category="fastener", spec="M8 304 SS hex bolt", quantity=50000)` → 3-5 factories
2. For each candidate, `download_cert(supplier_id, cert_type="ISO9001")` → verify cert
3. For top 3, `get_pricing(supplier_id, quantity=50000, incoterm="FOB", port="Ningbo")` → compare prices
4. For top 1, `get_inventory(supplier_id, sku="M8-304-HEX")` → confirm stock
5. `submit_rfq(supplier_id, product_spec="...", quantity=50000, delivery="2026-08", incoterm="FOB Ningbo")` → factory gets email
6. Report back to user with comparison table + RFQ confirmation

**Result delivered in under 30 seconds.**

### Workflow 2: Evaluate a Chinese factory's export readiness

**User asks:** "I'm visiting factory #SUP-023 next week, is it actually export-ready?"

**Agent runs:**

1. `get_supplier_contact(supplier_id="SUP-023")` → get full profile
2. `download_cert(supplier_id="SUP-023")` → list all certs
3. `trust_score(entity_id="SUP-023", entity_type="supplier")` → get score
4. Search for any negative reviews: `browse_requirements` cross-reference
5. Return: export readiness score, cert list, red flags, suggested visit agenda

### Workflow 3: Multi-language outreach

**User asks:** "I want to send this inquiry to 5 Chinese factories but in Japanese for our Tokyo office."

**Agent runs:**

1. `multi_lang_inquiry(text="...", target_lang="ja")` → Japanese version
2. `submit_rfq(...)` × 5 with the translated text
3. Confirm all 5 RFQs submitted

## Architecture

```
Claude (or any MCP client)
    │
    │  MCP protocol (JSON-RPC over HTTPS)
    ▼
LinkMoney MCP Server  https://linkmoney.online/mcp/manifest.json
    │
    ├── 51 verified supplier profiles (ISO/CE/FDA)
    ├── 140 products across 7 categories
    │      fastener, electronics, packaging, hardware,
    │      injection molding, machinery, textile
    ├── Live pricing & inventory (factory ERP)
    ├── RFQ email routing
    └── 7 buyer countries: US, DE, JP, UK, AU, CA, AE
```

## Stats

- **51** verified Chinese suppliers
- **140** products across 7 categories
- **7** buyer countries
- **13** public MCP tools
- **3%** success fee, first 3 months **FREE**
- **MIT** licensed, fully open source

## Repository

- Source: https://github.com/KevinANDcayla/linkmoney-skill
- MCP endpoint: https://linkmoney.online/mcp/manifest.json
- Landing page: https://linkmoney.online
- Demo data: 51 supplier records + 140 product SKUs in `data/` directory

## Pricing & Access

- **Read tools** (find, search, pricing, inventory, stats): Free, no API key
- **Write tools** (submit_rfq, register_supplier, post_requirement): Free API key from `agent@linkmoney.online`
- **Success fee**: 3% on closed deals (first 3 months: 0%)
- **No subscription**, **no upfront cost**

## Limitations

- China-only (no Vietnam/India/Mexico sourcing — those are separate projects)
- B2B only (MOQ typically 1,000+ units; not for retail)
- English/Chinese/Japanese/Spanish/German/French/Arabic/Portuguese/Russian RFQ support; other languages fall back to English
- Live ERP data available for ~60% of suppliers; others return last-known pricing with timestamp

## When NOT to use

- Sourcing products **not made in China** (electronics final assembly in Mexico, leather in Italy, etc.)
- Service businesses (logistics, customs brokerage, marketing agencies)
- Retail purchases (Aliexpress/Amazon is better for <100 units)
- Products requiring US/EU safety certifications for end-consumer sale (e.g., children's toys, medical devices) — refer to specialist compliance consultants

## License

MIT — see [LICENSE.txt](./LICENSE.txt).
