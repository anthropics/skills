# Channel Data Template

Fill this out in ~20 minutes. The three scripts in this skill all consume JSON; this template gives you the schema with annotations on **what to put** and **why**.

If you don't know a value, **leave it `null` (or the explicit "$0 unknown") and note it** — the scripts surface unknowns explicitly rather than silently substituting.

---

## Intake checklist (before you fill anything)

- [ ] Define "channel" — a coherent go-to-market motion (e.g., `direct`, `partner-led`, `marketplace`, `reseller`, `oem`). NOT a marketing source.
- [ ] Confirm allocation methodology is the **same** across all channels (revenue-share or activity-driver, not mixed)
- [ ] Confirm retention numbers are **per-channel**, not pooled
- [ ] Confirm "channel-sourced" deals meet the strict definition: partner originated the opportunity AND brought it unqualified
- [ ] Identify your industry profile: `saas | api | enterprise-software | marketplace | hardware`

---

## Template 1 — Input for `cost_to_serve_calculator.py`

Run **once per channel**.

```json
{
  "channel_name": "partner-led-EMEA",
  "deal_volume": 80,
  "gross_revenue": 4000000,
  "costs": {
    "sdr_attribution": 60000,
    "ae_attribution": 240000,
    "sales_engineer_attribution": 90000,
    "channel_manager_attribution": 180000,
    "customer_success_attribution": 120000,
    "support_attribution": 70000,
    "marketing_attribution": 50000,
    "partner_discount": 600000,
    "partner_MDF": 80000,
    "partner_enablement_time": 40000,
    "certification_investment": 20000,
    "channel_conflict_overhead": 15000,
    "tooling_attribution": 25000,
    "overhead_allocation_pct": 15.0
  }
}
```

### Field-by-field guidance

| Field | What to put |
|---|---|
| `channel_name` | Coherent GTM motion. Examples: `direct`, `partner-led`, `marketplace`, `reseller-NA`, `oem`. Naming matters — the optimizer recognizes `direct` and `partner` substrings for constraint enforcement. |
| `deal_volume` | Closed-won deal count, trailing-twelve-months (TTM). |
| `gross_revenue` | ARR (or annualized contracted revenue) closed in same TTM window. |
| `sdr_attribution` | Loaded cost of SDR time on this channel. If 30% of SDR team works on this channel, allocate 30% of total SDR loaded cost. |
| `ae_attribution` | Same logic for AE time. |
| `sales_engineer_attribution` | SE / solution architect time. Frequently underestimated for partner-led — includes partner technical enablement. |
| `channel_manager_attribution` | Loaded cost of channel-manager headcount. Direct channel = $0; partner channel = full loaded cost of channel team allocated by channel. **Do not leave $0 for partner channels** — the script flags it. |
| `customer_success_attribution` | CS team allocation. |
| `support_attribution` | Tier-1 / tier-2 support allocation. Partner-sourced customers often escalate to vendor faster — instrument support tickets by channel. |
| `marketing_attribution` | Demand-gen, content, events allocated to this channel. |
| `partner_discount` | Total $ given up in partner discount/margin for the TTM. |
| `partner_MDF` | Market Development Funds disbursed. |
| `partner_enablement_time` | Loaded $ of YOUR team's time spent on partner enablement. Frequently $0 in practice; should not be. |
| `certification_investment` | Partner certification programs, training events, ongoing enablement spend. |
| `channel_conflict_overhead` | Time/cost spent resolving deal conflicts between direct and channel teams. Industry: 5-8% of channel-team time. |
| `tooling_attribution` | CRM seats, PRM (Partner Relationship Management) tools, channel-specific tooling. |
| `overhead_allocation_pct` | Shared overhead allocated to this channel, as % of channel revenue. **Must be consistent across channels.** |

---

## Template 2 — Input for `channel_roi_analyzer.py`

Run **once across all channels**.

```json
{
  "profile": "saas",
  "channels": [
    {
      "channel": "direct",
      "investment_ttm": {
        "programs": 200000,
        "headcount_cost": 1600000,
        "partner_program_cost": 0,
        "mdf": 0,
        "tooling": 80000,
        "training": 60000
      },
      "returns_ttm": {
        "new_arr": 3800000,
        "expansion_arr": 900000,
        "retained_arr_attributable": 2400000
      }
    },
    {
      "channel": "partner-led",
      "investment_ttm": {
        "programs": 150000,
        "headcount_cost": 360000,
        "partner_program_cost": 280000,
        "mdf": 120000,
        "tooling": 30000,
        "training": 80000
      },
      "returns_ttm": {
        "new_arr": 1400000,
        "expansion_arr": 200000,
        "retained_arr_attributable": 900000
      }
    }
  ]
}
```

### Field guidance

| Field | What to put |
|---|---|
| `profile` | One of `saas`, `api`, `enterprise-software`, `marketplace`, `hardware`. Tunes LTV multiplier and marginal-decay alpha. |
| `investment_ttm.programs` | One-time program spend (events, content, campaigns). |
| `investment_ttm.headcount_cost` | Loaded headcount cost dedicated to this channel. |
| `investment_ttm.partner_program_cost` | Partner-program operating cost (PRM tooling, partner-portal infra, partner-only marketing). Distinct from MDF. |
| `investment_ttm.mdf` | Market Development Funds. |
| `investment_ttm.tooling` | Channel-specific tools. |
| `investment_ttm.training` | Internal training + partner training cost. |
| `returns_ttm.new_arr` | New ARR sourced by this channel, TTM. Strict definition: channel originated AND qualified. |
| `returns_ttm.expansion_arr` | Expansion ARR from customers sourced by this channel. |
| `returns_ttm.retained_arr_attributable` | Renewed ARR from customers sourced by this channel. |

---

## Template 3 — Input for `channel_mix_optimizer.py`

Run **once across all channels** with constraints.

```json
{
  "profile": "saas",
  "channels": [
    {
      "name": "direct",
      "deal_count_ttm": 120,
      "arr_ttm": 6000000,
      "avg_deal_size": 50000,
      "gross_margin_pct": 75,
      "cac": 18000,
      "sales_cycle_days": 75,
      "retention_rate": 0.92,
      "expansion_rate": 1.18,
      "partner_discount_pct": 0
    },
    {
      "name": "partner-led",
      "deal_count_ttm": 80,
      "arr_ttm": 4000000,
      "avg_deal_size": 50000,
      "gross_margin_pct": 75,
      "cac": 10000,
      "sales_cycle_days": 90,
      "retention_rate": 0.86,
      "expansion_rate": 1.08,
      "partner_discount_pct": 20
    }
  ],
  "constraints": {
    "min_direct_pct": 30,
    "max_partner_concentration_pct": 50
  }
}
```

### Field guidance

| Field | What to put |
|---|---|
| `name` | Channel name. Use `direct` / `partner` substrings for constraint enforcement to work. |
| `gross_margin_pct` | Use the **true gross margin** from `cost_to_serve_calculator.py` output, not the headline number. |
| `cac` | Fully loaded CAC. Includes the channel-specific costs from the cost-to-serve calculator. |
| `retention_rate` | **Per-channel** retention rate, not pooled. Critical input. |
| `expansion_rate` | Net expansion (1.0 = flat, 1.20 = 120% NRR). |
| `partner_discount_pct` | The discount % given up at sale (0 for direct channels). |
| `constraints.min_direct_pct` | Floor on direct-channel share (e.g., 30 = "at least 30% of investment must go to direct"). |
| `constraints.max_partner_concentration_pct` | Ceiling on any single partner channel (e.g., 50 = "no single partner channel may exceed 50%"). |

---

## After filling

1. Save each template as a JSON file (e.g., `channel-cts-partner.json`, `channel-roi.json`, `channel-mix.json`)
2. Run in sequence:
   ```bash
   python scripts/cost_to_serve_calculator.py --input channel-cts-partner.json --output markdown > out-cts-partner.md
   python scripts/channel_roi_analyzer.py --input channel-roi.json --profile saas --output markdown > out-roi.md
   python scripts/channel_mix_optimizer.py --input channel-mix.json --profile saas --output markdown > out-mix.md
   ```
3. Bring all three reports to the quarterly channel review.
