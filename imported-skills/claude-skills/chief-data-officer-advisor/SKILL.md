---
name: "chief-data-officer-advisor"
description: "Chief Data Officer advisory for startups: AI training data rights and consent provenance, data product strategy (warehouse vs lakehouse vs mesh, build-vs-buy), B2B customer-data-as-asset valuation and M&A readiness, data team org evolution. Use when deciding whether to train models on customer data, choosing data architecture, valuing data for fundraising or M&A, sequencing data hires, or when user mentions CDO, chief data officer, data strategy, data mesh, lakehouse, training data, data product, data monetization, or customer data asset. NOT a tactical data engineering skill — strategic decisions only."
license: MIT
metadata:
  version: 1.0.0
  author: Alireza Rezvani
  category: c-level
  domain: chief-data-officer-leadership
  updated: 2026-05-12
  python-tools: ai_training_data_audit.py, data_product_strategy_picker.py, data_asset_valuator.py
  frameworks: training-data-rights-matrix, data-product-strategy, customer-data-as-asset, data-team-org-evolution
---

# Chief Data Officer Advisor

Strategic data leadership for startup CDOs and founders without one. **Four decisions, no surveys:**

1. **Can we train our model on this data?** — origin × consent × use-case matrix
2. **Warehouse, lakehouse, or mesh — and what do we build vs buy?** — stage-driven architecture
3. **What is our customer data worth?** — strategic value + M&A multiplier + productization paths
4. **What data role do we hire next?** — stage-to-role map, centralize-vs-embed trigger

This skill does **not** cover tactical data engineering. For schema design, observability, query optimization, RAG, or ML platform implementation, see `engineering/database-designer/`, `engineering/observability-designer/`, `engineering/data-quality-auditor/`, `engineering/sql-database-assistant/`, `engineering/rag-architect/`, `engineering/llm-cost-optimizer/`.

## Keywords

CDO, chief data officer, AI training data, consent provenance, training rights, GDPR Article 6 lawful basis, GDPR Article 22, EU AI Act high-risk, ePrivacy, copyright fair use, hiQ v. LinkedIn, scraped data, synthetic data, data product, data mesh, lakehouse, medallion architecture, dbt, Snowflake, BigQuery, Databricks, Fivetran, Airbyte, reverse ETL, feature store, customer data as asset, data monetization, data productization, anonymization, k-anonymity, differential privacy, M&A data diligence, data org, analytics engineer, data engineer, data scientist, data product manager, centralize vs embed, hub and spoke

## Quick Start

```bash
# Audit data sources for AI training eligibility
python scripts/ai_training_data_audit.py                              # uses embedded sample
python scripts/ai_training_data_audit.py path/to/sources.json

# Pick data architecture + build-vs-buy + sequencing
python scripts/data_product_strategy_picker.py                        # uses embedded Series A SaaS
python scripts/data_product_strategy_picker.py path/to/profile.json

# Value the customer data corpus + productization viability
python scripts/data_asset_valuator.py                                 # uses embedded B2B sample
python scripts/data_asset_valuator.py path/to/corpus.json
```

## Key Questions (ask these first)

- **What decision does this data drive?** (If none, why are we collecting it?)
- **What's the consent provenance of every source we want to train on?** (TOS-only is not the same as explicit opt-in.)
- **Who are the internal data consumers, and how many distinct domains do they span?** (Drives centralize-vs-embed and warehouse-vs-mesh.)
- **In an M&A scenario, is our data a moat or a liability?** (Customer carve-outs in MSAs can flip the answer.)
- **Are we hiring an analytics engineer or a data scientist next?** (They solve different problems; founders confuse them.)
- **Have we run an anonymization audit before any external sharing?** (k-anonymity ≥ 5 is the floor, not the ceiling.)

## Core Responsibilities

### 1. AI Training Data Rights

The 2026 question every startup is facing: **can we use customer data to train our model?**

The answer is rarely binary. It depends on three independent dimensions:

| Dimension | Values |
|---|---|
| **Origin** | 1st-party-explicit-opt-in / 1st-party-TOS-only / partner-licensed / scraped / synthetic |
| **Data class** | Anonymous aggregate / behavioral / PII / 3rd-party content / regulated (PHI, PCI, kids) |
| **Use case** | In-product personalization / fine-tune our model / train foundation model / external sharing |

Each combination produces GO / MITIGATE / NO-GO. **Run** `ai_training_data_audit.py` on a JSON inventory of sources.

See `references/ai_training_data_rights.md` for the full matrix + GDPR Art. 6 lawful basis decision tree + EU AI Act high-risk triggers.

### 2. Data Product Strategy

**Architecture choice (warehouse vs lakehouse vs mesh) is stage-driven, not preference-driven:**

- **Warehouse only** (Snowflake / BigQuery / Postgres): ≤5 data consumers, <2TB, no ML use cases
- **Lakehouse** (warehouse + object storage, often Databricks or Snowflake-with-Iceberg): 5–25 data consumers, 2TB–1PB, 1–3 ML use cases
- **Data mesh**: 25+ data consumers across 4+ domains, federated ownership culture in place

**Build vs buy is decided per layer:**

| Layer | Buy unless | Build only if |
|---|---|---|
| Storage / warehouse | Never build | (You’re a data infra company) |
| ELT / ingest | Never build | Source isn’t supported by Fivetran/Airbyte |
| Modeling (dbt) | Always build | This is your IP |
| BI / dashboards | Buy at <100 consumers | Embedded analytics for customers |
| Feature store | Defer until 3+ prod models | Then build OR buy Tecton/Hopsworks |
| ML platform | Defer until 5+ prod models | Then buy SageMaker/Vertex/Databricks |

**Run** `data_product_strategy_picker.py` for a stage-specific recommendation. See `references/data_product_strategy.md` for kill criteria per architecture and the build-vs-buy decision tree.

### 3. B2B Customer-Data-as-Asset

**The shift:** at Series B+, customer data is no longer just operational — it’s an asset that can be:
- A defensibility moat (replicating requires years of customer cohort)
- An M&A multiplier (1.2x–2x ARR uplift for strategic buyers)
- A direct revenue stream (anonymized industry benchmarks, embedding endpoints, licensing)

But it can also be a **liability**:
- 47/380 customers with MSA carve-outs makes productization legally infeasible
- Anonymization audits often reveal re-identification risk above tolerable thresholds
- Regulatory exposure increases linearly with productization (GDPR Art. 28 processors vs Art. 26 joint controllers)

**Run** `data_asset_valuator.py` with corpus characteristics to get strategic value score + productization paths + risk-adjusted value.

See `references/customer_data_as_asset.md` for the valuation framework, M&A diligence prep checklist, and contractual constraint audit pattern.

### 4. Data Team Org Evolution

**The wrong question:** "Should we hire a data scientist?"
**The right question:** "What’s the next decision we can’t make because we lack data, and what role unblocks that?"

Stage-to-role map (B2B SaaS baseline):

| Stage | First hire | Then | Then |
|---|---|---|---|
| Pre-seed / seed | Founder-as-analyst (SQL + spreadsheets) | — | — |
| Series A (Series A) | Analyst | Analytics engineer (dbt) | — |
| Series B | Data engineer | Senior analyst (embedded in GTM) | Data PM (if 3+ teams need data) |
| Growth | Manager of analytics | ML engineer (if model is core) | Head of Data |
| Late-stage | Head of Data → CDO | Specialized: BI, MLE, DPO | Federated owners per domain (mesh) |

**Centralize-vs-embed trigger:** when 3+ functional areas (sales, marketing, product, ops, CS) need bespoke data weekly, the central team becomes the bottleneck. Move to hub-and-spoke (central platform + embedded analysts) before that becomes a hiring crisis.

See `references/data_team_org_evolution.md`.

## Workflows

### Workflow 1: AI Training Decision (1 hour)
**Goal:** Decide whether a specific data source can train a specific use case.

```bash
# 1. Build sources.json with one entry per data source
# 2. Run the audit
python scripts/ai_training_data_audit.py sources.json
# 3. For each MITIGATE: assign owner + remediation
# 4. For each NO-GO: document the kill reason for the legal log
# 5. Cross-check with cs-general-counsel-advisor on top-3 mitigation items
# 6. Log via /cs:decide
```

### Workflow 2: Architecture Decision (1 day)
**Goal:** Pick warehouse / lakehouse / mesh and the build-vs-buy split for the next 12 months.

```bash
python scripts/data_product_strategy_picker.py profile.json
# Cross-check with cs-cto-advisor on engineering capacity
# Cross-check with cs-cfo-advisor on 3-year TCO
# Log via /cs:decide; consider /cs:freeze 90 if signing a multi-year SaaS contract
```

### Workflow 3: Data Asset Valuation for M&A Prep (3 days)
**Goal:** Value the data corpus and prepare for due diligence.

1. Inventory the corpus: size, freshness, exclusivity, customer overlap, contractual restrictions
2. Run `data_asset_valuator.py`
3. Run the M&A diligence prep checklist in `customer_data_as_asset.md`
4. Surface contractual carve-outs to cs-general-counsel-advisor for re-papering plan
5. Decide productization path (benchmark report / embedding endpoint / direct license)
6. Log via /cs:decide

### Workflow 4: Data Team Roadmap (1 week)
**Goal:** Build the next 18 months of data hires aligned to business decisions.

1. List the top 5 decisions the business can’t make today due to missing data or analysis
2. Map each decision to the role that unblocks it
3. Sequence hires (one role at a time, ramp before next)
4. Cross-check with cs-chro-advisor on comp bands and leveling
5. Identify the centralize-vs-embed trigger date

## Output Standards (when invoked via cs-cdo-advisor)

```
**Bottom Line:** [one sentence — decision and rationale]
**The Decision:** [one of the 4 framings]
**The Evidence:** [numbers, not adjectives]
**How to Act:** [3 concrete next steps]
**Your Decision:** [the call only the founder can make]
```

## Adjacent Skills

- `c-level-advisor/skills/cto-advisor/` — architecture capacity, scaling cliffs
- `c-level-advisor/skills/ciso-advisor/` — data security, threat modeling for productized data
- `c-level-advisor/skills/general-counsel-advisor/` — contractual constraints, DPA, training-data rights
- `c-level-advisor/skills/cfo-advisor/` — build-vs-buy TCO, M&A valuation math
- `c-level-advisor/skills/chro-advisor/` — data team hiring, leveling, comp
- `engineering/skills/database-designer/` — tactical schema design
- `engineering/skills/rag-architect/` — tactical AI/RAG implementation
- `engineering/llm-cost-optimizer/` — model cost management

## References

- [ai_training_data_rights.md](references/ai_training_data_rights.md) — The training-rights matrix + GDPR Art. 6 / EU AI Act decision tree
- [data_product_strategy.md](references/data_product_strategy.md) — Warehouse / lakehouse / mesh kill criteria + build-vs-buy decision tree
- [customer_data_as_asset.md](references/customer_data_as_asset.md) — Valuation framework + M&A diligence prep + productization paths
- [data_team_org_evolution.md](references/data_team_org_evolution.md) — Stage-to-role map + centralize-vs-embed trigger

---

**Version:** 1.0.0
**Status:** Production Ready
**Disclaimer:** Decisions touching training data rights, data productization, or M&A data diligence should involve qualified counsel. This skill surfaces decisions and tradeoffs — it does not replace legal review.
