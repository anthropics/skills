# Financial Operations (FinOps)

## ERP Selection: NetSuite vs. Sage Intacct vs. Others

### When to Upgrade from QuickBooks
- Outgrowing QuickBooks indicators: >$5M ARR, multi-entity structure, need for revenue recognition automation (ASC 606), audit preparation, or Series B investor scrutiny
- Typical upgrade timing: Series A to Series B transition

### NetSuite (Oracle)
**Best for**: Companies that need a true ERP (not just accounting) — inventory management, order management, CRM integration, multi-subsidiary
- **Strengths**: Comprehensive modules (financials, inventory, CRM, HR, project management), global multi-currency/multi-entity, strong reporting and dashboards, widely understood by investors/auditors
- **Weaknesses**: Implementation complexity (3–6 months), expensive ($30K–$100K+ annually for mid-market), requires dedicated admin
- **SaaS-specific**: Advanced Revenue Management (ARM) module for ASC 606 automation; subscription billing through SuiteBilling or integrate with Maxio/Chargebee

### Sage Intacct
**Best for**: Finance-first organizations that don't need the full ERP stack; especially strong for professional services, nonprofits, and multi-entity structures
- **Strengths**: Best-in-class financial reporting and dimensional reporting, faster implementation (2–4 months), strong multi-entity consolidation, native ASC 606 revenue recognition, AICPA preferred accounting platform
- **Weaknesses**: Less robust for operations beyond finance (no native inventory, order management limited), smaller ecosystem
- **SaaS-specific**: Excellent subscription billing integration (Maxio/Chargebee native connectors), automated revenue recognition, project accounting

### QuickBooks Enterprise
**For**: Sub-$5M revenue companies; straightforward billing models; <10 users
- Not suitable for: Multi-entity, complex ASC 606, audit-ready financials, investor reporting at scale

### Integration Stack (Modern Finance Tech)
A best-in-class finance tech stack for growth-stage SaaS:
- **ERP**: NetSuite or Sage Intacct
- **Billing / Revenue Recognition**: Maxio (formerly Chargify + SaaSOptics), Chargebee, or Zuora
- **AP Automation**: Bill.com, Tipalti (for international), or Airbase
- **Expense Management**: Ramp, Brex, or Concur
- **Payroll**: Rippling, Gusto, or ADP Run (for >250 employees)
- **FP&A**: Mosaic, Pigment, Cube, or Anaplan (for complex models)
- **Data**: Looker/Tableau connected to a data warehouse (Snowflake, BigQuery) for analytics

---

## Month-End Close Process

A well-run month-end close for a growth-stage SaaS company should complete within 5–7 business days of month-end. Best-in-class: 3–5 days.

### Close Calendar Template (5-Day Close)
| Day | Activity |
|---|---|
| Day 1 | Lock AP: all vendor invoices coded and approved; payroll finalized |
| Day 1 | Revenue recognition run: billing system exports to ERP; ASC 606 schedules updated |
| Day 2 | Bank reconciliations; credit card reconciliations |
| Day 2 | Prepaids and accruals: insurance, software subscriptions, vendor accruals |
| Day 3 | Deferred revenue roll-forward; commissions (ASC 340-40) amortization |
| Day 3 | Fixed assets and capitalized software amortization |
| Day 4 | Intercompany eliminations (if multi-entity); stock-based compensation journal entries |
| Day 4 | First-pass trial balance review; flux analysis (flagging large unexplained variances) |
| Day 5 | CFO review; final adjustments; B/S reconciliation sign-off; close GL |
| Day 5–7 | Flash report to CEO and board; begin management reporting package |

### Common Close Bottlenecks and Solutions
- **Late invoices from vendors**: Require electronic invoicing; set AP cutoff at Day 2
- **Credit card reconciliation**: Issue corporate cards with spend management tools (Ramp, Brex) that auto-code and sync to ERP
- **Revenue recognition complexity**: Use billing system + revenue recognition software (Maxio, Chargebee) that automates 606 schedules
- **Manual journal entries**: Document all recurring JEs as templates; automate where possible

### Close Quality Controls
- **Reconcile all balance sheet accounts monthly**: Every B/S account should have a supporting schedule
- **Three-way tie-out**: Revenue recognized = sum of customer contract schedules = GL; AR aging = AR sub-ledger = GL
- **Flux analysis**: For every P&L line, calculate variance vs. prior month and prior year; require explanation for any variance >$10K or >10%

---

## AP Automation

### Process Flow
1. Invoice received (email, EDI, vendor portal)
2. OCR/AI extracts key fields (vendor, amount, due date, GL code)
3. 3-way match: invoice vs. purchase order vs. receiving confirmation
4. Routed for approval based on dollar threshold (e.g., <$1K auto-approve; $1K–$10K manager; >$10K VP)
5. Approved invoices scheduled for payment batch (twice weekly)
6. Payment via ACH, wire, or check; automated remittance advice to vendor

**Key AP platforms**: Bill.com (best for SMB/mid-market), Tipalti (best for international multi-entity), Airbase (best for combined AP + expense + corporate cards)

---

## AR Automation

### Billing and Collections Workflow
1. Contract signed → auto-generate invoice in billing system
2. Invoice sent via email + PDF; offer ACH/credit card payment portal
3. Automated payment reminders at net-7, net-14, net-30 intervals
4. Auto-apply payment receipts to open invoices; reconcile to bank
5. Aged AR report reviewed weekly; escalate to AE for accounts >45 days past due

**Key AR platforms**: Stripe Billing, Chargebee, Maxio (for SaaS billing); HighRadius, Versapay, or YayPay for collections automation

---

## Expense Management

### Corporate Card and Expense Policy
- Issue corporate cards (Ramp, Brex) to all employees with defined spend categories and limits
- Set merchant category code restrictions at card level (prevent personal purchases)
- Require receipt upload within 24 hours; receipt-matching automation reduces reconciliation time by 80%
- Defined expense policy: per diems for travel, maximum meal/entertainment limits, pre-approval for >$500 non-recurring expenses

### Payroll Systems
- **<50 employees**: Gusto (simple, low-cost, good integrations)
- **50–500 employees**: Rippling (all-in-one HR + payroll + benefits + IT) or ADP Workforce Now
- **500+ employees**: Workday, ADP Enterprise, or Ceridian Dayforce
- Ensure payroll integration to ERP via direct connect or file import (avoid manual journal entries)
- Run payroll on a defined schedule; avoid off-cycle runs (each one costs $100–$500 in admin time)
