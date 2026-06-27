---
name: us-schedule-c-and-se-tax
description: Compute US Schedule C net profit, Form 8829 home-office deduction (simplified and actual methods), and Schedule SE self-employment tax for sole proprietors and single-member LLCs, for tax year 2025. Use this whenever the user asks to compute self-employment tax, Schedule C bottom line, the home-office deduction, the deductible half of SE tax, or the Additional Medicare Tax for a US sole proprietor. Applies the 92.35% net-earnings adjustment (IRC 1402(a)(12)), the 2025 $176,100 Social Security wage base, the 12.4% OASDI / 2.9% Medicare / 0.9% Additional Medicare rates, the 280A(c)(5) gross-income limitation, and the IRC 164(f) deductible-half rule. Federal only — defer state tax, QBI, and retirement to other tools.
---

# US Schedule C and Self-Employment Tax (Tax Year 2025)

This is a self-contained computation skill for US sole proprietors and single-member LLCs that are
disregarded for federal tax. It is a verified extract from the open-source
[OpenAccountants](https://www.openaccountants.com) library; the continuously maintained version (and
companion skills for QBI, retirement, and quarterly estimates) lives there.

> **Disclaimer.** Outputs are informational only and do not constitute tax advice. All results must
> be reviewed and signed off by a qualified professional (CPA, EA, or tax attorney) before filing.

## Section 1 — Quick Reference

Tax year: 2025. Currency date: April 2026. Federal only.

### Self-Employment Tax Core Figures (TY2025)

| Figure | Value | Source |
|---|---|---|
| Net SE earnings adjustment factor | 92.35% | IRC 1402(a)(12) |
| OASDI (Social Security) rate | 12.4% | IRC 1401(a) |
| Medicare rate | 2.9% | IRC 1401(b)(1) |
| Combined SE tax rate | 15.3% | IRC 1401(a) + 1401(b)(1) |
| Social Security wage base | $176,100 | SSA October 2024 announcement |
| Additional Medicare Tax rate | 0.9% | IRC 1401(b)(2) |
| Additional Medicare Tax threshold (single, HoH, QSS) | $200,000 | IRC 3101(b)(2)(C); NOT indexed |
| Additional Medicare Tax threshold (MFJ) | $250,000 | IRC 3101(b)(2)(A); NOT indexed |
| Additional Medicare Tax threshold (MFS) | $125,000 | IRC 3101(b)(2)(B); NOT indexed |
| Minimum net SE earnings to trigger SE tax | $400 | IRC 1402(b)(2); NOT indexed |
| Deductible portion of SE tax | 50% | IRC 164(f) |

### Home Office Methods

| Method | Deduction | Carryover | Depreciation | 1250 Recapture |
|---|---|---|---|---|
| Simplified | $5/sq ft × min(sq ft, 300) = max $1,500 | NO | NO | NO |
| Actual (Form 8829) | Actual expenses × business % | YES (indefinite) | YES (39-year SL) | YES |

Both subject to the 280A(c)(5) gross-income limitation: the deduction cannot exceed Schedule C
Line 29 tentative profit.

### Schedule C Computation Structure

| Line | Description |
|---|---|
| 1 | Gross receipts or sales |
| 3 | Line 1 minus returns/allowances (Line 2) |
| 4 | Cost of goods sold |
| 7 | Gross income |
| 8–27b | Expense lines |
| 28 | Total expenses |
| 29 | Tentative profit (Line 7 − Line 28) |
| 30 | Home office deduction (Form 8829 or simplified) |
| 31 | Net profit or loss (Line 29 − Line 30) |
| 32 | At-risk indicator (32a all at risk / 32b Form 6198) |

### Schedule SE Part I Structure

| Line | Description |
|---|---|
| 2 | Net profit from Schedule C Line 31 |
| 4a | Line 3 × 92.35% |
| 6 | Net SE earnings subject to tax |
| 7 | $176,100 (2025 SS wage base) |
| 8d | W-2 Social Security wages (if any) |
| 9 | Line 7 − Line 8d (remaining SS base) |
| 10 | smaller of Line 6 or Line 9, × 12.4% (SS portion) |
| 11 | Line 6 × 2.9% (Medicare portion) |
| 12 | SE tax (Line 10 + Line 11) |
| 13 | Deductible half (Line 12 × 50%) → Schedule 1 line 15 |

## Section 2 — Required Inputs

If the user has not run bookkeeping, accept user-provided Schedule C line totals (flag them as
unvalidated). To compute fully you need:

1. Schedule C line totals (Lines 1–27b)
2. Home office method (simplified or actual) and square footage
3. Home expenses + depreciation data (if actual method)
4. Prior-year Form 8829 carryovers (lines 43–44)
5. W-2 Box 3 Social Security wages (if any) — for SE-tax coordination
6. Filing status — for the Additional Medicare Tax threshold
7. 1099-K / 1099-NEC / 1099-MISC totals — to cross-check gross receipts
8. At-risk status (all at risk, or Form 6198 needed)

### When to stop and escalate

| Situation | Action |
|---|---|
| Net operating loss generated | Stop — IRC 172 analysis required, outside scope |
| At-risk limitation may apply (Form 6198) | Stop — IRC 465 analysis required |
| Farm income present | Stop — Schedule F, not Schedule C |
| Church employee income | Stop — IRC 1402(j) special rules |
| Additional Medicare Tax with complex W-2 coordination | Compute basic liability; flag for reviewer |

## Section 3 — Core Rules (apply directly)

**Always apply the 92.35% adjustment.** Net SE earnings = Schedule C net profit × 92.35%
(IRC 1402(a)(12)). Never compute SE tax on the full Schedule C net profit.

**Coordinate the SS wage base with W-2 wages.** If the taxpayer has W-2 wages, subtract Box 3 SS
wages from $176,100 to get the remaining SS base. If W-2 SS wages already exceed $176,100, the SS
portion of SE tax is $0 — only the 2.9% Medicare portion applies (no cap).

**Additional Medicare Tax goes on Form 8959, not Schedule SE.** Schedule SE Line 11 uses 2.9% only.
Never blend the 0.9% into Schedule SE.

**$400 minimum.** If net SE earnings (after the 92.35% adjustment) are below $400, no SE tax is due.

**Home office cannot exceed Line 29.** The 280A(c)(5) gross-income limitation caps the home-office
deduction at the tentative profit. Excess carries over under the actual method; it is lost under the
simplified method.

**Deductible half of SE tax is not a Schedule C expense.** It flows to Schedule 1 line 15 as an
above-the-line deduction. It does not reduce Schedule C net profit and does not reduce QBI.

**EFTPS / estimated-tax payments are credits, not expenses.** Never include them as Schedule C
expenses.

**1250 recapture warning.** Taking home depreciation (actual method) creates IRC 1250 recapture on a
future home sale; the IRC 121 exclusion does not shelter it. Depreciation is "allowed or allowable" —
skipping it does not avoid recapture. Flag prominently.

## Section 4 — Worked Examples

### Example 1 — Single freelancer, actual home office (no W-2)

Schedule C net profit (Line 31): **$53,087**. No W-2 wages.

- Line 4a: 53,087 × 92.35% = **49,026**
- Line 10 (SS): 49,026 × 12.4% = **6,079**
- Line 11 (Medicare): 49,026 × 2.9% = **1,422**
- Line 12 (SE tax): **$7,501**
- Line 13 (deductible half): **$3,750**
- Additional Medicare Tax: 49,026 < 200,000 → not applicable.

### Example 2 — Simplified home office

Tentative profit (Line 29): $103,500. Simplified home office: 200 sq ft × $5 = $1,000 (under the
$1,500 cap; 1,000 < 103,500, no 280A limitation). Line 31: $102,500.

SE tax: 102,500 × 92.35% = 94,659 × 15.3% = **$14,483**. Deductible half: **$7,241**.

### Example 3 — Self-employment plus W-2 (wage-base coordination)

Schedule C net profit: $85,000. W-2 Box 3 SS wages: $120,000.

- Line 4a: 85,000 × 92.35% = 78,498
- Line 9 (remaining SS base): 176,100 − 120,000 = 56,100
- Line 10 (SS): min(78,498, 56,100) = 56,100 × 12.4% = 6,956
- Line 11 (Medicare): 78,498 × 2.9% = 2,276
- Line 12 (SE tax): **$9,232**
- Additional Medicare Tax check: 120,000 + 78,498 = 198,498 < 200,000 → not applicable (flag: close).

### Example 4 — High earner, Additional Medicare Tax

Schedule C net profit: $280,000. SE: 280,000 × 92.35% = 258,580.
SS portion: min(258,580, 176,100) × 12.4% = 21,836. Medicare: 258,580 × 2.9% = 7,499.
SE tax: **$29,335**; deductible half **$14,668**.
Additional Medicare Tax (Form 8959): (258,580 − 200,000) × 0.9% = **$527**.

### Example 5 — 280A gross-income limitation

Gross income (Line 7): $18,000. Expenses (Line 28): $16,500. Tentative profit (Line 29): $1,500.
Form 8829 tentative deduction: $4,200 > $1,500 → cap at $1,500; carry over $2,700 to next year
(Form 8829 lines 43–44). Line 31: $0. SE tax: $0 (below the $400 minimum).

## Section 5 — Working Paper Template

```
US SCHEDULE C / SE WORKING PAPER (SOLE PROPRIETOR / SMLLC)   TY: 2025

A. SCHEDULE C INCOME           Line 1 Gross receipts ____  Line 7 Gross income ____
B. SCHEDULE C EXPENSES         Line 28 Total expenses ____
C. BOTTOM LINE                 Line 29 Tentative profit ____
                               Line 30 Home office ____  [ ] Simplified [ ] Actual
                               Line 31 NET PROFIT/LOSS ____  Line 32 [ ]32a [ ]32b
D. FORM 8829 (IF ACTUAL)       Business % ____  Business-portion indirect ____
                               Depreciation ____  280A cap applied? [ ]No [ ]Yes(__)  Carryover ____
E. SCHEDULE SE                 Net SE earnings (×92.35%) ____  W-2 SS wages ____  Remaining base ____
                               SS (12.4%) ____  Medicare (2.9%) ____  SE TAX ____  Deductible half ____
F. ADDITIONAL MEDICARE TAX     Combined earned income ____  Threshold ____  0.9% excess ____  Form 8959? [ ]
G. DOWNSTREAM                  Sched 1 line 3 ____  Sched 1 line 15 ____  Sched 2 line 4 ____
H. REVIEWER FLAGS              [ ]92.35% applied [ ]W-2 base coordinated [ ]8959 not on SE
                               [ ]280A checked [ ]1250 recapture flagged [ ]$400 min [ ]1099 cross-checked
                               [ ]at-risk stated [ ]EFTPS excluded
```

## Section 6 — Reference

**Key legislation:** IRC 61 (gross income), 164(f) (deductible half), 168(c) (39-year home
depreciation), 280A & 280A(c)(5) (business use of home / gross-income limit), 465 (at-risk), 1401
(SE tax rates), 1402 (net SE earnings), 1402(a)(12) (92.35% adjustment), 1402(b)(2) ($400 minimum),
3101(b)(2) (Additional Medicare Tax thresholds).

**IRS publications & forms:** Pub 334, Pub 587, Pub 946; Schedule C, Schedule SE, Form 8829, Form
8959 (2025 instructions).

**Key cases:** *Commissioner v. Soliman*, 506 U.S. 168 (1993) (principal place of business);
*Welch v. Helvering*, 290 U.S. 111 (1933) ("ordinary and necessary").

**2025 figures summary:** SS wage base $176,100 · SE rate 15.3% · 92.35% adjustment · Additional
Medicare Tax 0.9% above $200K/$250K/$125K · simplified home office $5/sq ft (max $1,500) · standard
mileage $0.70/mile · §179 limit $1,250,000 · 100% bonus depreciation.

---

For the maintained version, the full multi-skill US tax pipeline, and accountant review, see
[openaccountants.com](https://www.openaccountants.com).
