# Securities Law for Founders Reference

## SAFE (Simple Agreement for Future Equity)

**Origin**: Created by Y Combinator in 2013. Designed to be simpler than convertible notes — no interest, no maturity date, not technically debt.

**Legal classification**: SAFEs are securities under federal law. Must comply with federal securities laws (typically Reg D) and applicable state blue sky laws.

### SAFE Mechanics

**Post-Money SAFE** (YC standard since 2018; ~87% of SAFEs issued in Q3 2024):
- Investor ownership percentage = Investment Amount / Post-Money Valuation Cap
- Example: $200K SAFE on $4M post-money cap = exactly 5% ownership at conversion (before option pool for next round)
- Advantage: investor knows exact ownership before round closes; company can calculate total dilution from all SAFEs

**Pre-Money SAFE** (older, now rare):
- Conversion calculated on pre-money valuation; investor ownership depends on size of financing round — less predictable for investors

**Key SAFE Terms:**
- **Valuation Cap**: maximum company valuation at which SAFE converts; investor gets more shares if company valuation at priced round exceeds cap
- **Discount Rate**: percentage reduction on per-share price vs. new investors in priced round; 10%–30% typical; converts at discounted price
- **MFN (Most Favored Nation)**: if company issues future SAFEs on better terms, existing SAFE holder's terms automatically update to match; common in SAFEs without valuation cap or discount
- **Pro-Rata Rights**: investor right to participate in future rounds up to their pro-rata ownership percentage — often in side letter, not main SAFE

**YC SAFE Variants (current):**
1. Post-Money Safe: Valuation Cap, no Discount
2. Post-Money Safe: Discount, no Valuation Cap
3. Post-Money Safe: MFN, no Valuation Cap, no Discount
4. Post-Money Safe: Conversion Percentage (newer variant)
Note: YC officially discontinued the "Valuation Cap + Discount" variant in 2021.

**SAFE vs. Convertible Note:**
| Feature | SAFE | Convertible Note |
|---|---|---|
| Interest | None | Typically 5–8% |
| Maturity | None | 12–24 months (risk of default) |
| Debt on balance sheet | No | Yes |
| Negotiation complexity | Low | Medium |
| Investor protection at dissolution | Minimal | Creditor priority |
| SEC treatment | Security (not debt) | Debt security |

---

## Regulation D Exemptions

Reg D (17 CFR §230.501 et seq.) provides exemptions from SEC registration under Securities Act of 1933.

### Rule 506(b) — Most Common for SAFEs/Notes
- No general solicitation or advertising
- Unlimited accredited investors
- Up to 35 non-accredited but "sophisticated" investors (must have sufficient knowledge and experience in financial matters)
- Issuer must "reasonably believe" investors are accredited/sophisticated
- No cap on raise amount
- File Form D with SEC within 15 days of first sale
- Blue sky law preempted for accredited investors; state notice filings may be required

### Rule 506(c) — Allows General Solicitation
- Can publicly advertise the offering (emails, social media, etc.)
- ALL investors must be accredited
- Must take "reasonable steps to verify" accredited status
- March 2025 SEC guidance: minimum investment threshold of $200K (natural persons) or $1M (entities) + investor representations may satisfy verification requirement
- Common for publicly announced fundraising on AngelList, etc.

### Rule 504
- Raise up to $10M in 12 months
- Permits general solicitation in certain circumstances
- Less common for tech startups; blue sky laws apply

**Accredited Investor Definition** (most relevant for startups):
- Natural person: $1M+ net worth (excluding primary residence) OR income $200K+ (individual) or $300K+ (joint) in each of prior 2 years with reasonable expectation of same
- Entity: $5M+ in assets; or all equity owners are accredited; or certain investment companies
- 2020 expansion: knowledgeable employees of private funds; SEC/FINRA license holders; family offices

**Form D**: Simple online filing (EDGAR). Must file within 15 days of first sale. No substantive review by SEC — administrative requirement. Failure to file: technical violation; can bar future offerings; embarrassing in diligence but generally curable.

**State Blue Sky Laws**: Reg D preempts state securities registration for Rule 506 offerings to accredited investors. States can still require notice filings (usually simple form + small fee). Non-accredited investors in 506(b) are NOT preempted — must comply with applicable state law.

---

## Section 409A Valuation

**Legal basis**: Internal Revenue Code §409A (effective 2009). Governs all deferred compensation including stock options.

**Why it matters**: Options granted at exercise price below Fair Market Value (FMV) are treated as deferred compensation — triggering:
- 20% excise tax on the spread (income above exercise price) AT TIME OF VESTING (not exercise)
- Immediate income recognition at vesting
- Additional interest penalties
- These taxes hit the EMPLOYEE, not the company; but creates massive employee relations problem and potential SEC/accounting issues

**Safe harbor methods for establishing FMV:**
1. **Independent appraisal by qualified appraiser**: most protective; IRS must prove valuation is "grossly unreasonable" to challenge (reversed burden of proof). REQUIRES: ABV- or ASA-credentialed valuator; performed within 12 months; no material changes.
2. **Illiquid startup formula method**: startups that are less than 10 years old with no established trading market can use reasonable valuation method reflecting company's value (based on assets, discounted cash flows, comparable transactions). Less protective than independent appraisal.
3. **Binding formula**: used for buyback rights (less applicable to option grants)

**Cost**: $1,500–$9,000 depending on company stage and complexity. Early-stage (pre-revenue): $1,500–$3,000. Late-stage: $5,000–$9,000+.

**Frequency requirements:**
- Valid for 12 months from appraisal date
- Must be updated within 90 days of any "material event"
- Material events: priced financing round, LOI for acquisition, filing IPO registration, material change in financial performance

**Practical guidance**: Get 409A BEFORE granting any options. Many formation service providers (Carta, Stripe Atlas, Clerky) now include 409A as part of incorporation package. Refresh after each priced round.

---

## Section 83(b) Election

**Legal basis**: IRC §83(b). Allows taxpayer to elect to include in gross income the fair market value of property received for services at time of transfer (rather than when restrictions lapse/vesting occurs).

**When it applies**: Restricted stock subject to vesting. NOT applicable to unvested stock options (different tax treatment under §83(e)(3)).

**Why founders should file**: At grant, FMV is typically near cost basis (= minimal income). Without 83(b), each tranche of vesting stock is taxable at FMV on vesting date — if company value has grown, could mean large ordinary income tax bills on each vesting event, even without liquidity.

With 83(b), founder pays tax at grant on the spread (often $0 or nominal), and future appreciation is capital gains (lower rate, taxed only on sale).

**83(b) for ISOs**: Generally not recommended (ISOs get favorable tax treatment differently); but for early exercise of ISOs when spread is zero, 83(b) can help with AMT timing.

**Filing deadline**: 30 days from the date of stock transfer. Irrevocable. Cannot be filed late. IRS does not grant extensions.

**How to file**:
1. Complete written 83(b) election statement (no IRS form — write own)
2. Mail to IRS Service Center where you file your taxes (USPS certified mail recommended)
3. Keep a copy
4. Attach copy to federal tax return for year of transfer
5. Notify the company
Note: IRS now accepts email submissions in some cases — consult attorney/accountant.

**Common mistake**: Founders assume 83(b) is automatic or that attorney handled it. It is the founder's personal tax obligation. Miss the 30-day window and it's permanent.

---

## Equity Compensation Plan Compliance

**ISO vs. NQSO:**
| Feature | ISO (Incentive Stock Option) | NQSO (Non-Qualified) |
|---|---|---|
| Tax at exercise | No regular income tax if AMT applies | Ordinary income on spread |
| Tax at sale | Capital gains (if holding periods met) | Capital gains on post-exercise appreciation |
| Eligible recipients | Employees only (including directors who are employees) | Anyone (employees, contractors, advisors) |
| Individual grant limit | $100K in options exercisable in any year | No limit |
| 409A requirement | Exercise price ≥ FMV at grant | Exercise price ≥ FMV at grant (409A) |
| Disqualifying disposition | If sold < 2yr from grant or < 1yr from exercise, ordinary income | N/A |

**Option pool**: typically 10–20% of fully diluted shares pre-Series A. Investors often require option pool "refresh" at each round (dilution falls on founders pre-round). The "option pool shuffle" can significantly dilute founders — negotiate to establish option pool post-money in SAFE, not pre-money.

**Alternative minimum tax (AMT)**: ISO exercise that creates a spread triggers AMT preference item — even if no regular tax owed. Can create large AMT bills in hot IPO years. Founders should consult tax advisor before large ISO exercises.

---

## Secondary Transactions

Private company stock sales by employees/founders before IPO or M&A. Increasing market (AngelList, Forge Global, Nasdaq Private Market).

**ROFR (Right of First Refusal)**: Company and investors typically have ROFR on any transfer. Founder must offer shares to company first (at proposed sale price), then investors, before selling to third party. ROFR triggers must be respected or transaction may be void.

**Company consent**: Some charters require board approval for transfers. Check certificate of incorporation and stockholder agreements.

**Insider trading**: Even private company insiders may have material nonpublic information obligations. SEC Reg 10b-5 applies to securities fraud regardless of company's public/private status. 10b5-1 plans can provide safe harbor.

**Tender offers**: Structured secondary liquidity events require compliance with SEC tender offer rules (Schedule TO) if structured as issuer tender offer or third-party tender offer to a large number of holders.

**Form D on secondary**: If secondary creates a new class of securities or involves general solicitation, may require new Reg D filing.
