# Corporate Formation Reference

## Entity Type Comparison

### Delaware C-Corporation
**Why Delaware?**
- Delaware General Corporation Law (DGCL, Title 8, Delaware Code) is the most developed corporate statute in the US, with decades of Court of Chancery precedent covering fiduciary duties, stockholder rights, and M&A transactions.
- Court of Chancery: specialized business court with no juries, fast decisions, expert judges — critical for investor disputes, M&A, and derivative suits.
- Investor familiarity: virtually all VC term sheets, NVCA model documents, YC SAFE templates, and Cooley/Fenwick/Wilson Sonsini standard docs assume Delaware C-corp.
- Multiple stock classes: common stock (founders/employees) and preferred stock (investors) with customizable liquidation preferences, anti-dilution, voting rights.
- No state income tax on income earned outside Delaware.
- March 2025: Significant DGCL amendments enacted clarifying fiduciary duties and conflicted transactions (Section 144 reforms).

**Formation Costs**
- State filing fee: $89 (Certificate of Incorporation)
- Registered agent: $50–$300/year (must have Delaware physical address)
- Attorney fees for full incorporation package: $1,500–$5,000 (or $0–$500 via Stripe Atlas, Clerky, Gust)
- Foreign qualification in operating state: $200–$800/state

**Annual Costs (Minimum)**
- Delaware franchise tax: $175 minimum (small companies) — WARNING: under the Authorized Shares Method, a company with 10M authorized shares pays ~$85,000/yr; use the Assumed Par Value Capital Method to keep tax at $400–$1,000 for early-stage companies.
- Annual report filing fee: $50 (due March 1)
- Registered agent: $50–$300/yr
- Total minimum: ~$275–$575/yr before legal fees

**Corporate Governance Structure**
- **Board of Directors** (DGCL §141): Manages the corporation's business and affairs. Can be 1 person at inception. Quorum = majority of total directors unless bylaws specify otherwise (minimum ⅓). Board acts by majority vote at duly noticed meetings or by unanimous written consent.
- **Officers**: CEO, CFO, Secretary (minimum required in most states). Officers appointed by and serve at pleasure of the board.
- **Stockholders**: Vote on fundamental changes (mergers, asset sales, charter amendments, election of directors). Protected by appraisal rights in certain mergers.
- **Bylaws**: Internal operating rules (DGCL requires bylaws). Cover board composition, officer titles, meeting procedures, notice requirements, proxy voting, indemnification.

**Key Governing Documents**
1. **Certificate of Incorporation** (charter): Filed with Delaware; sets authorized share structure, par value, board size, and any supermajority voting requirements.
2. **Bylaws**: Internal operating rules; adopted by board at organizational meeting.
3. **Stockholder/Investor Rights Agreement**: Negotiated at Series A; covers registration rights, information rights, pro-rata rights.
4. **Right of First Refusal and Co-Sale Agreement**: Restricts founder stock transfers; investors get ROFR/co-sale on any transfer.
5. **Voting Agreement**: Board composition commitments; drag-along rights.

**Capitalization Table Basics**
- Founders: typically receive restricted stock (vesting over 4 years, 1-year cliff)
- Employees: stock options from equity incentive plan (typically 10–20% of fully diluted shares)
- Investors: convertible preferred stock

### LLC vs. C-Corp
| Factor | LLC | C-Corp |
|---|---|---|
| Default tax | Pass-through (K-1) | Double taxation (corporate + personal) |
| VC fundable? | Generally no (pension funds can't hold LLC interests in many cases) | Yes |
| QSB stock (§1202 exclusion)? | No | Yes (up to $10M or 10x basis gain excluded) |
| Employee stock options? | Limited (profits interests, not true options) | Yes (ISOs and NQSOs) |
| Governance complexity | Low | High |
| Best for | Bootstrapped, real estate, joint ventures | VC-track startups |

### S-Corporation
- Maximum 100 shareholders, all US persons/residents
- One class of stock only (no preferred stock for investors)
- Pass-through taxation
- **Rarely appropriate for VC-track startups** — investor preferred stock immediately violates one-class rule

## Foreign Qualification

When a Delaware-incorporated company "does business" in another state, it must register as a foreign corporation in that state. Triggers include: physical office, employees on-site, recurring business transactions.

**Cost examples (2025):**
- California: $100 filing fee + minimum franchise tax ($800/yr)
- New York: $250 filing fee
- Texas: $750 filing fee (corporations)
- Most states: $150–$800 filing fee + annual report/fee

**Process:** File Certificate of Authority (or equivalent) with the state's Secretary of State. Must maintain a registered agent in each state.

## Corporate Governance Best Practices for Startups

**Board Composition Pre-Series A**
- Typically 1–3 directors (founders only, or founders + 1 independent)
- At Series A: typically 5-member board (2 founders, 2 investors, 1 independent)
- Independent directors provide fiduciary check and expertise

**Protective Provisions (Preferred Stock Rights)**
Standard NVCA protections require preferred stockholder consent for:
- Changing preferred rights
- Creating senior or pari passu securities
- Dividends above threshold
- Liquidation/dissolution
- Changing authorized shares
- Merger/asset sale

**Written Consent in Lieu of Meeting**
Delaware permits stockholder and board action by written consent (DGCL §228) — useful for fast-moving startups; requires consent of holders with requisite voting power.

**Annual Housekeeping**
- Annual board meeting (or written consent confirming officers)
- Stock ledger maintenance
- 83(b) elections tracked
- Section 409A valuations current
- Delaware franchise tax filed by March 1
- Foreign qualifications renewed annually
