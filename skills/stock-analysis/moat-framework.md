# Moat Framework Reference

## What a moat actually is

A moat is a structural advantage that allows a company to earn returns on capital above its cost of capital for an extended period — despite competition. "They have great products" is not a moat. "Their AI is the best" is not a moat. A moat is a *structural* feature that makes it hard for competitors to replicate the returns, not just the product.

The correct test: **If a well-capitalized, intelligent competitor threw $5B and 5 years at copying this business, how much market share would they have? How much margin would the original company still hold?**

---

## Step 1: Identify the value chain layer

Where a company sits in its value chain determines how durable its moat is and who the real threats are. This matters most in tech.

**Layer 1 — Chip / hardware**: Capital-intensive, long-cycle, tends to be winner-take-most once scale is reached. Moats from manufacturing process, design IP, and customer qualification cycles. Disruption is slow but when it comes, it's structural.

**Layer 2 — Compute / infrastructure / cloud**: AWS, Azure, GCP, data centers. Massive capex, but creates switching costs through deep integration. Hyperscalers have unique bundling leverage over software layers above them.

**Layer 3 — Model / AI layer**: Currently a contested layer. Large foundation model companies have data/compute moats, but open-source compresses the gap. Moat is currently strongest for whoever has the most proprietary training data and RLHF infrastructure.

**Layer 4 — Application / software layer**: Where most public companies live. Moats here come from network effects, switching costs, and data advantages — not from the software code itself (which can be copied). Most vulnerable to disruption from Layer 3 moving up.

**Layer 5 — Distribution / marketplace layer**: Two-sided networks, ad exchanges, app stores. Moats from liquidity and data flywheels. Can be extraordinarily profitable but vulnerable to disintermediation (the layer above disintermediating the middleman).

*Note which layer the company sits in. Then identify whether the layers above or below it are threats.*

---

## Step 2: Classify the moat type

Be specific. "They have a moat" is not useful. Which type?

### Network effects
Value of the product increases as more users join. Types:
- **Direct** (same-side): More users → more value for existing users (social networks, communication tools)
- **Indirect** (cross-side): More buyers → more sellers → more buyers (marketplaces, ad exchanges, payment networks)
- **Data network effects**: More usage → better AI/algorithm → better product → more usage (most dangerous moat in tech because it compounds invisibly)

*Test: Would a competitor with an identical product and 1/10th the users be significantly worse? If yes, network effect is real.*

### Switching costs
High friction or risk in migrating to a competitor. Types:
- **Data/integration lock-in**: The customer's own data is inside the product (databases, CRM, ERP)
- **Workflow embeddedness**: Employees trained on the product; changing it disrupts operations
- **Contractual lock-in**: Multi-year contracts with exit penalties
- **Learning curve lock-in**: Platform is complex to learn; migration requires retraining

*Test: How long does a typical customer migration take? What's the loaded cost? If it's > 6 months and 1x annual contract value, switching costs are real.*

### Cost advantages
Lower unit costs than competitors through scale, location, or unique resource access.
- **Scale economies**: Fixed cost spread across more units (manufacturing, software R&D, distribution infrastructure)
- **Proprietary resource access**: Unique raw materials, talent pools, land rights
- **Process advantages**: Manufacturing innovation that cannot easily be copied

*Test: Can a competitor with 50% the revenue deliver the same margin? If not, why not?*

### Regulatory / government-backed moats
Licenses, certifications, IP protection, government contracts.
- Often more fragile than they appear (regulations change, IP expires)
- Most valuable when combined with another moat type

### Brand / intangibles
Customers pay a premium for the name. Requires consistent delivery over decades. Difficult to build, difficult to assess accurately.
- *Test: Do customers choose this brand even when a cheaper alternative exists? What's the premium they'll pay?*

---

## Step 3: Distinguish "owned" from "rented" moat

This is the most important question the short-seller reports on AppLovin asked — and it's the right question for any business.

**Owned moat**: The company controls the source of the advantage. Examples:
- Proprietary data the company collected from its own users/transactions
- Owned infrastructure (data centers, fiber, manufacturing plants)
- Deep brand equity built over decades
- Patents or trade secrets that cannot easily be engineered around

**Rented moat**: The advantage depends on a third party's permission that could be withdrawn. Examples:
- Access to another platform's API that could change terms (Meta, Apple, Google App Store, TikTok)
- Data derived from third-party identifiers that violate platform TOS
- Regulatory moat in a jurisdiction with an unstable regulatory environment
- "First-mover" advantage in a market that hasn't attracted serious capital yet

*Rented moats are still moats — until they're not. They require a specific question: "What happens if the permission is revoked?" If the answer is "the business shrinks significantly," the rented moat is a key risk, not a key asset.*

---

## Step 4: Assess moat durability

How long does the moat last? Classify:

| Durability | Horizon | Characteristics |
|---|---|---|
| Exceptional | 20+ years | Buffett-grade. Brand + network + switching cost all reinforcing. Coca-Cola, Visa. |
| Strong | 10–20 years | One dominant moat, high switching costs, slow-moving category. |
| Real but contested | 5–10 years | Identifiable moat but meaningful competitive threat exists. Need active monitoring. |
| Time-limited lead | 2–5 years | Technology or data advantage that compounds but can be replicated by well-capitalized entrants. |
| Fragile | 0–2 years | Based on first-mover luck, regulatory ambiguity, or borrowed platform access. |

*For tech-sector businesses: assume AI-driven businesses have shorter moat horizons than they appear. Every foundation model advance compresses application-layer edges. The question is whether the company has proprietary data + distribution that the AI runs on — not just whether their AI is currently better.*

---

## Step 5: Identify real competitors

The scariest competitor is usually not the obvious one.

**Framework for finding the real threat:**
1. Who has the most data + capital + infrastructure in an adjacent space who *hasn't* competed yet but could?
2. What new category of entrant does the technology make possible? (e.g., "SDK-less" players in ad-tech)
3. Which hyperscaler could bundle this capability into their existing offering at zero marginal cost?
4. What happens when the AI layer gets good enough that the application layer becomes unnecessary? (The "SaaSpocalypse" question)

Always map competitors in three buckets:
- **Direct competitors** (same product, same customer)
- **Indirect competitors** (different approach, same job-to-be-done for the customer)
- **Platform/hyperscaler threats** (could make the product a commodity feature of something bigger)

---

## Step 6: Pricing power test

A company with a real moat should be able to raise prices without losing customers. Test by examining gross margin trends.

- **Gross margin expanding or stable over 3+ years**: Pricing power likely exists
- **Gross margin compressing**: Company is buying growth with margin — pricing power is weak or they're in a price war
- **Extremely high margins (>70% gross, >40% EBITDA)**: Real pricing power — but also a signal that attracts competition and regulatory scrutiny

*Note: Unusually high margins are simultaneously the bull case and the bear case. A business with 84% EBITDA margins doesn't stay there for a decade in a competitive market without a very specific reason. Identify that reason clearly, because if it goes away, the margin compresses and the multiple compresses simultaneously — a double hit.*

---

## Moat score guidance

Use this for the **Moat Durability** dimension in Stage 8 scoring:

| Score | Meaning |
|---|---|
| 9–10 | Exceptional, multi-decade moat. Multiple reinforcing types. Buffett-grade. |
| 7–8 | Strong, 10–15 year visibility. One dominant moat type with supporting advantages. |
| 5–6 | Real but contested. 5–8 year horizon. Known specific threats. |
| 3–4 | Narrow or fragile. 2–4 years. Relies on speed or permission. |
| 1–2 | No durable moat identified. Competing on price or execution only. |

*Penalize for any rented moat component that is under active regulatory or platform threat.*
