# Policy Design Canon

Authoritative sources on **how to design a commercial policy as an artifact** — not how to discount, but how to write the document that governs discounting. The seven sources below ground the *structure* the skill emits (matrix + exception flow + lint).

The shared insight: a policy is only as good as the gaming surface it removes. Cliffs, ambiguous strategic-value definitions, and missing approver tiers are not stylistic flaws — they are gaming surfaces that AEs and customers will discover within one quarter.

---

## 1. SaaStr (Jason Lemkin) — Deal Policy Structure

Lemkin's SaaStr corpus on deal policy makes one structural argument repeatedly: **the policy must be writable on a single page that AEs can scan in the deal room.** If the policy needs a six-page memo to operate, no AE will follow it under quarter-close pressure.

Concrete practices:

- One discount matrix, one exception flow, one approver table. Three artifacts, max.
- Approver chains stop at the **lowest-authority hop that can sign** — not "escalate to CFO every time." Over-escalation trains AEs to over-discount because they assume the chain will accept whatever they propose.
- "Strategic value" must be defined with **concrete tests**, not adjectives. "Top-20 named account in 2026 target list" is a test; "important customer" is not.

**Cite this for:** the single-table matrix output of `discount_matrix_builder.py` and the lint rule L06 (`strategic_value_undefined`).

URL: https://www.saastr.com/

---

## 2. Winning by Design (Jacco van der Kooij) — Commercial Discipline

Van der Kooij's *Revenue Architecture* and the Winning by Design blueprints frame commercial policy as one of the **four operating systems** that govern recurring revenue (alongside ICP, motion, and metrics). Two principles the skill enforces:

- **Discount is a tool, not a verb.** Every discount must trade for something the customer commits to in writing — term length, prepay, expansion, reference. Discount-for-nothing is a leak.
- **The policy must distinguish "concession" from "investment"** — a strategic discount that pays back via expansion is an investment; a year-end discount that buys forecast is a concession. Investments get logged on the strategic-value tier; concessions don't.

**Cite this for:** the structure of `COMPENSATING_LIBRARY` in `exception_router.py` — every band of exception severity carries a non-negotiable list of customer commitments.

URL: https://winningbydesign.com/

---

## 3. Forrester — Deal Desk Maturity Research

Forrester's deal-desk research (Bob Apollo, Mary Shea) defines four maturity levels:

1. **Ad hoc** — discounts approved by relationship; no consistent record
2. **Formalized** — written policy exists; not data-backed; reviewed annually at best
3. **Operationalized** — policy is data-backed; quarterly reviewed; approver chain enforced
4. **Strategic** — policy is a product; A/B-tested band changes; tied to NRR targets

The skill targets level 3-4. The lint pass enforces the structural requirements (no inversion, no gaps, no cliffs, data-backed bands).

**Cite this for:** the framing that commercial policy is a designed artifact subject to lint, version control, and review — not folklore.

URL: https://www.forrester.com/

---

## 4. MIT Sloan — Incentive-System Gaming Research

MIT Sloan (Robert Gibbons, Bengt Holmström) published the foundational work on **multitask agency problems**: when agents are paid for outcome A but can game on dimension B, they will. Apply directly to discount policy:

- If "strategic value" lets an AE override the matrix, AEs will define every deal as strategic.
- If there's a cliff at $99K vs $100K ARR, AEs will split deals or pad them.
- If the precedent rule (last quarter's exception = this quarter's floor) isn't broken explicitly in policy, drift compounds.

**Cite this for:** lint rule L05 (`cliff_edge`) and the precedent-risk flag in `exception_router.py` — both are responses to predictable gaming surfaces that the agency-theory literature identifies.

URL: https://mitsloan.mit.edu/faculty/directory/robert-gibbons

---

## 5. McKinsey — Commercial Policy Effectiveness Studies

McKinsey's B2B pricing practice has published multiple studies on commercial policy effectiveness. The headline finding across deployments:

- **Companies that move from ad-hoc to operationalized commercial policy capture 2-4 pts of margin within 4 quarters** — without raising prices, without losing deals.
- **The biggest single move is closing the strategic-value loophole** — defining concrete tests so the tier isn't a catch-all.

**Cite this for:** the ROI claim that justifies the skill's existence. The skill produces the policy; the policy captures 2-4 pts of margin via McKinsey's deployment evidence.

URL: https://www.mckinsey.com/capabilities/growth-marketing-and-sales/our-insights

---

## 6. Bain — Discount Discipline & Pricing Power

Bain's *Pricing Power* research argues that commercial-policy maturity is the strongest internal predictor of pricing power. Two structural claims:

- **Discount discipline > price increases** for margin expansion. Raising list 5% and giving 10% more discount nets to a margin loss; holding list and tightening discount bands nets to a gain.
- **The CFO must own margin floors; the CRO must own discount bands; the Head of Deal Desk owns the matrix.** Mixing these accountabilities is the most common source of policy drift.

**Cite this for:** the `min_margin_pct` constraint input to `discount_matrix_builder.py` (CFO-owned) versus the `max_discount_pct_without_exception` (CRO/Deal-Desk-owned). The skill separates these by design.

URL: https://www.bain.com/insights/topics/pricing/

---

## 7. Salesforce CPQ — Commercial Policy Implementation Best Practices

Salesforce's CPQ implementation guides (and the surrounding ISV community) document the operational reality of encoding commercial policy in a system of record. Three practical lessons:

- **Every exception must produce machine-readable audit metadata.** "VP approved by email" doesn't survive an audit; "approval record in CPQ with timestamped justification + compensating commitments + named approver" does.
- **Approver chains should be enforced by the system, not by manager discipline.** Manager discipline degrades under quarter-end pressure; system enforcement doesn't.
- **The matrix must be versioned.** When you change a band, the old version must remain readable so historical deals can be audited against the policy that was in force at sign.

**Cite this for:** the structured `audit_trail` JSON block emitted by `exception_router.py` — designed to be machine-readable and persistable.

URL: https://www.salesforce.com/products/cpq/

---

## Synthesis: design principles the skill enforces

| Principle | Source | Where it shows up in the skill |
|---|---|---|
| One-page matrix, no six-page memo | SaaStr / Lemkin | `discount_matrix_builder.py --output markdown` produces one table |
| Discount-for-nothing is a leak | Winning by Design | `COMPENSATING_LIBRARY` per severity band in exception router |
| Policy as designed artifact | Forrester | The lint pass exists |
| Gaming surfaces are predictable | MIT Sloan | Lint rules L05 (cliff), L06 (undefined strategic), L01 (inversion) |
| Operationalized policy = 2-4 pts margin | McKinsey | ROI justification for the skill |
| CFO owns floor, CRO owns bands | Bain | Separate input parameters in `target_constraints` |
| Machine-readable audit metadata | Salesforce CPQ | `audit_trail` JSON block |
