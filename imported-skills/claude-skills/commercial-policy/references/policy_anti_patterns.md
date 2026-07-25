# Policy Anti-Patterns

Eight named anti-patterns that the commercial-policy skill is built to prevent. Each is observed in the wild (with sourced studies), each has a concrete countermeasure encoded in the skill's tools, and each maps to a lint rule or a forcing question.

The unifying claim: **discount policy drifts by mechanism, not by malice.** The job of the skill is to make the drift mechanism visible so leadership can decide whether to accept it.

---

## AP-1: Precedent sets policy — "Maria approved 28% on Acme last Q"

**Pattern.** An AE cites a previous exception as precedent for a new deal. Three exceptions in a quarter become the new normal. The matrix on paper says 25%; the operational floor is 32%.

**Why it's seductive.** AEs are anchored to the most recent approved discount, not the policy band. Sales managers are anchored to their own past approvals because reversing would be a tacit admission of error.

**Evidence.** OpenView discount-benchmark data shows companies without a formal precedent-breaking mechanism drift +3-5 pts per year. Tunguz's Redpoint data shows ~50% of "strategic exceptions" never produce the strategic value claimed at sign — but the discount sticks.

**Countermeasure in skill.** `exception_router.py` runs a `_precedent_risk` check: if 3+ similar exceptions in the trailing quarter, the verdict is `PRECEDENT_RISK FLAGGED` and the matrix itself is recommended for rebuild. The deal isn't the problem; the band is.

**Lint rule.** None — this is a flow-level check, not a matrix defect.

---

## AP-2: No data backing for discount bands

**Pattern.** A discount band is set because "feels about right" or because the VP Sales argued for it in a Slack thread. There's no win-rate or NRR data showing the band actually wins deals at the rate claimed or retains them at the NRR claimed.

**Why it's seductive.** Setting the band by feel is fast. Building the data infrastructure to back it is slow and exposes uncomfortable findings (e.g., "our 35% band has 15% lower NRR than the 20% band").

**Evidence.** RevOps Co-op playbooks consistently identify "policy designed without retention data" as the #1 cause of margin erosion in years 2-3 post-launch. Bessemer's State of the Cloud benchmarks the gap: policies with retention backing show NRR 8-15 pts higher.

**Countermeasure in skill.** `discount_matrix_builder.py` requires `current_deals[]` as input and emits a `data_backing` block per cell showing `n_observed_deals`, `win_rate`, `nrr_12mo_observed`. Cells with `n < 5` are flagged `THIN`.

**Lint rule.** L08 (`thin_data_in_critical_cell`) — fires for enterprise/strategic cells with thin data.

---

## AP-3: No compensating commitments required for exception discount

**Pattern.** An AE asks for 40% (above the 35% policy max). VP Sales approves via email. No multi-year prepay, no expansion path, no reference commitment, no MSA tightening. The customer banks the discount and gives nothing structural back.

**Why it's seductive.** Asking for commitments slows the deal. At quarter end, the AE and the VP both prefer the path of least resistance.

**Evidence.** Winning by Design (van der Kooij) frames this as the "discount-for-nothing leak": the single highest-leverage place to find margin in a mature GTM. McKinsey B2B pricing studies find that capturing compensating commitments on exceptions alone returns 1-2 pts of margin annually.

**Countermeasure in skill.** `exception_router.py` populates `required_compensating_commitments[]` for any non-in-policy request, scaled by severity (deeper exception → more commitments).

**Lint rule.** L10 (`missing_exception_marker`) — fires when a high-discount cell exists without `exception_required=true`, which would route it through the router.

---

## AP-4: Approver tiers misaligned with margin floor

**Pattern.** Sales Manager is authorized to approve discounts up to a cap that produces margins below the CFO-set floor. The CFO never sees the deal because the chain stops at the manager. By the time the CFO learns about it (in the quarterly margin review), 12 deals are already signed.

**Why it's seductive.** Aligning approver tiers with margin floors requires the CFO, CRO, and Head of Deal Desk to agree on numbers — which is hard.

**Evidence.** Bain's *Pricing Power* research identifies this as the single most common policy defect in mid-market SaaS. The fix is structural: the CFO must own the margin floor; that floor must show up as a per-cell field in the matrix.

**Countermeasure in skill.** `discount_matrix_builder.py` derives `margin_floor_pct` per cell from the input `target_constraints.min_margin_pct`, and surfaces it next to the approver tier.

**Lint rule.** L03 (`margin_floor_below_constraint`) — fires when any cell falls below 50% margin floor.

---

## AP-5: No audit trail for exceptions

**Pattern.** An exception is approved by Slack DM or email. No timestamp, no structured justification, no record of the compensating commitments. Six months later, the customer asks for the same discount at renewal — and no one can find the original commitments.

**Why it's seductive.** Slack and email are faster than CPQ or a structured form. At quarter end, structure feels like friction.

**Evidence.** Salesforce CPQ implementation guides cite this as the #1 reason commercial-policy efforts fail in years 2-3. Forrester's deal-desk maturity model puts "machine-readable audit trail" at the boundary between level 2 (formalized) and level 3 (operationalized).

**Countermeasure in skill.** `exception_router.py` emits a structured `audit_trail` block: `deal_id`, `requested_by`, `submitted_at`, `justification`, `compensating_commitments_required`, `approver_chain`. The block is JSON, so it can be persisted to CPQ or a deal-desk system.

**Lint rule.** None — flow-level, not matrix-level.

---

## AP-6: Cliff edges at round-number ARR thresholds

**Pattern.** Policy says: ARR ≥ $100K → enterprise band (up to 30% discount). ARR < $100K → mid band (up to 22% discount). An AE working a $98K deal pads it to $100K to access the deeper band. Or splits a $105K deal into two $52.5K deals to dodge approval.

**Why it's seductive.** Round-number thresholds are easy to remember and easy to write into policy. The gaming surface is invisible until you look at the deal distribution and notice an unnatural cluster at $100,001.

**Evidence.** MIT Sloan agency-theory literature (Holmström, Gibbons) on multitask gaming. The practical evidence in SaaS: any policy with a hard cliff produces a visible bimodal distribution of deal sizes around the cliff within 2-3 quarters.

**Countermeasure in skill.** Bands in the matrix are smoothed by adjacent strategic-tier bonuses, term bonuses, and payment penalties — so the maximum discount changes gradually rather than cliffing.

**Lint rule.** L05 (`cliff_edge`) — fires when adjacent cells differ by > 10 pts on the discount max.

---

## AP-7: "Strategic value" undefined → catch-all for any discount

**Pattern.** The policy includes a "strategic value" override that allows AEs to exceed the band. "Strategic" is undefined or defined vaguely ("important customer"). Within a quarter, 60% of deals are flagged strategic and the matrix has been rendered meaningless.

**Why it's seductive.** Defining "strategic" with concrete tests requires the GTM leadership team to write down which customers count and which don't — a politically expensive exercise.

**Evidence.** SaaStr (Lemkin) covers this as one of the top-three policy failures. Forrester deal-desk research cites it as the #1 cause of "operationalized" policies sliding back to "formalized."

**Countermeasure in skill.** The matrix has explicit strategic tiers (`standard`, `logo`, `expansion`, `lighthouse`). The user must supply `strategic_value_definitions_supplied=true` plus tests; if not, the lint flags it.

**Lint rule.** L06 (`strategic_value_undefined`) — fires when strategic tiers are used without verifiable definitions.

---

## AP-8: No quarterly policy review based on win-rate data

**Pattern.** The matrix is published, AEs are trained, the policy is declared "live" — and then nobody touches it for 18 months. Meanwhile competitive pricing, customer mix, and product economics shift. The matrix is now wrong in 30-50% of cells, and nobody knows which ones.

**Why it's seductive.** A live policy is a finished policy. Revisiting it implies the previous version was wrong, which is politically awkward.

**Evidence.** OpenView discount-benchmark research shows the disciplined-cohort companies revise their matrix quarterly. The undisciplined cohort revises annually or less, and shows margin drift of -2 to -4 pts per year. RevOps Co-op community studies replicate the finding.

**Countermeasure in skill.** The matrix is a versioned artifact. Each cell's `data_backing` block surfaces the empirical win-rate and NRR; cells where observed NRR < `target_nrr` are flagged `meets_target_nrr=false`, signaling cells due for review.

**Lint rule.** L09 (`cell_unreviewed`) — fires when a cell has zero observed deals (i.e., nobody has tested the band yet).

---

## Synthesis: the 8 anti-patterns and where they're caught

| # | Anti-pattern | Caught by | Lint rule |
|---|---|---|---|
| AP-1 | Precedent sets policy | `exception_router._precedent_risk` | — |
| AP-2 | No data backing | `discount_matrix_builder.data_backing` per cell | L08 |
| AP-3 | No compensating commitments | `exception_router.COMPENSATING_LIBRARY` | L10 |
| AP-4 | Approver/margin misalignment | per-cell `margin_floor_pct` next to approver | L03 |
| AP-5 | No audit trail | `exception_router.audit_trail` JSON block | — |
| AP-6 | Cliff edges | smoothed bands in matrix builder | L05 |
| AP-7 | Strategic value undefined | `strategic_value_definitions_supplied` flag | L06 |
| AP-8 | No quarterly review | `data_backing.n_observed_deals` per cell | L09 |

## Sources (8)

1. OpenView Partners — Annual SaaS Benchmark Survey (2018-2025): https://openviewpartners.com/blog/saas-benchmarks/
2. Tomasz Tunguz — Discount Distribution Studies (Redpoint blog): https://tomtunguz.com/
3. MIT Sloan — Robert Gibbons / Bengt Holmström agency-theory papers: https://mitsloan.mit.edu/faculty/directory/robert-gibbons
4. SaaStr (Jason Lemkin) — Discount Policy + Strategic-Value Posts: https://www.saastr.com/
5. Winning by Design (Jacco van der Kooij) — *Revenue Architecture*: https://winningbydesign.com/
6. Forrester — Deal Desk Maturity Research: https://www.forrester.com/research/
7. RevOps Co-op — Community Policy Design Playbooks: https://www.revopscoop.com/
8. Bain — *Pricing Power* + Discount Discipline Studies: https://www.bain.com/insights/topics/pricing/
