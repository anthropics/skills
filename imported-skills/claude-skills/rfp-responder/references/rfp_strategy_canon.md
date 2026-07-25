# RFP Strategy Canon — Industry Research on RFP Win-Rates and Buyer Behavior

This reference grounds the `winrate_predictor.py` factor weights in published industry research. The model is opinionated but defensible: every factor maps to a citation below.

## Headline findings the skill encodes

### Base win-rates are honestly grim

- Average competitive B2B RFP win-rate: 15-25% across industries (Bain, Gartner).
- With disciplined bid/no-bid qualification: 35-45%.
- Without qualification: 5-12% — sales-engineering capacity burned on unwinnable pursuits.

The skill's 20% NO-BID threshold is calibrated to land below the disciplined-pursuit floor.

### Incumbents win renewal RFPs 70-80% of the time

Absent a named failure event (security breach, missed SLA, executive turnover at the incumbent), incumbents win 70-80% of renewal RFPs (Forrester B2B-RFP research). This is the empirical basis for the −30% incumbent penalty when incumbent_advantage is "strong."

### Late entry is structurally penalized

If you weren't part of the conversation before the RFP issued, the RFP was scoped to someone else's strengths. Forrester data: late-entry vendors win 8-12% of RFPs vs 25-35% for vendors who engaged in capture. The skill's −15% late-entry penalty is the midpoint of this gap.

### Relationship strength dominates content quality at the margin

Bain: in deals where the named champion advocates internally, win-rate lifts 20-30 percentage points over the "warm but no champion" baseline. The skill's +25% champion factor is the lower bound of this range.

### Decision-criteria alignment is bimodal

When buyer decision criteria align >80% with your strengths, win-rate is roughly 2x the base rate. When alignment is <50%, win-rate collapses to ~30% of base (McKinsey B2B sales research). The skill encodes this as a +10 / 0 / −10 step function rather than a continuous curve, because the bimodality is the honest reality.

### Competitor count compresses win-rate predictably

- 1 competitor (sole-source consideration): 60-80% win-rate
- 2 competitors: 35-50%
- 3 competitors: 20-30%
- 4-5 competitors: 12-18%
- 6+ competitors: 5-10%

The skill's competitor-count factor (+20 / +5 / 0 / -10 / -20) tracks this curve.

## Industry profile tuning

The skill exposes 5 profiles via `--profile`. Each shifts the base rate:

- **enterprise-software (+5)**: longer sales cycles, deeper technical evaluation, but disciplined buyers reward fit-honest vendors. Base rate slightly above average.
- **saas (0)**: market baseline.
- **services (−5)**: commoditized for many engagement types, weaker differentiation moats, harder to defend price.
- **government (−15)**: FAR-governed, compliance-heavy, incumbent-favored, evaluation timelines extend 2-4x. Forrester / GSA data.
- **healthcare (−10)**: regulatory overhead (HIPAA, FDA, HITRUST), risk-averse procurement, longer pilot cycles. Gartner healthcare-vertical research.

## What this skill deliberately does NOT model

- **Pricing positioning** — outside scope; consume from `commercial/pricing-strategist`.
- **Proposal aesthetics / production quality** — Shipley canon says these matter at the margin (3-5 percentage points) but never override fit, win-themes, and relationship. Skill omits.
- **Evaluator psychology** — Strategic Proposals research shows evaluators score on the rubric they were given. The skill assumes the rubric is the source of truth; theme-injection happens within rubric constraints.

## Sources

1. **Federal Acquisition Regulation (FAR)**, especially Parts 14 (Sealed Bidding) and 15 (Contracting by Negotiation), at acquisition.gov/far. Governs US federal RFPs. Defines the compliance-matrix requirement, evaluation-factor disclosure rules, and proposal-format constraints that drive the "government" profile penalty.

2. **GSA (General Services Administration) RFP and procurement guidance**, at gsa.gov. Quantifies federal evaluation timelines (typically 90-180 days) and the disproportionate weight federal evaluators give to past-performance citations — relevant to proof-point substantiation discipline.

3. **Forrester Research, B2B Buyer Studies** — recurring annual research on B2B buying behavior. Sources the 70-80% incumbent renewal-win-rate, the late-entry penalty, and the "5-10 vendor longlist" reality of modern RFP processes.

4. **Gartner, RFP Best Practices** — published guidance for IT-buyer organizations. Quantifies vendor-shortlist sizes by deal value, evaluation-cycle length by industry, and the structural advantage of fit-honest responses over feature-checklist responses.

5. **Bain & Company, B2B Sales and RFP-Win-Rate Research** — Bain's commercial-discipline practice publishes regular benchmarks on disciplined-pursuit win-rates (35-45%) vs respond-to-everything win-rates (5-12%). The 20% NO-BID threshold in `winrate_predictor.py` is calibrated against this data.

6. **McKinsey & Company, B2B Sales Practice** — McKinsey research on decision-criteria alignment and win-rate. Sources the bimodal alignment effect (>80% alignment doubles base rate; <50% collapses to 30% of base) encoded in `alignment_factor()`.

7. **B2B International (now Kantar B2B), Buyer Behavior in RFP Processes** — research on how B2B evaluation committees actually score responses. Confirms that compliance-matrix presence, proof-point substantiation, and rubric-aligned response structure are the top-3 evaluator-cited differentiators.

8. **Patrick Lencioni, *Getting Naked: A Business Fable About Shedding the Three Fears That Sabotage Client Loyalty*** (Jossey-Bass, 2010). The "we don't have a proof point for this — here's what we'd do instead" honesty discipline that informs the skill's hard rule: surface GAPs, never invent. Lencioni's "tell the kind truth" principle operationalized as a refusal to fabricate evidence.
