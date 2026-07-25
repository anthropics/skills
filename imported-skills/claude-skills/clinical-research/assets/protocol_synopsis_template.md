# Protocol Synopsis — Template

> Fill this before running the tools. This is a synopsis, not a full protocol. Every section
> ends in a named owner who must sign. Output of this skill is an ESTIMATE — a biostatistician,
> medical monitor, and regulatory owner sign the final protocol.

## 1. Study identification
- Study ID:
- Sponsor / department:
- Phase: [1 | 2 | 3 | 4]
- Development area / profile: [drug | device | biologic | diagnostic | digital-therapeutic]

## 2. Objectives
- Primary objective:
- Secondary objective(s):
- Estimand (population, treatment, endpoint, intercurrent-event strategy, summary measure):

## 3. Design
- Type: [parallel-group RCT | crossover | adaptive | single-arm]
- Arms & allocation ratio:
- Randomization & stratification factors:
- Blinding:

## 4. Population
- Indication:
- Key inclusion criteria:
- Key exclusion criteria:
- Estimated eligible population:
- Number of sites / countries:

## 5. Endpoints
| Endpoint | Type (clinical / surrogate / PRO) | Validated? | Proposed class (PRIMARY / KEY-SECONDARY / EXPLORATORY) |
|---|---|---|---|
|  |  |  |  |

- Multiplicity control (if >1 primary):

## 6. Statistical plan (placeholder — biostatistician owns the final)
- Design for sample size: [means | proportions | survival]
- Assumed effect size / difference / HR + **source citation**:
- alpha (two-sided): ___   power: ___   dropout: ___
- Estimated n (from `sample_size_estimator.py`):

## 7. Feasibility & budget
- Target enrollment / enrollment months:
- Visits per patient / invasive procedures:
- Planned budget (USD):
- Phase-gate verdict (from `phase_gate_scorer.py`):

## 8. Owners to sign (named, not roles)
- Principal Investigator:
- Medical Monitor:
- Biostatistician:
- Regulatory Owner:

## 9. Assumptions register
- (List every assumption behind the effect size, dropout, eligible pool, and budget. Each must trace to a source or be flagged as an unverified planning assumption.)
