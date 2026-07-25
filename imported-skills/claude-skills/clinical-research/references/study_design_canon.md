# Study Design Canon

Reference knowledge base for prospective clinical study design. Use this when filling the protocol synopsis and defending design choices at a phase gate.

## The estimand-first mindset (ICH E9(R1))

Before choosing an endpoint or a sample size, define the **estimand**: the precise treatment effect the trial will estimate. ICH E9(R1) defines five attributes — population, treatment, endpoint (variable), intercurrent-event handling strategy, and population-level summary. Skipping the estimand is the most common cause of a trial that "succeeds" statistically but answers the wrong question. Intercurrent events (treatment discontinuation, rescue medication, death) must have a pre-specified strategy (treatment-policy, hypothetical, composite, while-on-treatment, principal-stratum).

## Design selection

- **Parallel-group RCT** — the default for confirmatory efficacy. Two or more arms, randomized, concurrent controls.
- **Crossover** — each subject is their own control; only valid for chronic, stable, reversible conditions with adequate washout.
- **Adaptive designs** — pre-planned modifications (sample-size re-estimation, arm dropping, seamless phase 2/3). Powerful but require simulation and regulatory pre-agreement (FDA Adaptive Designs guidance, 2019).
- **Single-arm** — only defensible with a well-characterized natural history / external control, common in rare disease and oncology early phases.

## Randomization & blinding

Randomization removes selection bias; stratify on strong prognostic factors (and always on site in multicenter trials). Blinding (single / double / triple) removes ascertainment and analysis bias. Document the unblinding plan and the DSMB charter for any interim looks.

## Multiplicity

Any trial with more than one primary endpoint, more than two arms, or interim analyses inflates the family-wise type-I error. Pre-specify the control strategy: hierarchical (fixed-sequence) testing, Bonferroni / Holm, or a graphical (Bretz-Maurer) approach. The FDA Multiple Endpoints guidance (2022) is the operative reference.

## Reporting standards as design checklists

CONSORT 2010 (parallel-group RCT reporting) and SPIRIT 2013 (protocol content) are reporting standards — but used proactively they are design checklists. If you cannot fill a SPIRIT item, the design has a gap.

## Sources

1. ICH E8(R1), *General Considerations for Clinical Studies* (2021) — quality-by-design, fit-for-purpose study design.
2. ICH E9, *Statistical Principles for Clinical Trials* (1998) and the **E9(R1) Addendum on Estimands and Sensitivity Analysis** (2019).
3. Schulz, Altman & Moher, *CONSORT 2010 Statement* — BMJ 2010;340:c332.
4. Chan et al., *SPIRIT 2013 Statement: defining standard protocol items for clinical trials* — Ann Intern Med 2013;158:200-207.
5. FDA, *Multiple Endpoints in Clinical Trials: Guidance for Industry* (2022).
6. FDA, *Adaptive Designs for Clinical Trials of Drugs and Biologics* (2019).
7. Friedman, Furberg, DeMets, *Fundamentals of Clinical Trials*, 5th ed. (Springer, 2015).
