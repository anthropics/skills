# Endpoints and Statistical Power

Reference for endpoint selection and sample-size estimation. Pairs with `endpoint_selector.py` and `sample_size_estimator.py`.

## Endpoint hierarchy

- **Clinical outcome** — directly measures how a patient feels, functions, or survives (mortality, stroke, symptom resolution). Strongest regulatory standing.
- **Surrogate endpoint** — a biomarker intended to substitute for a clinical outcome (LDL cholesterol, viral load, tumor response). Only acceptable if **validated** for the specific indication. FDA maintains a public Surrogate Endpoint Table listing surrogates that have supported approvals; the BEST glossary defines the validation hierarchy (candidate → reasonably likely → validated).
- **Patient-reported outcome (PRO)** — measured directly from the patient via a validated instrument. FDA's 2009 PRO guidance sets the bar for instrument validity, reliability, and content validity.

The tool penalizes an **unvalidated surrogate** so it cannot anchor a PRIMARY endpoint — this mirrors the regulatory reality that an unvalidated surrogate carries approval risk.

## Choosing the effect size (the hardest input)

The single most consequential — and most abused — input is the assumed effect size. It must be **clinically meaningful** and **externally justified**, never reverse-engineered from the n you can afford.

- For **means**, the effect is Cohen's d (standardized mean difference). Cohen's conventional small/medium/large (0.2 / 0.5 / 0.8) are last resorts, not anchors — prefer a published or anchor-based MCID.
- For **proportions**, specify the control and treatment rates from prior data; the absolute difference drives n.
- For **survival**, specify the target hazard ratio; required *events* (not patients) drive power via Schoenfeld's approximation, then n follows from the overall event probability.

## Power formulas the tool implements

- **Two-sample means:** n_per_arm = 2·((z_α + z_β)/d)², adjusted for allocation ratio k.
- **Two-sample proportions:** n = [z_α·√(2·p̄·q̄) + z_β·√(p₁q₁ + p₂q₂)]² / (p₁ − p₂)².
- **Survival (Schoenfeld):** required events E = 4·(z_α + z_β)² / (ln HR)²; n = E / P(event).

All inflate for dropout by 1/(1 − dropout). These are estimates; a biostatistician produces the binding justification, possibly via simulation.

## Sources

1. Cohen, J., *Statistical Power Analysis for the Behavioral Sciences*, 2nd ed. (1988).
2. Schoenfeld, D., *Sample-size formula for the proportional-hazards regression model* — Biometrics 1983;39:499-503.
3. Chow, Shao, Wang & Lokhnygina, *Sample Size Calculations in Clinical Research*, 3rd ed. (CRC, 2017).
4. FDA, *Surrogate Endpoint Resources for Drug and Biologic Development* (public Surrogate Endpoint Table).
5. FDA-NIH BEST (Biomarkers, EndpointS, and other Tools) Resource glossary (2016, updated).
6. FDA, *Patient-Reported Outcome Measures: Use in Medical Product Development* (2009).
7. Fleming & DeMets, *Surrogate end points in clinical trials: are we being misled?* — Ann Intern Med 1996;125:605-613.
