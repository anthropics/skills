# Materials Science Pressure Test Suite

Use this reference when validating whether the materials skill bundle is behaving safely across modules.

## Coverage

The suite covers these modules:

- materials-research
- materials-reader
- materials-citation
- materials-polishing
- materials-response
- materials-html-deck
- materials-figure
- materials-data

## Pressure Themes

The suite intentionally includes more than three failure classes:

- overclaim from performance to mechanism
- fake citation, DOI, impact factor, or citation count
- journal mismatch across CBM, CCC, RMPD/IJPE, and JBE
- missing experimental conditions
- literal translation and claim-strength drift
- weak novelty and uncited gaps
- figure caption overinterpretation
- HTML deck missing data fabrication
- FAIR data availability overclaim
- reviewer response defensiveness
- statistics, replicate, and unit omissions
- scope creep and companion-module overuse

## Audit Command

```powershell
python scripts/audit_pressure_assets.py --skill-root "$CODEX_HOME/skills/materials-research" --json
```

The audit should report `status: pass`, at least 12 pressure tests, at least 10 example files, all required modules covered, and no missing themes.

## Use In Practice

Before declaring the materials bundle improved, run the audit and read the pressure scenario closest to the requested output. If the output violates any `Failure Signs`, revise the skill, reference, script, or example before treating the behavior as safe.


### Ceramics

| File | Theme |
|---|---|
| ceramics-overclaim-strength.md | Overclaiming mechanical properties without Weibull statistics |

### Thermal Insulation

| File | Theme |
|---|---|
| insulation-missing-standard.md | Reporting conductivity without standard or mean temperature |
