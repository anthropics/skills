# materials-doe

**Version:** v1.1.0

**What it does** — Design-of-experiments planning and matrix generation for
materials science and engineering research. Supports six design
modes: classical DOE, orthogonal array/Taguchi methods, mix design, factor
screening (Plackett-Burman, fractional factorial), response surface methodology
(CCD, BBD), and mixture design (Simplex lattice, Simplex centroid, extreme
vertices). Use it when the user needs an experimental matrix, factor screening
plan, orthogonal array, mixture design, response surface plan, or guidance on
sample size and replication for materials testing. The skill plans experiments
and emits structured matrices; it does not execute tests, analyze collected
data, or produce manuscript text.

**Built from** — Six design-mode cores plus a domain experiment library:

- `static/core/classical-doe.md` — full factorial, OFAT, sample size,
  replication, randomization
- `static/core/orthogonal-tables.md` — Taguchi L9/L16/L25 arrays, S/N ratio,
  range and ANOVA analysis guidance
- `static/core/mix-design-guide.md` — mix proportion design, D-optimal, component
  bounds and constraints for multi-component systems
- `static/core/screening-designs.md` — Plackett-Burman design, fractional
  factorial design (2^(k-p)), resolution levels, factor screening
- `static/core/response-surface.md` — response surface methodology (RSM),
  central composite design (CCD), Box-Behnken design (BBD), optimization
- `static/core/mixture-design.md` — Simplex lattice, Simplex centroid,
  extreme vertices, mixture design for formulation optimization
- `static/reference/` — 8 domain experiment references (asphalt,
  cement-concrete, polymers, metals, ceramics, functional, nano, insulation)
  plus a factor-level template and DOE figure-package routing
- `scripts/` — 3 helpers: `orthogonal_analysis.py`, `mix_design_calc.py`,
  `experiment_plot.py`
- `assets/templates/` — analysis script, experiment plan CSV, and methods
  paragraph templates

**Supported design modes** — Six design modes covering the full DOE workflow:

1. **经典 DOE (Classical DOE)** — Full factorial, OFAT (one-factor-at-a-time),
   sample size determination, replication, randomization
2. **正交表/田口方法 (Orthogonal Array / Taguchi)** — Taguchi L9/L16/L25
   arrays, signal-to-noise (S/N) ratio, range analysis, ANOVA guidance
3. **配合比设计 (Mix Design)** — Mix proportion design, D-optimal, component
   bounds and constraints for multi-component systems
4. **筛选设计 (Screening Design)** — Plackett-Burman design, fractional
   factorial design (2^(k-p)), resolution levels, factor screening
5. **响应面法 (Response Surface Methodology)** — RSM, central composite
   design (CCD), Box-Behnken design (BBD), optimization
6. **混料设计 (Mixture Design)** — Simplex lattice, Simplex centroid,
   extreme vertices, formulation optimization

**Outputs** — Factor-level matrices, analysis strategy notes, and a structured
handoff for downstream skills:

| Output | Description |
|---|---|
| Test matrix | Factor-level table in CSV or markdown |
| Analysis strategy | Notes on ANOVA, S/N ratio, or RSM approach |
| DOE handoff | Structured handoff for downstream skills |

**Usage examples** — Typical requests the skill handles:

- "Design an L9 orthogonal array for asphalt modifier dosage, curing time, and temperature"
- "Generate a mix design matrix for three-component mortar system"
- "Plan a factorial experiment for concrete durability factors"

**Key rules enforced**

- Plans experiments and generates matrices only; never executes tests or
  analyzes collected data.
- Loads only the selected design, material, domain, output, and output-format
  routes; resolved files are applied once.
- Loads companion skills only for an explicit handoff. Static route budgets in
  `evals/context-routes.yaml` cover standalone and multi-skill workflows.
- Factor list and level count must be confirmed before generating any matrix
  (blocking gate).
- Design mode (classical, orthogonal, mix-design, screening, response-surface,
  mixture-design) must be resolved before loading mode-specific references.
- Claims about optimality or statistical power must be backed by the chosen
  design's properties.
- For data analysis or figure production, hand off to `materials-data` or
  `materials-figure` instead of doing it here.

**Reference files**

```text
skills/materials-doe/
├── README.md
├── SKILL.md
├── manifest.yaml
├── scripts/
│   ├── orthogonal_analysis.py    Taguchi S/N ratio and range analysis
│   ├── mix_design_calc.py        mixture/simplex matrix calculator
│   └── experiment_plot.py        DOE matrix and response plotting
├── assets/
│   └── templates/
│       ├── analysis-script-template.py   ANOVA/regression analysis scaffold
│       ├── experiment-plan-template.csv  factor-level matrix template
│       └── methods-paragraph-template.md methods section paragraph template
└── static/
    ├── core/
    │   ├── classical-doe.md       classical factorial, OFAT, sample size
    │   ├── orthogonal-tables.md   Taguchi arrays and S/N analysis
    │   ├── mix-design-guide.md    mix proportion design, D-optimal
    │   ├── screening-designs.md   Plackett-Burman, fractional factorial
    │   ├── response-surface.md    RSM, CCD, Box-Behnken design
    │   ├── mixture-design.md      Simplex lattice/centroid, extreme vertices
    │   ├── contract.md            evidence contract
    │   ├── stance.md              skill stance
    │   └── workflow.md            planning workflow
    └── reference/
        ├── asphalt-experiments.md       asphalt/binder experiment factors
        ├── cement-experiments.md         cement/concrete/mortar factors
        ├── polymers-experiments.md       polymer/composite factors
        ├── metals-experiments.md         metal/alloy factors
        ├── ceramics-experiments.md       ceramic sintering factors
        ├── functional-experiments.md     functional/dielectric factors
        ├── nano-experiments.md           nanoparticle/2D material factors
        ├── insulation-experiments.md     insulation material factors
        ├── factor-level-template.md      factor-level matrix template
        └── doe-figure-package.md         DOE figure-package routing
```

**Validation**

- Bundle verification: `python .\scripts\run_release_checks.py --json`
- Focused route-budget check:
  `python .\scripts\check_skill_architecture.py --skill materials-doe --json`
