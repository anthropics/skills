# DOE Skill Contract

This contract defines the output handoff fields and quality gates for the materials-doe skill.

## Promises

- Produce experiment plans, factor tables, and analysis scripts that follow DOE best practice.
- Select the design from factor count, objective, interaction risk, and constraint type.
- Keep all statistical claims tied to data, formulas, or standard procedures.
- Produce handoff-ready outputs when another `materials-*` skill is the better continuation point.

## Refusals

- Do not invent experimental data, factor levels, or statistical significance.
- Do not silently skip replications or interaction effects without stating the assumption.
- Do not recommend a design mode without checking the user's factor count and constraint type.
- Do not treat engineering mix proportioning as a statistical mixture design.
- Use `[needs data: ...]` for unresolved inputs instead of assuming values.

## Handoff Fields

| Field | Description | Format |
|---|---|---|
| `experiment_plan` | Full experiment layout: factor-level table, run order, replication strategy | Markdown table or CSV |
| `design_mode` | One of: `classical`, `orthogonal`, `screening`, `response-surface`, `mix-design`, `mixture-design` | Enum string |
| `factors` | Factor names, levels, units, and ranges | Markdown table |
| `analysis_script` | Python script for range analysis, ANOVA, or mix calculation | `.py` file |
| `methods_paragraph` | Draft methods text describing the DOE procedure | Markdown paragraph |
| `figure_script` | Python script for main-effect plots, interaction plots, or mix charts | `.py` file |
| `data_template` | Empty CSV template with correct column headers for data entry | `.csv` file |
| `optimal_combination` | Predicted optimal factor-level combination and expected response | Markdown summary |

## Quality Gates

Before handing off to a downstream skill, verify:

1. **Factor completeness** — every factor has a name, unit, and at least two levels.
2. **Orthogonality** — for orthogonal designs, the array is a standard L9/L16/L25 or equivalent.
3. **Replication plan** — at least one replicate per run is recommended; if omitted, state the assumption.
4. **Analysis match** — the analysis method matches the design mode (range analysis for orthogonal, ANOVA for classical, domain formula for mix design).
5. **Control group** — classical designs include a baseline/control treatment.
6. **Mix design constraints** — for mix design mode, target strength, slump, and durability requirements are specified.
7. **Script reproducibility** — analysis and figure scripts run without modification on the data template.

## Handoff Routing

| Downstream skill | Trigger |
|---|---|
| `materials-data` | When the experiment plan needs a FAIR-compliant data package |
| `materials-figure` | When main-effect or interaction plots are needed |
| `materials-writing` | When a methods paragraph or results section is needed |
| `materials-polishing` | When the methods paragraph needs English refinement |
