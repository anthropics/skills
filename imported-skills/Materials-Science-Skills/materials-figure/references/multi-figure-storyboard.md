# Multi-Figure Storyboard Guide

This reference explains how to orchestrate multiple figures within a single manuscript using the storyboard gate. The storyboard prevents a set of individually-valid figures that are narratively incoherent or mutually redundant — a common failure mode in materials-science manuscripts where each figure is defensible on its own but the set as a whole does not build a coherent argument.

**Scope**: This template orchestrates FIGURES within a manuscript (fig1, fig2, ...). It is distinct from the single-figure multi-panel storyboard (`assets/templates/figure_storyboard.yaml`) which orders PANELS within one figure (A, B, C, D). The two compose: each figure listed here may itself use the panel-level storyboard internally.

---

## 1. Storyboard Structure

The storyboard lives at `assets/templates/figure-storyboard/figure_storyboard.yaml` (or a copy in your working directory). It contains four sections:

### 1.1 Manuscript Metadata

```yaml
title: "Manuscript title here"
manuscript_type: "research"   # research | review | case-study
target_journal: "cbm"         # must match a preset in figure-style-presets.yaml
```

- **title**: Free text; used in validation reports.
- **manuscript_type**: Drives which roles are required (see §3).
- **target_journal**: Must match a preset key in `assets/templates/figure-style-presets.yaml` so the `style_consistency` constraint can resolve the shared palette.

### 1.2 Narrative Arc

```yaml
narrative_arc:
  - figure_id: "fig1"
    figure_name: "system_setup"
    role: "establish_system"
    claim: "The emulsion system achieves a stable bonding interface."
    contract_path: "fig1/figure_contract.md"
    evidence_depends_on: []

  - figure_id: "fig2"
    figure_name: "mechanism"
    role: "prove_mechanism"
    claim: "FTIR and rheology evidence link the dosage window to a cross-linking mechanism."
    contract_path: "fig2/figure_contract.md"
    evidence_depends_on: ["fig1"]
```

Each figure entry contains:
- **figure_id**: Short stable identifier used by `evidence_depends_on`.
- **figure_name**: Human-readable name (also matched inside contract text).
- **role**: Narrative role (see §2 for the complete enum).
- **claim**: One-sentence core claim this figure must defend.
- **contract_path**: Path to this figure's `figure_contract.md` (relative to the storyboard file).
- **evidence_depends_on**: List of `figure_id`s whose evidence this figure builds on. Must form a DAG (no cycles).

### 1.3 Cross-Figure Constraints

```yaml
cross_figure_constraints:
  - type: "style_consistency"
    shared_palette: "cbm"
    shared_fonts: true
    shared_rcparams: true
    description: "All figures share the cbm color palette and font stack."

  - type: "evidence_flow"
    rule: "Later figures' evidence chains must cite earlier figures' claims."

  - type: "no_redundancy"
    rule: "No two figures show the same data panel."

  - type: "claim_progression"
    rule: "Later figures' claims must build on earlier figures' evidence."

  - type: "role_coverage"
    rule: "Manuscript type determines which roles must appear."

  - type: "acyclic_dependency"
    rule: "evidence_depends_on must form a directed acyclic graph."
```

### 1.4 Validation Rules

```yaml
validation:
  required_roles_research: ["establish_system", "prove_mechanism", "show_performance"]
  required_roles_review: ["establish_system", "summarize"]
  required_roles_case_study: ["establish_system", "show_performance"]
  min_figures: 1
  max_figures: 12
  allow_cycles: false
```

---

## 2. Narrative Roles

The complete role enum:

| Role | Purpose | When to use |
|---|---|---|
| `establish_system` | Introduce the material/system/setup | First figure in any manuscript |
| `prove_mechanism` | Defend the underlying mechanism | Research articles with mechanism claims |
| `show_performance` | Report performance metrics | Any manuscript with quantitative results |
| `validate_durability` | Show performance persists over time/conditions | Durability-focused studies |
| `summarize` | Synthesize findings or trade-offs | Last figure in review/case-study |
| `compare` | Compare systems/conditions side by side | Comparative studies |
| `method_development` | Present a new method or protocol | Method papers |

### 2.1 Role Coverage by Manuscript Type

- **research**: Must include `establish_system` → `prove_mechanism` → `show_performance`
- **review**: Must include `establish_system` → `summarize`
- **case-study**: Must include `establish_system` → `show_performance`

Missing required roles trigger a **warning** in the storyboard check.

---

## 3. Evidence Dependencies

Each figure declares which earlier figures its evidence builds on via `evidence_depends_on`. This creates a directed graph that must be **acyclic** (a DAG).

### 3.1 Why Dependencies Matter

Dependencies enforce **evidence flow**: later figures must cite earlier claims, not repeat them. A figure that claims "bond strength improves" without referencing the mechanism figure's evidence is making an unsupported assertion.

### 3.2 Common Dependency Patterns

**Linear progression** (most common):
```yaml
fig1 (establish_system) -> fig2 (prove_mechanism) -> fig3 (show_performance) -> fig4 (validate_durability)
```

**Branching** (when multiple mechanisms or performance metrics):
```yaml
fig1 (establish_system) -> fig2 (prove_mechanism_A)
                        -> fig3 (prove_mechanism_B)
fig2 + fig3 -> fig4 (show_performance)
```

**Parallel comparison** (when comparing two systems):
```yaml
fig1 (establish_system_A) -> fig2 (show_performance_A)
fig3 (establish_system_B) -> fig4 (show_performance_B)
fig2 + fig4 -> fig5 (compare)
```

### 3.3 Cycle Detection

A cycle occurs when a figure (directly or transitively) depends on itself:

```yaml
# BAD: fig2 depends on fig3, which depends on fig2
fig2: evidence_depends_on: [fig3]
fig3: evidence_depends_on: [fig2]
```

Cycles are **errors** by default (`allow_cycles: false`). They indicate circular reasoning in the narrative.

---

## 4. Cross-Figure Constraints

### 4.1 Style Consistency

All figures must share:
- Color palette (resolved from `target_journal` in `figure-style-presets.yaml`)
- Font stack (set via `apply_publication_style()`)
- rcParams (axes linewidth, legend frameon, spine visibility)

The `shared_palette` field must match a key in `figure-style-presets.yaml`.

### 4.2 Evidence Flow

Later figures' evidence chains must cite earlier figures' claims. The validator checks that each figure's `figure_contract.md` mentions the `figure_id` or `figure_name` of its dependencies.

### 4.3 No Redundancy

No two figures may show the same data panel. The validator extracts (evidence source, source anchor) fingerprints from each contract's Evidence Chain table and flags duplicates.

**Placeholder handling**: Anchors containing "example", "template", "placeholder", "tbd", or "n/a" are skipped to avoid false positives on templates.

### 4.4 Claim Progression

Later figures' claims must build on earlier figures' evidence, not repeat them. This is a qualitative check — the validator ensures claims are non-empty and non-placeholder, but the narrative progression is ultimately a human judgment.

### 4.5 Role Coverage

The manuscript type determines which roles must appear (see §2.1). Missing roles trigger a warning.

### 4.6 Acyclic Dependency

The `evidence_depends_on` graph must be a DAG. Cycles are errors by default.

---

## 5. Running the Storyboard Check

### 5.1 Basic Usage

```bash
# Basic validation
python scripts/check_storyboard.py figure_storyboard.yaml

# JSON output for programmatic processing
python scripts/check_storyboard.py figure_storyboard.yaml --json
```

**Exit codes**:
- `0` = pass
- `1` = warning
- `2` = error

### 5.2 Validation Checks

The script runs 10 checks:

| Check | Severity | What it validates |
|---|---|---|
| `narrative_completeness` | error | All required fields present in each figure entry |
| `figure_count` | error | Number of figures within [min, max] bounds |
| `role_validity` | error | All roles are in the valid enum |
| `role_coverage` | warning | Required roles for manuscript type are present |
| `dependency_targets_exist` | error | All `evidence_depends_on` targets exist in the arc |
| `acyclic_dependency` | error/warning | Dependencies form a DAG (severity depends on `allow_cycles`) |
| `claim_nonempty` | error/warning | All claims are non-empty and non-placeholder |
| `contract_evidence_linkage` | warning | Each contract references its declared dependencies |
| `no_redundancy` | warning | No duplicated panel data sources across figures |
| `style_consistency` | warning | `style_consistency` constraint declares a `shared_palette` |

### 5.3 Example Output

```
STATUS: PASS
  [PASS   ] narrative_completeness: 4 figures in narrative arc, all required fields present
  [PASS   ] figure_count: 4 figures within [1, 12]
  [PASS   ] role_validity: all roles are valid
  [PASS   ] role_coverage: research manuscript covers required roles: establish_system, prove_mechanism, show_performance
  [PASS   ] dependency_targets_exist: all evidence_depends_on targets exist in narrative_arc
  [PASS   ] acyclic_dependency: evidence dependencies form a DAG
  [PASS   ] claim_nonempty: all figure claims are non-empty and non-placeholder
  [PASS   ] contract_evidence_linkage: 4 contract(s) reference their declared dependencies
  [PASS   ] no_redundancy: 4 contract(s) checked; no duplicated panel data sources
  [PASS   ] style_consistency: style_consistency declared with shared_palette='cbm'
```

---

## 6. Storyboard Workflow

### 6.1 When to Write the Storyboard

Write the storyboard **before** individual figure contracts when:
- The manuscript has 2+ figures
- The figures are meant to build a cumulative argument
- You want to prevent narrative gaps or redundancy

### 6.2 Step-by-Step Workflow

```
1. Draft figure_storyboard.yaml
   - Define manuscript_type, target_journal
   - List figures in narrative order
   - Assign roles, claims, and dependencies

2. Run check_storyboard.py
   - Fix errors (missing fields, invalid roles, cycles)
   - Address warnings (missing roles, placeholder claims)

3. Write individual figure_contract.md files
   - Each contract must reference its dependencies
   - Each contract's evidence chain must not duplicate other figures' panels

4. Run validate_materials_claims.py on each contract
   - Fix XRD/FTIR/performance errors
   - Address warnings

5. Plot figures
   - Apply shared palette and style from target_journal preset
   - Ensure cross-figure consistency

6. Final storyboard check
   - Re-run check_storyboard.py to confirm all checks pass
```

### 6.3 Iterating on the Storyboard

The storyboard is a living document. As you write contracts and plot figures, you may discover:
- A figure needs to be split into two
- Two figures are redundant and should merge
- The narrative order needs adjustment
- A dependency is missing or incorrect

Update the storyboard and re-run the check after each change.

---

## 7. Example: Research Article Storyboard

```yaml
title: "WER-EA Modified Emulsified Asphalt: Bonding Mechanism and Performance"
manuscript_type: "research"
target_journal: "cbm"

narrative_arc:
  - figure_id: "fig1"
    figure_name: "system_setup"
    role: "establish_system"
    claim: "The WER-EA emulsion achieves a stable bonding interface across the 5-8 wt% dosage window."
    contract_path: "fig1/figure_contract.md"
    evidence_depends_on: []

  - figure_id: "fig2"
    figure_name: "mechanism"
    role: "prove_mechanism"
    claim: "FTIR oxirane ring disappearance and rheology crossover link the dosage window to epoxy cross-linking."
    contract_path: "fig2/figure_contract.md"
    evidence_depends_on: ["fig1"]

  - figure_id: "fig3"
    figure_name: "performance"
    role: "show_performance"
    claim: "Bond strength peaks at 1.2 MPa at 6 wt% WER-EA, attributed to the fig2 mechanism."
    contract_path: "fig3/figure_contract.md"
    evidence_depends_on: ["fig2"]

  - figure_id: "fig4"
    figure_name: "durability"
    role: "validate_durability"
    claim: "Moisture aging retention >85% validates that the fig3 performance persists under environmental conditioning."
    contract_path: "fig4/figure_contract.md"
    evidence_depends_on: ["fig3"]

cross_figure_constraints:
  - type: "style_consistency"
    shared_palette: "cbm"
    shared_fonts: true
    shared_rcparams: true
    description: "All figures share the cbm color palette and font stack."

  - type: "evidence_flow"
    rule: "Later figures' evidence chains must cite earlier figures' claims."
    description: "fig2 references fig1; fig3 references fig2; fig4 references fig3."

  - type: "no_redundancy"
    rule: "No two figures show the same data panel."
    description: "Cross-check panel data sources across figures."

  - type: "claim_progression"
    rule: "Later figures' claims must build on earlier figures' evidence."
    description: "The narrative arc shows progression: system -> mechanism -> performance -> durability."

  - type: "role_coverage"
    rule: "Research manuscripts require establish_system, prove_mechanism, show_performance."
    description: "All three required roles are present."

  - type: "acyclic_dependency"
    rule: "evidence_depends_on must form a DAG."
    description: "fig1 -> fig2 -> fig3 -> fig4 is a linear chain with no cycles."

validation:
  required_roles_research: ["establish_system", "prove_mechanism", "show_performance"]
  required_roles_review: ["establish_system", "summarize"]
  required_roles_case_study: ["establish_system", "show_performance"]
  min_figures: 1
  max_figures: 12
  allow_cycles: false
```

---

## 8. Example: Review Article Storyboard

```yaml
title: "Construction Materials Durability: A Review"
manuscript_type: "review"
target_journal: "ccc"

narrative_arc:
  - figure_id: "fig1"
    figure_name: "taxonomy"
    role: "establish_system"
    claim: "Durability mechanisms fall into four categories: chemical, mechanical, thermal, and environmental."
    contract_path: "fig1/figure_contract.md"
    evidence_depends_on: []

  - figure_id: "fig2"
    figure_name: "evidence_map"
    role: "summarize"
    claim: "The evidence heatmap shows that chemical degradation (chloride, sulfate) dominates the literature, while thermal fatigue is under-studied."
    contract_path: "fig2/figure_contract.md"
    evidence_depends_on: ["fig1"]

cross_figure_constraints:
  - type: "style_consistency"
    shared_palette: "ccc"
    description: "All figures share the ccc color palette."

  - type: "no_redundancy"
    rule: "No two figures show the same data panel."

validation:
  required_roles_research: ["establish_system", "prove_mechanism", "show_performance"]
  required_roles_review: ["establish_system", "summarize"]
  required_roles_case_study: ["establish_system", "show_performance"]
  min_figures: 1
  max_figures: 12
  allow_cycles: false
```

---

## 9. Common Pitfalls

### 9.1 Missing Dependencies

**Problem**: fig3 claims "performance improves due to mechanism" but does not list fig2 in `evidence_depends_on`.

**Fix**: Add fig2 to fig3's dependencies and ensure fig3's contract references fig2's claim.

### 9.2 Redundant Panels

**Problem**: fig2 and fig3 both show the same FTIR spectrum from the same data source.

**Fix**: Remove the duplicate panel from one figure, or clarify that they show different aspects (e.g., fig2 shows the full spectrum, fig3 shows the oxirane region zoom).

### 9.3 Placeholder Claims

**Problem**: A figure's claim is "TBD" or "placeholder".

**Fix**: Write the actual claim. Placeholder claims indicate the figure is not ready for production.

### 9.4 Cycle in Dependencies

**Problem**: fig2 depends on fig3, which depends on fig2.

**Fix**: Break the cycle by reordering the narrative or removing a dependency. Cycles indicate circular reasoning.

### 9.5 Style Inconsistency

**Problem**: fig1 uses the `cbm` palette, fig2 uses `nature_material`.

**Fix**: Set `shared_palette` in the `style_consistency` constraint and apply it to all figures.

---

## 10. Integration with Materials Validation

The storyboard check validates **narrative structure**; the materials validation (`validate_materials_claims.py`) validates **scientific claims**. Use both together:

```bash
# Check storyboard structure
python scripts/check_storyboard.py figure_storyboard.yaml

# Validate each figure's materials claims
for fig_dir in fig1 fig2 fig3 fig4; do
    python scripts/validate_materials_claims.py $fig_dir
done
```

A manuscript passes when:
- Storyboard check returns `pass` (or `warning` with addressed warnings)
- All figure contracts return `pass` or `warning` (no errors)

---

## 11. Best Practices

1. **Write the storyboard first**: Before writing any figure contract, draft the storyboard to establish the narrative arc.

2. **Keep claims specific**: Each figure's claim should be a single sentence that the figure's evidence can defend. Avoid vague claims like "the material performs well".

3. **Make dependencies explicit**: If a figure's claim builds on another figure's evidence, list it in `evidence_depends_on`. This enforces evidence flow.

4. **Check for redundancy early**: Before plotting, verify that no two figures show the same data panel. Redundancy is easier to prevent than to fix.

5. **Iterate**: The storyboard is a living document. Update it as you write contracts and plot figures.

6. **Combine with materials validation**: For figures with XRD/FTIR/performance claims, run both the storyboard check and the materials validator.

---

## Related files

- [SKILL.md](../SKILL.md) — When to use this skill
- [contract.md](../static/core/contract.md) — The eight-point figure contract
- [figure_storyboard.yaml](../assets/templates/figure-storyboard/figure_storyboard.yaml) — Storyboard template
- [check_storyboard.py](../scripts/check_storyboard.py) — Storyboard validation script
- [materials-validation.md](materials-validation.md) — Materials knowledge validation
- [figure-package-protocol.md](figure-package-protocol.md) — Complete figure package workflow
