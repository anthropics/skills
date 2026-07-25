# Factor-Level Definition Template

Standard template and guidance for defining factors and levels in civil engineering materials experiments.

## Template

| Factor | Unit | Level 1 | Level 2 | Level 3 | Level 4 | Level 5 |
|--------|------|---------|---------|---------|---------|---------|
| Factor A | — | — | — | — | — | — |
| Factor B | — | — | — | — | — | — |
| Factor C | — | — | — | — | — | — |
| Factor D | — | — | — | — | — | — |

## Example: Waterborne Epoxy Modified Emulsified Asphalt

| Factor | Unit | Level 1 | Level 2 | Level 3 | Level 4 | Level 5 |
|--------|------|---------|---------|---------|---------|---------|
| Epoxy content | % | 5 | 10 | 15 | 20 | 25 |
| Curing temperature | °C | 25 | 40 | 55 | 70 | 85 |
| Curing time | h | 2 | 4 | 6 | 8 | 12 |
| Emulsifier dosage | % | 0.5 | 1.0 | 1.5 | 2.0 | 2.5 |
| Mixing speed | rpm | 500 | 1000 | 1500 | 2000 | 2500 |

## How to Define Factors: 5 Steps

### Step 1: Identify controllable variables

List all process parameters, raw material proportions, and curing conditions that may influence the target response. Focus on variables that can be controlled and measured in the lab.

### Step 2: Screen for significance

Use literature review or preliminary single-factor tests to eliminate variables with negligible effect. Retain 3–6 factors for orthogonal design.

### Step 3: Select factor ranges

Choose ranges that are:
- Practically achievable in the lab.
- Cover the expected optimum region.
- Within the bounds of relevant standards or specifications.

### Step 4: Choose level count and spacing

- **3 levels**: minimum for detecting curvature; use for screening.
- **4–5 levels**: use when the response surface is complex or the range is wide.
- Spacing: evenly distributed across the range unless prior knowledge suggests otherwise.

### Step 5: Define response variables

Select measurable outputs that directly reflect performance:
- Mechanical: compressive strength, tensile strength, bond strength.
- Durability: water absorption, chloride penetration, freeze-thaw resistance.
- Workability: slump, flow, setting time.
- Functional: thermal conductivity, adhesion, softening point.

## Common Factor Ranges by Domain

### Asphalt

| Factor | Typical Range | Common Levels |
|--------|--------------|---------------|
| Modifier content (%) | 2–12 | 3, 5, 7, 9 |
| Mixing temperature (°C) | 140–180 | 140, 150, 160, 170 |
| Mixing time (min) | 10–40 | 10, 20, 30 |
| Curing temperature (°C) | 20–60 | 25, 35, 45, 55 |
| Asphalt content (%) | 4–7 | 4.5, 5.0, 5.5, 6.0 |
| Emulsifier dosage (%) | 0.5–3.0 | 1.0, 1.5, 2.0 |
| Aggregate gradation | — | AC-13, AC-16, AC-20 |
| Aging time (h) | 0–72 | 0, 24, 48, 72 |

### Cement / Concrete

| Factor | Typical Range | Common Levels |
|--------|--------------|---------------|
| Water-cement ratio | 0.30–0.60 | 0.35, 0.40, 0.45, 0.50 |
| Cement content (kg/m³) | 300–500 | 320, 360, 400, 440 |
| SCMs replacement (%) | 0–40 | 10, 20, 30, 40 |
| Superplasticizer (%) | 0–2.0 | 0.5, 1.0, 1.5 |
| Curing temperature (°C) | 20–60 | 20, 30, 40, 50 |
| Curing humidity (%) | 50–100 | 60, 70, 80, 90 |
| Sand ratio (%) | 30–45 | 33, 36, 39, 42 |
| Fiber content (%) | 0–1.5 | 0, 0.5, 1.0, 1.5 |

### Ceramics

| Factor | Typical Range | Common Levels |
|--------|--------------|---------------|
| Sintering temperature (°C) | 1000–1400 | 1050, 1150, 1250, 1350 |
| Sintering time (h) | 1–8 | 1, 2, 4, 6 |
| Additive content (%) | 0–10 | 0, 2, 5, 8 |
| Particle size (μm) | 0.5–10 | 1, 2, 5, 8 |
| Pressing pressure (MPa) | 50–200 | 50, 100, 150, 200 |
| Heating rate (°C/min) | 2–10 | 2, 5, 8, 10 |

### Thermal Insulation

| Factor | Typical Range | Common Levels |
|--------|--------------|---------------|
| Density (kg/m³) | 20–200 | 30, 60, 100, 150 |
| Foaming agent (%) | 1–10 | 2, 4, 6, 8 |
| Fiber content (%) | 0–5 | 0, 1, 2, 3 |
| Binder ratio | 0.1–0.5 | 0.15, 0.25, 0.35 |
| Curing temperature (°C) | 20–80 | 25, 40, 55, 70 |
| Sample thickness (mm) | 10–50 | 10, 20, 30, 40 |

## YAML record export

After the factor-level table is confirmed, convert it into an `experiment-record.yaml` fragment:

```yaml
factors:
  - name: <factor_a>
    unit: <unit>
    type: continuous
    levels: [<level_1>, <level_2>, <level_3>]
  - name: <factor_b>
    unit: <unit>
    type: continuous
    levels: [<level_1>, <level_2>, <level_3>]

response_variables:
  - name: <response_a>
    unit: <unit>
    measurement_method: "<standard or protocol>"
    replicate_count: 3
```

Fill in `design.runs` from the chosen design matrix (orthogonal, RSM, screening, or mixture).
