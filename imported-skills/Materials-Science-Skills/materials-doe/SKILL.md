---
name: materials-doe
version: "1.1.0"
description: Use when planning, generating, or auditing design-of-experiments matrices for materials science and engineering research. Covers classical factorial, Taguchi orthogonal arrays, screening designs (Plackett-Burman, fractional factorial), response surface methodology (CCD, Box-Behnken), and mixture designs.
---

# Materials Science Design of Experiments

Plan and generate design-of-experiments matrices for materials research.

## Routing protocol

1. Read [manifest.yaml](manifest.yaml), then load every `always_load` file.
2. Apply profile-first routing from `.materials/profile.yaml`; on first use, ask for direction once and save it locally.
3. Detect all five axes: `design_mode`, `material_family`, `domain`, `output`, and `output_format`.
4. Read each selected path from the manifest once. Load `references.on_demand` only when its named condition applies.
5. Follow the selected design fragment to confirm factors, levels, constraints, replication, randomization, and analysis strategy.
6. Generate the requested matrix or plan and verify its design-specific invariants.
7. Emit `experiment-record.yaml` by default; use textual output only when the `output_format` route selects it.
8. Invoke companion skills only for a requested handoff. Do not preload their context for a standalone DOE task.

## Gates

- BLOCKING: Factor list and level count must be confirmed before generating any matrix.
- Resolve the design mode before loading mode-specific references.
- Mixture components and bounds must be feasible and sum to the declared total.
- Replication, randomization, controls, and interaction assumptions must be explicit.
- Claims about optimality or statistical power must be backed by the chosen design's properties.
