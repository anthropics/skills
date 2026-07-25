---
name: materials-figure
description: >-
  Submission-grade scientific figure workflow for materials science and engineering research. Use whenever the user asks to create, revise, audit, or polish manuscript figures, multi-panel materials science plots, or journal-ready SVG/PDF/TIFF outputs for materials journals, construction materials research, or civil engineering publications. Before plotting, define the figure's conclusion, evidence logic, export needs, and review risks. Use Python (matplotlib/seaborn) for all figure generation, previewing, exporting, and QA. Supports materials characterization plots (XRD, FTIR, TG/DTG), performance curves, mechanism schematics, and review evidence maps. Not for dashboards or Illustrator/Figma-first infographics. Also trigger on materials science figure needs such as 材料科学配图、土木材料论文图、XRD/FTIR光谱图、性能曲线图、机理示意图、综述证据图.
version: 2.1.0
author: Community contribution, refactored into static/dynamic layers
---

# Materials Science Figure Making — Router

## Layered architecture

- **Static layer** under `static/` — reusable fragments (profile protocol, stance, figure contract, workflow, backend, domain guides).
- **Dynamic layer** — this file plus [manifest.yaml](manifest.yaml). The router detects the request's axes, loads only the matching fragments, and runs the shared workflow.

The router stays short on purpose. Update fragments and the manifest, not this file, when adding scope.

## Routing protocol

1. **Load the manifest and the core layer.** Read [manifest.yaml](manifest.yaml), then load every file under `always_load` (profile protocol, contract, stance, workflow). These four files carry profile precedence, the figure contract, the operating stance, and the 8-step workflow that apply to every figure job.

2. **Resolve the profile, backend, and axes.** Apply the precedence `explicit direction in the current request > saved .materials/profile.yaml > neutral/general fallback`. Read the saved profile before resolving `material_family` and `domain`; on first use, ask for the materials direction once and save it locally. Then read [manifest.yaml](manifest.yaml) for the axis table and apply the Python blocking gate before any rendering.

3. **Run the workflow.** Follow [static/core/workflow.md](static/core/workflow.md) end-to-end: validate the storyboard first for multi-figure tasks, write the figure contract before any code, run materials validation when material entities are present, load the Python backend fragment, check source data anchors, then generate the figure package and run visual QA.

## Blocking gate

The Python backend is mandatory. Before rendering, check Python and required plotting packages (matplotlib, numpy, PIL; seaborn for heatmaps/statistical plots). If the runtime or packages are unavailable, stop before rendering and report the exact blocker. Do not generate mock data, write plotting scripts, create previews, or render placeholder figures until the claim, source-data anchor, and figure contract are clear. Python is the runtime gate; the contract, storyboard when applicable, materials validation when applicable, source-anchor, and visual-QA gates remain stop conditions.

## References

Deep references under `references/` are not defaults. Open them on demand per the `references.on_demand` table in the manifest — for example `figure-package-protocol.md` to build a complete figure package, `characterization-figures.md` for XRD/FTIR/TG/SEM plotting patterns, `performance-figures.md` for strength/bonding/viscosity curves, `mechanism-figures.md` for mechanism schematics, `figure-qa-contract.md` before final delivery, and `figure-production-spec.md` for export DPI, TIFF/EPS/PDF, final size.

When the figure contains materials-science entities (XRD peaks/phases, FTIR wavenumbers/functional groups, performance values), loading `static/core/materials_kb.yaml` and running `validate_materials_claims.py` are mandatory before plotting. Figures without those entities may skip this conditional gate. See [static/core/contract.md](static/core/contract.md) for the validation rules.
