# Nanomaterials Source Screening and Quality Standards

Use this reference when screening nanoparticles, nanotubes, nanowires, nanosheets, 2D materials, graphene, MXenes, quantum dots, and nanocomposite literature for citation mapping, review construction, or evidence auditing.

## Evidence layers for nanomaterials

| Layer | What it covers | Typical sources |
|---|---|---|
| Synthesis | Bottom-up/top-down methods, capping agents, solvents, yield | ACS Nano, Nano Letters, Chemical Communications |
| Size/morphology | TEM/SEM/AFM size distribution, aspect ratio, layer number | ACS Nano, Nanoscale |
| Crystal structure | XRD, Raman, HRTEM, SAED | Nano Letters, Small |
| Surface chemistry | Functional groups, zeta potential, XPS, FTIR | Langmuir, Journal of Physical Chemistry C |
| Colloidal stability | Dispersion, agglomeration, solvent compatibility | Langmuir, Nanoscale |
| Properties | Optical, electronic, magnetic, catalytic, mechanical | Advanced Materials, Nature Nanotechnology |
| Toxicity/environmental | Cell viability, ROS, biodistribution, ecotoxicity | ACS Nano, Environmental Science & Technology |

## Source quality tiers

| Tier | Definition | Examples |
|---|---|---|
| **Primary experimental** | Original data from controlled synthesis with full characterization of size, structure, and properties | Research article with synthesis protocol, TEM/XRD, property measurement |
| **Review evidence** | Synthesis of multiple primary sources | Review article, perspective, book chapter |
| **Method/standard** | Test standard or widely accepted protocol | ISO/TS 19337 (nanoparticle tracking), ASTM E2524 (nanoparticle dispersion), DLS best practices |
| **Weak background** | Conference abstract, thesis without peer review, patent without characterization, non-peer-reviewed preprint | — |

## Reviewer-safe screening rules

### Synthesis and reagents
- ✅ Precursors, solvents, capping agents, temperature, time, atmosphere, purification method all reported → `high`
- ⚠️ Synthesis route reported but reagent ratios or purification missing → `screening needed`
- ❌ Only target material named without synthesis detail → `low`

### Size and morphology
- ✅ Representative TEM/SEM + size distribution (n ≥ 100 for particles, n ≥ 30 for 2D sheets) + method → `high`
- ⚠️ Imaging presented without size histogram → `screening needed`
- ❌ Size claim without imaging or DLS without TEM validation → `low`

### Crystallinity and phase
- ✅ XRD/Raman/HRTEM with peak assignment/phase identification → `high`
- ⚠️ XRD without peak assignment or phase reference → `screening needed`
- ❌ Crystallinity assumed from synthesis recipe → `low`

### Surface chemistry / dispersion
- ✅ Surface functionalization described + zeta potential or stability data + solvent → `high`
- ⚠️ Functional group mentioned but not quantified → `screening needed`
- ❌ Dispersion claimed without zeta potential or imaging evidence → `low`

### Layer number (2D materials)
- ✅ AFM/Raman/ISTEM with statistical layer count → `high`
- ⚠️ Single image used to represent bulk sample → `screening needed`
- ❌ Layer number inferred from color optical image alone → `low`

## Claim-source mapping rules

| Claim type | Minimum evidence | Move to |
|---|---|---|
| Size-property relationship | Size distribution + property measurement + structure link | Mechanism table + Figure plan |
| Surface functionalization effect | Surface characterization + stability/property comparison + controls | Mechanism table |
| Catalytic/photocatalytic activity | Reaction conditions + catalyst loading + normalized activity + stability | Citation matrix + Figure plan |
| Biomedical/toxicity claim | Cell line/organism + dose + exposure time + viability assay + controls | Citation matrix |
| 2D material electronic/optical property | Layer-thickness statistics + device/ spectroscopy data + environmental conditions | Mechanism table + Figure plan |
| Scalability/application potential | Yield/throughput data + reproducibility + limitation statement | Review discussion only |
