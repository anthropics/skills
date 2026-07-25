# Process / Material Inventions (default for civil)

Identify raw materials, sequence, conditions, ranges, intermediate states,
product characteristics, and measurement methods. Preserve disclosed range
boundaries and units literally. Do not generalize a single experimental
point into an unsupported genus or range.

## Civil materials checklist

When drafting for civil / building materials, pay special attention to:

- **Raw materials**: cement clinker grade, aggregate type and gradation,
  supplementary cementitious materials (SCM: fly ash, slag, silica fume,
  calcined clay), polymer binder (epoxy, PU, acrylate), fiber reinforcement
  (glass, carbon, basalt, PVA, steel), additive dosages (water reducer,
  retarder, accelerator, air-entrainer).
- **Process parameters**: water-to-binder ratio (w/b), curing temperature
  and duration, mixing sequence and time, compaction energy, post-treatment
  (steam, autoclave, carbonation).
- **Performance metrics**: compressive strength (MPa), flexural strength
  (MPa), splitting tensile strength (MPa), elastic modulus (GPa), chloride
  diffusion coefficient (m²/s), carbonation depth (mm), frost resistance
  (cycles), shrinkage (μm/m), fatigue life (S-N curve).
- **Microstructure indicators**: XRD phase composition (CSH, CH, C2S, C3S,
  AFt, AFm, CaCO3), FTIR functional groups (cm⁻¹), SEM morphology, MIP pore
  size distribution (nm), BET surface area (m²/g).
- **Range honesty**: a single mix design is one point; a "compressive
  strength of 50-80 MPa" requires multiple data points spanning the range
  in the source. Do not extrapolate.

## Claim verb guidance

For process claims, prefer:

- "包括以下步骤：" / "包含：" / "其特征在于："
- Method steps: 提供、混合、搅拌、浇注、振捣、养护、测试、表征

For product claims:

- "一种 X，其特征在于："
- Define composition by content ranges with units (wt%, vol%, mol%)
- Define microstructure by measurable parameters (phase content, porosity,
  pore size)

## Figure handoff to materials-figure

Methodology figures (process flowcharts, equipment schematics, micro-
structure representations) are produced by the `materials-figure` skill:

1. This skill generates the figure description text and the figure number
   reference (e.g., "图1为本发明方法的工艺流程图");
2. The user invokes `materials-figure` with the desired chart type
   (flowchart, schematic, microstructure) to produce PNG/SVG;
3. The figure is inserted at the corresponding `outputs/` location.

Do not produce charts inside this skill — keep responsibilities clear.

## Common anti-patterns to avoid

- "高性能" / "耐久" without measurable parameter
- "本发明" in independent claim body (only in title/abstract)
- Range without unit (e.g., "含量 0.1-5" — must be 0.1-5 wt%)
- Single point extrapolated to range
- Method claim missing the final technical result (the last step must name
  a concrete domain output)
