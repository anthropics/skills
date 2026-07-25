# Domain: Additive Manufacturing Metals

## Usage

Covers metals produced by laser powder bed fusion (L-PBF/SLM), electron beam melting (EBM),
directed energy deposition (DED/LMD), and binder jetting. Common alloys: 316L, Inconel
718/625, Ti-6Al-4V, AlSi10Mg, 17-4PH, CoCr. Applicable to aerospace, medical implants,
tooling, and rapid prototyping.

## Core logic

1. Process parameters (laser power, scan speed, hatch spacing, layer thickness, scan strategy) control melt pool geometry and thermal gradient.
2. Solidification conditions (G·R ratio) determine columnar-to-equiaxed transition, grain size, and crystallographic texture.
3. As-built microstructure (metastable phases, residual stress, dislocation density) differs fundamentally from wrought/cast equivalents.
4. Post-processing (stress relief, HIP, heat treatment, machining) transforms microstructure and closes porosity; properties depend on combined process chain.
5. Anisotropy (build direction vs. transverse), surface roughness, and defect population (lack-of-fusion, keyhole porosity) govern structural reliability.

## Key evidence categories

- Density: Archimedes method, CT scanning (porosity size/shape/distribution)
- Mechanical: tensile (XY and XZ directions), hardness maps (cross-section), fatigue (high-cycle and low-cycle)
- Microstructural: SEM/EBSD (grain morphology, texture, phase), optical microscopy (etch response, melt pool boundaries)
- Residual stress: neutron diffraction, hole-drilling, contour method
- Surface: profilometry (Ra, Rz), CT (surface-connected porosity)
- Thermal: DSC (phase transformation, precipitate dissolution), in-situ monitoring (melt pool imaging, pyrometry)

## Reviewer risks

- Anisotropy ignored; properties reported from single build orientation without acknowledging directional dependence.
- Surface roughness effects on fatigue not isolated; machined vs. as-built specimens conflated in property databases.
- Post-processing (stress relief parameters, HIP pressure/temperature/time) not standardized or fully reported.
- Defect population (type, size, distribution) not quantified by CT; density alone insufficient for structural qualification.
- Process parameter set not reported with sufficient detail (energy density alone is inadequate; individual parameters required).
