# Materials for Papers — Top Journal Style Examples

Real-world example figures for materials science manuscripts, following the style conventions of leading materials journals.

## Purpose

This directory contains reproducible figure source examples for common materials science manuscript types. Each example includes:

- **plot.py**: Complete plotting script with journal-specific formatting
- **data/**: CSV source data files (synthetic but realistic)
- **figures/**: Generated locally when `plot.py` is run; image outputs are ignored in the public package

These examples demonstrate how to create publication-ready figures using matplotlib with proper rcParams, font handling, and output settings.

## Journal Categories

### Civil & Building Materials (CBM / CC Research style)

| Example | Journal Style | Chart Type | Content |
|---------|--------------|------------|---------|
| `cement_hydration_xrd/` | Cement and Concrete Research | Stacked XRD | Hydration phase evolution (1d, 3d, 7d, 28d) |
| `concrete_durability_retention/` | Construction and Building Materials | Grouped bar | Freeze-thaw, carbonation, chloride retention |
| `asphalt_bonding_performance/` | Construction and Building Materials | Grouped bar + dual axis | WER/SBS/EVA bonding under dry/wet/aged |
| `tack_coat_interface_schematic/` | Construction and Building Materials | Schematic | Pavement layer structure with tack coat |

### Traditional Materials Journals (Acta Mat / JACS / MSE A / Polymer / CST style)

| Example | Journal Style | Chart Type | Content |
|---------|--------------|------------|---------|
| `steel_microstructure_ebsd/` | Acta Materialia | Multi-panel | IPF maps, grain boundaries, pole figures |
| `ceramics_weibull_reliability/` | J. Am. Ceram. Soc. | Weibull plot | 3Y-TZP vs Al₂O₃ strength distribution |
| `alloy_stress_strain/` | Mater. Sci. Eng. A | Stress-strain | Ti-6Al-4V tensile with work hardening |
| `polymer_thermal_degradation/` | Polymer | TGA/DTG | PE/PP/PS/PMMA thermal degradation |
| `composite_fatigue_sn/` | Compos. Sci. Technol. | S-N curve | CFRP vs GFRP fatigue life |

### High-Impact General Journals (Adv. Mat. / ACS Nano / Adv. Funct. Mat. style)

| Example | Journal Style | Chart Type | Content |
|---------|--------------|------------|---------|
| `nanoparticle_size_distribution/` | ACS Nano | TEM + histogram + DLS | Nanoparticle size statistics |
| `2d_material_raman_mapping/` | Advanced Materials | Raman spectra + mapping | Graphene D/G/2D peak mapping |
| `multifunctional_composite_radar/` | Advanced Functional Materials | Radar chart | Multi-property comparison |

## Running Examples

Each example is self-contained. To regenerate a figure:

```powershell
cd figure_name
python plot.py
```

The script will read data from `data/` and save the figure to `figures/`. Generated images are local outputs and are not tracked in the public GitHub delivery.

## Requirements

- Python 3.10+
- matplotlib
- numpy
- csv (standard library)

All scripts use `matplotlib.use("Agg")` for headless rendering.

## Journal-Specific Conventions

### Civil & Building Materials (CBM / CC Research)
- **Data density**: High — multiple groups, conditions, error bars
- **Statistics**: Significance markers (*, **, ***), p-values
- **Layout**: Grouped comparisons, dual Y-axes for retention
- **Colors**: Muted, professional palette

### Traditional Materials Journals
- **Acta Materialia**: EBSD IPF maps, pole figures, grain boundary networks
- **JACS**: Weibull analysis, statistical rigor, n ≥ 10
- **MSE A**: Stress-strain with yield/UTS annotations, work hardening
- **Polymer**: TGA/DTG dual-axis, decomposition temperature annotations
- **CST**: S-N curves on log-log scale, Basquin fitting

### High-Impact General Journals
- **ACS Nano**: TEM + statistical histograms, log-normal fitting
- **Advanced Materials**: Raman mapping with spatial color maps
- **Advanced Functional Materials**: Radar charts, multi-property comparison

## Relationship to Other Assets

- **templates/figure-package/**: Contract and QA templates
- **examples/figure-packages/**: 3 runnable figure packages with real CSV data

The `materials4papers/` examples are **reference implementations**, not automated tools. They demonstrate best practices for creating publication-ready figures from real experimental data.

## License

These examples are provided as reference material for materials science figure generation. Use them as templates for your own manuscript figures.
