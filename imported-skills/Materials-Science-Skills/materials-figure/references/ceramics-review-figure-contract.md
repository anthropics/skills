# Ceramics Review Figure Contract

Use this contract when planning or reviewing figures for ceramics manuscripts. Each figure panel must meet these standards before it is considered journal-ready.

## Panel-level standards

| Standard | XRD | SEM/TEM | Weibull | Sintering | TGA/DSC | Stress-Strain | Impedance |
|---|---|---|---|---|---|---|---|
| Data quality | 2θ covers major peaks; step ≤0.02 | Scale bar visible; consistent mag; n >= 5 images | n >= 10 specimens; failure origin recorded | Heating rate + atmosphere reported | Heating rate, atmosphere, sample mass | Test standard, geometry, loading rate | Freq spans semicircle; T controlled |
| Annotation | (hkl) labels; ICDD reference | Grain size callouts; EDS labels | Confidence bounds; sigma_0 | Theoretical density line | Peak T markers; mass loss % | Elastic modulus; fracture point | Equivalent circuit; R and CPE |
| Caption boundary | "XRD indicates [phases] under tested conditions." | "SEM shows [feature] at [mag]." | "m = [value] from n = [n] specimens." | "Densification under [atm] up to [T]C." | "Thermal events at [T]C; literature-supported." | "Compressive response; rate-dependent." | "Impedance at [T]C. R_g = [value]." |

## Example captions

**XRD overlay for phase identification:**
> XRD patterns of Al2O3-ZrO2 composites sintered at 1550C. Al2O3 (ICDD 01-075-0782), t-ZrO2 (ICDD 01-070-4426). No monoclinic ZrO2 peaks detected, indicating full tetragonal stabilization by 3 mol% Y2O3.

**Sintering curve with theoretical density:**
> Relative density of Al2O3-5vol%SiC composites vs sintering temperature. Heating rate: 5C/min, dwell: 2 h, air. Dashed line: theoretical density of alpha-Al2O3 (3.96 g/cm3). Error bars: +/- 1 SD (n = 3).

**Weibull plot for strength reliability:**
> Weibull probability plot of flexural strength for 3Y-TZP with 0.5 wt% Al2O3. n = 15, sigma_0 = 405 MPa, m = 30.1. 95% confidence bounds shown as dashed curves.

**TGA/DSC thermal analysis:**
> TGA (solid) and DSC (dashed) curves of Al2O3 precursor under N2 atmosphere (10C/min). The endothermic peak at [T]C corresponds to [reaction]; mass loss of [X]% attributed to [process].

**Compressive stress-strain:**
> Representative compressive stress-strain curves of Al2O3 with fine and coarse grain sizes. Tested per ASTM C773 at 0.5 mm/min crosshead speed. The finer-grained material shows higher peak stress but reduced strain to failure.

## Figure package checklist

- [ ] Every panel has a defined evidence type and certainty tier
- [ ] XRD reference patterns cited with ICDD/JCPDS numbers
- [ ] SEM scale bars readable at publication size
- [ ] Weibull plot includes specimen count and confidence bounds
- [ ] Sintering curve includes heating rate and atmosphere in caption
- [ ] TGA/DSC includes heating rate, atmosphere, and sample mass
- [ ] Stress-strain includes test standard and loading rate
- [ ] Impedance includes frequency range, temperature, and circuit fit
- [ ] Caption boundary states what the data do NOT prove
- [ ] Color palette accessible (colorblind-safe)
- [ ] Font size >= 8 pt at final figure width
- [ ] DPI >= 600 for halftone, >= 1200 for line art
- [ ] All panels within a figure use consistent labeling style
