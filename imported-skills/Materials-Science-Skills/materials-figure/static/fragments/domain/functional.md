# Functional / Electronic Materials — Figure Guide

## Common figure types

| Figure type | When to use | Key requirements |
|---|---|---|
| J-V / I-V curve | Solar cells, diodes, transport measurement | Forward & reverse scan; dark & light if relevant; temperature |
| UV-vis absorption/transmission | Bandgap determination, optical properties | Tauc plot inset; baseline correction |
| PL spectrum | Luminescence, defect states, quantum confinement | Excitation wavelength; normalized/intensity scale |
| XRD pattern | Phase, crystallinity, epitaxy | Peak labels; substrate peak noted; FWHM for quality |
| EIS (Nyquist/Bode) | Electrochemical properties, impedance | Frequency range; equivalent circuit model; temperature |
| Cyclic voltammogram | Electrochemical behavior, redox peaks | Scan rate; reference electrode; potential window |
| Device performance (PCE, EQE) | Solar cells, photodetectors, LEDs | Active area; light intensity; statistics across devices |

## Typical multi-panel structure

**Panel A**: Material characterization (XRD + UV-vis/Raman confirming structure & bandgap)
**Panel B**: Functional property (J-V curves or PL spectra)
**Panel C**: Device performance (efficiency/response with statistics)
**Panel D**: Stability (performance retention over time or cycles)

## Reviewer-sensitive pitfalls

- ⚠️ J-V curve without specifying scan direction or rate.
- ⚠️ Bandgap from Tauc plot without stating direct/indirect assumption.
- ⚠️ Solar cell efficiency without device area or number of devices.
- ⚠️ EIS without equivalent circuit fit or frequency range.
- ⚠️ PL intensity compared without normalization or identical measurement conditions.

## Caption boundary phrases

- `J-V characteristics of [device] under [illumination/dark] at [temperature]. Scan rate: [value].`
- `UV-vis absorption spectra of [material] with Tauc plot (inset) showing bandgap of [value] eV.`
- `Nyquist plots of [material] at [temperature]. Symbols: experimental data; lines: equivalent circuit fit.`
- `Device performance distribution across [n] devices. Box represents 25th–75th percentile; whiskers represent min–max range.`
