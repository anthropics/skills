# Photonic / Optoelectronic Materials Source Screening

Use this reference when screening photonic, optoelectronic, and light-management materials literature.

## Evidence layers

| Layer | Typical sources | Key markers |
|---|---|---|
| Growth/fabrication | APL, Optics Express, ACS Photonics | Deposition, lithography, layer stack, contacts |
| Structural/compositional | XRD, XPS, TEM, EDX | Phase, stoichiometry, interface quality |
| Optical | UV-Vis, PL, PLE, transmittance | Bandgap, emission, absorption, quantum yield |
| Device | APL, IEEE TED, Nature Photon. | EQE, responsivity, response time, active area |
| Stability | ACS Photonics, APL | Operational lifetime, thermal quenching, encapsulation |

## Reviewer-safe screening rules

### Optical spectra
- ✅ Measurement geometry, excitation wavelength/power, detector calibration reported → `high`
- ⚠️ Peak wavelength quoted without excitation conditions → `screening needed`
- ❌ Bandgap estimated without showing raw spectrum or Tauc plot → `low`

### Photoluminescence quantum yield
- ✅ Integration sphere or calibrated reference + excitation density + solvent/atmosphere → `high`
- ⚠️ PLQY from relative comparison only → `screening needed`
- ❌ PLQY inferred from brightness or visual observation → `low`

### Device performance
- ✅ EQE/responsivity spectrum + bias + active area + illumination + statistics → `high`
- ⚠️ Single metric reported without spectral response → `screening needed`
- ❌ Performance compared across different device architectures without normalization → `low`

## Claim-source mapping

| Claim | Minimum evidence | Destination |
|---|---|---|
| High EQE/responsivity | Spectral response + bias + statistics | Citation matrix |
| Narrow emission / high color purity | PL FWHM + stability + measurement conditions | Mechanism table |
| Waveguide/lasing action | Threshold + mode structure + pump conditions | Mechanism table + Figure plan |
| Photostability | Accelerated aging + output tracking + atmosphere | Citation matrix |
