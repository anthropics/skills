# Dielectric / Piezoelectric / Ferroelectric Materials Source Screening

Use this reference when screening dielectric, ferroelectric, and piezoelectric materials literature.

## Evidence layers

| Layer | Typical sources | Key markers |
|---|---|---|
| Synthesis/processing | J. Am. Ceram. Soc., J. Eur. Ceram. Soc., Chem. Mater. | Powder route, sintering, film deposition, electrode |
| Phase/crystallinity | XRD, Rietveld, Raman | Perovskite structure, phase purity, texture |
| Microstructure | SEM, TEM, AFM | Grain size, porosity, film thickness, interfaces |
| Dielectric response | Impedance analyzer, LCR meter | ε′, tan δ, frequency and temperature dependence |
| Ferroelectric | P-E loop, Sawyer-Tower, PFM | Pr, Ec, saturation polarization |
| Piezoelectric | d33 meter, resonance method | d33, kp, electromechanical coupling |
| Reliability | Fatigue, imprint, thermal depoling | Cycling data, retention, temperature dependence |

## Reviewer-safe screening rules

### Dielectric data
- ✅ Frequency + temperature range + ac amplitude + sample geometry reported → `high`
- ⚠️ Single-frequency permittivity quoted without context → `screening needed`
- ❌ Dielectric constant compared across different frequencies/temperatures without acknowledgment → `low`

### Ferroelectric hysteresis
- ✅ P-E loop frequency, maximum field, sample area, film thickness reported → `high`
- ⚠️ Only Pr/Ec values given without loop → `screening needed`
- ❌ Ferroelectricity inferred from composition alone → `low`

### Piezoelectric coefficient
- ✅ d33 measurement method + load + sample orientation + n ≥ 3 → `high`
- ⚠️ d33 reported without method or orientation → `screening needed`
- ❌ d33 from resonance extrapolation without validating geometry → `low`

## Claim-source mapping

| Claim | Minimum evidence | Destination |
|---|---|---|
| High permittivity/low loss | Frequency-temperature data + microstructure + leakage | Citation matrix |
| Ferroelectric switching | P-E loops + thickness + fatigue data | Mechanism table + Figure plan |
| Piezoelectric enhancement | d33 + microstructure + poling conditions | Citation matrix |
| Energy storage density | P-E loop + efficiency + cycling stability | Mechanism table + Figure plan |
