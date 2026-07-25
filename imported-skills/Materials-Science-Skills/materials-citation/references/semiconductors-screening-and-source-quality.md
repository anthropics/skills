# Semiconductors Source Screening and Quality Standards

Use this reference when screening semiconductor and thin-film device literature.

## Evidence layers

| Layer | Typical sources | Key markers |
|---|---|---|
| Material growth | APL, J. Crystal Growth, JVST | Deposition method, substrate, temperature, thickness |
| Structural | XRD, TEM, AFM, RHEED | Crystallinity, phase, surface roughness, defect density |
| Electronic | Hall, I-V, C-V, DLTS | Carrier type/density/mobility, doping profile, trap levels |
| Optical | UV-Vis, PL, ellipsometry | Bandgap, absorption coefficient, recombination lifetime |
| Device | IEEE EDL, TED, APL | Active area, contact geometry, measurement conditions |
| Reliability | IEEE TED, APL | Bias-temperature stress, aging, encapsulation |

## Reviewer-safe screening rules

### Carrier transport
- ✅ Hall geometry, magnetic field, temperature, contact method reported → `high`
- ⚠️ Hall data reported without geometry or temperature → `screening needed`
- ❌ Mobility inferred from conductivity alone → `low`

### Device metrics
- ✅ Active area verified + illumination/bias conditions + statistics (n ≥ 3) → `high`
- ⚠️ Single best device reported → `screening needed`
- ❌ Efficiency/gain quoted without defining active area or conditions → `low`

### Contact quality
- ✅ Ohmic/Schottky behavior shown with contact resistivity or TLM → `high`
- ⚠️ I-V linearity mentioned but no contact characterization → `screening needed`
- ❌ Device performance attributed to active layer ignoring contact effects → `low`

## Claim-source mapping

| Claim | Minimum evidence | Destination |
|---|---|---|
| Mobility improvement | Growth + structural + Hall + comparison | Citation matrix |
| Bandgap engineering | XRD/SAED + optical + composition | Mechanism table |
| Device performance record | Full protocol + statistics + conditions | Citation matrix |
| Degradation mechanism | Accelerated stress + in-situ characterization | Mechanism table + Figure plan |
