# 2D Materials Source Screening and Quality Standards

Use this reference when screening graphene, transition metal dichalcogenides, MXenes, and other 2D materials literature.

## Evidence layers

| Layer | Typical sources | Key markers |
|---|---|---|
| Synthesis/exfoliation | ACS Nano, Nano Letters, 2D Materials | CVD, exfoliation, transfer, substrate |
| Layer number | AFM, Raman, TEM, optical contrast | Statistical layer count, peak ratio, contrast analysis |
| Crystal quality | HRTEM, SAED, Raman FWHM | Defect density, grain boundaries, doping |
| Surface/edge | XPS, STM/AFM, EELS | Functional groups, adsorbates, edge termination |
| Electronic/optoelectronic | Transport, PL, Hall | Mobility, on/off ratio, bandgap, exciton behavior |
| Device | ACS Nano, Nature Nanotech. | Channel dimensions, contacts, dielectric, bias conditions |

## Reviewer-safe screening rules

### Layer number
- ✅ AFM step height + Raman/PL + statistical count (n ≥ 30) → `high`
- ⚠️ Optical contrast used without calibration → `screening needed`
- ❌ Layer number inferred from optical color alone → `low`

### Electronic transport
- ✅ Channel dimensions + contact material + dielectric + temperature + hysteresis check → `high`
- ⚠️ Mobility reported without channel geometry or contact effects → `screening needed`
- ❌ Mobility estimated from conductivity without Hall or device → `low`

### CVD growth
- ✅ Precursors, T, pressure, time, substrate, transfer method reported → `high`
- ⚠️ Growth reported but nucleation density/domain size missing → `screening needed`
- ❌ Large-area growth claimed without uniformity map → `low`

## Claim-source mapping

| Claim | Minimum evidence | Destination |
|---|---|---|
| High mobility | Device dimensions + transport + contact characterization | Citation matrix |
| Layer-dependent properties | Layer statistics + property series + modeling | Mechanism table + Figure plan |
| Doping/defect engineering | Spectroscopy + transport + spatial mapping | Mechanism table |
| Heterostructure behavior | Interface characterization + transport/optical data | Mechanism table + Figure plan |
