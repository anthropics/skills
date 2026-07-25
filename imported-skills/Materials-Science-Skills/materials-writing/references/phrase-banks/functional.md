# Functional / Electronic Materials Phrase Bank

Use this bank for semiconductors, dielectrics, piezoelectrics, photonic/optoelectronic materials, and electrochemistry manuscripts.

---

## phrase-bank

### synthesis and fabrication

- `[Material] was deposited/grown/synthesized by [method] on [substrate] at [temperature]°C under [atmosphere/pressure], yielding [film thickness/layer count] of [value].`
- `The [doping/stoichiometry/composition] was controlled by adjusting [precursor ratio/deposition parameter/dopant concentration] between [range], resulting in [carrier concentration/conductivity type].`
- `Device fabrication followed a [layer structure], with [electrode material] as [cathode/anode/contact] and active area of [value] mm².`

### electronic properties

- `Hall effect measurements reveal [n-type/p-type] conductivity with carrier concentration of [value] cm⁻³ and mobility of [value] cm² V⁻¹ s⁻¹ at [temperature] K.`
- `The current-voltage (I-V) characteristic shows [ohmic/Schottky/rectifying] behavior with [specific contact resistivity/barrier height] of [value].`
- `Capacitance-voltage (C-V) profiling indicates a doping density of [value] cm⁻³ with a depletion width of [value] µm at [bias] V.`

### optical properties

- `UV-vis absorption spectrum shows an absorption edge at [value] nm, corresponding to a [direct/indirect] bandgap of [value] eV by Tauc plot.`
- `Photoluminescence (PL) spectrum exhibits a peak at [value] nm attributed to [band-to-band/exciton/defect] emission, with FWHM of [value] nm.`
- `The [reflectance/transmittance/extinction] coefficient reaches [value] at [wavelength], indicating [optical quality/property].`

### dielectric and piezoelectric

- `The dielectric constant ε′ reached [value] at [frequency] Hz and [temperature], with a dielectric loss tan δ of [value].`
- `Polarization-electric field (P-E) hysteresis shows [remanent polarization] of [value] µC cm⁻² and [coercive field] of [value] kV cm⁻¹, characteristic of [ferroelectric/antiferroelectric] behavior.`
- `Piezoelectric coefficient d₃₃ of [value] pC/N was measured by [Berlincourt/d33 meter], [comparable to/surpassing] [reference material].`

### electrochemical properties

- `The [material] electrode delivers an initial [discharge/charge] capacity of [value] mAh g⁻¹ at [current] mA g⁻¹, with capacity retention of [value]% after [number] cycles.`
- `Cyclic voltammetry shows [reversible/quasi-reversible/irreversible] redox peaks at [potential] V vs. [reference electrode], attributed to [redox couple/reaction].`
- `Electrochemical impedance spectroscopy (EIS) reveals a charge transfer resistance of [value] Ω, with [Warburg/semicircle] behavior characteristic of [diffusion/kinetic] control.`

### device performance

- `The [solar cell/ photodetector/LED] achieves a [PCE/EQE/responsivity] of [value]% under [illumination/bias], with [open-circuit voltage/short-circuit current/external quantum efficiency] of [value].`
- `The device retains [value]% of initial performance after [duration] under [operating condition], with degradation primarily attributed to [mechanism].`
- `A [power conversion efficiency/response time/detection limit] of [value] represents a [factor] improvement over [reference/control], attributable to [optimization].`

---

## reviewer-red-flags

- Reporting efficiency/capacity without measurement conditions (temperature, scan rate, illumination intensity).
- No device-to-device statistics (single best device is not representative).
- Attributing all device performance to the active material without considering contact/interface effects.
- Missing hysteresis in J-V or polarization measurements.
- Stability data from unrealistically short test duration.
- Comparing performance with literature without normalizing for test conditions.

---

## safe-claim-patterns

- `[Material] exhibits [property] of [value] at [condition], which is [comparison] relative to [reference], within the range of reported values for [material class].`
- `The [performance metric] of [value] was achieved in a [device configuration], though [interface/contact/measurement] contributions have not been fully decoupled.`
- `[Material] demonstrates [property] suitable for [potential application] at [operation condition], pending [long-term stability/scalability/device integration] assessment.`
- `Efficiency/capacity of [value] was obtained from [number] devices, with a standard deviation of [value], indicating [acceptable/low] reproducibility requiring further optimization.`
