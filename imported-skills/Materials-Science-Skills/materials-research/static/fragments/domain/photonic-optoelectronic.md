# Domain: Photonic & Optoelectronic Materials

Covers LEDs (III-nitride, perovskite), solar cells (Si, perovskite, organic, tandem), photodetectors, and laser diodes.

## Core logic

1. Active layer design (quantum well thickness, absorber composition, band alignment) determines emission/absorption wavelength and carrier confinement.
2. Carrier injection (LED) or extraction (solar cell) efficiency depends on contact quality, transport layers, and interface recombination.
3. Light extraction (photonic crystals, surface roughening, anti-reflection coatings) can dominate external efficiency; internal processes alone are incomplete.
4. Device efficiency (EQE, PCE, luminous efficacy) must be decomposed into internal and external contributions to identify loss channels.
5. Lifetime testing (T80, T70, L70) under accelerated conditions (high current, elevated temperature, humidity) is essential; initial performance is not durability.
6. Encapsulation and packaging significantly affect lifetime and spectral stability; bare-device data are insufficient for application claims.

## Key evidence categories

- J-V curves: open-circuit voltage (Voc), short-circuit current (Jsc), fill factor (FF), PCE (solar) or forward voltage (LED)
- EQE/IQE spectra: wavelength-resolved quantum efficiency
- EL/PL spectra: peak position, FWHM, color coordinates (CIE for LEDs)
- Luminous efficacy (lm/W) and CRI for white LEDs
- T80/T70 lifetime data under operating conditions (current density, temperature)
- Absorption/transmission spectra, Tauc analysis for bandgap

## Reviewer risks

- Efficiency roll-off at operating current density ignored; champion EQE at low current, not at target drive current.
- Lifetime data insufficient; T80 tested for <1000 h or only at low stress conditions.
- Encapsulation effects missing; bare perovskite solar cell tested in N2 but claimed for outdoor use.
- Thermal droop in LEDs not reported; efficiency at 350 mA/mm² differs from peak at low current.
- Solar cell stability under MPPT (maximum power point tracking) not tested; only J-V sweep shown.
