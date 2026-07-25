# Domain: Semiconductors

Covers silicon (Si), gallium arsenide (GaAs), gallium nitride (GaN), perovskites (MAPbI3, CsPbBr3), quantum dots (CdSe, InP, PbS), and related electronic/optoelectronic materials.

## Core logic

1. Synthesis or crystal growth method (Czochralski, MBE, MOCVD, solution processing) determines crystal quality, defect density, and scalability.
2. Bandgap engineering (alloying, quantum confinement, strain) tunes absorption/emission wavelength; the relationship must be modeled, not just measured.
3. Defect characterization (trap states, dislocations, vacancies) governs non-radiative recombination and device efficiency.
4. Carrier transport properties (mobility, concentration, lifetime) require Hall effect or SCLC measurements; optical data alone are insufficient.
5. Stability under operating conditions (light, heat, moisture, bias stress) must be tested; initial performance degrades without encapsulation or composition tuning.
6. Single-crystal benchmarks cannot be extended to polycrystalline or thin-film forms without grain boundary effects discussion.

## Key evidence categories

- XRD: crystal structure, phase purity, lattice parameters, crystallite size (Scherrer)
- Photoluminescence (PL): peak position, FWHM, defect emission bands
- UV-Vis-NIR: absorption onset, Tauc plot for bandgap extraction
- Hall effect: carrier type, mobility, concentration (temperature-dependent preferred)
- I-V curves: contact quality, ideality factor, series/shunt resistance
- External quantum efficiency (EQE), time-resolved PL (TRPL): carrier lifetime

## Reviewer risks

- Stability under operating conditions ignored; champion device shown without degradation data.
- Single-crystal vs. polycrystalline gap; grain boundary recombination not discussed.
- Defect characterization insufficient; PL peak position reported but trap density (DLTS, TPC) missing.
- Perovskite degradation under humidity/light not addressed or only tested in glovebox.
- Carrier mobility from optical measurements confused with electrical mobility (Hall).
