# Functional / Electronic Materials — Writing Guide

Loaded automatically when the domain is functional/electronic materials (semiconductors, dielectrics, piezoelectrics, photonics, optoelectronics, electrochemistry).

## Domain narrative arc

The strongest arc for functional materials follows a **composition-structure-property-device** logic:

1. Application context: what device or function is targeted (sensor, solar cell, battery, LED, memory, actuator).
2. Material limitation: performance metric that blocks adoption (efficiency, stability, switching speed, cycling life, leakage current).
3. Design strategy: composition engineering, doping, heterostructure, defect control, or interface engineering.
4. Property evidence: electronic, optical, electrochemical, or electromechanical characterization.
5. Structure evidence: XRD, TEM, XPS, Raman, or other techniques linking structure to function.
6. Device integration: how the material performs in a device-relevant configuration.
7. Boundary: stability under operating conditions, scalability of synthesis.

## Key evidence chain

Synthesis → structure (phase, defect, interface) → functional property (bandgap, conductivity, polarization, efficiency) → device performance → stability

Functional properties must be measured under relevant operating conditions (temperature, frequency, bias, illumination).

## Section guidance

### Introduction
- Start from the performance metric that matters for the target device.
- Gap should be a performance ceiling: "current [material class] achieves [X efficiency/stability] but requires [Y] for commercial viability."
- Avoid: lengthy history of the material class before stating the problem.

### Methods
- Synthesis: precursor, temperature, time, atmosphere, substrate, deposition method.
- Characterization: instrument model, measurement parameters (frequency range, scan rate, voltage window, temperature).
- Device fabrication: layer structure, electrode material, active area, encapsulation.
- Report measurement conditions that affect results (humidity, temperature, light intensity).

### Results
- Structure characterization first (XRD, Raman, XPS, TEM) to confirm phase and quality.
- Functional property: present the key metric with error margins.
- Stability/cycling data if applicable.
- Use Arrhenius or other relevant plots for temperature-dependent data.

### Discussion
- Link functional performance to specific structural features.
- Compare with state-of-the-art values for the same material class.
- Address the stability-performance trade-off explicitly.

### Conclusion
- State the material, the key functional metric, and the condition under which it was achieved.
- Acknowledge stability and scalability limitations.
- Do not claim "commercial potential" without cost or scalability data.

## Reviewer-sensitive points in functional materials

- ⚠️ Efficiency/capacity reported without device-to-device variation or measurement uncertainty.
- ⚠️ "High performance" claimed without comparison to established benchmarks.
- ⚠️ Stability data reported for unrealistically short duration.
- ⚠️ Defect/mechanism claims without direct characterization (XPS, EPR, TEM).
- ⚠️ Electrochemical data without clarifying contribution from the material vs. the electrode/electrolyte system.

## Common pitfalls

| Pitfall | Example | Fix |
|---|---|---|
| Missing benchmark | "efficiency of 18%" vs what? | Always cite the relevant state-of-the-art value |
| Ignoring hysteresis | J-V curve measured in one direction only | Report forward and reverse scans |
| Overclaiming stability | "stable after 100 cycles" without capacity retention % | Report both retention % and coulombic efficiency |
| Device vs. material confusion | attributing all performance to the active material | Discuss electrode, interface, and measurement contributions |
