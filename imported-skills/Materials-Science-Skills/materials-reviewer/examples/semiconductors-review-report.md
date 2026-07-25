# GaN Power Device Review Simulation

Simulated peer review for a manuscript submitted to *IEEE Electron Device Letters*.
Manuscript topic: "Enhancement-mode AlGaN/GaN HEMT with recessed-gate structure: threshold voltage stability and breakdown characteristics."

---

## Reviewer A

**Overall assessment:** Major Revision

**Focus:** originality, technical validity, device physics

**Scores**

| Dimension | Score (0-5) |
|---|---|
| Originality | 3 |
| Importance | 4 |
| Interdisciplinary | 2 |
| Technical Validity | 3 |
| Readability | 3 |

### Major comments

1. **[severity: high] [location: Results S3.1] Gate leakage current mechanism is not adequately discussed.**
   The manuscript reports a gate leakage current of 1.2 × 10^(-6) A/mm at V_GS = 5 V but does not identify the dominant conduction mechanism. For a recessed-gate HEMT, possible mechanisms include Poole-Frenkel emission, Fowler-Nordheim tunneling, or trap-assisted tunneling through the AlGaN barrier. Temperature-dependent I-V measurements are essential to deconvolve these contributions.
   *Evidence needed:* Gate leakage current measured at 300 K, 350 K, and 400 K with a Poole-Frenkel plot to extract the trap energy level.

2. **[severity: high] [location: Results S3.2] Breakdown voltage scaling with gate-drain distance is not benchmarked.**
   The reported breakdown voltage of 850 V at L_GD = 10 μm requires comparison with the theoretical limit for the given AlGaN/GaN material system. A benchmarking table against state-of-the-art recessed-gate GaN HEMTs with comparable L_GD and AlGaN barrier thickness is necessary to establish the significance of the result.
   *Evidence needed:* Comparison table including breakdown voltage, L_GD, R_on,sp, and figure-of-merit (BV^2/R_on,sp) for at least five recent recessed-gate GaN HEMT publications.

### Minor comments

- The on-resistance (R_on) of 6.8 Ω·mm at V_GS = 6 V should be normalized to the active device area for fair comparison.
- Figure 4: The transfer characteristics in semi-log scale need clearer labeling of the subthreshold swing region.
- The interface state density (D_it) extracted from the conductance method lacks error bars.

**Recommendation:** Major Revision. The device performance is promising, but the physical mechanism analysis is incomplete without temperature-dependent leakage characterization and proper benchmarking.

---

## Cross-Review Synthesis

### Agreed issues

- **Gate leakage mechanism analysis is insufficient** for a device-physics journal.
- **Benchmarking against state-of-the-art** is needed to substantiate the performance claims.
- **Interface characterization** (D_it extraction) requires more rigorous statistical reporting.

### Combined recommendation

**Major Revision.** Priority actions:
1. Perform temperature-dependent gate leakage measurements and extract conduction mechanism parameters.
2. Provide a comprehensive benchmarking table with BV^2/R_on,sp figure-of-merit.
3. Report D_it with error bars from multiple device measurements (n ≥ 5).