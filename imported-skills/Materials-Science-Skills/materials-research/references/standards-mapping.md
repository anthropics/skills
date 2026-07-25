# GB/T, JTG, ASTM, EN, ISO Standards Mapping

Use this reference when converting Chinese laboratory test descriptions into internationally legible manuscript methods. Always verify the official standard year and exact clauses before submission.

> Companion reference: [test-standards-mapping.md](test-standards-mapping.md) organizes related standards by evidence need, such as moisture resistance, workability, durability, or LCA claims. Use both references for complete coverage.

## Concrete and Cementitious Materials

| Test | Chinese standard | International counterpart | Key difference to report |
|---|---|---|---|
| Concrete compressive strength | GB/T 50081-2019 | ASTM C39 / EN 12390-3 | GB commonly uses cubes; ASTM C39 uses cylinders. Cube and cylinder strengths are not directly interchangeable. |
| Concrete flexural strength | GB/T 50081-2019 | ASTM C78 / EN 12390-5 | Loading configuration and specimen geometry may differ. |
| Splitting tensile strength | GB/T 50081-2019 | ASTM C496 / EN 12390-6 | Report specimen diameter/height and loading rate. |
| Chloride migration | GB/T 50082 RCM method | NT Build 492 / ASTM C1202 as related but not equivalent | RCM migration coefficient and ASTM C1202 charge passed measure different quantities. |
| Carbonation | GB/T 50082 | No single direct ASTM equivalent | CO2 concentration, RH, exposure time, and specimen size control comparability. |
| Freeze-thaw | GB/T 50082 | ASTM C666 | Temperature range, cycle regime, and failure criterion differ. |
| Drying shrinkage | GB/T 50082 / GB/T 50081 family methods | ASTM C157 | Report curing age, RH, temperature, and specimen size. |

Manuscript wording:

```text
Compressive strength was measured according to GB/T 50081-2019 using
100 mm cubic specimens cured at 20 +/- 2 degC and >95% RH for 28 days.
When compared with ASTM C39 cylinder-based literature, the specimen geometry
difference should be considered.
```

## Asphalt, Emulsified Asphalt, and Pavement Materials

| Test | Chinese standard | International counterpart | Key difference to report |
|---|---|---|---|
| Penetration | JTG E20 T0604 | ASTM D5 / EN 1426 | Mostly comparable; confirm temperature, load, and time. |
| Softening point | JTG E20 T0606 | ASTM D36 / EN 1427 | Mostly comparable; report ring-and-ball details. |
| Ductility | JTG E20 T0605 | ASTM D113 | Stretching rate and temperature must be stated. |
| Emulsified asphalt residue | JTG E20 T0651 | ASTM D244 | Evaporation/distillation procedures may differ. |
| Emulsion storage stability | JTG E20 emulsion stability methods | ASTM D244 related methods | Storage temperature, duration, and residue calculation must be explicit. |
| Tack coat / pull-off adhesion | JTG E20 T0719 as reference or lab method | ASTM D4541 / EN ISO 4624 as related pull-off methods | Loading rate, substrate, dolly adhesive, curing condition, and failure mode differ. |
| Asphalt mixture moisture susceptibility | JTG E20 / Chinese mixture methods | AASHTO T283 / EN 12697 family | Conditioning and retained-strength definitions differ. |

Manuscript wording:

```text
Pull-off bond strength was measured using a laboratory pull-off fixture
adapted from JTG E20 T0719. The test used [substrate], [application rate],
[curing condition], and [loading rate]. Because the fixture differs from
ASTM D4541, the values are interpreted for within-study comparison rather
than direct cross-standard ranking.
```

## How to Compare Literature

Use direct numerical comparison only when:

- specimen geometry is comparable.
- curing or aging conditions are comparable.
- loading rate and temperature are comparable.
- property definitions are the same.

If not comparable, write:

```text
The literature values are used as contextual benchmarks rather than direct
equivalents because the test standards and specimen configurations differ.
```

## Citation and Translation Rules

- Keep the original standard name in Methods when the experiment was actually performed under GB/T or JTG.
- Add ASTM/EN/ISO only as `related` or `comparable` unless the method is truly equivalent.
- Do not silently convert cube strength to cylinder strength without an explicit conversion model and citation.
- State the standard year, specimen size, curing condition, and loading rate in the same paragraph.
