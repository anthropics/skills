# Reference Gap Audit

> **Domain context**: The `domain` axis has loaded domain-specific citation guidance for [detected domain]. The gap checks below are universal; the domain guide lists domain-specific evidence standards and reviewer expectations.

Flag a citation gap when:

- a paragraph makes a broad field claim without a review or recent primary source,
- a mechanism is inferred without mechanism evidence,
- a test standard is used without naming the standard or precedent,
- a journal scope claim relies on memory,
- all citations are old while the topic is active,
- citations support adjacent materials but not the studied material system.

Suggested risk labels:

- `must-fix`: likely reviewer objection or desk-reject risk,
- `strengthen`: acceptable but thin,
- `optional`: useful for polish or positioning.

## Domain-specific gap checks

### Civil construction materials
Flag `must-fix` when:
- a formulation claim lacks evidence from a directly matched material system,
- a mechanism claim relies only on strength/bonding values without FTIR, SEM, or thermal evidence,
- a durability claim uses only short-term data without accelerated aging,
- field applicability claimed without field validation or engineering boundary.

### Ceramics
Flag `must-fix` when:
- sintering conditions are claimed without density or phase evidence,
- mechanical property claims lack Weibull statistics or specimen numbers,
- phase identification lacks reference pattern matching or Rietveld quantification.

### Metals
Flag `must-fix` when:
- strength improvement claimed without ductility or toughness data,
- microstructure claims lack quantitative grain size or phase fraction measurements,
- heat treatment parameters incomplete (especially cooling rate).

### Polymers
Flag `must-fix` when:
- crosslinking claimed without gel content, DSC exotherm, or FTIR evidence,
- compatibility claimed without thermal (single Tg) or morphological (SEM/TEM) evidence,
- mechanical properties reported without thermal characterization (Tg/Tm).

### Functional materials
Flag `must-fix` when:
- efficiency/capacity reported without device-to-device variation,
- stability claims based on unrealistically short test duration,
- benchmark comparison missing for claimed "high performance."

### Nanomaterials
Flag `must-fix` when:
- particle size claimed from XRD alone without TEM confirmation,
- size distribution statistics missing (≥100 particles required),
- surface chemistry claims without XPS, FTIR, or zeta potential evidence.
