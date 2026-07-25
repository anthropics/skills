# Literature Matrix Template

## Purpose
Source x Theme cross-tabulation for systematic evidence mapping. Used by the synthesis_agent to organize evidence before writing the synthesis narrative.

## Matrix Structure

### Basic Matrix

```markdown
## Literature Matrix: [Research Topic]

**Date compiled**: [YYYY-MM-DD]
**Total sources**: [N]
**Themes identified**: [N]

| Source | Year | Level | Theme A | Theme B | Theme C | Theme D | Theme E |
|--------|------|-------|---------|---------|---------|---------|---------|
| Author1 | 2024 | II | ✓ Supports | — | ✓ Supports | ✗ Contradicts | — |
| Author2 | 2023 | III | ✓ Supports | ✓ Supports | — | — | ✓ Supports |
| Author3 | 2022 | VI | — | ✓ Supports | ✓ Supports | ✓ Supports | — |
| Author4 | 2024 | I | ✓ Supports | ✓ Supports | ✗ Contradicts | — | ✓ Supports |
| Author5 | 2023 | IV | ✗ Contradicts | — | ✓ Supports | ✓ Supports | — |
| **Totals** | | | **4✓ 1✗** | **3✓ 0✗** | **3✓ 1✗** | **2✓ 1✗** | **2✓ 0✗** |

### Legend
- ✓ Supports: Source provides evidence supporting this theme
- ✗ Contradicts: Source provides evidence contradicting this theme
- — : Source does not address this theme
- Level: Evidence hierarchy level (I = highest, VII = lowest)
```

### Extended Matrix (with detail)

```markdown
## Extended Literature Matrix

| Source | Method | Sample | Theme A: [name] | Theme B: [name] | Quality |
|--------|--------|--------|-----------------|-----------------|---------|
| Author1 (2024) | RCT, N=500 | University students, US | "Finding X was significant (p<.001)" — Supports | Not addressed | A |
| Author2 (2023) | Case study, N=3 institutions | Asian universities | "Institution A showed..." — Supports | "However, in context B..." — Partial | C |
| Author3 (2022) | Meta-analysis, k=42 | Global | "Pooled effect size d=0.45" — Strong support | "Subgroup analysis revealed..." — Mixed | A |
```

### Convergence Summary

```markdown
## Evidence Convergence Summary

| Theme | Sources For | Sources Against | Net | Strength | Confidence |
|-------|-----------|----------------|-----|----------|-----------|
| Theme A | 4 (Levels I, II, III, IV) | 1 (Level VI) | +3 | Strong | High |
| Theme B | 3 (Levels I, III, IV) | 0 | +3 | Strong | High |
| Theme C | 3 (Levels II, III, VI) | 1 (Level I) | +2 | Contested | Medium |
| Theme D | 2 (Levels IV, VI) | 1 (Level II) | +1 | Weak | Low |
| Theme E | 2 (Levels I, III) | 0 | +2 | Moderate | Medium |

### Interpretation Guide
- **Strong** (≥3 supporting, higher-level evidence): Confident finding
- **Moderate** (2-3 supporting, mid-level evidence): Likely finding, more evidence welcome
- **Weak** (1-2 supporting, lower-level evidence): Tentative, needs more research
- **Contested** (evidence on both sides): Genuine debate, report both sides
- **Gap** (0 sources): Knowledge gap identified
```

### Gap Identification

```markdown
## Knowledge Gaps

| Gap | Type | Implication | Priority |
|-----|------|-------------|----------|
| No data on [population X] | Empirical | Cannot generalize to this group | High |
| Only [method type] used | Methodological | Triangulation needed | Medium |
| No studies since [year] | Temporal | Evidence may be outdated | Medium |
| Only studied in [region] | Geographic | Generalizability unknown | Low |
| No theoretical framework for [finding] | Theoretical | Theory development opportunity | Low |
```

## Usage Notes
- Start with the Basic Matrix for initial organization
- Upgrade to Extended Matrix as synthesis deepens
- Convergence Summary should directly inform the synthesis narrative
- Gap Identification feeds into the Discussion section
- Update the matrix as new sources are added — it is a living document
