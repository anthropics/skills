# Mode Spectrum: Fidelity vs Originality

**Status**: v3.2
**Source**: Lu et al. (2026, Nature 651:914-919) Figure 1c — template-based mode produces higher-quality, lower-variance papers; template-free mode produces more diverse outputs but lower mean quality and higher variance. ARS maps this finding onto its own mode taxonomy.

---

## Why this spectrum exists

Not all modes should treat templates and examples the same way. A `systematic-review` needs rigid structure (PRISMA checklist, predefined sections) — templates are load-bearing. A `socratic` dialogue needs room to wander — heavy templates kill exploration.

Lu et al.'s template-based vs template-free comparison gives us a language for this trade-off: **fidelity** (reproducible, template-heavy, lower variance) vs **originality** (exploratory, template-light, higher variance, higher ceiling on novelty).

ARS modes fall on a spectrum between these poles. This table is the reference for decisions about:
- How much template/example material to load at mode start
- Whether to inline templates in SKILL.md or load from sub-files on demand (v3.1 Phase 3)
- Whether to suggest the mode when the user's goal is "predictable output" vs "creative exploration"

---

## Mode spectrum table

| Skill | Mode | Spectrum position | Template load | Rationale |
|---|---|---|---|---|
| deep-research | `systematic-review` | Fidelity | Heavy | PRISMA protocol, predefined search strategy, reproducible steps |
| deep-research | `lit-review` | Fidelity | Heavy | Structured annotated bibliography, fixed output format |
| deep-research | `three-way-scan` | Fidelity | Medium | Fixed WHY/HOW/WHAT per-paper frame + cross-paper synthesis, lighter than lit-review |
| deep-research | `fact-check` | Fidelity | Heavy | Claim → evidence → verdict pipeline, no room for drift |
| deep-research | `quick` | Fidelity | Heavy | Time-boxed brief, fixed 3-section format |
| deep-research | `review` | Balanced | Medium | Review has structure but allows domain-specific adaptation |
| deep-research | `full` | Balanced | Medium | Structured output but methodology selection is exploratory |
| deep-research | `socratic` | Originality | Light | User-led dialogue, templates constrain exploration |
| academic-paper | `full` | Balanced | Medium | Section templates loaded, but writing adapts to argument |
| academic-paper | `outline-only` | Balanced | Medium | Structure templates needed, but outline is creative |
| academic-paper | `revision` | Fidelity | Heavy | R&R tracking template, point-by-point responses |
| academic-paper | `revision-coach` | Balanced | Medium | Coaching is semi-structured; roadmap template loaded |
| academic-paper | `abstract-only` | Fidelity | Heavy | Fixed abstract structure (background/method/results/conclusion) |
| academic-paper | `lit-review` | Fidelity | Heavy | Annotated bibliography format |
| academic-paper | `format-convert` | Fidelity | Heavy | Format conversion is purely mechanical |
| academic-paper | `citation-check` | Fidelity | Heavy | Citation audit is checklist-driven |
| academic-paper | `plan` | Originality | Light | Socratic planning dialogue, no forced chapter sequence |
| academic-paper | `disclosure` (v3.2) | Fidelity | Heavy | Venue policy database → templated output |
| academic-paper | `rebuttal-audit` | Fidelity | Heavy | Per-comment coverage checklist against an existing rebuttal draft, advisory QA |
| academic-paper-reviewer | `full` | Balanced | Medium | Review rubric loaded, but reviewer perspectives are dynamic |
| academic-paper-reviewer | `re-review` | Fidelity | Heavy | R&R traceability matrix, checklist-driven |
| academic-paper-reviewer | `quick` | Fidelity | Heavy | Fixed EIC quick-assessment format |
| academic-paper-reviewer | `methodology-focus` | Fidelity | Heavy | Focused on statistical/methods rubric |
| academic-paper-reviewer | `guided` | Originality | Light | Socratic dialogue, adaptive to what the user needs |
| academic-paper-reviewer | `calibration` (v3.2) | Fidelity | Heavy | Fixed 5x ensembling protocol, no creative adaptation |

---

## Mode recommendation

- User wants "predictable" / "consistent" → suggest **Fidelity** modes
- User wants to "explore" / "think through" → suggest **Originality** modes
- Unclear → suggest **Balanced** modes as default
