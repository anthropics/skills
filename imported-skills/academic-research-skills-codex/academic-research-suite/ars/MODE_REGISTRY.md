# Mode Registry

Single source of truth for all modes across the ARS suite. **27 modes** across 4 skills.

When adding or modifying modes, update this file first — SKILL.md files and CLAUDE.md should reference this registry.

Last updated: v3.16.0 (2026-07-12)

---

## deep-research (8 modes)

| Mode | Spectrum | Output | Oversight | Triggers |
|------|----------|--------|-----------|----------|
| `full` | Balanced | APA 7.0 report, 3,000-8,000 words | High | "research [topic]", "deep research", "academic analysis" |
| `quick` | Fidelity | Research brief, 500-1,500 words | Medium | "quick brief", "30 minute summary", "quick research" |
| `review` | Balanced | Reviewer report on provided text | High | "review this paper", "evaluate this paper", "assess this source" |
| `lit-review` | Fidelity | Annotated bibliography + synthesis | Medium | "literature review", "annotated bibliography" |
| `three-way-scan` | Fidelity | WHY/HOW/WHAT paper shortlist + cross-paper synthesis | Low | "WHY HOW WHAT papers", "3W literature scan", "compare these papers" |
| `fact-check` | Fidelity | Claim-by-claim verification report | Medium | "verify claims", "fact-check", "evidence verification" |
| `socratic` | Originality | Research Plan Summary + INSIGHT collection | Very High | "guide my research", "help me think through", "I'm not sure what to research" |
| `systematic-review` | Fidelity | PRISMA 2020 report, 5,000-15,000 words | Medium | "systematic review", "meta-analysis", "PRISMA" |

## academic-paper (11 modes)

| Mode | Spectrum | Output | Oversight | Triggers |
|------|----------|--------|-----------|----------|
| `full` | Balanced | Complete paper draft (IMRaD or domain-appropriate) | High | "write a paper", "academic paper", "research paper" |
| `plan` | Originality | Chapter Plan + INSIGHT collection (Socratic) | Very High | "guide my paper", "help me plan", "step by step paper" |
| `outline-only` | Balanced | Detailed outline + evidence map | High | "paper outline", "just need an outline" |
| `revision` | Fidelity | Revised draft + point-by-point R&R responses | High | "revise paper", "incorporate reviewer feedback" |
| `revision-coach` | Balanced | Revision Roadmap + Response Letter Skeleton | Medium | "parse reviews", "I got reviewer comments" |
| `abstract-only` | Fidelity | Bilingual abstract (zh-TW + EN) + keywords | Medium | "write abstract" |
| `lit-review` | Fidelity | Annotated bibliography in paper format | Medium | "literature review paper", "write a lit review" |
| `format-convert` | Fidelity | Formatted document (LaTeX/DOCX-via-Pandoc/PDF/MD) | Low | "convert to LaTeX", "convert citations to [format]" |
| `citation-check` | Fidelity | Citation error report | Low | "check citations", "verify references" |
| `disclosure` | Fidelity | Venue-specific AI-usage disclosure statement | Low | "AI disclosure for [venue]", "generate AI usage statement" |
| `rebuttal-audit` | Fidelity | Advisory QA of an existing rebuttal draft (per-comment coverage + gaps + risk flags); no generation; no Schema 11 emission | Low | "audit my response", "check my rebuttal", "did I miss any reviewer comment" |

## academic-paper-reviewer (6 modes)

| Mode | Spectrum | Output | Oversight | Triggers |
|------|----------|--------|-----------|----------|
| `full` | Balanced | 5 review reports + Editorial Decision + Revision Roadmap | High | "review paper", "peer review", "manuscript review" |
| `re-review` | Fidelity | Revision verification checklist + residual issues | Medium | "check revisions", "verification review" |
| `quick` | Fidelity | EIC quick assessment + key issues list | Low | "quick review", "quick look" |
| `methodology-focus` | Fidelity | In-depth methodology review | Medium | "check methodology", "focus on methods" |
| `guided` | Originality | Socratic issue-by-issue dialogue | Very High | "guide me to improve", "walk me through issues" |
| `calibration` | Fidelity | Calibration Report (FNR/FPR/AUC) + confidence disclosure | Medium | "calibrate reviewer", "measure reviewer accuracy" |

## academic-pipeline (1 orchestrator + 1 resume mode)

| Mode | Spectrum | Output | Oversight | Triggers |
|------|----------|--------|-----------|----------|
| (pipeline) | Balanced | 10-stage orchestrated workflow | Very High | "academic pipeline", "research to paper", "full paper workflow" |
| `resume_from_passport=<hash>` | Fidelity | Resume a prior pipeline run from a Material Passport reset boundary. Opt-in (`ARS_PASSPORT_RESET=1`). See `academic-pipeline/references/passport_as_reset_boundary.md`. | High | "resume from passport", "continue pipeline from reset boundary" |

---

## Summary

| Metric | Count |
|--------|-------|
| Total modes | 27 |
| Fidelity | 16 (59%) |
| Balanced | 7 (26%) |
| Originality | 4 (15%) |

### Oversight levels

| Level | Meaning |
|-------|---------|
| Very High | User-led dialogue or mandatory checkpoints at every stage |
| High | User confirms key decisions (RQ, outline, configuration) |
| Medium | Structured format with limited decision points |
| Low | Mechanical/template-driven, minimal human input |
