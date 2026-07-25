# VLM Figure Verification Protocol (Optional)

**Status**: v3.3
**Used by**: `visualization_agent`
**Requires**: Multimodal LLM with vision capability (e.g., Claude with vision, GPT-4V)

---

## Purpose

After the visualization_agent generates a figure, an optional verification loop uses a vision-capable LLM to check the rendered figure against the paper's data and APA 7.0 standards. This catches issues invisible in code review: truncated labels, overlapping text, incorrect data rendering, misleading scales.

Inspired by PaperOrchestra's Plotting Agent (Song et al., 2026), which uses a "VLM critic" in a closed-loop refinement system.

---

## When to use

- **Recommended**: When figures contain complex data (multi-panel, many categories, statistical plots)
- **Optional**: For simple figures (single bar chart, basic line plot)
- **Required**: When the pipeline is in `final-check` mode (Stage 4.5+)
- **Skip**: When no multimodal capability is available (graceful degradation)

---

## Verification Checklist

The VLM receives the rendered figure image and the source data, then checks:

### Data Accuracy
1. Do the plotted values visually match the source data? (e.g., a bar labeled "45%" should be approximately 45% of the axis range)
2. Are all data series present? (no missing categories or groups)
3. Do error bars / confidence intervals appear correct in scale?

### APA 7.0 Compliance
4. Are both axes labeled with descriptive text and units?
5. Is the legend present and readable (for multi-series)?
6. Is the figure title in the correct format (bold label + italic title)?
7. Are fonts readable at publication size (no text < 8pt)?

### Visual Quality
8. Is any text truncated, overlapping, or cut off at figure edges?
9. Are colors distinguishable (no two series with visually identical colors)?
10. Is the figure free of chart junk (3D effects, unnecessary gridlines)?

---

## Verification Loop

```
Step 1: visualization_agent generates figure code
Step 2: Execute code to render figure image
Step 3: Send figure image + source data + checklist to VLM
Step 4: VLM returns pass/fail for each checklist item
Step 5: If any FAIL:
  - VLM describes the specific issue
  - visualization_agent modifies code to fix
  - Return to Step 2 (max 2 iterations)
Step 6: If all PASS or max iterations reached:
  - Attach verification result to Figure Package
  - Any remaining issues noted in figure caption Note
```

**Max iterations**: 2 refinement cycles (3 total renders). If issues persist after 2 fixes, flag for user review rather than continuing the loop.

---

## Output Addition to Figure Package

When VLM verification is run, the Figure Package (from visualization_agent) includes:

```markdown
### VLM Verification
- **Status**: PASS / PASS_WITH_NOTES / NEEDS_REVIEW / SKIPPED
- **Iterations**: [N] (1 = passed first time, N/A if SKIPPED)
- **Issues found**: [list of issues, if any]
- **Issues fixed**: [list of fixes applied]
- **Remaining issues**: [issues that could not be auto-fixed, if any]
```

---

## Figure/Table Trace (#261)

The VLM checklist above answers *"does the rendered figure match the source data?"* — a faithful-rendering check. It does **not** answer *"does the caption's interpretation follow from the data, and does the manuscript cite this artifact for a claim it actually supports?"* That is a different failure: a figure can render perfectly while its caption overstates what the data shows, or the manuscript can cite it for a claim the figure does not support. Kong et al. (2026) §3.4 names this — "an AI-generated figure may look professional while containing … invalid quantitative relationships" — and it is the **visual analog of the prose partial-evidence trap** addressed for citations in #213 (sub-claim decomposition before citation judgment) and for review synthesis in #214 (sub-claim inventory before consensus). Same trap, different artifact type; the implementations stay separate.

To make that checkable, the Figure Package carries a `figure_table_trace[]` block — one entry per visual artifact (figure **or** manuscript table) that links the rendered output back to its data and its claims. This is a **prose contract** read by the visualization_agent (producer) and the integrity_verification_agent (consumer); it is **not** a machine-validated schema and adds no lint, no JSON Schema, and no gold fixture (there is no deterministic downstream parser — mirroring the #214 prose-layer decision, not the #213 schema-layer one).

### Trace block format

```yaml
figure_table_trace:
  - artifact_id: "fig-3"               # figure number or table id, stable within the package
    source_data:
      dataset_id: "abl-n128"           # logical dataset name
      file: "results/abl_n128.csv"     # path or pointer to the raw data
    transformation: {script: "scripts/plot_fig3.py", hash: "a1b2c3d"}
      # OR a precise manual-derivation pointer, e.g.
      # transformation: "manual derivation: see §4.2 paragraph 2 (mean over 3 seeds, SE bars)"
    caption_claim: "Accuracy improves monotonically with N up to N=256."
    supported_manuscript_claims:                            # claims the figure is cited to support
      - claim: "Accuracy scales with model size up to N=256."   # claim TEXT (+ optional locator below)
        locator: "Results §4.2, ¶3"                              # where the manuscript makes it
    limitations:
      - "Only N=128, 256, 512 tested; the monotonic claim between those points is interpolation."
```

### Field rules

1. **`source_data`** — every claim-bearing artifact must point to a real dataset/file. A figure whose data origin is unstated is untraceable.
2. **`transformation`** — either a `{script, hash}` pair (reproducible) **or** a precise manual-derivation pointer naming the section/paragraph and the operation. A vague value (`"computed manually"`, `"see paper"`) is **not** sufficient and is treated by the integrity gate as untraceable.
3. **`caption_claim`** — the interpretive claim the caption makes. May be **compound** ("accuracy improves AND variance decreases"); the integrity gate decomposes it into atomic sub-claims before judging (borrowing the #213 decomposition *as prose guidance only* — no `PARTIAL` verdict, no `sub_claim_breakdown[]` schema is imported).
4. **`supported_manuscript_claims`** — the manuscript claim(s) this artifact is cited to support, each as **claim text + an optional manuscript `locator`** (section/paragraph). It does **not** use a bare claim ID: the `visualization_agent` can run before the draft and its `claim_intent_manifest` exist (figures are produced in Stage 2, alongside the outline; the manifest is emitted by the prose agents during drafting), so a `(manifest_id, claim_id)` reference would dangle. When a manifest *does* exist (e.g. a revision-stage figure), an entry MAY additionally carry `manifest_id` + `claim_id` to join the scoped key — but the text + locator is the always-available primary. Each listed claim must actually reference the artifact in the manuscript and must not be overstated by it. The integrity gate checks this **both directions**: every listed claim must cite the artifact (forward), and every **substantive** manuscript use of the artifact must be covered by a listed claim (reverse) — a one-sided trace that declares only the support the author wants seen, while the manuscript leans on the figure for an unlisted claim, is an omission the reverse check catches. Incidental or structural mentions that assert nothing about the data ("see Figure N for the architecture", "results are summarized in Table N", a bare "(Figure N)" pointer) are exempt and must NOT be padded into the trace.
5. **`limitations`** — caveats the scholar knows about the artifact (e.g. "N=3 trials; error bars are SE not SD"). **The agent does not auto-detect missing limitations.** An empty `limitations: []` surfaces a named advisory (`[FIGURE-LIMITATIONS-EMPTY]`), not a silent pass; a **non-empty** limitation that never appears in the manuscript is a blocking issue (the agent knew it and the manuscript dropped it).

**Required keys.** All six keys — `artifact_id`, `source_data`, `transformation`, `caption_claim`, `supported_manuscript_claims`, and `limitations` — MUST be present on every entry. `limitations` is required but its value MAY be `[]` (so the empty-limitations advisory still fires); an entry that **omits** any key, including `artifact_id` (the figure↔trace linking key) or the `limitations` key, is malformed and the integrity gate FAILs it for a claim-bearing artifact.

**Tables.** When a manuscript table has a `figure_table_trace[]` entry, the same checks apply. For a standalone table with no trace, the integrity gate surfaces a trace-unavailable finding rather than treating absence as a pass.

---

## References

- Song, Y. et al. (2026). PaperOrchestra. *arXiv:2604.05018*. — Section 4 Step 2 (Plotting Agent with VLM critic).
- Zhu, D. et al. (2026). PaperBanana: Automating academic illustration for AI scientists. *arXiv:2601.23265*. — Closed-loop VLM refinement system.
- Kong, L. et al. (2026). AI for Auto-Research: Roadmap & User Guide. *arXiv:2605.18661*. — §3.4 (figure/table fidelity failures; the motivation for the trace layer, #261).
