# Review Compilation Workflow

Use this workflow when pipeline outputs need to become a review outline, mini
review, or structured literature synthesis.

## Phase 1: Inventory Existing Knowledge

1. Gather pipeline digests, candidate tables, reader packages, citation
   matrices, Zotero/library exports, and local notes.
2. Deduplicate by DOI, external ID, and normalized title-year key.
3. Label papers by source depth: metadata-only, abstract-screened,
   full-text-read, or data-extracted.
4. Separate direct evidence from background context.

## Phase 2: Fill Critical Gaps

1. Use `gap-analysis.md` to identify weak subtopics.
2. Run targeted searches for the weakest subtopics only.
3. Promote candidates to `materials-reader` before using them as support.
4. Update the candidate table with the new source-depth labels.

## Phase 3: Audience Filter

Filter the inventory for the intended reader:

| Keep | Remove or demote |
|---|---|
| Directly relevant materials-system evidence | Generic method papers with low transfer value |
| Papers that change the review's classification or mechanism map | Papers the audience already knows unless needed as anchors |
| Quantitative benchmarks and standard methods | Low-information background summaries |
| Local/domain-specific papers with unique data | Duplicate conclusions without new evidence |

## Phase 4: Structure Design

Build the review around a causal or problem-solving chain rather than a
catalogue of materials.

Recommended structure:

1. Field problem and application boundary.
2. Material-system taxonomy.
3. Mechanisms or failure modes.
4. Performance evidence and testing methods.
5. Controlling factors and design variables.
6. Remaining gaps and DOE/data needs.
7. Engineering implications and outlook.

## Phase 5: Figure And Table Plan

Plan figures before prose:

- Mechanism schematic or classification map.
- Evidence matrix table.
- Timeline or research-trend plot.
- Method-comparison table.
- Gap-to-next-experiment map.

Route visual outputs to `materials-figure` and evidence mapping to
`materials-citation`.

## Phase 6: Writing Handoff

Before sending to `materials-writing`, provide:

- Review thesis in one sentence.
- Section-level claims and forbidden claims.
- Source-depth distribution.
- Gap report path or summary.
- Figure/table plan.
