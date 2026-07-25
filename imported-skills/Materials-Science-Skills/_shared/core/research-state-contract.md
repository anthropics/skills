# Research State Contract

This contract links the materials skills into one traceable research state. It is
a lightweight handoff object, not an application database.

## Purpose

Use a research state whenever a workflow spans literature, DOE, datasets,
figures, writing, or reviewer risk. The state keeps every claim connected to its
source depth, planned design, data package, figure anchor, and remaining
uncertainty.

## Architecture

```text
materials-research
  -> research-state
     -> materials-literature-pipeline / materials-citation / materials-reader
        -> source_map
     -> materials-doe
        -> doe_map
     -> materials-data
        -> data_map
     -> materials-figure
        -> figure_map
     -> materials-writing
        -> claim_map
     -> materials-reviewer
        -> risk_map
```

Every participating skill reads and writes its section of the research state.
The orchestrator (`materials-research`) validates cross-section consistency.

## Required Sections

| Section | Purpose | Typical producer | Key fields |
|---|---|---|---|
| `project` | Scope, material family, target domain, and active research question | `materials-research` | `project_id`, `title`, `material_family`, `domain`, `research_question` |
| `source_map` | Candidate papers, reader packages, citation roles, evidence layer | `materials-literature-pipeline`, `materials-citation`, `materials-reader` | `candidates`, `reader_packages`, `citation_handoffs` |
| `doe_map` | Factors, levels, run IDs, hypotheses, response variables | `materials-doe` | `design_id`, `factors`, `responses`, `planned_runs` |
| `data_map` | FAIR package status, metadata gaps, data availability boundary | `materials-data` | `package_id`, `fair_status`, `metadata_gaps` |
| `figure_map` | Figure IDs, source anchors, caption boundaries, visual evidence | `materials-figure` | `figure_ids`, `source_anchors`, `caption_boundaries` |
| `claim_map` | Allowed claims, forbidden claims, confidence, support chain | `materials-writing`, `materials-reviewer` | `claims`, `forbidden_claims`, `confidence_labels` |
| `risk_map` | Reviewer risks, missing evidence, next action, owner skill | `materials-research`, `materials-reviewer` | `reviewer_risks`, `next_actions` |

## State Rules

1. **Claim provenance**: A claim cannot be promoted from hypothesis to
   manuscript claim unless it has at least one source, DOE rationale, dataset,
   or figure link.
2. **Evidence boundary**: Metadata-only papers are candidate evidence; they are
   not support until read by `materials-reader` or verified through source
   excerpts.
3. **Discovery scoring**: Literature-pipeline scores rank reading priority
   only. `score_total` is recalculated from `topic_fit`,
   `evidence_layer_score`, `method_relevance`,
   `material_system_proximity`, `source_quality`, and `actionability`; scores
   do not promote a source-depth label.
4. **DOE-data alignment**: DOE planned runs and available datasets may disagree.
   Preserve planned design IDs and mark unresolved data gaps in
   `data_map.metadata_gaps`.
5. **Raw data blocking**: Missing raw or processed data paths block FAIR
   packaging until resolved or explicitly declared unavailable.
6. **Caption-claim consistency**: Figure captions must reference
   `figure_map.caption_boundary` and cannot imply stronger evidence than
   `claim_map.confidence` allows.
7. **Risk propagation**: Any `risk_map` entry with no owner skill or next action
   is a blocking gap. Every risk must route to a specific skill.

## Lifecycle

### 1. Init

`materials-research` creates the state from `research-state-template.yaml` when
the user starts a multi-skill workflow.

### 2. Populate

Each skill writes its section as it completes its work:

- `materials-literature-pipeline` -> `source_map.candidates`
- `materials-doe` -> `doe_map`
- `materials-data` -> `data_map`
- `materials-figure` -> `figure_map`
- `materials-writing` -> `claim_map`
- `materials-reviewer` -> `risk_map`

### 3. Validate

`materials-research` validates cross-section consistency before allowing
downstream claims:

- Every claim in `claim_map` has a source, DOE rationale, dataset, or figure
  link.
- Every data package that claims DOE support records the corresponding
  `doe_map.design_id` or an explicit gap.
- Every `risk_map` entry has an owner skill and next action.

### 4. Audit

`materials-reviewer` audits the complete state for evidence gaps, claim
overreach, and reviewer risks before submission.

## Routing

| Starting point | Route to |
|---|---|
| User asks for full workflow | `materials-research` (init state) |
| Need literature discovery | `materials-literature-pipeline` |
| Need formal experiment design | `materials-doe` |
| Need raw/processed data packages | `materials-data` |
| Need plots and mechanism maps | `materials-figure` |
| Need draft claims and section contracts | `materials-writing` |
| Need pre-submission risk audit | `materials-reviewer` |
| Cross-section consistency check | `materials-research` (validate state) |

## Minimal YAML Shape

Use `research-state-template.yaml` when a machine-readable state is useful.
Markdown summaries may include only the relevant sections, but must keep the
same field names.
