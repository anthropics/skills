# Materials Science Paper Production Orchestrator

Use this reference when `materials-research` must coordinate a full paper
production workflow instead of answering a single research question. The
orchestrator routes work across reader, citation, literature pipeline,
writing, polishing, reviewer, response, figure, data, and HTML deck skills
without duplicating those contracts.

## Operating Contract

1. Detect paper stage, workflow mode, output package, task, domain, and journal.
2. Name the active route in one line.
3. Check whether standard artifacts already exist.
4. Load only the companion skill guidance needed for the next step.
5. Emit handoff artifacts, paper gate rows, and weakness-routing rows whenever
   work cannot be completed safely in the current skill.

Default status values for the workflow are `pass`, `fail`, `blocked`, and
`not_applicable`. A blocked gate must name the missing input and next skill.

## Standard Artifacts

- `reader-package/package_manifest.json`
- `reader-package/source_map.json`
- `reader-package/citation_handoff.csv`
- `reader-package/figure_handoff.csv`
- `reader-package/review_handoff.md`
- `claim-evidence-boundary table`
- `mechanism-evidence table`
- `weakness-routing-template.csv`
- `paper-gate-report-template.md`
- `figure_contract.md`
- `data/FAIR package manifest`
- `submission-package/submission-package.yaml`

## Route A: WER-EA Mini-Review

Use this route for WER-EA mini-review, waterborne epoxy modified emulsified
asphalt review, modified emulsified asphalt bonding-performance review, or
review-paper planning.

| Phase | Route to | Required output |
|---|---|---|
| Scope and angle | materials-research | review question, scope boundary, target audience, candidate journal family |
| Literature Coverage | materials-citation | search strings, inclusion/exclusion criteria, source quality notes, citation matrix |
| Source Anchoring | materials-reader | reader-package, source_map, claim-evidence-mechanism-boundary rows |
| Review architecture | materials-writing | evidence-role outline and claim-evidence-boundary table |
| Figure planning | materials-figure | study flow, mechanism map, evidence heatmap, dosage window, caption_boundary |
| Reviewer Simulation | materials-reviewer | two-reviewer report plus weakness-routing rows |
| Revision loop | routed companion skills | fixed artifacts and regression_check updates |
| Submission Fit | materials-research | journal-fit note, missing official-source verification, submission checklist |

The WER-EA mini-review route must separate performance evidence, direct
mechanism evidence, inferred mechanism, durability/service evidence, and missing
field evidence.

For filled
revision-loop proof artifacts, see
`../_shared/paper-production/examples/wer-ea-mini-review-weakness-routing.csv`
and `../_shared/paper-production/examples/wer-ea-mini-review-gate-report.md`.

## Route B: Experimental Manuscript

Use this route for an experimental manuscript on WER-EA bonding performance,
test-matrix planning, results-to-discussion work, or manuscript planning from
experimental data.

| Phase | Route to | Required output |
|---|---|---|
| Hypothesis and claim map | materials-research | research question, independent/dependent variables, controls, expected claim |
| Standards and conditions | materials-reader; materials-data | test standards, curing/conditioning, replicate definition, metadata |
| Data package | materials-data | raw/processed data map, FAIR package manifest, data availability boundary |
| Figure/table plan | materials-figure | figure_contract, source data needs, uncertainty display, caption_boundary |
| Manuscript draft | materials-writing | section plan, claim-evidence-boundary table, draft sections |
| Claim-strength audit | materials-polishing | evidence_level-aware wording and overclaim notes |
| Reviewer Simulation | materials-reviewer | two-reviewer report plus weakness-routing rows |
| Submission Fit | materials-research | journal-fit note and live-verification placeholders |

Experimental manuscript routing must not promote performance improvement to
mechanism proof without chemical, microstructural, rheological, or interface
evidence.

## Route C: Submission Package

Use this route for cover-letter drafting, highlights, graphical abstract
planning, declaration checks, or final packaging for submission.

| Phase | Route to | Required output |
|---|---|---|
| Journal fit confirmation | materials-research | target journal family, article type, live-verification placeholders, submission checklist |
| Manuscript package audit | materials-writing; materials-polishing | title, abstract, highlights, keywords, claim-strength-safe summary |
| Figure and graphical abstract intake | materials-figure | figure package status, caption_boundary check, graphical abstract concept |
| Data and declaration boundary | materials-data | data availability boundary, FAIR package status, declaration inputs |
| Reviewer-risk regression | materials-reviewer; materials-response | unresolved weakness rows, revision proof, final reviewer-risk note |
| Final assembly | materials-submission | `submission-package/` with `submission-package.yaml`, human-readable `MANIFEST.md`, generated artifacts, input statuses, and final missing-input list |

Submission-package routing must keep live journal facts explicit. If scope,
formatting, article type, declarations, or checklist items depend on current
publisher guidance, mark them for live verification instead of guessing.

Route C is implemented by `materials-submission`. When the user asks for
cover-letter drafting, highlights, submission checklist, or final package
assembly, route to `materials-submission` instead of duplicating the
assembly logic in `materials-research`.

## Paper-Level Quality Gates

Use `../_shared/paper-production/paper-gate-report-template.md` for the report.

| gate_id | gate_name | Blocking question | Failure route |
|---|---|---|---|
| G1 | Literature Coverage | Are search strategy, screening criteria, source quality, recent literature, and citation roles documented? | materials-citation |
| G2 | Source Anchoring | Does each major claim have page/section/figure/table anchors and original excerpts? | materials-reader |
| G3 | Mechanism Boundary | Are measured, inferred, speculative, and missing mechanism links separated? | materials-reader; materials-citation |
| G4 | Figure And Table Integrity | Do figure_handoff, caption_boundary, source_anchor, and text references align? | materials-figure |
| G5 | Manuscript Logic | Does the draft follow an argument chain rather than a paper list? | materials-writing |
| G6 | Reviewer Simulation | Are reviewer risks prioritized, routed, fixed, and regression-checked? | materials-reviewer |
| G7 | Submission Fit | Are journal scope, article type, cover letter, highlights, and declarations checked with live verification where needed? | materials-research |

## Weakness Routing

Use `../_shared/paper-production/weakness-routing.md` and
`../_shared/paper-production/weakness-routing-template.csv`.

Required workflow:

1. Convert each failed gate or reviewer concern into one weakness row.
2. Set `route_to` to the responsible skill or skills.
3. Name the `expected_artifact` that proves the fix.
4. Keep `status=open` until the routed skill produces a fix.
5. Set `status=regression-checked` only after the original gate or reviewer
   concern is rechecked.

## Default Output Shape

For a paper-production request, return:

- route line,
- current paper_stage / workflow_mode / output_package,
- required artifacts already available,
- blocked gates and missing inputs,
- weakness-routing rows to create or update,
- next skill and exact expected artifact,
- reviewer-risk note.
