# WER-EA Mini-Review Gate Report Example

This filled example shows how the WER-EA mini-review route can remain blocked
at source anchoring and mechanism-boundary stages while still keeping the next
skill and proof artifact explicit.

| gate_id | gate_name | status | evidence_checked | missing_inputs | routed_weakness_ids | next_skill | reviewer_risk |
|---|---|---|---|---|---|---|---|
| G1 | Literature Coverage | pass | search strategy, screening criteria, source quality notes, and recent-year coverage are recorded in `citation_handoff.csv` | none | none | materials-citation | coverage risk is controlled if recent-year updates continue |
| G2 | Source Anchoring | blocked | 18 papers are anchored in `source_map.json`, but 12 mechanism claims still lack page-level anchors | rebuilt `reader-package/source_map.json` for the missing papers | W-G2-001 | materials-reader | unsupported mechanism synthesis may survive into drafting |
| G3 | Mechanism Boundary | blocked | performance evidence, direct mechanism evidence, and inferred mechanism are partially separated | completed `claim-evidence-boundary table` with measured/inferred/speculative tags | W-G3-001 | materials-reader; materials-citation | review narrative may still overstate mechanism certainty |
| G4 | Figure And Table Integrity | fail | figure intake exists and source anchors exist, but the mechanism-map caption is still too strong | caption rewrite tied to `figure_handoff.csv` and `caption_boundary` | W-G4-001 | materials-figure | reviewers may reject the figure for overstating chemical interpretation |
| G5 | Manuscript Logic | blocked | evidence-role outline exists but argument transitions still depend on missing mechanism-boundary cleanup | revised claim-evidence-boundary table | W-G3-001 | materials-writing | the draft may collapse back into a paper list |
| G6 | Reviewer Simulation | pass | reviewer risk loop ran once and the wording fix was rechecked | none | W-G6-001 | materials-polishing | residual wording risk is controlled after downgrade |
| G7 | Submission Fit | not_applicable | journal fit can be postponed until the review package clears G2-G5 | target journal family and live author-guide verification | none | materials-research | current package is not ready for final journal targeting |

Allowed `status` values: `pass`, `fail`, `blocked`, `not_applicable`.
