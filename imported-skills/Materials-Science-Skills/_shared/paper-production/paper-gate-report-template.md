# Paper Gate Report

Use this table for the paper-level quality gate report. Keep one row per gate.

| gate_id | gate_name | status | evidence_checked | missing_inputs | routed_weakness_ids | next_skill | reviewer_risk |
|---|---|---|---|---|---|---|---|
| G1 | Literature Coverage | blocked | search strategy; screening criteria; source quality; recent literature; citation roles | screened source list | W001 | materials-citation | Literature gap may make novelty and evidence coverage look weak. |
| G2 | Source Anchoring | blocked | source_map.json; page anchors; figure/table anchors; original excerpts | full reader package | W002 | materials-reader | Unsupported claims may survive into the draft. |
| G3 | Mechanism Boundary | blocked | measured; inferred; speculative; missing mechanism links | mechanism evidence table | W003 | materials-reader; materials-citation | Mechanism narrative may exceed actual evidence. |
| G4 | Figure And Table Integrity | blocked | figure_handoff; caption_boundary; source_anchor; text references | figure contract | W004 | materials-figure | Captions may overstate or visually imply unsupported certainty. |
| G5 | Manuscript Logic | blocked | argument chain; section transitions; contribution/gap alignment | claim-evidence-boundary table | W005 | materials-writing | Draft may read as a paper list rather than a review argument. |
| G6 | Reviewer Simulation | not_applicable | two-reviewer report; cross-review synthesis; routed weaknesses | manuscript draft | W006 | materials-reviewer | Reviewer risks are not yet independently pressure-tested. |
| G7 | Submission Fit | not_applicable | journal scope; article type; cover letter; highlights; declarations | target journal and final package | W007 | materials-research | Journal mismatch or stale author-guide facts may remain. |

Allowed `status` values: `pass`, `fail`, `blocked`, `not_applicable`.
