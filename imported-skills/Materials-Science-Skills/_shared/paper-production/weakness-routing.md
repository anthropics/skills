# Paper Production Weakness Routing

Use this shared route map when a materials paper-production workflow finds
a reviewer weakness, self-review risk, or paper-level gate failure. The route
does not fix the manuscript by itself; it names the responsible skill, required
artifact, and regression check so the next step is explicit.

## Required Row Contract

Every weakness-routing row must include these fields:

`weakness_id, source, severity, weakness_type, evidence_gap, route_to, required_fix, expected_artifact, status, regression_check`

Allowed `severity` values are `critical`, `major`, and `minor`.

Allowed `status` values are `open`, `routed`, `fixed`, `blocked`, and
`regression-checked`.

## Default Route Map

| Weakness type | Route to | Required fix | Expected artifact |
|---|---|---|---|
| citation coverage too narrow | materials-citation | Run targeted search, source quality audit, and citation matrix update. | updated citation matrix |
| recent {material_domain} literature missing | materials-citation | Run recent-year {material_domain} search and update screening criteria. | recent-source addendum |
| mechanism evidence too speculative | materials-reader; materials-citation | Rebuild claim-evidence-mechanism-boundary rows and mark missing evidence. | mechanism evidence table |
| source anchor missing | materials-reader | Add page, section, figure, table, original excerpt, and confidence label. | source_map update |
| manuscript reads like paper list | materials-writing | Rebuild section logic around evidence roles and review questions. | revised argument chain |
| claim strength exceeds evidence | materials-polishing | Downgrade causal or novelty wording using evidence_level and weakness route. | polished claim-strength note |
| figure caption overclaims mechanism | materials-figure | Rewrite caption_boundary and link panels to source_anchor and figure_handoff rows. | revised figure contract |
| experimental variables unclear | materials-research; materials-data | Rebuild variables, controls, conditions, standards, and metadata. | test matrix and data manifest |
| reviewer response lacks proof of change | materials-response | Add point-by-point action, manuscript location, evidence basis, and revision proof. | response package row |

## Gate Interaction

Paper-level gates should emit one or more weakness-routing rows when they fail
or become blocked. The `routed_weakness_ids` field in
`paper-gate-report-template.md` links the gate report back to this table.

## Regression Rule

A weakness is not done when a skill produces a draft fix. It is done only after
the original gate or reviewer concern is rechecked and the row status becomes
`regression-checked`.
