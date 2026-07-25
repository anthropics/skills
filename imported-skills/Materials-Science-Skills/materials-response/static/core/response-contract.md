# Response Row and Package Contract

Each response row contains:

`comment_id, concern_type, strategy, reviewer_comment, response,
manuscript_action, evidence_basis, revision_proof, author_input_needed, status`

Allowed status values are `open`, `blocked`, `drafted`, `revised`, and
`regression-checked`.

`revision_proof` names the verified section, paragraph, figure, table, or line
range. When proof is unavailable, leave it empty, set
`author_input_needed=true`, and use `status=blocked` or `status=drafted`.

A complete package contains a revision summary, point-by-point rows, unresolved
author inputs, and a final regression check. Tone polishing occurs only after
the technical response is evidence-bound.
