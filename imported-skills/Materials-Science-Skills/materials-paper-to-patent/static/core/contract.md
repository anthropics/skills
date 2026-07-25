# Contract

`materials-paper-to-patent` translates inspected source material into
evidence-grounded Chinese invention-patent artifacts. Create stable P/E/F/C
source IDs before formal drafting, and map every claim feature to source
evidence.

Use only `explicit`, `inherent`, `needs-confirmation`, or `unsupported` as
support states. Only `explicit` or `inherent` features are claim-eligible.
Exclude `unsupported` features from formal claims. A `needs-confirmation`
feature blocks its claim mapping and becomes a specific inventor question
outside formal claims until confirmed.

While any `needs-confirmation` item or inventor question remains unresolved,
the overall status must remain `incomplete-draft`; do not assign
`review-draft` or completed package status.
Normalize prose `incomplete draft` to canonical status `incomplete-draft`;
never emit `incomplete draft` as a status or any alternate enum value.

Do not invent experimental evidence, implementation details, inventorship,
ownership, filing or priority facts, publication dates, prior-art conclusions,
legal sufficiency, or official CNIPA outcomes.

When missing evidence, inventor facts, validation errors, or quality-threshold
gaps block a complete package, preserve the gaps and label the result
`incomplete-draft`.
