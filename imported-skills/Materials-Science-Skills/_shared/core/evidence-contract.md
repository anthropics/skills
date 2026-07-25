# Evidence Contract

Every output must protect the link between claim and evidence.

## Claim-evidence ladder

For each major claim, identify:

- Claim: the sentence or conclusion.
- Evidence: test, figure, table, citation, or observation.
- Mechanism: what explains the evidence.
- Boundary: conditions where the claim may not hold.
- Missing input: what the author must provide before submission.

Use this audit table when checking drafts:

| Claim type | Minimum support |
|---|---|
| Performance improvement | Control group, dosage, test condition, quantitative result, variability if available |
| Mechanism | FTIR/XPS/SEM/AFM/fluorescence/thermal/rheology or equivalent direct evidence |
| Durability | Water, temperature, ageing, freeze-thaw, chemical, UV, traffic, or service-condition stress |
| Sustainability | Functional unit, comparison boundary, material source, energy/carbon/waste logic, and explicit tradeoff/limitation language |
| Engineering applicability | Workability, storage stability, constructability, curing, cost, compatibility, or field constraints |
| Data interpretation | Control comparison, test condition, unit, replication/variability, figure-to-claim mapping |

## Missing evidence language

If evidence is absent, use visible flags:

- `[needs quantitative result]`
- `[needs control group]`
- `[needs mechanism evidence]`
- `[needs functional unit or LCA boundary]`
- `[needs carbon factor or waste-processing evidence]`
- `[needs live journal verification]`
- `[confirm with supervisor/co-authors]`

## Anti-overclaim rules

Prefer:

- "indicates", "suggests", "is consistent with", "may be attributed to"

Avoid unless proven:

- "proves", "completely solves", "universal", "first", "green material", "field-ready"

For sustainability language:

- Do not use "green", "low-carbon", or "sustainable" from waterborne chemistry, waste use, or recycled content alone.
- If no complete LCA exists, label any estimate as a screening calculation and define the functional unit.
- If only durability or bonding data exist, phrase environmental value as a service-life hypothesis requiring verification.

For review articles, distinguish:

- consensus in the literature,
- competing explanations,
- methods used to measure the phenomenon,
- knowledge gaps,
- proposed future work.

For experimental articles, distinguish:

- measured result,
- inferred mechanism,
- practical implication,
- limitation or untested condition.

## Experiment record evidence links

When an `experiment-record.yaml` is available, each entry in its `evidence_links` list maps directly to the claim-evidence ladder above:

- `claim` → the sentence or conclusion.
- `evidence_type` + `figure_or_table` → the evidence.
- `mechanism_evidence` → the mechanism.
- `boundary` → the conditions where the claim may not hold.

Use the record's `evidence_links` to pre-populate an evidence audit table before drafting or reviewing a manuscript. If `mechanism_evidence` is absent, flag `[needs mechanism evidence]` before allowing a mechanism claim in the Discussion.
