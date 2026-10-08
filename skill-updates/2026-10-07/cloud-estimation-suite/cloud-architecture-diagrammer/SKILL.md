---
name: cloud-architecture-diagrammer
description: Draw cloud topology from a structured inventory and evidenced flows, verify architecture before estimate finalisation, and export SVG and PNG with XLSX embedding. Use for inventory-consistent architecture diagrams and documented neutral or official-provider icon provenance.
---

# Cloud architecture diagrammer

**Created by the repository maintainers.** This open-source skill provides
generic architecture diagram methodology without client-specific inputs.

**Licence:** CC BY 4.0. Share and adapt for any purpose with credit to the
repository maintainers. Include the full licence in the distributed bundle;
provider icon rights remain separate.

**Feedback & support:** Route methodology feedback to the maintainer contact
that distributed the suite; use a public issue tracker only once one exists.
Correct execution mistakes before proposing methodology changes.

Produce topology records in the common `EstimateModel`, SVG and PNG exports,
and a validated XLSX primary deliverable with the PNG in `03_Architecture`.
For a consolidated estimate, return the graph and records for the common
merge. Keep all twelve sheets; mark irrelevant sections `Non applicable`
with a reason. Express scoped drawing/verification effort in JH (jour-homme),
with eight hours per JH editable. Keep Build, monthly Run and provider costs
separate; drawing a component does not establish its price or delivery JH.

## Verify topology before finalising the estimate

Read [references/topology-workflow.md](references/topology-workflow.md)
for the graph-to-workbook interface and verification order. Read
[references/domain-contract.json](references/domain-contract.json) for
graph fields, common bindings and artifact requirements. Read
[references/icon-policy.md](references/icon-policy.md) when selecting icons,
including the provider-neutral default.

Use the same structured inventory and explicit flow data as the workbook.
Classify nodes as live, partially deployed, planned or unknown; use
authorised read-only evidence for live topology. Missing access yields a
measurement instrument and blocking task, not inferred network connectivity.
Retain contradictions between documentation and observed state as decisions.

Draw before estimate finalisation. Trace user ingress, service calls, data,
backup/recovery, delivery and management flows across environment, zone and
provider boundaries. A table can describe a security control and a hosting
location independently; the topology must show that traffic actually passes
through the control. Check functional compatibility and protection scope,
not only that both endpoints exist. An untraceable or incompatible flow
becomes an explicit risk, assumption or priced decision branch. Do not
finalise an affected recommendation until its unresolved status is visible.

Preserve stable inventory IDs for nodes and stable flow IDs for directed
edges. Include external actors and third-party services in the inventory.
Require unique IDs, exact node coverage of the model's inventory and known
source/target node IDs for every edge. Reject dangling flows and nodes absent
from inventory before generating final artifacts. Keep flow evidence in
source records keyed by flow ID or explicitly linked in notes; do not guess
edges from node order or proximity. Put source evidence, state and optional
detail in common notes rather than inventing unsupported model columns.

## Render once from the verified graph

Use the locally supplied canonical common renderer and workbook builder,
not a separate drawing implementation. Pass the same graph to both exports
and the builder. Preserve the returned manifest's node IDs, edge IDs,
icon sources, icon provenance, output hashes and warnings. Neutral labelled
symbols are the default. Official packs require recorded provenance and
applicable redistribution/trademark terms; missing or unverified assets
fall back to neutral symbols with the warning retained.

For alternative topologies use separate complete models and labelled
artifacts; the common model has no architecture branch selector. Preserve
`Economique`, `Standard` and `Resilient` scenarios with equal service scope.
Reconcile existing drawing/verification coverage before adding JH; return
risks and decisions to their domain owner without double counting remediation.
Use the common recalculation adapter and validator, then inspect the finished
image and workbook for legibility, clipping, crossed nodes, hidden flows and
meaningful boundary labels. Keep formulas and cached values intact.

Read [references/common-methodology.md](references/common-methodology.md) when
constructing the complete model or using the local workbook runtime.

## Pre-delivery gate

Re-read these rules and references against the final artifacts. Record
pass/fail and counts for these checks:

- Exact inventory/node coverage, unique IDs and resolved directed endpoints;
  every evidenced flow is retained and every unsupported flow is visible
  as an issue. Verification happened before estimate finalisation.
- SVG, PNG, embedded image, node/flow tables and manifest describe the same
  graph. Reopen XLSX and verify embedded PNG hash against the manifest.
- Provider pack provenance and notices survive export and embedding;
  neutral fallbacks and renderer warnings are reported explicitly.
- Relevant JH, scenarios, costs, phasing, prose and workbook synthesis
  reconcile. Reopen recalculated XLSX in formula and values modes, scan
  errors and report the engine and cache status.
- Sweep public files and examples, jointly, for identifying names, domains,
  accounts, IPs, paths, traceable topology, dates and copied amounts.
  Report findings count and remove traceable data. Resolve links from their
  containing document; verify resources, full CC BY licence and separate
  icon rights in the clean multi-file `.skill` archive before public delivery.
