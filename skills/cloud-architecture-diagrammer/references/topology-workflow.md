# Topology and artifact interface

Use [domain-contract.json](domain-contract.json) for required graph fields
and [icon-policy.md](icon-policy.md) for provider assets. The locally supplied
common tooling is canonical; packaging includes it in each independent
bundle. Never depend on a sibling skill's files or duplicate the renderer.

## Project the common model

`EstimateModel.inventory` is the identity source of truth. Reuse inventory
`id`, `component` and `environment`; join architecture `provider` and
recorded zone/state using the same component ID. Record zone, source IDs,
state and optional labels in inventory/architecture notes because the
common rows do not have typed zone/evidence columns. Unknown zone/state is
explicit, not silently filled with a presumed production boundary.

Supply the canonical renderer an object with `nodes` and `edges` lists:

```json
{
  "nodes": [
    {"id": "COMP-01", "component": "Application", "environment": "Target", "zone": "Private", "provider": "", "icon": ""},
    {"id": "COMP-02", "component": "Database", "environment": "Target", "zone": "Private", "provider": "", "icon": ""}
  ],
  "edges": [
    {"id": "FLOW-01", "source": "COMP-01", "target": "COMP-02", "label": "Authenticated database traffic"}
  ]
}
```

This is a synthetic interface example, not a verified deployable topology.
Edge evidence belongs in common source records: use source ID `FLOW-01`
or a documented link in source notes and describe observation/assumption,
protocol, purpose and trust boundary. Additional flow details are kept in
sources, not passed as fields that the renderer will discard. Edges are
explicit directed relationships; source-to-target service mapping is a
migration correspondence, not automatically a network edge.

Check set equality between inventory IDs and node IDs before rendering.
The workbook builder enforces this equality; standalone rendering enforces
graph identity and endpoints but does not receive the separate inventory.
Perform the inventory check explicitly for standalone exports. Include
external users, registries, DNS or third-party endpoints in the inventory
when they appear in the graph. Reject duplicate IDs and unknown endpoints.
For an empty inventory report zero nodes and why; do not treat a blank graph
as evidence that live infrastructure is absent.

## Check semantic topology

Trace each required flow through its actual hosting and control boundary.
Check ingress filtering, identity, transport, public/private exposure,
backup destinations, replication and recovery paths. A valid graph can
still show a control that never protects the user path; turn that defect
into a visible issue and a corrected/priced alternative. Keep uncertain
flows in the source/risk register until supported; draw no assumed edge as
an observed fact. Separate current, migration and target models when their
flows differ; do not overlay incompatible architectures in one estimate.

## Produce and reconcile artifacts

The canonical `render_diagram` takes graph, distinct SVG and PNG output paths
and an optional local icon pack. The canonical `build_workbook` receives the
same graph through its `architecture` argument and optional `icon_pack`.
It embeds the PNG, writes node/flow ranges and stores the diagram manifest
in `03_Architecture`. Preserve `DiagramManifest.to_dict()` with any exports;
it records relative icon paths and hashes without local private paths.

Reopen the XLSX and check embedded PNG bytes against the manifest hash,
node/edge IDs against the verified graph, and icon notices against the
chosen pack. Independently inspect SVG, PNG and workbook image legibility.
Deterministic bytes are guaranteed only within the same runtime, image
library version and rendering fonts; report those versions when comparing
hashes across environments. Recheck image/hash and cached values after
native spreadsheet recalculation. Report node/edge counts, unresolved
flow count and fallback warnings explicitly, including positive zero
markers; a successful command alone is insufficient artifact evidence.
