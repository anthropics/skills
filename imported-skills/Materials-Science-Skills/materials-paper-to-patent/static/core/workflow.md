# Patent Routing Workflow

1. Read the manifest and default core.
2. Apply profile-first routing and detect source format, task mode, and
   invention type.
3. Identify every source file and create stable P/E/F/C source IDs.
4. Stop if the substantive source cannot be inspected.
5. Load the selected source, task, and invention fragments from the manifest.
6. For disclosure analysis, build the source map, inventories, and evidence
   ledger without drafting claims.
7. Before any formal claim, load the patent knowledge base, detailed stage
   gates, and claim checklist.
8. Before a full package, also load the output contract and draft schema.
9. Exclude unsupported features from formal claims and turn
   needs-confirmation features into inventor questions.
10. Run the declared validators and emit the patent draft handoff.
