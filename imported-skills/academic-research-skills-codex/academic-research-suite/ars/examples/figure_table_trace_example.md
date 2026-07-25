# Example: `figure_table_trace[]` for an ML ablation paper (#261)

A documentation example (not an executable fixture) showing how the visualization_agent emits a `figure_table_trace[]` block and how the integrity_verification_agent's Phase C3 (Figure/Table Caption Fidelity) reads it. The paper is a fictional ablation study, *"Scaling depth in sparse retrievers"*, with three figures and one table.

Reference: `academic-paper/references/vlm_figure_verification.md` (Figure/Table Trace section). The trace is a **prose contract** — there is no JSON Schema or lint behind it (mirroring the #214 prose-layer decision, not the #213 schema-layer one).

---

## The trace block (in the Figure Package)

```yaml
figure_table_trace:
  # Case 1 — normal traced figure, single caption claim, limitation surfaced
  - artifact_id: "fig-1"
    source_data: {dataset_id: "depth-sweep", file: "results/depth_sweep.csv"}
    transformation: {script: "scripts/plot_depth.py", hash: "9f2a4c1"}
    caption_claim: "Retrieval recall@10 increases with encoder depth from 4 to 12 layers."
    supported_manuscript_claims:
      - {claim: "Recall improves with encoder depth over the tested range.", locator: "Results §4.1, ¶2"}
    limitations:
      - "Only depths {4, 8, 12} were run; intermediate depths are not measured."

  # Case 2 — compound caption claim (decomposed by the integrity gate before judging)
  - artifact_id: "fig-2"
    source_data: {dataset_id: "depth-sweep", file: "results/depth_sweep.csv"}
    transformation: {script: "scripts/plot_depth.py", hash: "9f2a4c1"}
    caption_claim: "Deeper encoders improve recall AND reduce variance across the three seeds."
    supported_manuscript_claims:
      - {claim: "Depth improves recall.", locator: "Results §4.1, ¶2"}
      - {claim: "Depth reduces cross-seed variance.", locator: "Results §4.1, ¶3"}
    limitations:
      - "Variance is computed over 3 seeds only; the variance-reduction claim is low-powered."

  # Case 3 — empty limitations → advisory, not silent pass
  - artifact_id: "fig-3"
    source_data: {dataset_id: "latency-bench", file: "results/latency_bench.csv"}
    transformation: "manual derivation: §5.3 paragraph 1 (median over 1000 queries, warm cache)"
    caption_claim: "Inference latency is flat from depth 4 to 12."
    supported_manuscript_claims:
      - {claim: "Depth does not increase inference latency.", locator: "Results §5.3, ¶1"}
    limitations: []

  # Table with a trace entry — same checks apply
  - artifact_id: "table-2"
    source_data: {dataset_id: "depth-sweep", file: "results/depth_sweep.csv"}
    transformation: {script: "scripts/make_table2.py", hash: "9f2a4c1"}
    caption_claim: "Per-depth recall@10 and recall@100 with 95% CIs."
    supported_manuscript_claims:
      - {claim: "Recall improves with encoder depth over the tested range.", locator: "Results §4.1, ¶2"}
      - {claim: "Depth improves recall.", locator: "Results §4.1, ¶2"}
    limitations:
      - "CIs are bootstrap (n=1000); not corrected for multiple comparisons across depths."
```

---

## How Phase C3 reads each case

### Case 1 — `fig-1` (normal, single claim)
- **(1) Trace completeness** — PASS. `{script, hash}` present; data file pointed to.
- **(2) Caption-claim support** — the single claim "recall increases with depth 4→12" follows from `depth_sweep.csv` if the plotted recall is monotone across the three measured depths. Judge against the data, not the rendering.
- **(3) Manuscript-claim linkage (both directions)** — *Forward:* the listed claim ("Recall improves with encoder depth over the tested range", Results §4.1 ¶2) must actually cite Figure 1 and must not say more than the data shows (asserting monotonicity at unmeasured depths would be an overstatement → FAIL). The claim is identified by text + locator, not by an id, because the figure can be produced before the draft's claim manifest exists. *Reverse:* the gate also scans the manuscript for every place it leans on Figure 1 — if §6 Discussion says "Figure 1 shows latency is unaffected" but that use is not in `supported_manuscript_claims`, the one-sided trace is an omission → FAIL (the author cannot quietly drop an unflattering use from the trace).
- **(4) Limitation visibility** — the "{4,8,12} only" limitation must appear in caption Note / Discussion / Limitations. If it does → PASS; if the scholar listed it but the manuscript dropped it → FAIL (blocking).

### Case 2 — `fig-2` (compound claim, decomposed)
The caption_claim is compound, so Phase C3 decomposes it (borrowing #213 *as prose guidance only*):
- sub-claim A: "deeper encoders improve recall"
- sub-claim B: "deeper encoders reduce variance across the three seeds"

Each is judged independently. A common failure: A holds in the data but B is asserted on 3 seeds with overlapping ranges — the caption claims B as established when the data only weakly supports it. A caption supported on A but **not** B is **not fully supported**: the entry takes the verdict of its weakest sub-claim, so the unsupported B routes the whole entry to **FAIL** caption-claim support (not PASS WITH NOTES — partial support is not a clean pass). The two manuscript claims ("Depth improves recall" §4.1 ¶2; "Depth reduces cross-seed variance" §4.1 ¶3) are checked separately for linkage and overstatement.

### Case 3 — `fig-3` (empty limitations)
- **(1)–(3)** judged as above; note the `transformation` here is a **precise manual-derivation pointer** (`§5.3 ¶1, median over 1000 queries, warm cache`) — acceptable. A vague `"computed manually"` would be UNTRACEABLE → FAIL for a claim-bearing artifact.
- **(4) Limitation visibility** — `limitations: []`. The gate does **not** invent a limitation; it emits **`[FIGURE-LIMITATIONS-EMPTY]`** as a named advisory (PASS WITH NOTES). A latency-flat claim with no stated caveats (cache state? hardware? batch size?) is exactly the kind of omission the advisory makes visible without pretending the agent can enumerate every missing caveat.

### `table-2` (table with trace)
Same four checks as a figure. The table is not a figure, but because it has a `figure_table_trace[]` entry the fidelity check applies in full. A standalone table with **no** trace entry would instead surface a trace-unavailable finding.

---

## Cross-reference

- **#213** — sub-claim decomposition before citation judgment (citation-layer half of the §F.3.2 partial-evidence trap). The decomposition idea in Case 2 is borrowed from here as prose guidance only.
- **#214** — sub-claim inventory before consensus in editorial synthesis (synthesis-layer half). #261 mirrors #214's prose-layer scope decision (no schema/lint/fixture).
- **Kong et al. (2026) §3.4** (arXiv:2605.18661) — the originating finding: an AI-generated figure can look professional while its caption/claims do not follow from the data.
