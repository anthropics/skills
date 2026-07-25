# Example: `cross_paper_tensions[]` for a literature synthesis (#262)

A documentation example (not an executable fixture) showing how the `synthesis_agent` emits a `cross_paper_tensions[]` inventory in its Step 3b / Contradictions & Resolutions section, and how a scholar reads it. The corpus is a fictional review of *"remote-work productivity"*, with six papers.

Reference: `deep-research/agents/synthesis_agent.md` (Step 3b — Cross-Paper Tension Inventory). The inventory is a **prose contract** — there is no JSON Schema or lint behind it (mirroring the #214 / #261 prose-layer decision, not the #213 schema-layer one): the producer (`synthesis_agent`) and the readers (the scholar, plus the downstream report/integrity LLM agents) all read prose, so machine-validating the YAML shape would prove field presence, not contradiction fidelity.

---

## The inventory block (in the Synthesis Report)

```yaml
cross_paper_tensions:
  # Case 1 — genuine contradiction, left unresolved (flagged for the scholar)
  - pair_id: CP-001
    paper_a: "alvarez2024"
    paper_b: "becker2023"
    candidate_basis: "shared RQ subtopic; opposite finding direction"
    overlap_topic: "effect of fully-remote work on individual task productivity"
    a_finding: "Fully-remote engineers showed a 13% productivity gain vs. office baseline."
    a_evidence_pointer: "Alvarez 2024, Results Table 3 (n=412, within-subject)"
    b_finding: "Fully-remote staff showed an 8% productivity decline vs. office baseline."
    b_evidence_pointer: "Becker 2023, §5.2 (n=1,030, cross-sectional survey)"
    pair_assessment: "contradiction"
    resolution_status: "flagged_unresolved"
    scholar_confirmation: "pending"

  # Case 2 — conditional difference (not a true contradiction), resolved in synthesis
  - pair_id: CP-002
    paper_a: "alvarez2024"
    paper_b: "okafor2025"
    candidate_basis: "shared construct/outcome/measure; bibliographic coupling"
    overlap_topic: "remote-work productivity by task type"
    a_finding: "Net productivity gain for fully-remote engineers."
    a_evidence_pointer: "Alvarez 2024, Results Table 3"
    b_finding: "Productivity loss for fully-remote roles requiring frequent synchronous coordination."
    b_evidence_pointer: "Okafor 2025, §4.3 (moderation by coordination intensity)"
    pair_assessment: "conditional_difference"
    resolution_status: "resolved_in_synthesis"
    resolution_pointer: "Synthesis Report > Contradictions & Resolutions, ¶2"
    scholar_confirmation: "pending"

  # Case 3 — checked but no material conflict (documents coverage, not an obligation)
  - pair_id: CP-003
    paper_a: "becker2023"
    paper_b: "dubois2024"
    candidate_basis: "shared RQ subtopic"
    overlap_topic: "self-reported remote-work satisfaction"
    a_finding: "Higher satisfaction among remote staff."
    a_evidence_pointer: "Becker 2023, §6.1"
    b_finding: "Higher satisfaction among remote staff (consistent magnitude)."
    b_evidence_pointer: "Dubois 2024, Fig. 2"
    pair_assessment: "no_material_conflict"
    resolution_status: "not_applicable"
    scholar_confirmation: "pending"

  # Case 4 — topics touch but evidence does not actually meet (insufficient overlap)
  - pair_id: CP-004
    paper_a: "okafor2025"
    paper_b: "dubois2024"
    candidate_basis: "shared RQ subtopic"
    overlap_topic: "remote work and productivity"
    a_finding: "Productivity moderated by coordination intensity (objective task metrics)."
    a_evidence_pointer: "Okafor 2025, §4.3"
    b_finding: "Satisfaction outcomes only; no productivity measure reported."
    b_evidence_pointer: "Dubois 2024, §2 (scope statement)"
    pair_assessment: "insufficient_overlap"
    resolution_status: "not_applicable"
    scholar_confirmation: "pending"

  # Case 5 — real conditional difference the synthesis noticed but did NOT yet reconcile
  - pair_id: CP-005
    paper_a: "becker2023"
    paper_b: "nguyen2022"
    candidate_basis: "shared construct/outcome/measure; opposite finding direction"
    overlap_topic: "productivity effect of remote vs. hybrid schedules"
    a_finding: "Fully-remote staff showed an 8% productivity decline."
    a_evidence_pointer: "Becker 2023, §5.2"
    b_finding: "Hybrid-schedule staff showed a 5% productivity gain; the schedule type is the apparent moderator."
    b_evidence_pointer: "Nguyen 2022, §4.1 (remote vs. hybrid split)"
    pair_assessment: "conditional_difference"
    resolution_status: "flagged_unresolved"
    scholar_confirmation: "pending"
```

**Coverage Note**: 6 papers in corpus (`alvarez2024`, `becker2023`, `okafor2025`, `dubois2024`, `nguyen2022`, `silva2025`); 5 candidate pairs considered (basis among the candidate-edge signals: shared RQ subtopic / shared construct / opposite finding direction / bibliographic coupling). This is a **scoped advisory scan, not complete pairwise contradiction detection** — the full corpus has 15 possible pairs; 10 were not exhaustively checked. In particular, `silva2025` (a manager-perception study) sits in a different topic neighborhood and was not paired against the productivity studies, and most `silva2025`/`nguyen2022` cross-pairs were not enumerated; a genuine tension among the unchecked pairs may exist and is **not claimed absent**. Bibliographic coupling was used as an inclusion signal only — low-coupling cross-camp pairs were not excluded on that basis. Scholar confirms each `resolution_pointer` and may flag additional cross-pairs.

---

## How a scholar (and the downstream report) reads each case

### Case 1 — `CP-001` (genuine contradiction, unresolved)
The two papers speak to the **same** outcome (individual task productivity under fully-remote work) and report **opposite directions** (+13% vs. −8%). The orthogonal axes carry distinct information: `pair_assessment: contradiction` says the conflict is real (not a definitional or scope artifact), while `resolution_status: flagged_unresolved` says the synthesis did **not** reconcile it. Because it is unresolved, there is **no `resolution_pointer`** — the agent must not invent one. The evidence pointers expose the most likely lever: Alvarez is within-subject (n=412), Becker is a cross-sectional survey (n=1,030); a scholar can see the design difference without re-reading both papers. `scholar_confirmation: pending` until the scholar decides whether to reconcile, present both, or weight by design.

### Case 2 — `CP-002` (conditional difference, resolved)
This is the axis-orthogonality payoff. Naively this looks like another contradiction (gain vs. loss), but `pair_assessment: conditional_difference` records that the divergence resolves on a moderator (coordination intensity) — Okafor's loss is for coordination-heavy roles, which is compatible with Alvarez's net gain. `resolution_status: resolved_in_synthesis` + a **required** `resolution_pointer` send the scholar to the exact paragraph where the synthesis explains the moderator. Had the issue's original single `conflict_type` enum been used, "conditional_difference" and "resolved" would have been forced into one value and the scholar could not tell *whether the difference was real but reconciled* from *whether it was never a real conflict*.

### Case 3 — `CP-003` (no material conflict)
A pair can be **listed without being a contradiction**. Becker and Dubois both find higher remote satisfaction at consistent magnitude. Recording it as `no_material_conflict` / `not_applicable` documents that the pair **was checked** (coverage), without manufacturing a tension. This mirrors #214's discipline that a checked-but-clear position is not opposition.

### Case 4 — `CP-004` (insufficient overlap)
The topics touch ("remote work") but the **evidence does not meet**: Okafor reports productivity, Dubois reports only satisfaction. `insufficient_overlap` records that the pair was considered and set aside because there is no shared measured construct to contradict — distinct from `no_material_conflict` (where they *do* measure the same thing and agree). Without this value the agent would be pushed to force a verdict on a non-comparison.

### Case 5 — `CP-005` (conditional difference, **un**resolved)
The third legal pairing on the orthogonal axes. Like CP-002 the divergence is a `conditional_difference` (schedule type — remote vs. hybrid — is the apparent moderator, not a true contradiction), but unlike CP-002 the synthesis **noticed it without yet reconciling it**: `resolution_status: flagged_unresolved`, so there is **no `resolution_pointer`** (omitted, exactly as the field rule requires for non-resolved status). CP-002 (`conditional_difference` + `resolved_in_synthesis`) and CP-005 (`conditional_difference` + `flagged_unresolved`) together show that the resolution axis moves independently of the assessment axis — the same conflict nature can be resolved or still open.

### The Coverage Note is load-bearing
The note is not boilerplate — it is the honesty mechanism that makes the recall limitation acceptable. It states the denominator (15 possible pairs), what was skipped (10), and names the paper in another neighborhood that was **not** paired. This is why the inventory may ship as a scoped scan: it never says "all contradictions addressed." Remove the note and the same block would be an overclaim.

---

## Cross-reference

- **#214** — sub-claim inventory before consensus in editorial synthesis (within-review version of "enumerate before asserting addressed"). #262 mirrors its prose-layer scope decision (no schema/lint/fixture).
- **#261** — figure/table fidelity trace (the figure version of the same enumerate-before-assert discipline), also prose-layer.
- **#213** — claim-audit sub-claim decomposition; got schema+lint only because it has a deterministic machine consumer. #262 does not, so it stays prose.
- **`devils_advocate_agent`** — stress-tests a single argument adversarially; it does **not** enumerate pairwise paper conflicts. Different scope; untouched.
- **Kong et al. (2026) §7.4.2** (L. Kong, "Roadmap & User Guide", arXiv:2605.18661) — the originating finding: research-synthesis systems summarize individual papers well but still struggle with multi-paper relational reasoning and cross-paper contradictions.
