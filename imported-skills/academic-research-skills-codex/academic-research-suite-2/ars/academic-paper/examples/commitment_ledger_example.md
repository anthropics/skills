# Commitment Ledger Worked Example (Kong A1 / v3.11)

This example traces three reviewer comments through the Schema 11 commitment ledger — from `revision_coach_agent` Step 3.5 extraction through revision execution and re-review verification per the new fulfillment-verification step.

> Companion to `revision_recovery_example.md`. Where that example focuses on RESOLVED/UNRESOLVABLE *outcomes*, this one focuses on per-promise *lifecycle*.

## Setup

Reviewer R1 raises three comments on a manuscript about CNN ablations on small image datasets:

- **R1-1:** "Please add an ablation on CIFAR-100 and clarify why ResNet-50 was preferred over Vision Transformer."
- **R1-2:** "Discussion should acknowledge the recent Patel 2025 baseline."
- **R1-3:** "It would strengthen the paper to include error bars across 5 seeds."

## Step 3.5 output: commitment_extracted (per revision_coach_agent)

```yaml
- concern_id: R1-1
  original_comment: "Please add an ablation on CIFAR-100 and clarify why ResNet-50 was preferred over Vision Transformer."
  commitment_extracted:
    - commitment_text: "add ablation on CIFAR-100"
      commitment_type: add_experiment
      required_evidence_type: new_table
    - commitment_text: "clarify why ResNet-50 was preferred over Vision Transformer"
      commitment_type: add_clarification
      required_evidence_type: discussion_paragraph

- concern_id: R1-2
  original_comment: "Discussion should acknowledge the recent Patel 2025 baseline."
  commitment_extracted:
    - commitment_text: "acknowledge Patel 2025 baseline in Discussion"
      commitment_type: add_citation
      required_evidence_type: new_citation

- concern_id: R1-3
  original_comment: "It would strengthen the paper to include error bars across 5 seeds."
  commitment_extracted:
    - commitment_text: "add error bars from 5-seed runs"
      commitment_type: add_experiment
      required_evidence_type: new_figure
```

Note R1-1 split into two commitments — compound comments decompose per Step 3.5 procedure.

## After revision: author fills fulfillment_status + rationale (nested per commitment)

The lifecycle fields are appended **inside each commitment object** (not as separate parallel lists). A `fulfilled` commitment carries `fulfillment_status` only — no `unfulfilled_rationale` placeholder.

```yaml
- concern_id: R1-1
  revision_location: "§4.3 Table 4; §5.2 ¶3"
  commitment_extracted:
    - commitment_text: "add ablation on CIFAR-100"
      commitment_type: add_experiment
      required_evidence_type: new_table
      fulfillment_status: fulfilled
    - commitment_text: "clarify why ResNet-50 was preferred over Vision Transformer"
      commitment_type: add_clarification
      required_evidence_type: discussion_paragraph
      fulfillment_status: fulfilled

- concern_id: R1-2
  revision_location: "§5.4 ¶1"
  commitment_extracted:
    - commitment_text: "acknowledge Patel 2025 baseline in Discussion"
      commitment_type: add_citation
      required_evidence_type: new_citation
      fulfillment_status: fulfilled

- concern_id: R1-3
  revision_location: "§4.3 Table 4 footnote"
  commitment_extracted:
    - commitment_text: "add error bars from 5-seed runs"
      commitment_type: add_experiment
      required_evidence_type: new_figure
      fulfillment_status: partial
      unfulfilled_rationale: "Computational budget allowed 3 seeds rather than 5; standard errors reported in Table 4 footnote. Five-seed replication acknowledged as future work in §6 Limitations."
```

## Re-review output: COMMITMENT_GAP surface (per re_review_mode_protocol step 5)

The re-reviewer walks each commitment_extracted entry:

- **R1-1, both commitments:** locate §4.3 Table 4 (new ablation table) + §5.2 ¶3 (ResNet vs ViT rationale) — both present and substantive. Status confirmed `fulfilled`.
- **R1-2:** locate §5.4 ¶1 — Patel 2025 cited. Status confirmed `fulfilled`.
- **R1-3:** locate §4.3 Table 4 footnote — finds 3-seed error bars + future-work acknowledgment in §6 Limitations. Author status `partial` is internally consistent (rationale form (c) "deferred to future work"). **No `COMMITMENT_GAP` surfaced** — rationale is present and one of the three valid forms.

## Contrast: a case that DOES surface COMMITMENT_GAP

If R1-3 instead had:
```yaml
- concern_id: R1-3
  revision_location: "§4.3 Table 4"
  commitment_extracted:
    - commitment_text: "add error bars from 5-seed runs"
      commitment_type: add_experiment
      required_evidence_type: new_figure
      fulfillment_status: not-fulfilled
      # unfulfilled_rationale absent on a not-fulfilled commitment — Schema 11 validation flags this
```

…the re-reviewer would surface:

> **COMMITMENT_GAP** (R1-3): commitment "add error bars from 5-seed runs" status not-fulfilled with no rationale. Author must provide one of: done-elsewhere pointer, rejection reasons, or future-work acknowledgment before final submission.

This is **advisory** — final responsibility rests with the author. Re-review does not block submission; it surfaces the gap so the author can act.

## Granular and uncategorizable evidence: `prose_edit` and `other`

The seven structural manuscript-evidence types cover the typical experiment / clarification / citation / restructure cases. Two further values handle the long tail of reviewer comments that would otherwise be misclassified or silently dropped:

Suppose R2 raises two more comments:

- **R2-1:** "Fix the typo in the definition of *consistency* on page 4 and correct the equation formatting in §3.2."
- **R2-2:** "The submission feels incomplete somewhere in the framing, please tighten it."

```yaml
- concern_id: R2-1
  original_comment: "Fix the typo in the definition of consistency on page 4 and correct the equation formatting in §3.2."
  commitment_extracted:
    - commitment_text: "fix typo in 'consistency' definition, p.4 (other: copy-edit, no structural change)"
      commitment_type: other
      required_evidence_type: prose_edit
    - commitment_text: "correct equation formatting in §3.2 (other: formatting fix, no structural change)"
      commitment_type: other
      required_evidence_type: prose_edit

- concern_id: R2-2
  original_comment: "The submission feels incomplete somewhere in the framing, please tighten it."
  commitment_extracted:
    - commitment_text: "tighten framing (reviewer unspecified — clarify location at re-review)"
      commitment_type: other
      required_evidence_type: other
```

R2-1's two commitments use `prose_edit`: both are sentence-/equation-level changes too granular to bucket as `methods_paragraph` or `new_section`, yet they ARE manuscript changes (so `acknowledgment_only` would be the wrong semantics). They verify at `revision_location` in the revised manuscript like any other manuscript-evidence type.

R2-2 is genuinely uncategorizable — the reviewer did not name a location or a deliverable. It uses `required_evidence_type: other`. At re-review this surfaces an **`EVIDENCE_TYPE_UNSPECIFIED`** advisory (distinct from `COMMITMENT_GAP`): the re-reviewer cannot pin the evidence and prompts the author to specify where the change landed. If the author populates `revision_location`, the re-reviewer verifies there; if not, the commitment is reported as unverifiable alongside the advisory.

Both values exist because `commitment_type` already carries an `other` escape hatch — without the matching `required_evidence_type` values, the agent's instruction to "extract commitments from every parsed comment" would force a typo fix into `methods_paragraph` (wrong) or omit it entirely (violates the every-comment rule).

## Why this matters (Kong §7.4.3 anchor)

Per Kong et al. 2026 §7.4.3, ICLR 2025 [21] documents a measurable commitment-fulfillment gap: persuasive rebuttal text + matrix saying "Verified: Y" can still hide that the actual experiment was not run. The commitment ledger forces per-promise lifecycle traceability — extracted promises, classified outcomes, mandated rationale — closing the gap at the artifact level instead of relying on reviewer vigilance.

---
**See also:** `revision_recovery_example.md`, `shared/handoff_schemas.md` Schema 11, `academic-paper-reviewer/references/re_review_mode_protocol.md` step 5.
