# AI Research Failure Mode Checklist

**Status**: v3.2
**Parent skill**: `academic-pipeline`
**Used at**: Stage 2.5 INTEGRITY (blocking), Stage 4.5 FINAL INTEGRITY (blocking), Stage 6 PROCESS SUMMARY (reporting only)
**Source**: Lu et al. (2026). Towards end-to-end automation of AI research. *Nature* 651, 914-919. doi:10.1038/s41586-026-10265-5 — Limitations section, Figure 2 (examples of failures in The AI Scientist's own accepted paper), Supplementary Information A.2.9 (debugging traces).

---

## Why this checklist exists

Lu et al. built the first autonomous AI research system to pass blind peer review (ICLR 2025 workshop). Their Limitations section enumerates the specific failure modes they observed — and most of them apply equally to human-in-the-loop AI research workflows like ARS.

These failures are dangerous because **they look like competent work**. A paper containing a hallucinated experimental result reads the same as a paper containing a real one. A shortcut-relying result reads the same as a genuine generalization. A methodology section describing experiments that were never actually run reads the same as a faithful account. The existing integrity verification catches citation hallucinations but is weak on the other failure modes.

The checklist exists to make these failures legible: **at Stage 2.5 and Stage 4.5, the integrity reviewer must explicitly rule out each of the 7 modes, or flag which are suspected and block the pipeline until the user acknowledges.**

This also extends the existing 5-type citation hallucination taxonomy (in `academic-paper-reviewer` references) into a broader 7-type AI research hallucination taxonomy. Citation hallucinations become mode 2 below.

---

## The 7 failure modes

### Mode 1: Implementation bug passing AI self-review

**What it is**: The analysis or experiment code has a bug (off-by-one, wrong variable, silent division-by-zero, type coercion, wrong flag) that produces numerically plausible but scientifically wrong results. The AI runs the code, looks at the output, sees nothing "obviously" wrong, and incorporates the result into the paper.

**Lu 2026 example**: Supplementary A.2.9 traces show The AI Scientist repeatedly accepting experimental runs that had silent crashes or numerical instabilities because the top-level metric "looked reasonable". Figure 2 shows an ICLR reviewer catching one such issue in the accepted paper — the paper's main analysis depended on a setup that the code did not actually implement.

**Detection questions at Stage 2.5**:
- For every numerical result in the draft: does the user have a saved log, notebook, or script run that produced this number? If yes, was the exit code 0 and were there zero warnings? If no log is saved, flag.
- Are any effect sizes suspiciously round (exactly 0.5, exactly 2x baseline, exactly zero variance across runs)? Suspiciously round numbers are a common signal of a constant leaking through a broken pipeline.
- Do error bars / confidence intervals actually vary across conditions, or are they suspiciously identical?

**Who catches it**: `methodology_reviewer_agent` at Stage 3 is downstream; the integrity gate at Stage 2.5 should ask the user directly.

---

### Mode 2: Hallucinated citation

**What it is**: A reference that does not exist, is miscited (wrong year, wrong journal, wrong authors), or is attributed a finding it does not contain. This is the mode ARS already covers most thoroughly via the 5-type citation hallucination taxonomy in `academic-paper-reviewer/references/`. It is included here for completeness of the 7-mode taxonomy.

**Lu 2026 example**: The AI Scientist pipeline includes a Semantic Scholar citation check to suppress this mode, acknowledging it as a primary failure class. PaperOrchestra (Song et al., 2026) extended this with a two-phase pipeline: web search discovery + sequential Semantic Scholar API verification (Levenshtein >= 0.70 title matching).

**Detection (v3.3 update)**: Covered by the existing integrity verification, now strengthened with Semantic Scholar API batch verification (Phase A0 in `integrity_verification_agent`). See `deep-research/references/semantic_scholar_api_protocol.md` for the API protocol. The S2 API provides structured, machine-readable verification that catches fabricated DOIs (DOI_MISMATCH pattern) missed by manual WebSearch.

**Who catches it**: `source_verification_agent` (Tier 0 S2 API + Tier 1 DOI + Tier 2 WebSearch) + `integrity_verification_agent` (Phase A0 + A1).

---

### Mode 3: Hallucinated experimental result

**What it is**: A result that does not correspond to any actual experiment run. The AI writes "we observed a 12% improvement" when no run produced a 12% improvement — either it averaged differently than the paper claims, or it reported a number from a crashed run, or it invented the number to match the narrative.

**Lu 2026 example**: Lu et al. specifically flag "hallucinated experimental results" as a Limitation, noting that automated reviewing struggles to detect them because the reviewer has no access to the underlying runs.

**Detection questions at Stage 2.5**:
- For every claim of the form "X% improvement" or "Y% reduction" or "outperforms baseline by Z": does the user have the raw numbers the paper's number was computed from?
- Does the table in the draft match a saved CSV / tensor log / wandb run the user can point to?
- Does the paper's "we ran N seeds" claim match the number of actual run directories the user has?

**Who catches it**: integrity gate at 2.5. This is harder than citation checking because there's no external database to verify against — the verification is against the user's own experiment logs.

---

### Mode 4: Shortcut reliance

**What it is**: The reported result is real but the model achieved it by exploiting a spurious feature rather than learning the intended generalization. A colour-biased MNIST model that gets 99% accuracy by reading the background colour, not the digit shape, is the canonical case.

**Lu 2026 example**: Figure 2b shows this exact case — The AI Scientist proposed a method, tested it on colour-biased MNIST, got high accuracy, and wrote a paper claiming the method "solved" the task. A reviewer caught that the method was exploiting the colour shortcut, not learning the digit shape. The paper was revised.

**Detection questions at Stage 2.5**:
- Is there any controlled ablation that rules out the most obvious shortcut feature? If the paper tests on dataset D, has the author run on a D-variant where the shortcut feature is removed?
- Does the paper's "ablation studies" section actually ablate the claimed mechanism, or does it ablate incidental hyperparameters?
- Is the baseline strong enough that beating it requires the proposed mechanism, not just more compute?

**Who catches it**: `devils_advocate_reviewer_agent` at Stage 3 is the natural home for this check, but it must be flagged at 2.5 so the user knows to prepare the ablation before Stage 3 arrives. Flag-only at 2.5, not block-only.

---

### Mode 5: Implementation bug reframed as novel insight

**What it is**: The pipeline produces an unexpected result that is actually caused by a bug, but the narrative-writing stage reframes the unexpected behaviour as a novel finding. The paper claims "we discovered that X behaves unexpectedly under condition Y" when in reality X behaves the expected way and condition Y is being mis-implemented.

**Lu 2026 example**: Lu et al. identify this as a compound failure mode — it requires Mode 1 (the bug) plus a writing-stage error in which the AI's narrative generator accepts the bug's output as real and builds a story around it. The paper reads *more* interesting than a bug-free version would have.

**Detection questions at Stage 2.5**:
- Does the draft contain any phrase like "surprisingly," "unexpectedly," "counterintuitively," or "contrary to our hypothesis"? For each such claim, can the user point to a literature reference that would have predicted the opposite? If no literature cites the opposite, the "surprise" may not be a surprise — it may be a bug.
- Did the surprising result appear on the first run, or only after many debugging iterations? First-run surprises are high-risk for this mode.
- Has the user attempted to reproduce the surprising result from scratch in a fresh environment?

**Who catches it**: integrity gate at 2.5. This is the most ARS-specific mode — it is the interaction of a bug (Mode 1) with narrative seduction.

---

### Mode 6: Methodology fabrication

**What it is**: The Methods section describes experiments, hyperparameters, datasets, or procedures that were not actually what the pipeline ran. The AI writes a plausible-sounding Methods section based on what a reasonable version of the experiment *would* look like, drifting from what actually happened.

**Lu 2026 example**: Lu et al. note that the writing stage of The AI Scientist sometimes produced Methods text that was disconnected from the actual hyperparameter log. They added a cross-check against the experiment run config to mitigate this.

**Detection questions at Stage 2.5**:
- Does every number in the Methods section (learning rate, batch size, epochs, dataset size, train/val split) appear in the user's actual run config / log?
- Does the Methods section describe any preprocessing step the user cannot point to in their code?
- Does the Methods section use the past tense where the actual pipeline didn't run?

**Who catches it**: integrity gate at 2.5. This requires the user to provide the actual run config as an integrity input, not just the paper text.

---

### Mode 7: Frame-lock at early pipeline stage

**What it is**: A wrong commitment made in early stages (research question framing, methodology choice, hyperparameter direction) that subsequent stages cannot back out of because they are structurally downstream of the commitment. The paper ends up well-executed but is answering the wrong question or using a fundamentally unsuitable method.

**Lu 2026 example**: Figure 3a traces The AI Scientist's agentic tree search and shows that most failed papers failed at Stage 2 (hyperparameter tuning) — the agent committed to a direction early and could not recover. This is the same frame-lock pattern ARS's anti-sycophancy protocol targets for dialogue, but here it applies to pipeline decisions.

**Detection questions at Stage 2.5**:
- If the user could go back to Stage 1 knowing what they know now, would they change the research question or methodology?
- Does the paper's Discussion section contain any phrase like "in hindsight" or "we realized later"? These are frame-lock tells.
- Is the paper's contribution better explained by the chosen framing, or despite it?

**Who catches it**: integrity gate at 2.5. If flagged, user is offered the option to return to Stage 1 or Stage 2 rather than proceeding to Stage 3.

---

## How the checklist runs at each stage

### At Stage 2.5 INTEGRITY (first integrity gate)

Run all 7 modes. For each mode, produce one of three outcomes:

- **CLEAR**: integrity reviewer has evidence that the mode does not apply. Record the evidence briefly.
- **SUSPECTED**: one or more detection questions returned a concerning answer. Must be surfaced to the user.
- **INSUFFICIENT EVIDENCE**: integrity reviewer cannot rule the mode in or out without user input (e.g., needs experiment logs the user hasn't provided).

**Block condition**: pipeline blocks if **any** mode is SUSPECTED, or if Modes 1, 3, 5, or 6 are INSUFFICIENT EVIDENCE (these four require user-provided logs to rule out and should not be silently skipped). Modes 2, 4, 7 INSUFFICIENT EVIDENCE can proceed with a warning and will be re-checked at 4.5.

**User acknowledgement options at block**:
- Confirm the flag — return to Stage 2 WRITE (or earlier) to fix
- Override with reasoning — user explicitly states why the flag is a false positive, reasoning is recorded in the process log for Stage 6
- Revise the specific passage and re-run the check

### At Stage 4.5 FINAL INTEGRITY

Re-run all 7 modes. Additional rule: any mode that was SUSPECTED at 2.5 must be resolved by 4.5 (CLEAR or user-Overridden-with-reasoning). If the same mode is still SUSPECTED at 4.5, the pipeline re-blocks and refuses to proceed to Finalize until the issue is addressed — no amount of revision loops can skip this.

### At Stage 6 PROCESS SUMMARY (AI Self-Reflection Report)

Report only, no blocking. The Self-Reflection Report includes a "Failure Mode Audit Log" section listing, for each of the 7 modes:
- Final status at 4.5 (CLEAR / OVERRIDDEN)
- History: was it ever SUSPECTED during the pipeline? At which stage? How was it resolved?
- If OVERRIDDEN: the user's reasoning

This makes the failure-mode history part of the permanent process record, giving future readers (and the user themselves) visibility into what the AI-human collaboration had to defend against.

---

## Relationship to existing ARS checks

| Existing check | Covers which modes |
|---|---|
| Citation hallucination taxonomy (5-type) | Mode 2 (fully) |
| `source_verification_agent` | Mode 2 (cross-check) |
| Existing Stage 2.5 integrity review | Mode 2, partial Mode 6 |
| `devils_advocate_reviewer_agent` (Stage 3) | Mode 4, partial Mode 7 |
| Anti-sycophancy protocol (v3.0) | Dialogue-level frame-lock, not pipeline-level Mode 7 |

Gap coverage provided by this checklist: **Modes 1, 3, 5, 6, and the pipeline-level aspect of Mode 7**. These are the modes that were not previously systematically checked.

---

## Open questions (for v3.3)

- **False positive rate**: Modes 1, 5, and 6 require the user to supply experiment logs. If the user is writing a purely theoretical paper or a qualitative study, many of these detection questions don't apply. The checklist needs a paper-type pre-filter that turns off inapplicable modes based on the paper type detected by `field_analyst_agent`. v3.2 ships with all modes always-on; v3.3 should add the pre-filter.
- **Override auditing**: if a user overrides a flag, is the reasoning ever reviewed? In v3.2 it goes into the Stage 6 record only. A stronger version would flag overrides for peer review during Stage 3 so that a reviewer can push back on the user's reasoning.

---

## References

- Lu, C. et al. (2026). Towards end-to-end automation of AI research. *Nature* 651, 914-919. [doi:10.1038/s41586-026-10265-5](https://doi.org/10.1038/s41586-026-10265-5) — Limitations section, Figure 2, Supplementary Information A.2.9.
- ARS `academic-paper-reviewer/references/` — existing 5-type citation hallucination taxonomy (Mode 2).
- ARS `academic-pipeline/references/claim_verification_protocol.md` — existing integrity verification that this checklist extends.
- ARS `academic-pipeline/references/integrity_review_protocol.md` — existing integrity review protocol that Stage 2.5 follows.
- ARS `ROADMAP_v3.2.md` — v3.2 integration plan, item 2.
