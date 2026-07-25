# Anti-Leakage Protocol (Knowledge Isolation)

**Status**: v3.3
**Used by**: `draft_writer_agent`, `report_compiler_agent`
**Source**: Adapted from PaperOrchestra (Song et al., 2026, Appendix D.4)

---

## Purpose

When the user provides comprehensive research materials (RQ Brief, Synthesis Report, Annotated Bibliography, experimental data), the writing agent should construct the paper **primarily from those materials**, not from LLM parametric memory. This prevents:

1. **Methodology fabrication (Failure Mode 6)**: The LLM writes a plausible Methods section from training data rather than the user's actual procedure
2. **Implicit knowledge leakage**: The LLM fills gaps with memorized content that may be inaccurate, outdated, or from a different context
3. **Unintentional plagiarism**: The LLM reproduces near-verbatim passages from training data

---

## Protocol

### When to activate

Activate when ALL of the following are true:
- The user has provided research materials via the pipeline handoff (RQ Brief + Synthesis Report + Annotated Bibliography)
- The paper is in `full` or `revision` mode (not `plan` or `outline-only`)
- The materials are substantive (not placeholder stubs)

### When NOT to activate

Do NOT activate when:
- The user is in `plan` or `socratic` mode (exploratory — LLM knowledge is expected)
- The materials are minimal (e.g., only a RQ Brief with no bibliography)
- The user explicitly requests the LLM to supplement with its own knowledge

### Prompt insertion

When activated, prepend the following to the draft_writer_agent's working context:

```
## Knowledge Isolation Directive

You are writing this paper based on the research materials provided in this session:
- RQ Brief, Synthesis Report, and Annotated Bibliography (from deep-research)
- Any additional materials the user has provided (experimental logs, datasets, prior drafts)

Priority rules:
1. PREFER session materials over your parametric knowledge for all factual claims
2. Every claim in the paper MUST be traceable to a source in the Annotated Bibliography or user-provided data
3. If the materials do not cover a topic the outline requires, flag it as [MATERIAL GAP] rather than filling from memory
4. Do NOT introduce references not present in the Annotated Bibliography unless explicitly asked by the user
5. The Methods section must describe ONLY what is documented in the user's materials — do not infer or interpolate experimental procedures

This is NOT a prohibition on using language skills or academic writing knowledge.
You may use your knowledge of academic conventions, writing style, logical argumentation,
and discipline norms. The restriction applies only to FACTUAL CONTENT — claims, citations,
data, and methodology descriptions must come from session materials.
```

### [MATERIAL GAP] handling

> **Tag vocabulary.** The `[MATERIAL GAP]`, `[WEAK EVIDENCE]`, `[GAP]` tags used throughout this protocol are canonically defined in [`shared/compliance_checkpoint_protocol.md#canonical-gap-tag-vocabulary`](../../shared/compliance_checkpoint_protocol.md#canonical-gap-tag-vocabulary). This section describes how the anti-leakage writing-time flag interacts with that vocabulary during manuscript production.

When a `[MATERIAL GAP]` is flagged:
1. The gap is surfaced at the next checkpoint
2. The user can provide additional materials, or authorize LLM supplementation for that specific gap
3. If supplemented: the gap section is tagged `[LLM-SUPPLEMENTED]` in the draft metadata for integrity review

---

## Relationship to existing checks

| Check | What it catches | Anti-leakage adds |
|-------|----------------|-------------------|
| Integrity gate (Stage 2.5) | Fabricated citations post-hoc | Prevents fabrication at writing time |
| Failure Mode 6 (Methodology fabrication) | Methods don't match actual procedures | Prevents LLM from inventing procedures |
| Writing Quality Check | AI-typical phrasing patterns | Anti-leakage prevents AI-typical *content* (as opposed to style) |

---

## References

- Song, Y. et al. (2026). PaperOrchestra. *arXiv:2604.05018*. Appendix D.4 (Anti-Leakage Prompt).
- Lu, C. et al. (2026). Towards end-to-end automation of AI research. *Nature* 651, 914-919. — Mode 6 (Methodology fabrication).
