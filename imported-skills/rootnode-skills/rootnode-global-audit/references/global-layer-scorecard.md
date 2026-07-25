# Global Layer Scorecard — Anchored Rubrics

Six dimensions scored 1-5. For each: state the score, cite specific evidence, explain the mapping. Score only dimensions where the user has provided the relevant layer content.

---

## Dimension 1: Preference Precision

Evaluates whether User Preferences text is concise, universally applicable, and free of domain-specific content.

**The Universality Test:** For each instruction, ask: "Would this instruction improve output in every conversation and Project, without degrading any of them?" If the answer is no for any plausible context, the instruction fails and belongs in Project CI.

| Score | Anchor |
|---|---|
| 5 | Every instruction passes the Universality Test. No domain-specific content. Concise — under ~500 words with no redundancy. Behavioral directives are clear and unambiguous. Preferences text reads as a foundation that enhances every context. |
| 4 | 1-2 instructions are borderline (pass Universality in most but not all contexts). No domain-specific content. Minor verbosity or redundancy. All core behavioral preferences are captured. |
| 3 | 3-5 instructions fail the Universality Test — they improve some contexts but degrade or are irrelevant in others. Some domain-specific content present. Moderate verbosity. Missing 1-2 behavioral preferences that the user demonstrates consistently across Projects. |
| 2 | More than half of the instructions are domain-specific or context-dependent. Preferences text reads like a single Project's CI transplanted to the global level. Significant verbosity or redundancy. Key behavioral preferences missing. |
| 1 | Preferences text is either empty/minimal (no meaningful behavioral foundation) or is a full Project CI pasted into Preferences (extensive domain-specific content that degrades most contexts). |

---

## Dimension 2: Style Coherence

Evaluates whether Styles work with, not against, other layers.

| Score | Anchor |
|---|---|
| 5 | Active Styles complement Preferences and do not conflict with any Project CI. Style choices are intentional and well-matched to the user's communication needs. No formatting conflicts between Style directives and output requirements. |
| 4 | Styles are mostly coherent. One minor tension between a Style directive and a Preference or CI instruction, but it does not produce visible output degradation. |
| 3 | One clear conflict between Style and another layer — e.g., a Style that enforces casual tone while a Project CI requires formal documentation output. The conflict produces inconsistent behavior in some contexts. |
| 2 | Multiple Style conflicts with Preferences or CIs. Styles appear to have been configured without considering other layers. Output quality visibly degrades in contexts where conflicts apply. |
| 1 | Styles actively undermine Preferences or CI directives. The user experiences contradictory behavior and may not understand the source of the conflict. |

**Scoring note:** If no Styles are active, score N/A — do not penalize the absence of Styles. If Style descriptions are not provided, note the dimension as "not evaluated — Style information not provided."

---

## Dimension 3: Memory Hygiene

Evaluates whether Global Memory is clean and well-organized.

| Score | Anchor |
|---|---|
| 5 | Every Memory entry is current, accurate, and appropriately scoped. No stale entries (facts that have changed). No reference-depth content that belongs in knowledge files. No behavioral patterns that should be codified as explicit Preferences or CI instructions. Memory serves its intended purpose: orientation context that helps Claude personalize responses. |
| 4 | 1-2 entries are borderline (slightly stale or could be codified, but not causing harm). No reference-depth content. Memory is mostly orientation-focused. |
| 3 | 3-5 entries have issues: stale facts, behavioral patterns that should be codified, or entries that duplicate Preferences content. Some entries consume Memory slots without providing orientation value. |
| 2 | Significant Memory quality issues. Multiple stale entries, reference-depth content stored in Memory (long procedures or detailed context that belongs in knowledge files), or behavioral instructions that should be in Preferences. Memory is being used as a catch-all rather than a focused orientation layer. |
| 1 | Memory is either empty (no orientation context captured) or severely degraded (majority stale, misplaced, or redundant entries). Memory actively misleads Claude rather than orienting it. |

**Scoring note:** Global Memory and Project Memory are separate. This dimension scores Global Memory only. If only Project Memory is provided, note this limitation and recommend the user provide Global Memory for this dimension, or suggest rootnode-memory-optimization for Project-scoped assessment.

---

## Dimension 4: Skill Portfolio Fitness

Evaluates whether the installed Skill set is well-curated for the user's needs.

| Score | Anchor |
|---|---|
| 5 | Every installed Skill serves a clear purpose in the user's workflow. No orphan Skills (installed but never useful). No missing Skills (user repeatedly performs tasks a Skill would automate). No Skill/Project collisions (Skill instructions don't conflict with any Project CI). Skill portfolio size is appropriate for the user's complexity. |
| 4 | 1-2 Skills are borderline (installed for occasional use but rarely triggered). No collisions. The portfolio covers the user's primary workflows. |
| 3 | Some portfolio fitness issues: 1-2 orphan Skills consuming description context for no benefit, or 1 missing Skill for a task the user frequently performs manually. Minor Skill/CI tension in one Project. |
| 2 | Multiple orphan Skills. Clear missing Skills for repeated workflows. Or a Skill/Project collision producing conflicting instructions in at least one Project. Portfolio was not curated — Skills were installed ad hoc without considering the whole. |
| 1 | Skill portfolio is either empty (user would benefit from Skills but has none) or severely overcrowded (many orphan Skills consuming context budget, multiple collisions, no clear curation strategy). |

**Scoring note:** If the user has no Skills installed, assess whether their usage patterns suggest Skills would be beneficial. If the user's workflows are simple enough that Skills aren't needed, score N/A.

---

## Dimension 5: Connector Alignment

Evaluates whether MCP Connectors match the user's actual needs.

| Score | Anchor |
|---|---|
| 5 | Every configured connector serves an active purpose. No orphan connectors (configured but unused). No missing connectors (Projects reference tools that aren't connected). Connector configuration matches the user's workflow integration needs. |
| 4 | 1-2 connectors are borderline (configured for occasional use). No missing connectors that actively impair workflow. |
| 3 | One clear misalignment: an orphan connector consuming context, or a missing connector that a Project CI references but can't access. |
| 2 | Multiple orphan connectors or missing connectors. CI instructions reference tools that aren't available, producing failed tool calls or workaround behaviors. Connector setup was not reviewed after Projects evolved. |
| 1 | Connector configuration is severely misaligned. Multiple CIs reference unavailable tools. Orphan connectors consume significant context budget. Or no connectors configured when the user's workflow clearly requires external tool access. |

**Scoring note:** If the user has no connectors configured and no Projects reference external tools, score N/A.

---

## Dimension 6: Cross-Layer Efficiency

Evaluates context budget efficiency across all global layers combined.

| Score | Anchor |
|---|---|
| 5 | No redundant layering (no instruction appears in both Preferences and CI). No silent overrides (every layer's directives are respected in context). Global layer context footprint is proportional to the value it delivers. Every token of global configuration earns its place. |
| 4 | One instance of minor redundancy or a near-silent override where the impact is negligible. Overall context efficiency is high. |
| 3 | 2-3 instances of redundant layering or inefficiency. Some context budget is wasted on duplicate instructions across layers. One silent override may be producing unintended behavior. |
| 2 | Significant cross-layer inefficiency. Multiple redundant instructions across Preferences, Styles, and Project CIs. Silent overrides producing confusing behavior. Global layers consume disproportionate context relative to their value. |
| 1 | Severe cross-layer waste. Global configuration is bloated, contradictory, or redundant to the point that it degrades rather than enhances Claude's performance. Multiple silent overrides produce unpredictable behavior. |

**Scoring note:** This dimension requires visibility into at least Preferences plus one other layer (Style, Memory, or Project CI). With only Preferences, score as "partially evaluated" based on internal Preferences efficiency alone.
