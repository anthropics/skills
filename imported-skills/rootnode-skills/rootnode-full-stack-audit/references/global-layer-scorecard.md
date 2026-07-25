# Global Layer Scorecard — Condensed Rubrics

Six dimensions evaluating the account-wide layers (User Preferences, Styles, Global Memory, Skills, Connectors). Each scored 1-5. For the full prose rubrics, see rootnode-global-audit if available.

## The Nine-Layer Architecture

For context, these are the nine layers of a Claude environment, ordered by processing priority:

| Layer | Scope | Content |
|---|---|---|
| L1 | Global | User Preferences |
| L2 | Global | Styles |
| L3 | Global | Global Memory |
| L4 | Global | Skills |
| L5 | Global | MCP Connectors |
| L6 | Project | Custom Instructions |
| L7 | Project | Knowledge Files |
| L8 | Project | Project Memory |
| L9 | Conversation | Chat context |

The Global Layer Scorecard evaluates L1-L5. The Project Scorecard evaluates L6-L8. The Cross-Layer Alignment Check evaluates interfaces between them.

## Scoring Anchors

### 1. Preference Precision

| Score | Anchor |
|---|---|
| 5 | Every instruction is universally applicable across all Projects. Concise, non-redundant, actionable. No domain-specific content that only applies to certain Projects. Clear categories (communication style, formatting defaults, working context). |
| 4 | Mostly universal. One or two instructions are borderline domain-specific but cause minimal harm in other contexts. Well-organized. |
| 3 | Mix of universal and domain-specific instructions. Some instructions help certain Projects but actively hurt others. Organization is loose. |
| 2 | Predominantly domain-specific instructions that should be in Project CIs. Or so vague ("be helpful") that they add no value. |
| 1 | No Preferences set, or Preferences that contradict each other or contain instructions harmful to most Projects. |

**Key boundary (3→4):** Would every instruction improve (or at minimum not harm) output in every Project the user runs?

**The Universality Test:** For each Preference instruction, ask: "Would this instruction improve output in a Project I haven't built yet?" If yes → keep. If no → demote to the specific Project CI where it belongs.

### 2. Style Coherence

| Score | Anchor |
|---|---|
| 5 | Styles complement other layers without conflict. Formatting choices align with (or don't contradict) Project output standards. Style scope is appropriate — not overriding domain-specific formatting needs. |
| 4 | Styles are well-configured. Minor tensions with specific Project output standards that could be resolved. |
| 3 | One or more Styles create observable friction with Project-level formatting instructions. User may not realize the Style is overriding their CI. |
| 2 | Active Style significantly conflicts with Project output requirements, producing inconsistent formatting. |
| 1 | Styles actively undermine Project quality — e.g., a casual Style applied to a Project requiring formal output. |

**Key boundary (3→4):** Is the user aware of how their active Style interacts with each Project's output requirements?

**N/A:** Score as N/A if no Styles are configured. This is neutral, not a penalty.

### 3. Memory Hygiene

| Score | Anchor |
|---|---|
| 5 | Global Memory contains current, accurate, orientation-critical facts. No stale entries. No entries that duplicate Preferences or CI content. No entries that belong in a specific Project's Memory instead. |
| 4 | Mostly clean. One or two entries are borderline stale or slightly redundant with Preferences. |
| 3 | Some stale entries, some misplaced entries (project-specific facts in global Memory), or moderate redundancy with Preferences. |
| 2 | Significant staleness, misplacement, or redundancy. Memory is cluttered enough to waste context budget. |
| 1 | Memory is severely outdated, contains contradictory information, or is so cluttered it degrades orientation quality. |

**Key boundary (3→4):** Is every Global Memory entry still accurate, still global (not project-specific), and not already stated elsewhere?

### 4. Skill Portfolio Fitness

| Score | Anchor |
|---|---|
| 5 | Installed Skills match the user's actual workflow needs. No orphan Skills (installed but never triggered). No collisions between Skills with overlapping descriptions. Skill descriptions are precise enough for reliable activation. |
| 4 | Good portfolio with minor issues — one underused Skill, or a pair with slightly overlapping trigger language. |
| 3 | Some Skills installed speculatively without clear use cases. Or multiple Skills with description overlaps that cause unreliable activation. |
| 2 | Skill portfolio is cluttered with unused Skills, or critical Skills are missing while irrelevant ones consume the description budget. |
| 1 | No Skills installed when the user's workflow would clearly benefit, or Skills that actively conflict with Project instructions. |

**Key boundary (3→4):** Does every installed Skill serve a recurring workflow need, and do Skills activate reliably on the right tasks?

**N/A:** Score as N/A if no Skills are installed. Evaluate whether Skills would add value and note as a recommendation if so.

### 5. Connector Alignment

| Score | Anchor |
|---|---|
| 5 | Configured Connectors match the tools referenced in Project CIs. No CI references to unconfigured tools. No orphan Connectors (configured but never used). Authentication is current. |
| 4 | Good alignment. One minor gap (a referenced tool not yet connected, or an unused Connector). |
| 3 | Some Project CIs reference tools that aren't configured as Connectors, or several Connectors are configured but unreferenced. |
| 2 | Significant mismatch — CIs expect tool access that isn't available, causing silent failures or workarounds. |
| 1 | No Connectors configured when Projects clearly depend on external tool access. |

**Key boundary (3→4):** Does every tool reference in every Project CI have a corresponding configured Connector?

**N/A:** Score as N/A if no Connectors are needed (Projects don't reference external tools).

### 6. Cross-Layer Efficiency

| Score | Anchor |
|---|---|
| 5 | Global layers (L1-L5) use context budget efficiently. No redundant instructions between Preferences and Project CIs. Skills and Connectors add capability without unnecessary context overhead. Total global context contribution is proportionate to value delivered. |
| 4 | Good efficiency with minor waste — slight redundancy between Preferences and one Project CI, or one Skill adding more context overhead than its activation frequency justifies. |
| 3 | Noticeable context waste. Preferences contain instructions that repeat in multiple Project CIs (should be consolidated or removed from one side). Or global layers consume disproportionate context relative to their contribution. |
| 2 | Significant inefficiency. Global layers consume substantial context budget while delivering marginal value. Multiple redundancies across layers. |
| 1 | Global layers actively waste context budget — e.g., verbose Preferences that duplicate Project CI content, creating double processing overhead in every conversation. |

**Key boundary (3→4):** If you removed all redundancy between global and Project layers, would the context budget freed be noticeable?
