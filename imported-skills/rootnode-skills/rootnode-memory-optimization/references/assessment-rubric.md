# Memory Assessment Rubric

Detailed assessment criteria for evaluating Memory edits in a Claude Project. Used during Stage 2a of the optimization pipeline. Each criterion is rated Pass / Partial / Fail with specific evidence.

---

## Layer Placement Decision Tree

Use this to determine which layer any piece of content belongs in:

```
Is this fact needed in EVERY conversation?
├── YES → Does it instruct behavior, or state a fact?
│   ├── Instructs behavior → Is it universal (all Projects/conversations)?
│   │   ├── YES → User Preferences
│   │   │   Examples: communication style, evidence standards,
│   │   │   formatting defaults, working style rules
│   │   └── NO → Custom Instructions (project-specific)
│   │       Examples: output formatting rules, persona definitions,
│   │       tool usage policies, mode definitions
│   └── States a fact → Memory
│       Examples: current project phase, active constraints,
│       key decisions, deployment targets, file count limits
└── NO → Is it needed in SPECIFIC conversations on demand?
    ├── YES → Knowledge file (searchable depth)
    │   Examples: decision rationale archives, procedure checklists,
    │   API reference tables, historical phase records
    └── NO → Does it need to be in the project at all?
        ├── YES (infrequent but critical) → Knowledge file
        └── NO → Remove it
```

**Key distinction: User Preferences vs. Custom Instructions.** User Preferences define universal behavioral rules that apply to every conversation and every Project — they are the always-loaded foundation. Custom Instructions define project-specific behavioral rules that apply only within one Project. The Universality Test determines which layer: "Would this instruction improve output in every conversation and Project, without degrading any of them?" If yes → Preferences. If no → CI.

**Key distinction: Memory vs. Custom Instructions.** Memory states facts ("This project is in Phase 3"). Custom Instructions define behavior ("When the user asks for a status update, format it as..."). If the content tells Claude what to do, it's a behavioral instruction and belongs in CI (or Preferences if universal). If it tells Claude what IS, it's an orientation fact and belongs in Memory.

**Key distinction: Memory vs. Knowledge files.** Memory is always-loaded — every conversation pays the token cost. Knowledge files are searched on demand — only loaded when relevant. Content that >50% of conversations need belongs in Memory. Content that <50% of conversations need belongs in a knowledge file, where it adds depth without consuming always-loaded budget.

---

## Six-Criterion Assessment

### Criterion 1: Orientation Coverage

**What to check:** Does Memory cover the facts that every conversation in this project needs to know?

**Pass:** Memory contains the project's current phase, active constraints, key recent decisions, and any identity facts critical to consistent behavior. A new conversation would start with enough context to avoid repeating foundational questions.

**Partial:** Memory covers some orientation but has gaps. Common gaps:
- Active constraints missing (file count limits, deferred features, architectural boundaries)
- Phase information absent or outdated
- Key decisions buried in knowledge files only — Claude discovers them through search, not upfront orientation
- Identity facts that affect every conversation missing from Memory

**Fail:** Memory is either empty, contains only auto-populated content with no manual edits, or the manual edits address peripheral concerns while core orientation is absent.

**Evidence required:** List the orientation facts that are present in Memory and the facts that are absent but needed (based on Stage 1's project comprehension).

### Criterion 2: Redundancy

**What to check:** Is the same information stored in multiple layers without purpose?

**Pass:** Each fact appears in exactly one layer, or appears in multiple layers with clear purpose (e.g., a one-line orientation pointer in Memory with detailed rationale in a knowledge file — the pointer and the detail serve different roles).

**Partial:** Some facts appear in both manual Memory edits and auto-populated memories, or in both Memory and a knowledge file, without the duplication serving a distinct purpose. The redundancy wastes slots or tokens but doesn't cause conflicting information.

**Fail:** Significant duplication across layers, especially:
- Manual Memory edits that restate what auto-populated memories already capture (user's name, role, location, stated preferences)
- Multi-paragraph content in both an institutional memory file and Memory edits
- The same constraint or decision stated in CI, Memory, AND a knowledge file with varying levels of detail and no clear authoritative source

**Evidence required:** Cite each redundant pair — the specific Memory edit and the specific other-layer content it duplicates.

### Criterion 3: Staleness

**What to check:** Are any Memory edits outdated?

**Pass:** All Memory edits reflect the project's current state. Phase markers are current. Constraints that have been lifted are removed. Decisions that were reversed are updated.

**Partial:** One or two edits reference past states but don't cause active harm (e.g., a phase marker one phase behind, a constraint that was relaxed but not removed).

**Fail:** Multiple edits reference completed phases, old decisions, or resolved constraints. The stale entries actively mislead Claude about the project's current state.

**Evidence required:** Cite each stale Memory edit and what it should say (or whether it should be removed).

### Criterion 4: Layer Misplacement

**What to check:** Are any Memory edits carrying content that belongs in a different layer?

**Common misplacements:**
- **Behavioral instructions in Memory:** "Always format output as markdown tables" belongs in Custom Instructions (or User Preferences if universal), not Memory. Memory states facts; CI and Preferences instruct behavior.
- **Reference depth in Memory:** Multi-sentence explanations, detailed procedures, or decision rationale crammed into a 500-character Memory edit. This content belongs in a knowledge file where it has room to be complete and structured.
- **Orientation facts in CI instead of Memory:** "This project is in Phase 3 — burn-in period" in Custom Instructions when it should be a Memory edit that can be updated without editing CI.
- **Universal preferences in CI instead of Preferences:** Communication style rules, formatting defaults, or working style instructions that apply to all contexts, locked inside a single Project's CI.

**Pass:** All Memory edits contain orientation facts appropriate for always-loaded context. No behavioral instructions. No reference-depth content compressed beyond usefulness.

**Partial:** One or two edits are borderline (e.g., a constraint stated in slightly prescriptive language that's technically orientation but reads like a behavioral instruction).

**Fail:** Multiple edits carry behavioral instructions or reference-depth content. Memory is being used as a dumping ground rather than a curated orientation layer.

**Evidence required:** Cite each misplaced edit, state which layer it belongs in, and why.

### Criterion 5: Slot Efficiency

**What to check:** Of 30 available slots, how well is the budget allocated?

**Pass:** Slot usage reflects the project's priorities. High-frequency orientation facts consume slots. Low-frequency or low-leverage facts do not. Remaining capacity is appropriate for the project's growth trajectory.

**Partial:** Slots are used but allocation is uneven — one project area over-represented while another has no Memory coverage. Or low-leverage facts consume slots that higher-leverage facts need.

**Fail:** Either: slots are nearly exhausted with low-quality entries, leaving no room for growth; or very few slots are used despite clear orientation gaps identified in Criterion 1.

**Evidence required:** State current slot usage (X of 30). Identify any low-leverage entries that could be removed to free slots for higher-priority content.

### Criterion 6: Codification Candidates

**What to check:** Are any Memory entries carrying stabilized behavioral patterns that should be codified as explicit instructions in User Preferences (if universal) or Custom Instructions (if project-specific)?

**Pass — no candidates:** Memory contains only factual orientation entries. No behavioral patterns, corrections, or working style observations are present. This is the expected state for a well-structured project — behavioral rules live in CI or Preferences, not Memory.

**Pass — with candidates identified:** Memory contains behavioral entries that have been evaluated. Those passing the Stability Test are flagged as codification candidates with destination and confidence level.

**Partial:** Memory contains entries that look behavioral ("user prefers X," "user corrected Y") but the Stability Test results are mixed — persistence is unclear or intentionality is ambiguous. These should be monitored rather than immediately codified.

**Fail:** Multiple Memory entries carry behavioral instructions or preference observations that have clearly stabilized (long persistence, consistent behavior, no contradictions) but have never been codified into explicit instructions. The project is relying on Memory to enforce behavior that should be in CI or Preferences.

**Evidence required:** For each behavioral Memory entry, cite the entry, apply the Stability Test (persistence + intentionality), and state whether it's a codification candidate. For candidates, state the destination (Preferences or CI) and confidence level.

See the Codification Assessment section below for detailed guidance on identifying and evaluating candidates.

---

## Memory Edit Quality Criteria

When evaluating existing edits or writing new ones, each Memory edit should be:

- **Concise:** Uses the 500-character limit efficiently. No filler words, no redundant context. Every character earns its place.
- **Self-contained:** Understandable without reading other Memory edits. A developer reading this single edit can grasp the fact without cross-referencing.
- **High-frequency:** Relevant to more than 50% of conversations in this project. If a fact only matters occasionally, it belongs in a knowledge file.
- **Current:** Reflects the project's actual state, not a past state. Phase markers, constraints, and decisions should be updated as the project evolves.
- **Non-behavioral:** States facts, not instructions. "This project uses Apache-2.0 licensing" (fact) belongs in Memory. "Always include license headers in generated files" (instruction) belongs in Custom Instructions. Exception: behavioral observations recorded by Memory synthesis ("user prefers X") are valid Memory entries — they record facts about the user's preferences. But when these stabilize, they become codification candidates.

---

## Codification Assessment

### What to look for

Memory entries that express behavioral preferences rather than factual context. Indicators:
- Language like "user prefers," "user wants," "user corrected," "user's style is"
- Entries describing communication patterns, output preferences, or working style
- Entries recording corrections Claude has learned ("user doesn't like bullet points")

### Stability Test anchoring

**Clear pass:** Pattern present across 5+ conversations over 2+ weeks. User has not contradicted it. Aligns with observable behavior in the conversation history.

**Clear fail:** Pattern recorded once. User explicitly overrode it in a later conversation. Pattern appears to be a situational request misrecorded as a permanent preference.

**Borderline (moderate confidence):** Pattern present in 2-3 conversations over a short period. Consistent but not yet proven durable. Recommend codification with moderate confidence — suggest the user monitor for one more cycle before committing.

### Layer placement decision tree

1. Is this entry a behavioral preference (how Claude should behave) or a factual observation (what the user is working on)?
   - Factual → stays in Memory (orientation). Not a codification candidate.
   - Behavioral → proceed to step 2.

2. Apply the Stability Test. Does it pass both persistence and intentionality?
   - No → stays in Memory. May become a candidate later.
   - Yes → proceed to step 3.

3. Apply the Universality Test. Would codifying this as an instruction improve every conversation and Project?
   - Yes → destination is User Preferences.
   - No → destination is the relevant Project CI.
