# Evolutionary Pathways — Recommendation Engine

Four pathways that strengthen the user's Claude environment over time by moving content to its optimal layer. Each pathway includes a test to validate the recommendation before acting.

---

## Cross-Project Pattern Analysis

**Prerequisite:** CIs from 3+ Projects.

Before running individual pathways, scan all provided Project CIs for repeated patterns. Identify instructions, rules, identity elements, or formatting standards that appear in 3+ Projects in identical or near-identical form. These are promotion candidates — content that has proven universal through organic repetition.

**How to identify patterns:** Look for:
- Identical behavioral rules (even if worded differently)
- Shared identity traits across Projects
- Common output formatting instructions
- Repeated tool usage patterns
- Similar knowledge file structures

**Output:** A pattern inventory listing each repeated pattern, where it appears, and how consistently it's expressed across Projects. This inventory feeds the Promotion pathway.

---

## Pathway 1: Promotion (Project → Global)

**Direction:** Move content from individual Project CIs to User Preferences.

**Trigger:** An instruction appears in 3+ Project CIs, indicating it's become a de facto universal behavior.

**The Universality Test:** For each promotion candidate, ask:
1. Would this instruction improve output in a Project I haven't built yet?
2. Does this instruction make sense outside its original domain?
3. Could this instruction ever harm output in a different Project context?

**Pass criteria:** Yes to #1 and #2, No to #3. If #3 is "maybe," the instruction is too domain-specific for Preferences — keep in CIs.

**Execution:**
1. Identify the instruction across all Projects where it appears
2. Draft a Preferences-appropriate version (concise, universally framed)
3. Note which Project CIs should have the instruction removed after promotion
4. Flag any Projects where the instruction has diverged — these may need the CI-specific variant retained

**Confidence level:** High when the instruction appears identically in 3+ Projects. Moderate when it appears with variations. Low when inferred from 2 Projects only.

**Deliverable:** Drafted Preferences text for each promotion candidate, plus a list of CI removals.

---

## Pathway 2: Demotion (Global → Project)

**Direction:** Move content from User Preferences to specific Project CIs.

**Trigger:** A Preferences instruction is domain-specific — it helps some Projects but is irrelevant to or harmful in others.

**The Specificity Test:** For each Preferences instruction, ask:
1. Does this instruction apply equally to all my Projects?
2. Is there any Project where this instruction would produce worse output?
3. Is this instruction really about a specific domain, tool, or workflow rather than a universal behavior?

**Fail criteria:** No to #1, Yes to #2 or #3. The instruction is too specific for Preferences.

**Execution:**
1. Identify the domain-specific instruction in Preferences
2. Determine which Projects benefit from it
3. Draft a CI-appropriate version for each benefiting Project
4. Remove from Preferences after placement in the appropriate CIs

**Common demotion candidates:**
- Technical jargon preferences ("always use camelCase") — only relevant to coding Projects
- Domain-specific depth instructions ("assume graduate-level knowledge of X")
- Tool-specific instructions ("always format output for Airtable")
- Audience-specific tone instructions that don't apply universally

**Confidence level:** High when the instruction clearly fails the Specificity Test. Moderate when the scope is debatable.

**Deliverable:** Identification of demotion candidates, destination Project CIs, and drafted CI text.

---

## Pathway 3: Codification (Memory → Preferences/CI)

**Direction:** Move stabilized behavioral patterns from Memory to Preferences or Project CI.

**Trigger:** A Memory entry represents a behavioral pattern that has persisted across conversations and hasn't been contradicted by the user — it's become a stable, intentional behavior that should be codified as an instruction.

**The Stability Test:** For each Memory entry, evaluate:
1. **Persistence:** Has this pattern been consistent across multiple conversations? (Not a one-time correction or temporary preference)
2. **Intentionality:** Did the user deliberately establish this pattern, or did it emerge incidentally?
3. **Behavioral impact:** Does this entry change how Claude behaves (instruction-like) or does it provide factual context (orientation-like)?

**Codification criteria:** High persistence + clear intentionality + behavioral impact = codification candidate. Low persistence or factual-only content = keep as Memory or remove if stale.

**Destination logic:**
- Universal behavioral patterns → User Preferences
- Project-specific behavioral patterns → Project CI
- Factual orientation content → stays in Memory (this is Memory's correct role)

**Execution:**
1. Identify Memory entries that pass the Stability Test
2. Determine destination (Preferences or specific Project CI)
3. Draft instruction text appropriate for the destination
4. Note the Memory entry for cleanup after codification (it becomes redundant)

**Confidence level:** Moderate for recently stabilized patterns (may still evolve). High for long-standing patterns the user has explicitly reinforced.

**Deliverable:** Codification candidates with destination, drafted text, and Memory cleanup notes.

---

## Pathway 4: Skill Extraction (Knowledge File → Skill)

**Direction:** Extract portable procedural content from knowledge files into a standalone Skill.

**Trigger:** A knowledge file (or section of a knowledge file) contains procedural content that is task-triggered, context-independent, and potentially useful across multiple Projects.

**The Portability Test:** For each extraction candidate, evaluate:
1. **Task-triggered:** Is this content activated by a specific task type, or is it always-on reference material? Skills activate on tasks; always-on content belongs in CI or knowledge files.
2. **Context-independent:** Does this content work without the specific Project's identity, rules, or other knowledge files? Skills must be standalone.
3. **Multi-project utility:** Would this content be useful in 2+ Projects, or is it deeply specific to one Project's domain?

**Extraction criteria:** Yes to all three = strong candidate. Yes to #1 and #2 but uncertain on #3 = possible candidate (worth extracting if the methodology is valuable enough standalone). No to any = keep as knowledge file.

**Execution:**
1. Identify the extractable content
2. Draft a Skill description (name, what it does, trigger phrases)
3. Outline the SKILL.md structure (what goes in the body vs. references/)
4. Note what the source knowledge file looks like after extraction (may shrink significantly)

**Confidence level:** High for clearly procedural, task-triggered content with proven cross-project utility. Lower for content whose portability is inferred rather than proven.

**Deliverable:** Draft Skill descriptions and extraction outlines. These are starting points for full Skill development, not finished Skills.

---

## Combining Pathways

The four pathways often interact:

- **Promotion + Demotion** in the same audit: One instruction gets promoted (universal) while another gets demoted (domain-specific). The net effect is cleaner layer separation.
- **Codification → Promotion:** A Memory pattern is first codified into a Project CI, then recognized as universal and promoted to Preferences in a later audit.
- **Demotion → Skill Extraction:** A demoted instruction placed in multiple Project CIs may later be extracted as a Skill if it proves to be a portable methodology.

Present all four pathways' recommendations together in the Evolutionary Roadmap section of the unified action plan. Order by confidence level (highest first) and group by action type so the user can work through them systematically.
