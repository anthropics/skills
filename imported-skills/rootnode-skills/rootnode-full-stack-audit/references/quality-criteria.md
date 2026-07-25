# Quality Criteria — Holistic Evaluation

Five criteria that evaluate the overall quality of a Project's architecture beyond the dimension-by-dimension Scorecard. These criteria assess how well the Project works as an integrated system.

---

## 1. Comprehensibility

**Question:** Could a new team member understand what this Project does and how it works by reading the Custom Instructions alone?

**Tests:**
- Read the CI from top to bottom. After one pass, can you explain the Project's purpose, its primary workflows, and its key constraints?
- Are there implicit assumptions that require background knowledge not provided in the CI or knowledge files?
- Is the organization logical — does information appear where you'd expect to find it?

**Pass:** The Project's purpose, workflows, and constraints are clear from the CI. Knowledge files provide supplementary depth, not essential context missing from CI.

**Partial:** The Project's purpose is clear but some workflows or constraints require knowledge file content or inference to understand.

**Fail:** The CI is disorganized, contains unexplained jargon, or requires external context not provided anywhere in the Project to understand.

---

## 2. Coherence

**Question:** Do all parts of the Project work together without contradiction?

**Tests:**
- Do any CI rules contradict each other? (e.g., "be concise" in one section and "provide comprehensive analysis" in another, without scoping to different contexts)
- Do knowledge files contradict CI instructions? (e.g., CI says "always use formal tone" but a knowledge file template uses casual language)
- Do Memory entries contradict CI or knowledge file content?
- Does the identity section align with the behavioral rules? (e.g., a "decisive advisor" identity paired with rules that encourage hedging)

**Pass:** No contradictions detected. Identity, rules, knowledge files, and Memory all reinforce the same intent.

**Partial:** Minor contradictions exist but are unlikely to cause observable output problems (e.g., slightly different phrasing of the same rule in two places).

**Fail:** Material contradictions exist that would cause Claude to produce inconsistent output depending on which instruction it prioritizes.

---

## 3. Efficiency

**Question:** Does the Project use its context budget wisely?

**Tests:**
- Is any content duplicated between CI, knowledge files, and Memory?
- Are there CI instructions that could be shorter without losing meaning?
- Are knowledge files appropriately sized, or do they contain large blocks of content that Claude rarely needs?
- Is the total context footprint (CI + knowledge files + Memory) proportionate to the Project's complexity?

**Pass:** No material duplication. CI is concise. Knowledge files are well-structured with appropriate granularity. Context budget is used proportionately.

**Partial:** Some duplication or verbosity exists but the total context footprint is still reasonable for the Project's complexity.

**Fail:** Significant duplication, verbose instructions that could be halved without losing meaning, or knowledge files containing large amounts of rarely-needed content that should be restructured.

---

## 4. Evolvability

**Question:** Can this Project be maintained and improved without architectural risk?

**Tests:**
- Could you add a new mode, workflow, or knowledge file without restructuring the CI?
- Could you update a single rule without risk of cascading contradictions?
- Are knowledge files modular (each serves one purpose) or monolithic (multiple purposes mixed in one file)?
- Is there a clear separation between stable architecture (identity, core rules) and evolving content (knowledge files, examples)?

**Pass:** The Project has clear separation of concerns. New content can be added by creating or updating a single component. Stable elements are isolated from evolving elements.

**Partial:** The Project is maintainable but some changes would require updates in multiple places. Minor coupling between components.

**Fail:** The Project is tightly coupled — changing one element requires changes in several others. Or the Project is so unstructured that maintenance requires understanding the entire system to make any change safely.

---

## 5. Instruction/Reference Separation

**Question:** Is behavioral instruction in CI and reference material in knowledge files, with clear boundaries between them?

**Tests:**
- Does the CI contain large blocks of reference material (templates, examples, data) that should be in knowledge files?
- Do knowledge files contain behavioral rules that should be in CI?
- Does the CI delegate to knowledge files with clear routing — specifying when to consult which file and for what purpose?
- Are there behavioral instructions in Memory that belong in CI?

**Pass:** CI contains identity, rules, modes, and output standards. Knowledge files contain reference material, templates, examples, and domain documentation. Routing from CI to knowledge files is explicit. Memory contains orientation facts only.

**Partial:** Mostly well-separated with one or two misplaced elements (e.g., a small template in CI that could be in a knowledge file, or a minor behavioral instruction in a knowledge file).

**Fail:** Significant mixing — CI contains large reference blocks, or knowledge files contain behavioral rules that Claude may or may not process depending on retrieval, or Memory contains instructions that should be in CI.
