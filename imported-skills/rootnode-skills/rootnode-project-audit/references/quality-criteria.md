# Quality Criteria Evaluation

Evaluate the Project against each criterion after completing the Scorecard and anti-pattern sweep. These are holistic criteria that assess the Project as a system, not individual components. Each criterion includes a specific test and pass/fail indicators.

---

## 1. Comprehensibility

**Test:** Read only the Custom Instructions. Can you construct a complete mental model of the Project — its purpose, scope, how to use it, what files exist, and when to consult them?

**Pass indicators:**
- Purpose is stated in the first 2–3 sentences
- Every knowledge file is named with routing guidance
- Operational modes are described with trigger conditions
- A new user could use this Project effectively after reading only the system prompt

**Fail indicators:**
- Purpose is implicit or buried
- Knowledge files are listed without usage guidance
- Modes are described without trigger conditions
- Understanding the Project requires reading the knowledge files, not just the system prompt

---

## 2. Coherence

**Test:** Check for content overlap between files, conflicting instructions between Custom Instructions and knowledge files, and inconsistent terminology. Also check that Memory edits do not contradict knowledge file content or Custom Instructions.

**Pass indicators:**
- Each concept has one authoritative location
- Terminology is consistent across all components
- No instruction in one place contradicts an instruction in another
- Memory edits and knowledge files present consistent facts

**Fail indicators:**
- The same concept is explained differently in two files
- Custom Instructions say "be concise" while an output section specifies 1500 words
- The system prompt uses "operational modes" while a knowledge file calls them "task profiles"
- A Memory edit states a fact that contradicts information in a knowledge file

---

## 3. Efficiency

**Test:** For every instruction in Custom Instructions, ask: "If I removed this, would the output get noticeably worse?" For every knowledge file, ask: "Is this file consulted often enough to justify its presence?" For Memory, ask: "Does every edit contain orientation-level facts that are relevant to most conversations?"

**Pass indicators:**
- Every instruction demonstrably improves output
- Every file serves a purpose that arises in a significant fraction of conversations
- Memory contains only current, orientation-level facts
- The system prompt contains behavioral rules and routing, not reference material

**Fail indicators:**
- Instructions added "just in case"
- Knowledge files for rare edge cases
- Reference material embedded in Custom Instructions
- Memory stuffed with reference-depth content or stale facts
- The system prompt could be 30%+ shorter without degrading output

---

## 4. Evolvability

**Test:** Imagine adding a knowledge file for a topic adjacent to the Project's domain. Would it slot in cleanly (add the file, add a routing entry), or would it require restructuring?

**Pass indicators:**
- Adding a file requires adding one routing entry to Custom Instructions
- No existing files need modification
- Architectural decisions are documented or self-evident

**Fail indicators:**
- Adding a file requires changing how existing components work
- Components are tightly coupled — changing one requires changing others
- No documentation of why the Project is structured the way it is

---

## 5. Instruction/Reference Separation

**Test:** Are all behavioral instructions in Custom Instructions and all reference material in knowledge files? Or are they mixed? Is always-loaded orientation in Memory and searchable depth in knowledge files? Or are the layers blurred?

**Pass indicators:**
- Custom Instructions contain only: identity, behavioral rules, knowledge file routing, operational modes, and output standards
- Knowledge files contain only: reference material, frameworks, data, templates, and examples
- Memory contains only: current orientation facts relevant to most conversations
- Each layer serves its designated function

**Fail indicators:**
- Custom Instructions contain data tables, extended examples, or framework descriptions
- Knowledge files contain "always do X" behavioral instructions that should be in the system prompt
- Memory contains detailed procedural content or historical rationale that belongs in knowledge files
- The same fact is maintained in multiple layers without a clear authoritative home

---

## Reporting

For each criterion, state **Pass**, **Partial**, or **Fail** with one to two sentences of evidence. Partial means some indicators pass and some fail — specify which. Link findings to the relevant Scorecard dimensions where they overlap (e.g., a Coherence failure often connects to Instruction Clarity or Knowledge & Context Architecture scores).
