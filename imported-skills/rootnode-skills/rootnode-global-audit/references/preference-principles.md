# User Preference Optimization Principles

User Preferences are the highest-precedence behavioral layer — they affect every conversation and every Project. This makes them the highest-leverage and highest-risk configuration surface. A well-crafted Preferences text provides a foundation that makes every interaction better. A poorly crafted one degrades interactions the user doesn't even think about.

---

## The Universality Test

The single most important test for any Preferences instruction:

**"Would this instruction improve output in every conversation and Project, without degrading any of them?"**

Apply this test to each instruction individually, not to the Preferences text as a whole. An instruction that passes in 9 out of 10 contexts but actively degrades the 10th is a Demotion candidate — it belongs in the 9 Projects' CIs, not in Preferences.

When applying the test, consider the user's full range of Claude usage — not just their primary Projects. Preferences affect conversations outside Projects too (ad-hoc questions, casual use, one-off tasks). An instruction that helps in structured Project work but makes casual conversation awkward fails the test.

---

## Five Structural Qualities

Well-optimized Preferences text exhibits all five:

**1. Universality.** Every instruction improves every context. No domain-specific content. No audience assumptions. No workflow details that only apply to certain tasks. This is the Universality Test applied as a quality criterion.

**2. Conciseness.** Minimal token footprint for maximum behavioral impact. Preferences consume context in every conversation — verbose Preferences impose a tax on every interaction. Target: under ~500 words. Every word must earn its presence.

**3. Complementarity.** Preferences provide a foundation that Projects build on, not compete with. Preferences should set behavioral baselines (communication style, evidence standards, format preferences) that Projects can extend or override for specific contexts. If Preferences and a Project CI contradict, the user experiences unpredictable behavior.

**4. Stability.** Content that rarely changes. Preferences should capture the user's enduring behavioral preferences — not current project details, temporary instructions, or context that changes monthly. Volatile content belongs in Project CI or Memory.

**5. Clarity.** Unambiguous behavioral directives, not vague aspirations. "Be concise" is vague — it means different things in different contexts. "Match response length to query complexity — short questions get short answers, complex analysis gets thorough treatment" is clear. Preferences should be specific enough that two instances of Claude, reading the same Preferences, would behave the same way.

---

## Five Common Failures

### Failure 1: The Transplanted CI

**Detection:** Preferences text reads like a single Project's Custom Instructions — domain-specific vocabulary, role definitions, workflow details, specific tool references.

**Why it fails:** Domain-specific instructions degrade every conversation outside that domain. A Preference like "Always analyze financial data using DCF methodology" produces bizarre behavior when the user asks Claude to write a poem.

**Fix:** Extract domain-specific content to the relevant Project's CI. Keep only the universal behavioral core in Preferences.

### Failure 2: The Aspirational Wishlist

**Detection:** Preferences filled with vague aspirations rather than behavioral directives — "be creative," "think deeply," "be helpful," "give great responses."

**Why it fails:** These instructions are too vague to produce consistent behavioral change. Claude's default behavior already aims to be helpful and thoughtful. Aspirational language wastes context tokens without changing output.

**Fix:** Convert each aspiration to a specific, testable behavioral directive. "Be creative" → (remove — too vague to operationalize). "Think deeply" → "When analyzing complex problems, consider second-order effects and unintended consequences before recommending a course of action."

### Failure 3: The Instruction Dump

**Detection:** Preferences text is extremely long (1000+ words), covering every conceivable scenario with extensive detail and edge-case handling.

**Why it fails:** Long Preferences consume context in every conversation. Extensive detail drowns signal in noise — Claude has difficulty identifying which instructions matter most. Edge-case rules for scenarios that arise once a month impose context cost on every interaction.

**Fix:** Ruthlessly compress. Keep the 5-10 highest-impact behavioral directives. Move edge-case rules to the Projects where those edges actually arise. Target under ~500 words.

### Failure 4: The Stale Preferences

**Detection:** Preferences reference past projects, outdated tools, former roles, or objectives the user has moved beyond.

**Why it fails:** Stale instructions cause Claude to optimize for contexts that no longer exist. Referencing a tool the user no longer uses produces irrelevant suggestions. Referencing a former role causes tone mismatches.

**Fix:** Audit each instruction against current reality. Remove references to past contexts. Update role descriptions and tool references. Schedule periodic review (quarterly is sufficient for most users).

### Failure 5: The Silent Conflict

**Detection:** Preferences instructions contradict each other, or a Preferences instruction contradicts a Style directive without the user's awareness.

**Why it fails:** Contradictory instructions produce inconsistent behavior — Claude follows one instruction in some contexts and the other in different contexts, with no predictable pattern. The user experiences unreliable behavior without understanding the cause.

**Fix:** Read each instruction against every other instruction. Check each instruction against active Styles. Resolve contradictions by choosing one directive and removing or subordinating the other. If both directives are needed in different contexts, move the context-specific one to the relevant Project CI.
