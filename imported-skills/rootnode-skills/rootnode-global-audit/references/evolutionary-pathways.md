# Evolutionary Pathways

Four pathways that strengthen the global foundation over time, plus the Cross-Project Pattern Analysis that feeds the Promotion pathway. Each pathway runs independently based on available information.

---

## Pathway 1: Promotion (Project → Global)

**Direction:** Instruction moves from Project CI to User Preferences.
**Trigger:** Same instruction (or semantic equivalent) appears in 3+ Project CIs.
**Test:** The Universality Test — "Would this instruction improve output in every conversation and Project, without degrading any of them?"

**Mechanism:**
1. Identify the candidate instruction across Projects. Quote each instance.
2. Determine the canonical form — the most precise, concise version across all instances.
3. Apply the Universality Test. Test against the user's known Projects and plausible future contexts.
4. If it passes: draft the Preferences instruction text. State which Projects' CIs can be trimmed.
5. If it partially passes: note which contexts it would degrade and recommend keeping in CI with a note about the tradeoff.

**Graceful degradation:** Requires CIs from 3+ Projects. With fewer, note that Promotion analysis is skipped and state the minimum input needed.

**Confidence guidance:** High confidence when the instruction appears verbatim in 3+ Projects and passes the Universality Test cleanly. Moderate when semantic equivalents appear (same intent, different phrasing). Lower when the instruction appears in 3+ Projects but the Universality Test reveals edge cases.

**Example:** "Always explain the reasoning behind decisions" appears in a coding Project, a strategy Project, and a research Project → strong Promotion candidate (universal behavioral directive). "Use Python for all code examples" appears in 3 Projects → weak candidate (degrades contexts where JavaScript or other languages are more appropriate).

---

## Pathway 2: Demotion (Global → Project)

**Direction:** Instruction moves from User Preferences to Project CI.
**Trigger:** A Preferences instruction fails the Universality Test — it improves some contexts but degrades or is irrelevant in others.
**Test:** The Specificity Test — "Does this instruction contain domain-specific content, audience assumptions, or workflow details that only apply to certain Projects?"

**Mechanism:**
1. Apply the Specificity Test to each Preferences instruction.
2. For failing instructions: identify which Projects benefit from the instruction.
3. Draft the CI placement — recommend which Projects should receive the instruction.
4. Draft the trimmed Preferences — the instruction removed or generalized.

**Graceful degradation:** Demotion analysis can run with Preferences alone (no Project CIs needed). However, identifying the correct destination Projects requires CI context.

**Confidence guidance:** High confidence when the instruction clearly contains domain-specific vocabulary. Moderate when the instruction is general but biased toward a specific workflow. Lower when the instruction is arguably universal but verbose.

**Example:** "When writing code, always include error handling and logging" in Preferences → Demotion candidate. It is valuable but only in coding contexts. Demote to coding Project CI. Keep a generalized version in Preferences if appropriate: "Be thorough and consider failure cases."

---

## Pathway 3: Codification (Memory → Preferences/CI)

**Direction:** Behavioral pattern moves from Memory (Global or Project) to explicit instruction (Preferences or CI).
**Trigger:** A Memory entry captures a behavioral preference that Claude should follow consistently — currently relying on Memory recall rather than explicit instruction.
**Test:** The Stability Test — "Has this pattern been stable for 4+ weeks with no conflicting updates? Would the user want this enforced even if Memory were cleared?"

**Mechanism:**
1. Scan Memory entries for behavioral directives (how Claude should act, not what the user's context is).
2. Apply the Stability Test. Recent entries (added in the last 1-2 weeks) are flagged as moderate confidence.
3. Determine destination: apply the Universality Test. If universal → codify as Preferences instruction. If project-specific → codify as CI instruction.
4. Draft the instruction text. Convert Memory's descriptive phrasing to directive phrasing (Memory: "User prefers concise responses" → Instruction: "Be concise. Match response length to query complexity.").
5. Prescribe the Memory edit — the entry can be removed once the instruction is codified, since the instruction now governs directly.

**Graceful degradation:** Requires Memory summary. Without it, the pathway is skipped.

**Confidence guidance:** High confidence for entries that have been stable for months and clearly describe behavioral preferences. Moderate for entries stable 4+ weeks. Lower for recent entries or entries where the behavioral intent is ambiguous.

**Example:** Memory entry "User always wants code examples in responses" → Codification candidate. Stable behavioral preference. Universality Test: improves coding contexts, neutral in non-coding contexts. Codify as Preferences instruction: "Include code examples when relevant to the discussion." Remove the Memory entry after codification is confirmed.

---

## Pathway 4: Skill Extraction (Knowledge File → Skill)

**Direction:** Procedural content moves from a Project knowledge file to a standalone Skill.
**Trigger:** A knowledge file contains a reusable procedure, workflow, or methodology that could benefit multiple Projects or users.
**Test:** The Portability Test — "Would this procedure work in a different Project with different CI, or does it depend on this specific Project's configuration?"

**Mechanism:**
1. Identify candidate content — look for step-by-step procedures, decision trees, checklists, or methodologies in knowledge files that are referenced across conversations.
2. Apply the Portability Test. Check for dependencies on the host Project's CI, other knowledge files, or specific tools.
3. If portable: produce a draft Skill description (following the Skills spec: what it does + when to use it + trigger phrases). Outline the Skill structure (what goes in SKILL.md body vs. references/).
4. If partially portable: note the dependencies and estimate the adaptation work.
5. Do not build the full Skill — produce the extraction outline and let the user decide whether to proceed.

**Graceful degradation:** Requires knowledge file descriptions or content. Without them, the pathway is skipped. Note that this pathway produces the lowest-confidence recommendations — portability is often inferred from the content alone, without testing in other contexts.

**Confidence guidance:** High confidence only when the procedure is clearly self-contained and uses no project-specific references. Moderate when minor adaptation would be needed. Lower when portability is inferred but untested.

**Example:** A Project knowledge file contains a detailed code review checklist that any developer could use → strong extraction candidate. A knowledge file contains a "how we do sprint planning at [company]" procedure → weak candidate (company-specific workflow, low portability without significant adaptation).

---

## Cross-Project Pattern Analysis

When the user provides Custom Instructions from 3+ Projects, run this analysis to identify patterns that feed the Promotion pathway.

**Step 1: Normalize.** For each Project CI, extract individual instructions — separate compound paragraphs into discrete behavioral directives.

**Step 2: Cluster.** Group semantically equivalent instructions across Projects. Two instructions are equivalent if they produce the same behavioral outcome even when phrased differently. Be strict — "be concise" and "keep responses brief" are equivalent; "be concise" and "be thorough" are not.

**Step 3: Score frequency.** For each cluster, count how many Projects contain an equivalent instruction. Clusters appearing in 3+ Projects are Promotion candidates.

**Step 4: Test universality.** Apply the Universality Test to each Promotion candidate. Not every repeated instruction is universal — a domain-specific instruction repeated across domain-similar Projects should stay in those Projects' CIs.

**Step 5: Draft recommendations.** For each candidate that passes: draft the Preferences instruction (canonical form), list the Projects whose CIs can be trimmed, and state the confidence level.

---

## Maturity Orientation

The global layer audit maps to a four-stage maturity model for context:

**Stage 1 — Sparse Global:** Preferences empty or minimal. No Styles. Memory accumulating organically. Few or no Skills or Connectors. Most configuration lives in individual Projects.

**Stage 2 — Emerging Patterns:** Some Preferences set. Cross-project patterns visible but not yet promoted. Memory contains behavioral directives that should be codified. Skill portfolio growing but not curated.

**Stage 3 — Optimized Foundation:** Preferences capture universal behavioral directives. Styles complement without conflicting. Memory is clean orientation context. Skills are curated and collision-free. Global layers provide a strong foundation that every Project builds on.

**Stage 4 — Self-Reinforcing System:** Global layers are actively maintained. New Projects start faster because the foundation handles shared concerns. Cross-project pattern analysis runs periodically. Evolutionary pathways are practiced habits, not one-time fixes.

Use these stages to orient the user on their current position and the direction of improvement. The maturity model is context, not methodology — it describes where the user is, not what steps to take (the pathways handle that).
