# Troubleshooting

Common issues with how this Skill is invoked or what it produces, with diagnoses and fixes. Read when the Skill output isn't landing or the user signals a specific problem.

For the structural patterns this Skill applies, see the other reference files. This document is symptom-organized — start with the symptom you're observing, find the matching diagnosis, apply the fix.

---

## Table of contents

1. Skill output issues (what gets produced)
2. Skill activation issues (how the Skill triggers)
3. Mode dispatch issues
4. Brief-related issues
5. Source discipline issues
6. Composition issues with other Skills

---

## 1. Skill output issues

### Symptom: CLAUDE.md draft is generic, not tailored to the project

**Diagnosis:** The design brief was missing or thin. The Skill is producing pattern-shape output without project-specific grounding.

**Fix:** Generate the brief first via the 5-question interview (see `cc-methodology-patterns.md` §10) before producing the deployment plan. The brief is the grounding artifact — without it, output drifts toward generic patterns. If the user wants a quick pass without a brief, narrow the deliverable scope (one section, one rule, one prompt) so the lack of grounding is bounded.

---

### Symptom: Output is too long and context-heavy

**Diagnosis:** The Skill is re-deriving the same pattern across multiple invocations instead of factoring it out.

**Fix:** Use TEMPLATE mode as a pressure release. Extract the reusable structural pattern into a `{project_code}_template_*` or `shared_template_*` artifact and reference it from delivery-project briefs. Future EVOLVE/DESIGN outputs can point to the template instead of re-deriving.

---

### Symptom: Output recommends rootnode runtime tooling for a project that doesn't need it

**Diagnosis:** The tool/agent gap discipline was skipped (see SKILL.md `Important` section). The Skill recommended handoff-trigger-check or critic-gate or similar without naming the specific operational gap.

**Fix:** For each runtime Skill recommendation, name the specific operational gap it fills in this project. If you can't, drop the recommendation. "Adding X for completeness" is anti-pattern.

---

### Symptom: Output makes claims without source backing

**Diagnosis:** Source discipline was skipped. Substantive technical claims about CC behavior, MCP capability, or pattern lack inline source tags.

**Fix:** Re-walk the output and tag every substantive claim per `source-grading-and-tagging.md` §2. If a claim is `[speculation]`, mark it explicitly — that's acceptable when labeled. If a claim has no source backing and isn't speculative, either find a source or remove the claim.

---

### Symptom: Output is in XML format, not Markdown

**Diagnosis:** The Skill produced CLAUDE.md content using XML tags. CLAUDE.md is consumed by Claude Code as Markdown — it's not a system prompt.

**Fix:** Convert to Markdown. Use `##` and `###` headers, fenced code blocks, tables for matrices. XML tags are for system prompts (chat-side Custom Instructions); CLAUDE.md is the standing context file CC reads as Markdown.

---

### Symptom: CLAUDE.md draft exceeds 200 lines

**Diagnosis:** The draft has placement-rule violations — multi-step procedures, path-specific rules, or reference material that should live elsewhere.

**Fix:** Apply the placement table from `cc-environment-design-patterns.md` §1. Multi-step procedures → Skills (`.claude/skills/`). Path-specific rules → `.claude/rules/{name}.md` with `paths:` frontmatter. Detailed reference → dedicated files the agent reads on demand. Behavioral guarantees → hooks. Trim CLAUDE.md until only "facts that matter every session" remain.

---

### Symptom: Halt-and-escalate triggers are vague

**Diagnosis:** Triggers were written as preferences ("halt if something seems risky") instead of as concrete conditions the agent can recognize unambiguously.

**Fix:** Re-write each trigger as a single concrete condition. See `cc-methodology-patterns.md` §8 for the format. Bad: "halt if the change feels risky." Good: "halt if the change would modify any line containing the string `# AUTHORITY:` in a CLAUDE.md-flagged file." Triggers must be verifiable from the agent's vantage point.

---

## 2. Skill activation issues

### Symptom: Skill doesn't fire when the user asks for CC design help

**Diagnosis:** Description-field auto-activation didn't match the user's phrasing.

**Fix:** Check the trigger phrases in the description field against the user's actual phrasing. The description includes "design CC for X", "build CC environment", "scaffold a Claude Code repo", "design CLAUDE.md" — if the user's phrasing differs significantly, paraphrase it to one of those triggers, or invoke the Skill explicitly. If a recurring user phrasing is missing from the description, that's a Skill-revision finding to feed back to rootnode-skill-builder.

---

### Symptom: Skill fires when it shouldn't (e.g., user asked for chat prompt help)

**Diagnosis:** The Skill's negative triggers didn't catch the case, or the Skill's positive triggers overlap with another Skill's domain.

**Fix:** The description has explicit negative triggers for chat-prompt evaluation (rootnode-prompt-validation) and chat-Project audit (rootnode-project-audit). If the user's request is genuinely chat-side and this Skill fired anyway, redirect to the correct Skill. If this misfire recurs, it's a description-tuning finding — the negative triggers may need strengthening.

---

### Symptom: Two Skills both seem to apply (this one + rootnode-project-audit)

**Diagnosis:** Domain overlap. This Skill audits Claude Code deployments (CLAUDE.md, `.claude/`, hooks, MCP). rootnode-project-audit audits chat-based Claude Projects (Custom Instructions, knowledge files, Project Memory).

**Fix:** Different surfaces. If the deliverable involves CC artifacts (CLAUDE.md, settings.json, agents/, skills/, hooks), this Skill applies. If the deliverable involves chat-Project Custom Instructions or knowledge files, rootnode-project-audit applies. Confirm with the user which surface they're working on.

---

## 3. Mode dispatch issues

### Symptom: Skill chose the wrong mode

**Diagnosis:** Signal-inferred mode dispatch picked the wrong mode based on phrasing.

**Fix:** Confirm the mode in one line at the start of the response (per SKILL.md Step 1). If the inferred mode is wrong, the user can correct in their next turn ("REMEDIATE, not EVOLVE — I want to close the loop on the hygiene findings"). Since mode is confirmed up-front, correction is cheap.

---

### Symptom: User wants multiple modes or Skills in one request (e.g., hygiene scan then REMEDIATE the findings)

**Diagnosis:** Multi-step requests are valid but should be sequenced explicitly, not merged.

**Fix:** Acknowledge the sequence in the opening confirmation: "Hygiene scan first (rootnode-repo-hygiene if installed), then REMEDIATE MODE to consume the findings and produce the EXECUTION_PLAN." Run hygiene to completion, surface the report, then transition to REMEDIATE. Don't intermix — the verbs have different output formats and different responsible Skills.

---

### Symptom: Request looks like RESEARCH but the user wants a recommendation, not a survey

**Diagnosis:** RESEARCH mode often gets misread as "give me all the options." It's "give me a decisive recommendation grounded in source-tagged evidence."

**Fix:** RESEARCH mode outputs always end with a decisive recommendation (adopt / defer / reject). If the user wants a survey without a recommendation, that's a different request — clarify and adjust output format accordingly.

---

## 4. Brief-related issues

### Symptom: User refuses the 5-question interview

**Diagnosis:** Brief generation feels heavy for what the user perceives as a small ask.

**Fix:** Use judgment. Small focused asks (one CLAUDE.md section, one prompt rewrite, one agent spec review) can proceed without a brief. The brief grounds multi-faceted design work. If the request is single-shot, skip the interview. If the request later expands, generate the brief at that point.

---

### Symptom: Brief exists but feels stale (project state has changed)

**Diagnosis:** Brief `last_updated` is > 90 days old, or front-matter enums no longer match reality (e.g., brief says `current_state: greenfield` but the project has shipped).

**Fix:** Surface the staleness explicitly. Offer to refresh the brief via a focused 2-3 question delta interview ("what's changed since last update?"). Don't re-run the full 5-question interview; just patch the changed sections.

---

### Symptom: Multiple briefs exist for similar projects, getting confusing

**Diagnosis:** No project-naming discipline; briefs from different delivery projects collide.

**Fix:** Brief filename is `{project_code}_design_brief.md` and it lives in the delivery project's KFs (or repo). One brief per delivery project. If multiple briefs are in chat-context for cross-project comparison work, name them inline (e.g., "the RT brief says X; the dt brief says Y").

---

## 5. Source discipline issues

### Symptom: Source tags on output feel performative / cluttered

**Diagnosis:** Tagging every trivial fact creates noise. The discipline applies to *substantive* claims about CC behavior, MCP capability, or design pattern — not to every sentence.

**Fix:** Tag the load-bearing claims (the ones that drive a recommendation or constraint). Don't tag obvious facts ("CLAUDE.md is a Markdown file"). The reader should be able to evaluate the evidence backing of recommendations, not be drowned in metadata.

---

### Symptom: User asks "why did you say X?" and the source tag was missing

**Diagnosis:** A substantive claim went out without a source tag. Backfilling the source under questioning is acceptable, but the missed tag is the symptom.

**Fix:** Find the source. State it. If it can't be found, mark the claim as `[speculation]` or retract it. Don't bluff.

---

### Symptom: Recommendation is grounded only in Tier 5 (community sources)

**Diagnosis:** The candidate has only community signal, not Anthropic primary docs or named practitioner backing.

**Fix:** Tag the recommendation as speculative ("[speculation — only Tier 5 sources support this]"). State what would upgrade the confidence (e.g., "if a named practitioner publishes a working example of this pattern, the recommendation would move to Tier 4"). Don't dress speculation as authoritative.

---

## 6. Composition issues with other Skills

### Symptom: This Skill recommends rootnode-handoff-trigger-check; user says it's not installed

**Diagnosis:** The Skill recommends optional runtime tooling that the user may not have. Cross-Skill references in this Skill use "if available" language.

**Fix:** The recommendation is conditional. If handoff-trigger-check isn't installed, the user can either (a) install it from the rootnode-skills repo at github.com/drayline/rootnode-skills, or (b) walk the 7 readiness conditions manually using `chat-to-code-handoff-patterns.md` §2 as the checklist.

---

### Symptom: This Skill's TEMPLATE mode output overlaps with rootnode-skill-builder territory

**Diagnosis:** TEMPLATE mode produces reusable artifacts; rootnode-skill-builder produces deployment-ready Skills. Both involve packaging reusable patterns.

**Fix:** Different output classes. TEMPLATE mode produces CC artifacts (CLAUDE.md skeletons, agent role specs, scope-authorization clause templates) for delivery projects. rootnode-skill-builder produces Skills (SKILL.md + references/) for the chat-side Skill ecosystem. If the user wants a new chat-side Skill, redirect to rootnode-skill-builder.

---

### Symptom: REMEDIATE feels like it's doing audit work that should belong to rootnode-repo-hygiene

**Diagnosis:** REMEDIATE consumes audit findings; it does not produce them. If REMEDIATE Phase 1 is generating findings (rather than reading them from `HYGIENE_REPORT.md`), the workflow is inverted.

**Fix:** Don't bypass rootnode-repo-hygiene by re-deriving the audit inside REMEDIATE. The two Skills are split for a reason — hygiene owns scan + diagnose; cc-design owns plan + execute. If the user invokes REMEDIATE without a hygiene report present, halt and recommend running hygiene first. The CP-only flow (paste findings) is acceptable but should still treat hygiene's output format as the input contract — REMEDIATE doesn't generate findings, it consumes them.

---

### Symptom: User asked the Skill to "review my CLAUDE.md" or "audit my CC project"

**Diagnosis:** These triggers belong to rootnode-repo-hygiene now, not this Skill. The user's phrasing routed here either because of vocabulary overlap or because rootnode-repo-hygiene isn't installed.

**Fix:** Three paths. (a) If rootnode-repo-hygiene is available, redirect: "audit-style review of an existing CC environment is rootnode-repo-hygiene's territory; want me to invoke that instead?" (b) If the user wants to review a *draft* CLAUDE.md *during design work* (not against a deployed environment), that fits EVOLVE mode framed as "review and propose deltas." (c) If rootnode-repo-hygiene isn't installed and the user wants the audit anyway, this Skill can do a one-off review using `cc-anti-patterns.md` as a checklist, but flag it as out-of-scope for v1.1+ — the proper home is rootnode-repo-hygiene, and the workflow should pivot there for repeat use.

---

## End of troubleshooting reference
