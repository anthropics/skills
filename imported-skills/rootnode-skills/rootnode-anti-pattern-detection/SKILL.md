---
name: rootnode-anti-pattern-detection
description: >-
  Detects seven structural anti-patterns in Claude Projects that cause
  unpredictable output, ignored instructions, and degraded quality. Diagnoses
  Monolith, Orphan File, Echo Chamber, Phantom Conversation, Kitchen Sink,
  Misaligned Hierarchy, and Blurred Layers. Use when user says "what's wrong
  with my project," "Claude ignores my instructions," "diagnose my project,"
  "why is output inconsistent," "review my project setup." Also trigger on
  symptom-phrased: "Claude doesn't follow my rules," "my instructions keep
  getting overridden," "my Project isn't behaving as designed." Use alongside
  rootnode-project-audit if available for deeper structural analysis. Activate
  whenever the user describes symptoms of unreliable, inconsistent, or degraded
  Claude Project output, even if they do not name a specific pattern. Do NOT use
  when the user's primary request is Memory-layer rebalancing (use
  rootnode-memory-optimization if available) or scoring a single prompt (use
  rootnode-prompt-validation if available).
license: Apache-2.0
metadata:
  author: rootnode
  version: "1.1.1"
  original-source: "AUDIT_FRAMEWORK.md"
---

# Anti-Pattern Detection for Claude Projects

> **Calibration:** Tier 2, Opus-primary. See repository README for model compatibility.

Detect and fix the seven structural mistakes that cause Claude Projects to underperform. Each pattern has specific detection criteria and symptoms — diagnose by evidence, not intuition.

## Critical: Evidence-First Diagnosis

Never assert a pattern without citing the specific component that exhibits it. For every pattern you detect, quote the exact text from the user's Custom Instructions or knowledge files that demonstrates the problem. If you cannot point to concrete evidence, the pattern is not confirmed.

## Reasoning discipline

A defensible diagnosis shows its evidence. Observe the specific file contents, structural features, duplication instances, and layer assignments; name the anti-pattern they match against the detection criteria; then explain the severity and impact. A summary diagnosis without the observation-pattern-impact chain is harder to act on and harder to dispute — the hard rule (evidence-first, above) keeps the assertion valid; the walk-through keeps it actionable.

If the diagnosis scope is unclear (which files are in scope? which Project layers? all seven patterns or a subset?), confirm scope with the user before proceeding. Do not proceed on inferred assumptions.

## When to Use This Skill

Use this when a user:
- Shares their Claude Project (Custom Instructions, knowledge file descriptions, or both) and asks what is wrong or how to improve it
- Describes symptoms of unreliable output: inconsistent quality, ignored instructions, Claude treating rules as optional, output that varies unpredictably across conversations
- Asks for a project review, diagnosis, or health check
- Is troubleshooting a specific problem with their Claude Project setup

If the user provides their Custom Instructions and/or knowledge file descriptions, check for all seven patterns systematically. Report only the patterns you find evidence for — do not pad the diagnosis with patterns that are not present.

## The Seven Anti-Patterns

### 1. The Monolith

**What it is:** Custom Instructions that exceed roughly 1500 words AND contain reference material (examples, frameworks, data tables, extended explanations) mixed in with behavioral instructions. Alternatively, a single knowledge file that serves multiple distinct purposes.

**Symptoms the user sees:** Inconsistent adherence to behavioral rules. Claude treats some instructions as optional. Output quality varies unpredictably.

**Detection criteria:**
- Custom Instructions contain data tables, extended examples, framework descriptions, or reference material alongside behavioral directives
- A single knowledge file covers multiple unrelated topics or serves both instructional and reference purposes
- The system prompt is doing double duty as both a behavioral directive and a reference document

**The fix:** Separate behavioral instructions from reference material. Custom Instructions should contain only identity, behavioral rules, knowledge file routing, operational modes, and output standards. Move all reference material — frameworks, examples, data, templates — into dedicated knowledge files. If a knowledge file serves multiple purposes, split it into single-purpose files.

### 2. The Orphan File

**What it is:** A knowledge file that exists in the Project but is not referenced by name in Custom Instructions, or is referenced with only an inventory description rather than routing guidance.

**Symptoms the user sees:** Claude rarely or never draws from the file's content. Information from the file is absent from output even when directly relevant to the user's question.

**Detection criteria:**
- A knowledge file is not mentioned at all in Custom Instructions
- A knowledge file is mentioned only as inventory ("This project contains company_info.md") rather than with routing guidance ("Consult company_info.md when the user asks about our product, market, or competitive position")
- The routing description does not tell Claude when to consult the file — only that it exists

**The fix:** Add explicit routing guidance to Custom Instructions for every knowledge file. Routing should specify the file name and the conditions under which Claude should consult it. Format: "Consult [filename] when [specific trigger conditions]." The trigger conditions should describe the user's likely questions or task types, not the file's internal structure.

### 3. The Echo Chamber

**What it is:** The same instruction, principle, or rule appears in multiple locations with different wording. This creates ambiguity about which version is authoritative.

**Symptoms the user sees:** Inconsistent behavior — Claude follows one version of the instruction in some conversations and a different version in others. Or Claude synthesizes the variations into a compromise that matches none of the intended versions.

**Detection criteria:**
- An instruction in Custom Instructions is restated (with different wording) in a knowledge file
- The same behavioral rule appears in multiple knowledge files with subtle variations
- Overlapping guidance exists across components — not identical text, but instructions that govern the same behavior with different specifics

**The fix:** Establish one authoritative location for each instruction. Behavioral rules belong in Custom Instructions. Reference material belongs in knowledge files. If the same concept must appear in multiple places, use identical wording — or better, state it once and reference that location. Audit for subtle duplicates: rules that use different language but govern the same behavior.

### 4. The Phantom Conversation

**What it is:** Custom Instructions written in a conversational, chatty style rather than as clear directives. The system prompt reads like a friendly briefing rather than an operating manual.

**Symptoms the user sees:** Claude treats instructions as suggestions rather than directives. Behavioral rules are followed inconsistently because the conversational framing reduces their perceived authority.

**Detection criteria:**
- Custom Instructions open with greetings or conversational preamble ("Hi Claude, in this project you'll be helping with...")
- Instructions are phrased as suggestions ("You might want to consider..." / "It would be great if you could...")
- The overall tone is collaborative rather than directive
- Rules use hedged language instead of clear imperatives

**The fix:** Rewrite Custom Instructions in imperative, declarative form. Replace "You might want to think about X" with "Consider X when [condition]." Replace "It would be great if you could be concise" with "Keep responses under [length] unless the task requires more." The system prompt is an operating specification, not a conversation. Directive language produces more reliable compliance.

### 5. The Kitchen Sink

**What it is:** Custom Instructions that contain rules for edge cases, rare scenarios, or "just in case" situations, diluting Claude's attention to the core behavioral rules that matter in the majority of conversations.

**Symptoms the user sees:** Core behavioral rules are followed less reliably. Output quality is mediocre across all scenarios rather than excellent for common scenarios. The system prompt is long but the output does not reflect the investment.

**Detection criteria:**
- Custom Instructions address more than 8-10 distinct behavioral instructions
- Instructions include conditional logic for scenarios that arise less than 10% of the time
- Rules include "just in case" provisions for rare situations
- The system prompt could be 30% or more shorter without degrading output for the user's typical tasks

**The fix:** Ruthlessly prioritize. Identify the 5-7 behavioral rules that affect the most conversations and keep those. Remove or move to a knowledge file any instruction that addresses a rare scenario. Apply the test: "If I removed this instruction, would the output for my typical tasks get noticeably worse?" If the answer is no, remove it. A shorter, focused system prompt outperforms a comprehensive one.

### 6. The Misaligned Hierarchy

**What it is:** Behavioral instructions placed in knowledge files rather than in Custom Instructions, without explicit delegation from the system prompt. Or: the system prompt is brief and high-level while a knowledge file contains the actual behavioral rules that should govern Claude's behavior.

**Symptoms the user sees:** Unpredictable adherence to behavioral rules. Claude may treat knowledge-file instructions as context rather than directives. Rules in knowledge files may be followed in some conversations and ignored in others.

**Detection criteria:**
- Knowledge files contain imperative instructions ("Always do X," "Never do Y," "When the user asks about Z, respond with...")
- The system prompt is notably brief while a knowledge file is doing the heavy behavioral lifting
- The system prompt does not explicitly delegate behavioral authority to knowledge files (e.g., it does not say "Follow the behavioral guidelines in style-guide.md")

**The fix:** Move all behavioral instructions to Custom Instructions. Knowledge files should contain reference material — facts, frameworks, data, templates, examples — not operating rules. If behavioral instructions must remain in a knowledge file (because of length constraints), the system prompt must explicitly delegate authority: "Follow the behavioral guidelines in [filename] as directives." Without this delegation, Claude may interpret knowledge-file instructions as informational context rather than rules to follow.

### 7. The Blurred Layers

**What it is:** Memory and knowledge files contain content that belongs in the other layer. Memory holds reference-depth content that should be in knowledge files, or knowledge files hold always-relevant orientation facts that should be in Memory. Or the same facts appear in both layers without a clear authoritative home.

**Symptoms the user sees:** Wasted always-loaded context on material Claude only needs occasionally (Memory overloaded with reference content). Or Claude starts conversations without key orientation context that would improve first-message relevance (orientation facts buried in knowledge files). Or Claude cites contradictory versions of the same fact from different layers (duplication with drift).

**Detection criteria:**
- Memory edits contain detailed explanations, procedural steps, decision rationale, or historical context — content that belongs in a knowledge file
- Knowledge files contain always-relevant orientation facts (current project phase, active constraints, key decisions) that should be in Memory for immediate availability
- The same fact appears in both a Memory edit and a knowledge file, with no clear authoritative source — creating a coherence risk if one is updated and the other is not

**The fix:** Apply the layer placement principle. Memory holds always-loaded orientation — concise facts relevant to most conversations (current phase, active constraints, key decisions). Knowledge files hold searchable depth — structured content consulted on demand. Move reference-depth content out of Memory into knowledge files. Move orientation facts out of knowledge files into Memory. For duplicated facts, choose one authoritative layer and remove the other copy, or replace the non-authoritative copy with a pointer. For deeper optimization, recommend rootnode-memory-optimization if available.

## How to Conduct the Diagnosis

1. **Read the user's Custom Instructions completely** before checking any pattern. Many patterns are only visible in the context of the full system prompt.

2. **Check each pattern in order.** Some patterns co-occur (Monolith + Misaligned Hierarchy is common; Echo Chamber + Orphan File is common). Checking systematically prevents you from stopping at the first issue found.

3. **For each pattern detected, cite specific evidence.** Quote the text that demonstrates the pattern. Name the specific file or section where the problem occurs.

4. **For each pattern detected, provide the specific fix** — not just "fix this" but the concrete action: what to move, what to rewrite, what to delete.

5. **Report patterns not found as clean.** A brief statement ("No Echo Chamber detected — instructions are not duplicated across components") confirms you checked and builds confidence in the diagnosis.

6. **Prioritize the fixes.** If multiple patterns are present, recommend the fix order. The Misaligned Hierarchy and Orphan File are typically highest priority because they cause the most severe compliance failures. The Kitchen Sink is typically lowest priority because it degrades quality gradually rather than causing outright failures.

## Output Format

Structure your diagnosis as:

For each pattern — state whether it was detected or not. If detected, provide:
- The specific evidence (quoted text from the user's Project materials)
- Why this is a problem (the specific impact on this Project, not generic consequences)
- The concrete fix (what to change, move, rewrite, or delete)

After all seven patterns, provide a prioritized action plan listing the fixes in recommended order.

Match response length to the severity of the findings. A Project with one minor pattern needs a focused, brief diagnosis. A Project with four patterns needs a thorough analysis. Do not inflate a clean diagnosis or pad a simple finding.

## Common Mistakes to Avoid

**Asserting patterns without evidence.** If you suspect a pattern but cannot quote specific text that demonstrates it, note the suspicion but do not diagnose it as confirmed.

**Diagnosing based on length alone.** Long Custom Instructions are not automatically a Monolith. The Monolith pattern requires mixed content types (behavioral instructions + reference material), not just length.

**Recommending knowledge files without routing.** When fixing a Monolith by moving reference material to a knowledge file, always include the routing guidance that should be added to Custom Instructions. Otherwise you create an Orphan File while fixing the Monolith.

**Over-diagnosing the Kitchen Sink.** Not every conditional instruction is a Kitchen Sink item. Instructions for scenarios that arise 20-30% of the time are legitimate. The Kitchen Sink pattern applies to truly rare edge cases (under 10% relevance).

**Ignoring the hierarchy question.** When reviewing knowledge files, always check whether they contain behavioral instructions. The Misaligned Hierarchy is one of the most common and most impactful patterns, and it is easy to overlook because knowledge files are often treated as "just reference material."
