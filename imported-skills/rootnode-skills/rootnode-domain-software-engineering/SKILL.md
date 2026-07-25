---
name: rootnode-domain-software-engineering
description: >-
  Specialized software engineering prompt methodology for Claude. Use when
  building prompts for system design, code review, incident response,
  security analysis, API design, architecture decisions, RFCs, ADRs,
  runbooks, or technical leadership. Trigger on: "build a prompt for code
  review," "system design prompt," "SRE prompt," "security review prompt,"
  "incident response prompt," "API design prompt," "architecture decision
  prompt," "RFC prompt," "runbook prompt." Provides 11 tested approaches
  across identity, reasoning, and output for engineering analysis. Do NOT use
  for general coding help, writing code, or debugging — this builds prompts
  that shape engineering analysis, not code itself. Do NOT use for evaluating
  existing prompts (use rootnode-prompt-validation if available).
license: Apache-2.0
metadata:
  author: rootnode
  version: "1.1"
  original-source: "DOMAIN_PACK_SOFTWARE_ENGINEERING.md"
---

# Software Engineering Prompt Methodology

> **Calibration:** Tier 1, Opus-primary. See repository README for model compatibility.

Specialized approaches for building Claude prompts that handle software engineering tasks — reliability engineering, security analysis, code review, API design, performance analysis, threat modeling, and engineering document formats (RFCs, ADRs, runbooks, code review feedback).

**When to use this Skill:** You have a task that requires engineering-domain expertise in a Claude prompt — not general system architecture (use a Technical Architect identity for that), but deeper specialization: SRE thinking, adversarial security analysis, code-level technical leadership, or engineering-specific deliverable formats.

**What this Skill provides:**
- 3 identity approaches (SRE / Platform Engineer, Security Engineer, Staff+ Engineer / Tech Lead)
- 4 reasoning methodologies (Code & Design Review, API Design, Performance & Scalability Analysis, Threat Modeling) — see `references/reasoning-approaches.md`
- 4 output format specifications (RFC, ADR, Runbook, Code Review Feedback) — see `references/output-formats.md`
- Behavioral countermeasures for engineering-specific Claude failure modes

## How to Use This Skill

### Step 1: Identify the Engineering Sub-Domain

Determine which specialization the task requires:

| Task Focus | Identity Approach | Primary Reasoning | Typical Output |
|---|---|---|---|
| Production reliability, incidents, observability, capacity | SRE / Platform Engineer | Performance & Scalability Analysis | Runbook |
| Threat modeling, security review, vulnerability assessment | Security Engineer | Threat Modeling | RFC or ADR |
| Code review, design review, technical mentorship | Staff+ Engineer / Tech Lead | Code & Design Review | Code Review Feedback |
| API contracts, versioning, developer experience | (Technical Architect or Staff+) | API Design | RFC or ADR |
| Proposing a significant technical change | (match to domain) | (match to task) | RFC |
| Recording an architecture decision | (match to domain) | (match to task) | ADR |

### Step 2: Select the Identity Approach

Choose one identity approach for the prompt. Each shapes Claude's perspective and priorities.

**SRE / Platform Engineer** — Use when the task involves production reliability, observability, incident management, capacity planning, infrastructure automation, or reducing operational toil. This identity thinks in terms of failure domains, blast radius, and recovery procedures — not just whether a system works, but how it fails and how quickly you recover.

```xml
<role>
You are a senior site reliability engineer with deep experience operating large-scale distributed systems in production. You think in terms of reliability budgets, failure domains, and degradation modes — not just whether a system works, but how it fails, how quickly you detect the failure, and how you recover.

You are skeptical of designs that optimize for the happy path. Every system you evaluate, you ask: What is the blast radius when this component fails? How do we know it has failed? What is the recovery procedure, and can an on-call engineer execute it at 3 AM under stress? If the answer to any of these is unclear, the design is incomplete.

You measure operational health concretely: deployment frequency, change failure rate, mean time to detection, mean time to recovery. You treat toil — repetitive manual work that scales with system size — as a reliability risk, not just an efficiency problem.
</role>
```

*Calibration notes:* This approach can push Claude toward over-engineering reliability for systems that don't need it — recommending multi-region failover for a low-traffic internal tool. Add context about traffic volume, SLA requirements, and team size to keep recommendations proportionate. For small teams, add: "Scale your reliability recommendations to a team of [N]. Practices that require dedicated SRE staffing are not viable — recommend approaches the existing engineering team can sustain." Also watch for Claude defaulting to Google SRE book terminology regardless of scale — error budgets and SLOs are powerful concepts, but the organizational overhead can exceed the benefit for small teams.

**Security Engineer** — Use when the task involves threat modeling, security architecture review, vulnerability assessment, secure design patterns, or evaluating security posture. This identity thinks adversarially — not "how does this system work?" but "how could this system be attacked?"

```xml
<role>
You are a senior security engineer with deep experience in application security, infrastructure security, and threat modeling. You think adversarially: for every system, you ask who would want to attack it, what they would target, and what capabilities they would need.

You design security in layers. No single control is sufficient — you assume every control can fail and design so that a single failure does not compromise the system. You distinguish between threats that are theoretical and threats that are practical given the system's exposure, value, and attacker profile.

You are pragmatic about risk. Perfect security does not exist. Your job is to identify the highest-impact risks, recommend controls proportionate to the threat, and be explicit about residual risk that the organization is accepting. You never obscure risk behind compliance checklists — meeting a compliance standard and being secure are different things, and you say so when they diverge.
</role>
```

*Calibration notes:* This approach can produce analysis that is overly alarming — treating every potential vulnerability as critical. Add: "Calibrate severity to this system's actual exposure and attacker profile. An internal admin tool with IP restrictions faces different threats than a public-facing API processing payments. Rank findings by realistic exploitability and business impact, not theoretical possibility." Also watch for recommendations that are technically sound but operationally infeasible — add team size and security maturity context.

**Staff+ Engineer / Tech Lead** — Use when the task involves code-level or design-level technical leadership — reviewing code, evaluating design proposals, making technical decisions within a team context, or providing mentoring-oriented technical feedback. Operates at the code and component level, not system-level architecture.

```xml
<role>
You are a staff engineer and technical lead with deep experience writing, reviewing, and maintaining production code at scale. You evaluate code and designs not just for correctness, but for maintainability — will the next engineer who touches this understand it? Can it be tested? Does it handle edge cases, or does it defer them?

Your feedback is specific and actionable. You do not say "this could be improved" — you say what should change, why, and what the better approach looks like. You distinguish between "must fix" (correctness, security, data integrity), "should fix" (maintainability, performance, clarity), and "consider" (style, alternative approaches, future-proofing).

You balance technical idealism with shipping reality. You know when to advocate for the right solution and when to accept pragmatic tradeoffs — and you are explicit about which you are doing and why. You treat every code review as an opportunity to raise the team's engineering standards, not just to gatekeep.
</role>
```

*Calibration notes:* This approach can produce feedback that is too thorough — commenting on every aspect rather than focusing on what matters. Add: "Focus your feedback on the three to five most impactful points. Not every observation needs to be raised — prioritize issues that affect correctness, security, or long-term maintainability over stylistic preferences." Also watch for Claude defaulting to a senior-teaching-junior tone. If the audience is a peer, add: "The recipient is a senior engineer. Your feedback should be collaborative and technically precise, not tutorial-style."

### Step 3: Add Reasoning and Output

Select a reasoning methodology and output format from the reference files:

- **Reasoning approaches** — see `references/reasoning-approaches.md` for four engineering-specific methodologies: Code & Design Review, API Design, Performance & Scalability Analysis, and Threat Modeling. Each includes the complete XML specification and calibration notes.
- **Output format specifications** — see `references/output-formats.md` for four engineering document formats: RFC, ADR, Runbook, and Code Review Feedback. Each includes the complete XML specification with section-level length guidance.

### Step 4: Assemble the Prompt

Combine the selected components into a complete prompt using this structure:

```
1. Identity approach (the <role> block) — sets Claude's perspective
2. Task description — what the user needs done, with specific context
3. Reasoning methodology (the <reasoning> block) — structures the analysis
4. Output format specification (the <output_format> block) — shapes the deliverable
5. Quality checks and countermeasures — inline from the section below
```

Include relevant context: system scale, team size, SLA requirements, and the specific technology stack. Engineering prompts that lack operational context produce generic recommendations.

### Step 5: Apply Quality Checks

Add these engineering-specific quality checks to any prompt built with this Skill:

- **Operational realism:** Every recommendation accounts for who operates the system. If a design or change increases operational complexity, this cost is stated — not hidden behind the technical benefits.
- **Failure mode coverage:** Designs, reviews, and analyses address what happens when things go wrong — not just how they work when everything is healthy. If failure modes are not discussed, the analysis is incomplete.
- **Proportionality:** Recommendations match the system's actual scale, team size, and reliability requirements. Enterprise-grade solutions for startup-scale problems, or vice versa, indicate miscalibrated analysis.
- **Specificity of commands and actions:** Runbooks, review feedback, and operational recommendations include exact commands, specific file paths, and concrete thresholds — not "check the logs" or "monitor the system."
- **Security as a dimension:** Any design or review that handles user input, authentication, authorization, or sensitive data addresses the security implications explicitly — even if security is not the primary focus.

## Critical: Engineering-Specific Behavioral Countermeasures

Software engineering prompts are especially susceptible to these Claude failure modes. Inline the relevant countermeasures into any prompt you build.

**Resume-driven design.** Claude may recommend technologies, architectures, or patterns that are technically impressive but inappropriate for the actual scale and team — Kubernetes for a single-service app, event sourcing for a CRUD system, microservices for a three-person team. Counter with: "Design for the actual scale and team. The best architecture is the simplest one that meets the requirements. If you recommend a complex approach, justify specifically why the simpler alternative is insufficient."

**Uncritical code review.** Claude's agreeableness tendency is especially problematic in code review — it may praise code that has genuine issues or soften critical findings with excessive hedging. Counter with: "Your job in this review is to find problems and improve the code, not to validate the author. Be direct about issues. If the code has a significant flaw, state it clearly and specifically."

**Buzzword architecture.** Claude may use terms like "event-driven," "domain-driven design," "hexagonal architecture," or "zero-trust" as design labels without actually applying the underlying principles. Counter with: "Do not name architectural patterns unless you are concretely applying them. If you reference a pattern, show how it specifically shapes this design — do not use it as a label."

**Happy-path bias.** Claude may produce designs and analyses that focus on how the system works under normal conditions while giving insufficient attention to failure modes, edge cases, and degraded states. Counter with: "For every component or interaction, describe the failure mode before the success path. What happens when this component is unavailable, slow, or returning errors?"

**Theoretical security.** When doing security analysis, Claude may list vulnerabilities from a textbook without calibrating to the actual system's threat profile. Counter with: "Every security finding must be tied to a specific component in this system and a realistic attack scenario. Do not list generic vulnerability categories — describe how each vulnerability could be exploited in this specific architecture."

## Troubleshooting

**Output is too generic / not engineering-specific enough.** The prompt likely lacks operational context. Add: system scale (requests/second, data volume), team size, SLA requirements, technology stack, and deployment environment. Engineering prompts without this context produce recommendations that could apply to any system.

**Recommendations are disproportionate to scale.** Add explicit scale constraints: "This is a [small/medium/large] system operated by a team of [N]. Recommendations must be sustainable by this team without dedicated [SRE/security/platform] staffing."

**Code review feedback is too soft.** Add the uncritical code review countermeasure (above) and: "This review must identify at least the most significant improvement opportunity. A review with no actionable findings is not useful."

**Security analysis reads like a checklist.** Add the theoretical security countermeasure (above) and specify the threat actor profile: "The primary threat actors for this system are [description]. Focus on attack vectors realistic for these actors."

**RFC alternatives section is a straw man.** Add: "Each alternative must be presented as a legitimate option that a reasonable engineer could prefer. If no alternatives are genuinely competitive, state that explicitly — do not fabricate weak alternatives."

For deeper prompt evaluation methodology, see `rootnode-prompt-validation` if available. For general prompt construction methodology beyond engineering-specific tasks, see `rootnode-prompt-compilation` if available.
