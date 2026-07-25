# Project Brief Template

This reference contains the complete brief template with per-field guidance, examples of strong vs. weak section content, and structural notes for the brief builder.

Read this file when assembling a brief (Generate Step 4) for the full template and field-level guidance.

---

## Complete Template

```markdown
# Project Brief: {PROJECT_NAME}

**Generated:** {YYYY-MM-DD}
**Project code:** {prefix_}
**Brief version:** {1.0, 2.0, etc. — increment on regeneration}
**Token estimate:** {approximate token count of this brief}
**Context mode at generation:** {Full-context | Retrieval (RAG)}

## 1. Identity & Purpose

{2-4 sentences: What this project is. What it does. Who it serves. What domain it operates in. What makes it distinct from other projects in the portfolio.}

## 2. Scope & Boundaries

**In scope:**
{What this project handles — task types, domains, deliverables.}

**Out of scope:**
{What this project explicitly does NOT handle. Where those excluded tasks are handled instead (name the project or tool if known).}

## 3. Current State

**Phase/Stage:** {Current phase, build stage, or maturity level}
**Active work:** {1-3 sentences on current focus areas}
**Recent decisions:** {Key decisions made recently that shape current direction}
**Blockers/Constraints:** {Active blockers, resource constraints, or dependencies waiting on external input}
**Last significant update:** {Date or approximate timeframe of last major change}

## 4. Architecture Summary

### Custom Instructions
{Structural summary of the CI — NOT a reproduction. Cover:
- Identity approach (what role/persona, if any)
- Key behavioral rules (the 3-5 most impactful rules)
- Operational modes (if the project has distinct modes, name them and state trigger conditions)
- Output standards (format requirements, length constraints, quality gates)
- Any notable structural patterns (XML tags, primacy-recency layout, etc.)}

### Knowledge Files

| File | Purpose | Type | Est. Tokens |
|------|---------|------|-------------|
| {filename} | {1-sentence purpose} | {Behavioral / Referential} | {estimate} |

**Notes:** {Any observations about knowledge file architecture — organization pattern, naming convention, cross-file dependencies, index files, etc.}

### Memory

**Orientation facts:**
{Identity, role, phase awareness, key constraints — facts Claude needs on every turn}

**State tracking:**
{Current phase, active work, recent decisions, progress markers}

**Behavioral preferences:**
{Communication style, output format preferences, working patterns}

**Active constraints:**
{Rules, boundaries, or limitations currently in effect}

### Skills & Connectors

**Relevant Skills:** {List installed Skills referenced or used by this project, with brief note on role}
**MCP Connectors:** {Configured connectors and how the project uses them}
**CI routing for Skills:** {Any CI instructions that route between Skills and knowledge files}

### Context Budget Health

**Mode:** {Full-context | Retrieval (RAG)}
**KF token estimate:** {Total knowledge file tokens, approximate}
**Pressure symptoms:** {None observed | Specific symptoms: forgetting instructions, generic responses, inconsistency}
**Assessment:** {Healthy | Monitor | Needs optimization — brief rationale}

## 5. Ecosystem Position

**Produces for ecosystem:** {What artifacts, decisions, methodology, or capabilities this project generates that other projects consume}
**Consumes from ecosystem:** {What this project depends on from other projects — shared files, upstream outputs, strategic direction}
**Upstream dependencies:** {Projects this project depends on, and for what}
**Downstream dependents:** {Projects that depend on this project, and for what}
**Strategic contribution:** {How this project advances the user's overall objectives}
**Source:** {Derived from: ecosystem map / project registry / project-internal context only}

## 6. Key Decisions & Rationale

{3-5 most important architectural or strategic decisions. These are the decisions a reader needs to understand to work effectively with or alongside this project.}

1. **{Decision title}:** {What was decided and why. 2-3 sentences.}
2. **{Decision title}:** {What was decided and why.}
3. **{Decision title}:** {What was decided and why.}

## 7. Active Risks & Gaps

**Known risks:** {Active risks that could affect this project's trajectory}
**Incomplete components:** {Planned but unbuilt elements}
**Planned future work:** {Documented roadmap items}
**Staleness concerns:** {Knowledge files, Memory, or CI sections that may be outdated}
**Health observations:** {Any architectural issues noted during brief generation — NOT audit findings, just observable structural facts}

## 8. Cross-Reference

**Build context:** {Link or reference to build_context.md or equivalent institutional memory, if it exists}
**Project registry:** {Reference to your project registry document, if you maintain one}
**Ecosystem map:** {Reference to your cross-project ecosystem map, if you maintain one}
**Related briefs:** {Briefs from upstream/downstream projects, if they exist}
**Key shared files:** {Shared files this project produces or consumes}
```

---

## Field Guidance

### Section 1: Identity & Purpose

**Strong example:**
> SUPPORT is the operations center for the customer support team's tooling and workflow design. It serves as the development hub for automation systems (ticket routing logic, response template library, escalation decision trees) and the documentation source for support team training. The project operates across customer experience design, automation engineering, and team enablement.

**Weak example:**
> This project is about customer support stuff. It helps with support operations.

The strong version establishes what, who, and domain in specific terms. The weak version is too vague to differentiate this project from any other prompt-related project.

### Section 2: Scope & Boundaries

**Strong example:**
> **In scope:** Ticket routing logic, response template library, escalation decision trees, support team training content, and customer-facing self-service documentation.
>
> **Out of scope:** Live customer interactions (handled in support team workflows). CRM administration (handled in CRM ops project). Product engineering work referenced by support tickets (separate engineering projects). Hiring and team management (handled in HR ops).

**Weak example:**
> This project does everything related to customer support.

Scope boundaries prevent Kitchen Sink architecture. Name where excluded work lives.

### Section 4: Architecture Summary — Custom Instructions

Summarize, don't reproduce. The receiving Project doesn't need the full CI text — it needs to understand the CI's design: what identity is set, what the key behavioral rules enforce, how modes work, and what output standards apply.

**Strong CI summary:**
> The CI uses a 5-layer architecture with XML tags. Identity is set as a senior support operations specialist with anti-genericism and evidence-discipline calibrations. Three operational modes govern different task types (template authoring, escalation logic design, training content development). Output standards enforce concrete examples and reproducible decision criteria. Knowledge files are referenced by name with specific routing triggers — the templates library is consulted for any template work, the escalation matrix for any escalation-related question, the training corpus for content development.

**Weak CI summary:**
> The CI tells Claude to be helpful and produce good support content.

### Section 4: Knowledge Files Table

The Type column distinguishes files that carry instructions Claude must follow (Behavioral) from files that carry information Claude can reference (Referential). This distinction matters because behavioral content in knowledge files is a reliability risk under RAG mode.

### Section 5: Ecosystem Position

Mark the source of ecosystem information. "Derived from: ecosystem map" carries higher fidelity than "Derived from: project-internal context only." When relationships are inferred rather than documented, state "Inferred — verify against full portfolio view."

### Section 6: Key Decisions

Select decisions that would change how someone interacts with or builds alongside this project. A receiving Project needs to know "SUPPORT uses canonical templates rather than dynamic generation, and template changes require sign-off from the support lead" because that shapes expectations. It does not need to know "we chose JSON over YAML for the escalation matrix file format."

### Section 7: Active Risks & Gaps

Health observations are observable structural facts, not diagnostic findings. "The CI is 2,400 words with mixed behavioral and referential content" is an observation. "The CI suffers from the Monolith anti-pattern scoring 2/5 on Instruction Clarity" is an audit finding. The brief documents observations; audits produce findings.

---

## Versioning

Briefs should be regenerated, not patched. When a project changes significantly (new phase, architectural restructuring, scope change), generate a fresh brief with an incremented version number. The Validate mode helps determine whether regeneration is warranted.

The change log is tracked in the ecosystem map, not in individual briefs. Each brief is a snapshot. The ecosystem map tracks when briefs were generated and updated.

---

## Consumption Guidance

When a brief is uploaded to a receiving Project, it functions as a reference knowledge file. The receiving Project's CI does not need to reference it explicitly — Claude will find it via retrieval when cross-project questions arise. However, if the receiving Project frequently needs cross-project context, adding a CI routing instruction improves reliability:

```
{code}_PROJECT_BRIEF.md — Reference brief for the {Project Name}. Consult when the user asks about {Project Name}'s architecture, capabilities, current state, or how this project relates to {Project Name}.
```

For projects that consume multiple briefs, consider whether a cross-project ecosystem map would be more token-efficient than multiple individual briefs. An ecosystem map summarizes the full portfolio in one document, whereas briefs cover individual projects in depth.
