# Source Grading and Tagging

The source authority hierarchy and the generalizable-vs-project-specific tagging discipline. This reference is for RESEARCH mode (always) and applies whenever a substantive technical claim needs source backing.

This Skill's source discipline is non-negotiable: every substantive claim about Claude Code behavior, MCP capability, or agent design pattern carries an inline source tag. Without source tags, recommendations imply more confidence than the evidence warrants — the difference between "Anthropic explicitly recommends this" and "a community member suggested this on Reddit" is the difference between a confident recommendation and a speculative note.

For the methodology patterns this discipline supports, see `cc-methodology-patterns.md`.

---

## Table of contents

1. The 5-tier source authority hierarchy
2. Inline source tag format
3. The generalizable-vs-project-specific tagging discipline
4. The "speculation" tag (and when it's acceptable)
5. Source authority in RESEARCH mode (operational checklist)

---

## 1. The 5-tier source authority hierarchy

Sources rank in 5 tiers. Higher-ranked sources override lower-ranked ones when they conflict.

### Tier 1 — Anthropic primary documentation

**The authoritative source for Claude Code behavior, API parameters, MCP spec, and Skills architecture.** Specifically:
- `https://docs.claude.com` and `https://code.claude.com/docs/en/*`
- Anthropic engineering blog at `https://www.anthropic.com/engineering`
- Anthropic news / announcements at `https://www.anthropic.com/news`

When these sources speak, they are authoritative. When they conflict with practitioner consensus, Tier 1 wins.

### Tier 2 — Anthropic engineering posts (topical)

Specific posts on agent patterns and CC workflows. Examples:
- "How and when to use subagents in Claude Code" (April 7, 2026)
- "How Anthropic teams use Claude Code" (July 23, 2025)
- "Building agents with the Claude Agent SDK" (September 29, 2025)

These are still Anthropic-authored, but on specific topics rather than reference documentation.

### Tier 3 — Documented working experience (project-specific)

The project's own documented experience (e.g., a project's own SYSTEM_DESIGN.md or design materials). Authoritative for "what was tried and what shipped" within the project's domain. Patterns generalize only when explicitly tagged with the basis for generalization.

### Tier 4 — Named practitioners with public artifacts

Sources useful for current state of practice; not authoritative on Claude internals. The bar for inclusion: a public artifact (post, repo, podcast episode) that can be cited directly.

Examples by category:
- **General CC patterns:** Simon Willison, Latent Space (swyx + alessio), alexop.dev, Jose Parreño Garcia, Daniel Miessler, Shrivu Shankar
- **Methodology repos:** obra/superpowers, rosmur/claudecode-best-practices, coleam00/context-engineering-intro, shinpr/claude-code-workflows, AnastasiyaW/claude-code-config, Marc Nuri, Will Urbanski, ChrisWiles/claude-code-showcase
- **Skill catalogs and observability:** VoltAgent/awesome-claude-skills, Liuziyu77/ClaudeScope, Indragie Karunaratne (PyAI talk)
- **2026 conference talks:** Thomas Schilling (Spring I/O), Sheena O'Connell (Python Unplugged), Jim Manico (OWASP London), Boris Cherny (YC creator interview), Felix Lee (Figma MCP demo)

When citing a practitioner, name both the practitioner and the artifact — not just "a practitioner said." The artifact is the verifiable source.

### Tier 5 — Community sources

Useful for surfacing emerging issues; never authoritative without independent verification. Treat all Tier 5 evidence as "signal that something is worth investigating," not as a basis for recommendations.

Examples:
- Anthropic Discord
- Reddit (r/ClaudeAI, r/ClaudeCode, r/Anthropic)
- GitHub Issues on official Anthropic repos
- Third-party tools and forks (Claudia, opcode, individual personal config repos)

A claim grounded only in Tier 5 is speculative. A claim grounded in Tier 4 is community evidence. Only Tier 1-3 are authoritative.

---

## 2. Inline source tag format

Every substantive claim carries an inline tag. Tag format:

| Source class | Tag format | Example |
|---|---|---|
| Tier 1 (Anthropic primary docs) | `[Anthropic docs]` or `[Anthropic docs: <specific page>]` | `[Anthropic docs: subagents page]` |
| Tier 2 (Anthropic engineering posts) | `[Anthropic engineering: <title or short ID>]` | `[Anthropic engineering: subagents post Apr 2026]` |
| Tier 3 (project-specific working experience) | `[<project> §<section>]` | `[production CC deployment §3.1]` |
| Tier 4 (named practitioner) | `[practitioner: <name> + <artifact>]` | `[practitioner: rosmur + claudecode-best-practices]` |
| Tier 5 (community) | `[community: <forum or source>]` | `[community: Reddit r/ClaudeAI thread X]` |
| Speculation (no source backing) | `[speculation]` | `[speculation]` |

**Where the tag goes:** at the end of the claim, in brackets. If a paragraph makes a single claim, one tag at the end. If a paragraph makes multiple claims with different sources, tag each claim.

**Multi-source convergence:** when 3+ independent sources converge on a pattern, tag with `[convergence: <list>]`. Example: `[convergence: Anthropic docs + obra/superpowers + rosmur]`.

**Examples of well-tagged claims:**

> CC's hooks-vs-Skills decision rule: "if failure is annoying, prompt or skill; if failure is unacceptable, hook." [convergence: obra/superpowers + rosmur]

> Sandboxing reduces permission prompts by ~84%. [Anthropic engineering: sandboxing post Oct 2025]

> The "transcript dump" anti-pattern (pasting chat history into CC as a prompt) is named identically across multiple practitioner sources. [convergence: Gemini + Perplexity + ChatGPT external research]

> The 4-agent S/B/C/X verification topology shipped 27/27 ship items without a halt violation. [production CC deployment §6]

> A "20k token threshold" for MCP tool schemas is a common community heuristic; not Anthropic-published. [community + practitioner consensus, treat as heuristic]

---

## 3. The generalizable-vs-project-specific tagging discipline

Patterns drawn from working examples (a production CC deployment, other projects) are tagged with their generalization status:

| Tag | Meaning |
|---|---|
| `[generalizable]` | Pattern works across CC work generally. Justification: structural feature transfers regardless of domain. |
| `[project-specific]` | Pattern was specific to one project's domain. Default tag — assume project-specific until proven otherwise. |
| `[generalizable structure, project-specific content]` | Structural pattern transfers; content does not. Example: 3-tier authority matrix shape generalizes; specific tier definitions don't. |
| `[forward-looking proposal]` | Described in source material but not actually implemented or validated. Recommend with explicit caution. |

**The default is project-specific.** Generalization claims need a basis. When tagging a pattern as `[generalizable]`, name the structural feature that makes it transfer.

**Examples:**

> The change_log discipline (every fix gets a diagnosis-fix-verification entry) is `[generalizable]` because the underlying need — durable institutional memory the next agent reads cold — applies to every multi-session CC project regardless of domain.

> The 3-archetype dispatch model is `[project-specific]` to its source domain — it reflects the specific structural variants of one project's source materials. Other content domains have different archetype shapes.

> The Authority Matrix is `[generalizable structure, project-specific content]` — every CC project has *some* content where the agent's authority must be bounded; the 3-tier shape generalizes; the specific tier definitions are project-specific.

> The Pattern-Miner agent (proposed in source material §10) is `[forward-looking proposal]` — described as a design hypothesis, not validated against actual unmet needs.

---

## 4. The "speculation" tag (and when it's acceptable)

Speculation isn't banned — it's labeled. There are legitimate uses:

- **Forward-looking design discussion:** "The handoff might benefit from automated readiness scoring [speculation] — no current source documents this approach."
- **Bridging between weak evidence:** "If sandboxing works for autonomy [Anthropic engineering: sandboxing post], it should also work for parallel CC sessions on the same machine [speculation — no direct source]."
- **Filling gaps in research coverage:** "Research gaps include long-running agent observability for multi-day work [speculation — emerging area, sparse sources]."

**The discipline:** speculate when needed, but mark it. The reader should know which claims are evidence-grounded and which are inference.

**Anti-pattern:** speculative claims dressed as authoritative. Examples to avoid:
- "Best practice is to..." without naming the practice's source
- "It's well-known that..." (well-known to whom? cite the source)
- Implied authority through formal language without backing

**When the only source class available for a topic is Tier 5:** flag the recommendation as speculative. RESEARCH mode outputs always have a "Speculative notes" section that names what couldn't be source-grounded.

---

## 5. Source authority in RESEARCH mode (operational checklist)

When producing a RESEARCH mode assessment, walk this checklist:

**Step 1 — Identify the operational gap.** What specific failure mode would the candidate fix? "Adding X for completeness" is anti-pattern (see SKILL.md `Important` section). Name the gap concretely.

**Step 2 — Survey by source class.** For each candidate, identify which source classes back it:
- Tier 1 (Anthropic primary)?
- Tier 2 (Anthropic engineering posts)?
- Tier 3 (working experience in this or similar projects)?
- Tier 4 (named practitioner with public artifact)?
- Tier 5 (community signal)?

**Step 3 — Use web search when current state matters.** If the candidate is recent (post-knowledge-cutoff or fast-evolving), use web search to verify current state. Cite specific URLs in the output.

**Step 4 — Tag every claim inline.** Per §2 above. The reader should be able to assess the evidence backing of each recommendation independently.

**Step 5 — State the recommendation decisively.** "Adopt," "defer," or "reject" — with reasoning. Hedging like "you could consider" is anti-pattern; the user comes to RESEARCH mode for a decision.

**Step 6 — Surface what couldn't be source-grounded.** RESEARCH mode outputs always include a "Speculative notes" section. If a meaningful part of the assessment is speculative, name it explicitly.

**Output format for RESEARCH mode** (from SKILL.md):

```markdown
## RESEARCH MODE: <topic>

### Gap
<one paragraph: what specific operational problem this addresses>

### Candidates
For each candidate:
- **<candidate name>** — [<source class>] What it does. How it maps to the gap.

### Fit analysis
For each candidate: where it fits the user's stack, where it doesn't, what the failure modes look like.

### Recommendation
Decisive: adopt / defer / reject. Reasoning.

### Speculative notes
What couldn't be source-grounded. Anything tagged [speculation] or relying only on Tier 5 sources.

### Sources cited
<list of URLs and references>
```

---

## End of source grading and tagging reference
