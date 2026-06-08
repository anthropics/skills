# Tech Stack Governance

## Technical Debt

### Definition and Taxonomy
Technical debt is the cost of future rework caused by choosing an expedient solution now instead of a better one that would take longer.

Ward Cunningham coined the term (1992). Common taxonomy:

| Type | Description | Example |
|------|-------------|---------|
| Deliberate (strategic) | Known shortcut taken intentionally to ship faster | Hardcoded config to meet a deadline |
| Deliberate (reckless) | Known shortcut taken without acknowledging the cost | Copy-paste architecture "we'll fix later" |
| Inadvertent | Didn't know better at the time | Code written before understanding the domain |
| Bit rot | Was fine when written; became debt as the world changed | Library no longer maintained; outdated patterns |

### Managing Technical Debt

**The key insight** (Will Larson, *An Elegant Puzzle*): The only scalable fix for technical debt is migration. Patching debt in place rarely solves it; planned, systematic migrations do.

**Debt classification approach**:
1. Identify: Make debt visible (debt register, ADRs, tech radar)
2. Assess: Impact of leaving it (risk, velocity tax, security exposure)
3. Prioritize: By cost of not addressing versus cost of fixing
4. Address: Allocate time explicitly — don't try to do it "whenever"

**Allocation model**: Reserve 20-30% of engineering capacity explicitly for tech debt and reliability. If your sprint always fills 100% with features, debt compounds indefinitely. Google's SRE model: 50% of SRE time on toil reduction (a parallel principle).

**Debt interest is real**: A poorly architected service imposes a tax on every engineer who touches it (slower development, higher bug rate, more incidents). Quantify this tax: "This service takes 3x as long to change as a similar well-architected one. That's costing us X engineer-weeks per quarter."

### Technical Debt Records (TDRs)
An extension of ADRs specifically for tracking known debt. Each TDR documents:
- The debt (what's wrong and why)
- How it was created (deliberate shortcut or inadvertent)
- The interest being paid (velocity tax, incident risk, security risk)
- The cost to fix
- Priority and owner

Tools: GitHub issues with labels, Notion database, Jira tech debt epic, dedicated tools like Stepsize.

## Architecture Decision Records (ADRs)

### What They Are
An ADR is a document that captures an important architectural decision, its context, the options considered, and the consequences. First popularized by Michael Nygard (2011).

### Standard MADR Format (Markdown Architectural Decision Records)
```markdown
# [Short title of the decision]

## Status
[Proposed | Accepted | Deprecated | Superseded by ADR-XXXX]

## Context
[What is the situation forcing this decision? What constraints exist?]

## Decision
[What was decided? State it clearly and directly.]

## Options Considered
- Option A: [description + pros/cons]
- Option B: [description + pros/cons]

## Consequences
[What are the results of this decision? Positive and negative.]
[What becomes easier? What becomes harder?]

## References
[Links to relevant documents, RFCs, research]
```

### When to Write an ADR
- Choosing a database or messaging system
- Selecting a programming language for a new service
- Adopting a new framework or major library
- Defining API design standards (REST vs. gRPC vs. GraphQL)
- Making architectural patterns mandatory (event sourcing, CQRS, etc.)
- Any decision that would be costly and disruptive to reverse

**Rule**: If you find yourself explaining the same architectural decision more than twice, write an ADR.

### Where to Store ADRs
- In the repository they apply to (most common): `docs/adr/` or `adr/`
- In a central architecture repository for org-wide decisions
- In a wiki (Confluence, Notion) — less ideal because they lose proximity to code
- AWS Prescriptive Guidance recommends a central ADR repository with links from individual service repos

### ADR Anti-Patterns
- Writing ADRs after the decision is already implemented and irreversible (theater)
- ADRs that describe what was built rather than why the decision was made
- ADRs that are never updated when context changes (stale ADRs are worse than none)
- No review process — ADRs should go through a lightweight review before acceptance

### Debt-Aware ADRs
Treat architectural decisions as financial transactions:
- Decision = Principal (the investment made)
- Drawbacks = Interest (the ongoing cost of the decision)
- Risk = Multiplier (how much the interest can grow)

Link ADRs to tech debt records when shortcuts are documented. This makes debt visible and creates a paper trail for future teams.

## ThoughtWorks Technology Radar

Published twice yearly (April and October). A snapshot of tools, techniques, platforms, languages, and frameworks across four rings:

| Ring | Meaning |
|------|---------|
| Adopt | We use this in production; recommend broadly |
| Trial | Worth pursuing; we are experimenting |
| Assess | Worth understanding; will affect us |
| Hold | Proceed with caution; consider alternatives |

**How to use it**: Don't follow it blindly — it reflects ThoughtWorks' experience (consulting-heavy, large enterprise). Treat it as a rich signal of industry direction, especially useful for identifying techniques and tools you haven't heard of yet.

**Volume 31 (October 2024) highlights**:
- Generative AI and LLMs moved to Adopt for many use cases in software delivery
- Rust gaining prominence in systems programming (now Trial for many teams)
- AI-assisted code review tools (Adopt/Trial)
- Platform engineering as a discipline (Adopt)

### Building Your Own Technology Radar
Many engineering orgs adapt the ThoughtWorks format for internal use. Steps:
1. Gather input from senior engineers across teams (what are we using? what should we standardize on? what should we retire?)
2. Categorize into the four rings
3. Present at an all-engineering forum
4. Publish internally; update semi-annually

## Build vs. Buy Framework

### The Core Question
"Build" means developing custom software internally. "Buy" means purchasing a SaaS, open-source, or vendor product.

### Decision Framework

**Factors favoring Buy**:
- Not your core competency (billing, HR software, email delivery, analytics)
- Commodity capability with good market solutions
- Speed to market is critical
- You can't attract the talent to build it well internally
- Total cost of ownership (TCO) is lower (factor in build cost + maintenance + opportunity cost)

**Factors favoring Build**:
- This is a core competitive differentiator
- No good external solution exists
- Security or compliance constraints prevent using third-party software
- Deeply custom integration requirements
- You have the talent and the build is tractable

**The McKinsey framework adds**:
- Business strategy alignment: does owning this capability create strategic advantage?
- Risk assessment: what's the cost of vendor failure or lock-in?
- Capability building: does building this internally grow organizational capability you need?

**Gartner 2024 finding**: Technical decision-makers who optimize the build vs. buy process achieve 30% faster time-to-market and 25% cost savings.

### The Third Option: Buy and Extend
Purchase a vendor solution but build extensions or integrations. Often the best balance — use the commodity 80% from the vendor, own the differentiating 20%.

### Build vs. Buy Mistakes
- **Not including TCO of building**: The "just build it" decision ignores ongoing maintenance cost (bug fixes, security patches, feature requests, on-call)
- **Not evaluating lock-in risk**: Buying a solution that becomes business-critical but has bad contract terms or no viable replacement
- **Not evaluating integration cost**: A cheaper SaaS that requires 6 months of integration work may cost more than a pricier one with good APIs
- **"Not Invented Here" syndrome**: Refusing to buy or use open source out of preference for building everything internally

## Vendor Management

### Key Principles

**Vendor concentration risk**: If a single vendor failure would cause significant business harm, you have concentration risk. The 2024 CrowdStrike incident (global IT outage from a software update) illustrated extreme vendor concentration risk in security tooling.

**Mitigation strategies**:
- Dual vendor for critical services where possible
- Design for vendor portability (avoid deep proprietary API lock-in where alternatives exist)
- Maintain documented runbooks for vendor outage scenarios
- Review vendor SLAs and ensure they match your requirements

**Contract governance**:
- Data portability clause: ensure you can get your data out
- Termination for convenience: avoid being locked into vendors you want to leave
- SLA with teeth: ensure financial penalties are meaningful, not symbolic
- Security addenda: ensure vendor meets your security standards

### Vendor Review Cadence
- Annual: Contract review, renewal decision, satisfaction assessment
- Quarterly: Usage and cost review, roadmap alignment
- Monthly (for critical vendors): Reliability and SLA compliance review

## Sources
- Michael Nygard — ADR documentation (cognitect.com, 2011)
- adr.github.io — MADR format and examples
- AWS Prescriptive Guidance — ADR Process documentation
- ThoughtWorks Technology Radar Vol. 30 (April 2024) and Vol. 31 (October 2024)
- InfoQ — "Thoughtworks Technology Radar Oct 2024: From Coding Assistance to AI Evolution"
- *An Elegant Puzzle* — Will Larson (Stripe Press, 2019)
- HatchWorks — "Build vs Buy Software: The Definitive Framework for 2025"
- McKinsey Build vs Buy Framework analysis (GraphApp AI, 2024)
- WorkingSoftware.dev — "Technical Debt Records"
