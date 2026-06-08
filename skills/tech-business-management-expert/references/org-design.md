# Engineering Org Design

## Core Mental Model: Conway's Law

Melvin Conway (1967): "Organizations which design systems are constrained to produce designs which are copies of the communication structures of those organizations." In practice: your software architecture will mirror your team communication structure, whether you intend it to or not.

**Reverse Conway Maneuver** (Team Topologies): Deliberately design your team topology first to match the architecture you want, then let the architecture evolve to match. If you want a microservices architecture, organize teams around services first. If you want a monolith, organize around the product.

**Implication for leaders**: Before any reorg, ask "what software architecture will this team structure produce?" Before any major architecture change, ask "what team structure change does this require?"

## Team Topologies: The Four Team Types

From Matthew Skelton and Manuel Pais, *Team Topologies* (2019):

### 1. Stream-Aligned Teams
- Own end-to-end delivery of a value stream (feature, user journey, or product area)
- Cross-functional: includes engineers, product manager, designer, QA
- Should be the dominant team type — the majority of your teams
- Metric: can deploy independently without waiting for other teams
- Danger sign: if they constantly need hand-offs to other teams, something is wrong

### 2. Platform Teams
- Provide internal platforms that stream-aligned teams self-serve
- Goal: reduce cognitive load on stream-aligned teams
- Think of them as building an internal product with stream-aligned teams as customers
- Interaction mode: X-as-a-Service (not consulting, not embedded)
- Bad pattern: platform teams becoming gatekeepers or bottlenecks
- Good pattern: golden paths, self-service, excellent internal docs

### 3. Enabling Teams
- Temporary, small, high-expertise groups who help stream-aligned teams adopt new capabilities
- Examples: DevOps enablement team, security champion team, observability evangelists
- Not permanent: they enable and then move on — they do not become a dependency
- Bad pattern: enabling teams that never transition ownership back

### 4. Complicated Subsystem Teams
- Own components that require deep specialist expertise (ML models, cryptography, video codecs)
- Should be rare — only when the complexity genuinely requires dedicated specialists
- Most teams mistakenly create too many of these, adding coordination overhead

## Three Team Interaction Modes

1. **Collaboration**: Two teams work closely together for a defined period to discover new patterns (high bandwidth, temporary)
2. **X-as-a-Service**: One team provides a service the other consumes with minimal interaction (scalable, clear API)
3. **Facilitating**: An enabling team helps another team learn and grow (temporary, goal-based)

## Cognitive Load

Teams should not be responsible for more than they can cognitively handle. Signs of overload:
- Context switching between many services/domains
- Too many incident pages from unrelated systems
- Can't keep up with their own technical debt

**Practical guidance**: A stream-aligned team should fully own no more than 2-3 medium-complexity services, or 1 large one. When teams are overloaded, split them rather than adding headcount to an overloaded team (more people in an overloaded team increases coordination overhead without reducing cognitive load).

## CTO vs. VP of Engineering

These are distinct roles that become separate positions around 15-20 engineers:

| Dimension | CTO | VP of Engineering |
|-----------|-----|-------------------|
| Primary orientation | External / future | Internal / present |
| Focus | Technology strategy, innovation, architecture | Execution, delivery, team health |
| Key relationships | Board, customers, investors, press | Engineering managers, product, design |
| Time horizon | 18-36 months out | Now to 6 months |
| Board involvement | ~70% serve on or present to board | ~25% |
| Compensation (2024) | $240K base, $400K+ with LTI | $180-220K base typically |
| Hiring decision | Helps hire VP Eng | Hires all engineers |

**Common failure modes**:
- Founding CTO trying to also be VP Eng as company grows past 40 engineers — split the role
- CTO who never talks to customers or joins sales calls — loses market signal
- VP Eng who wants to be an architect — dilutes execution focus

**When you have both**: CTO owns the "what technology" and "why", VP Eng owns the "how we build it" and "who builds it." They must have clear handshakes on roadmap, architecture review, and hiring bar.

**When you have only one**: At <20 engineers, one person can hold both roles. Title often reflects the company's emphasis (product-led = CTO, process-led = VP Eng).

## Span of Control

Engineering-specific norms:
- **Engineering Manager**: 5-8 direct reports (sweet spot: 6-7). Fewer than 5 is over-management. More than 10 makes meaningful 1-on-1s and development impossible.
- **Senior EM / Director**: 3-5 EMs (15-35 engineers total), or 3-5 senior ICs with management duties
- **VP of Engineering**: 3-6 direct report EMs/Directors; rarely manages more than 6 layers down with clear chains

**Forcing function**: A manager with 8+ direct reports will drop 1-on-1s, skip performance development, and rely on Slack pings. This creates attrition. Watch for managers secretly managing 10+ and burning out.

## Org Structure Patterns

### By Function (early stage, <30 eng)
- Frontend team, Backend team, Data team
- Fast to spin up, clear domains
- Problem: handoffs between teams delay features

### By Product/Feature (30-100 eng)
- Each team owns a feature area (checkout, search, notifications)
- Matches Team Topologies stream-aligned model
- Requires platform investment or teams duplicate infrastructure

### By Lifecycle Stage (100+ eng)
- Growth team, Core product, Platform, Data/ML
- Separates innovation from reliability
- Risk: Core product team feels like "maintenance mode"

## Reorg Principles (from Will Larson's *An Elegant Puzzle*)

1. Reorgs should solve a specific, stated problem — not be a response to general unhappiness
2. Announce clearly and quickly; rumor period is more damaging than the reorg itself
3. Make migrations and changes cheap — this is one of the highest-leverage skills in engineering leadership
4. A team that has been reorged more than once per year cannot build stable systems
5. The four team states: Falling Behind → Treading Water → Repaying Debt → Innovating. Goal is to get teams to Innovating state through deliberate interventions at each stage.

## Sources
- *Team Topologies* — Matthew Skelton & Manuel Pais (2019)
- *An Elegant Puzzle: Systems of Engineering Management* — Will Larson (2019), Stripe Press
- Korn Ferry 2024 Global Technology Executive Pay Study
- Spencer Stuart CTO board research (2021-2024)
- Jellyfish Engineering Manager Ratio data (2024)
- Conway's Law (1967), revised by academic review arxiv 2311.10475
