# Engineering Team Structure — The Decision: "How do we organize engineers to ship without coordination overhead?"

This reference answers exactly one decision: **at our headcount and work-stream complexity, what's the right structure — and when do we add managers?**

Pair with `scripts/eng_team_structure_designer.py` for automation.

## Core Principle: Conway's Law

> "Organizations design systems that mirror their own communication structure."
> — Melvin Conway, 1968

What this means in practice: the team structure you design today **becomes** the system architecture in 6-12 months. Plan accordingly.

If you have 3 teams, you'll have 3 services (or 3 major modules). If you split a team in half, expect a new service boundary to emerge. If you merge two teams, expect a merger of the services they owned.

**Operational implication:** team structure is an architecture decision. Coordinate with cs-cto-advisor.

## The Squad / Chapter / Tribe Model (Adapted)

Originated at Spotify (2014); refined by everyone else after observing Spotify's actual practice deviates from the public framework.

**Squad:** small autonomous team (5-9 engineers) owning a service or product area end-to-end. Has a dedicated EM (or tech lead at smaller scale), a product owner if customer-facing.

**Chapter:** functional discipline cutting across squads — backend chapter, frontend chapter, data chapter. Purpose: skill development, hiring calibration, technical standards. **NOT for ownership** (ownership stays in squads).

**Tribe:** group of related squads working toward a shared goal. E.g., "Platform tribe" = 3 squads working on shared infrastructure. Tribes have a director.

**Anti-pattern:** copying Spotify literally. The model evolves; what works at 100 engineers doesn't at 10.

## Headcount-to-Structure Map

| Total engineers | Structure | Manager layer |
|---|---|---|
| 1-5 | One team, no formal structure | Founder-CTO acts as EM |
| 6-15 | 2-3 informal pods around work streams | Founder-CTO or first promoted senior IC |
| 16-40 | Formal squads (5-9 ICs each), 4-6 squads total | First EM hires; chapters emerge informally |
| 41-100 | Squads + tribes; 2-3 tribes | Director per tribe; formal chapters |
| 100-300 | Multi-tribe; VPE + directors | VPE + 3+ directors + EMs |
| 300+ | Federated / business units | Group EMs / Sr Directors / VPE-of-VPEs |

## Span of Control

The hardest question: how many people should one manager have?

**Engineering benchmarks:**

| Manager type | Healthy span | Notes |
|---|---|---|
| EM (people manager, often part-time IC at smaller scale) | 5-8 ICs | More: 1:1s suffer. Less: EM gets pulled into IC work. |
| Director (manages EMs) | 4-6 EMs | More: directors lose visibility into IC concerns. Less: director becomes a glorified senior EM. |
| VPE | 3-6 directors | More: VPE loses time on strategic work. Less: VPE becomes a director. |

**Violations to watch:**
- One EM with 12 ICs → split squad or hire second EM
- One director with 8 EMs → split tribe or hire second director
- VPE with 8 directors → reorganize tribes

## The EM vs Tech Lead Distinction

A frequent source of confusion at growth stage.

**Tech Lead:**
- Senior IC who provides technical direction to the squad
- Code-first; reviews code; makes architecture decisions
- Does NOT do 1:1s, performance reviews, hiring panels (beyond technical interviews)
- Reports into an EM or directly to a director

**Engineering Manager:**
- People manager; runs 1:1s, performance reviews, career development
- May still code at smaller scale (player-coach model)
- At scale, EMs don't write production code regularly

**Player-coach EM (early stage):**
- Common 6-15 engineers
- EM contributes ~50% IC time, 50% management time
- Works only if the EM is genuinely strong technically AND people-skilled
- Breaks at ~6+ direct reports

**Specialist EM (scale):**
- 16+ engineers per EM
- EM contributes 0-20% IC time (mostly architecture review)
- People management is the job

**Anti-pattern:** Promoting your best IC to EM "because they earned it." Best ICs often fail as EMs. Provide management training; allow both tracks (IC ladder + manager ladder) so the IC track is just as prestigious.

## Manager-Trigger Rules

When to add an EM:

- **5-7 ICs without a dedicated EM:** first EM hire (or internal promote). The founder-CTO can't sustain 1:1s + performance reviews + hiring at this scale.
- **EM has 9+ direct reports:** split the squad or hire another EM. 1:1 quality degrades above 8.

When to add a director:

- **3+ EMs reporting directly to VPE/CTO:** VPE/CTO loses strategic time on individual EM coaching.
- **Director has 7+ EMs:** split the tribe or hire another director.

When to add a VPE:

- **Engineering org > 30 people AND CTO is spending > 50% on management vs strategy:** time for a VPE (or promote a director).
- **CTO is a co-founder more comfortable with strategy than execution:** VPE complement (CTO owns architecture; VPE owns execution).

## Squad Sizing Discipline

5-9 ICs per squad is the sweet spot, based on:

- **Below 5:** coordination overhead per output is too high; squad has too little capacity
- **5-9:** small enough for 1 EM, large enough to absorb variance (vacations, illness, attrition)
- **Above 9:** EM stretched; sub-groups form informally; communication breaks down

If a squad regularly drops below 5 or grows above 9, restructure.

## Cross-Functional Squad vs Component Squad

Two ways to organize work:

**Cross-functional (vertical):** squad owns a customer-facing area end-to-end. E.g., "Onboarding squad" has frontend + backend + designer + PM.

**Component (horizontal):** squad owns a technical layer. E.g., "Database squad" owns the data layer; consumers depend on them.

**Default:** cross-functional. Component squads are necessary at scale (platform, infra) but become bottlenecks if applied too broadly.

**Anti-pattern:** "all backend engineers in one squad" at 30+ engineer scale. Creates a bottleneck for every other team.

## Chapter Discipline

Chapters work when:
- Cross-squad skill alignment is valuable (consistent code style, library choices, training)
- Chapter lead is a credible senior IC, not a politically-appointed person
- Time commitment is bounded (chapter meetings 1-2 hours per week max)

Chapters break when:
- They acquire ownership ("the data chapter owns the data warehouse" — should be a squad's job)
- They become political fiefdoms ("you can't use that library without chapter approval")
- Time commitment grows beyond bounded weekly check-ins

## When This Reference Doesn't Help

- **Specific squad-mission writing.** Standard product management territory.
- **Hiring criteria for EMs vs senior ICs.** See `cs-chro-advisor`'s leveling references.
- **Comp differences between EM and senior IC tracks.** See `cs-chro-advisor`'s comp benchmarker.
- **Cross-functional roadmap planning.** See `cs-coo-advisor`'s operating cadence.

This reference is about structure design, not management process.

---

**Source authorities (non-exhaustive):**

- Henrik Kniberg + Anders Ivarsson — "Scaling Agile @ Spotify" (2012) — original squad/chapter/tribe model
- "Spotify's tribes model: A model worth copying?" — Kniberg's own 2020 retrospective on what worked and what didn't
- Will Larson — "An Elegant Puzzle: Systems of Engineering Management" (2019) — span-of-control + EM-vs-tech-lead distinctions
- Camille Fournier — "The Manager's Path" (2017) — the IC-to-EM transition + manager tracks
- Conway, Melvin — "How Do Committees Invent?" (1968) — origin of Conway's Law
- Mark Schwartz — "A Seat at the Table" (2017) + "The Art of Business Value" (2016) — eng leadership at scale
- Patrick Lencioni — "The Five Dysfunctions of a Team" (2002) — team dynamics at the squad level
- Empirical: extensive engineering leadership essays from Stripe, Shopify, GitHub, Netflix, Spotify, Atlassian engineering blogs
