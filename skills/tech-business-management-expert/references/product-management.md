# Product Management in Tech Companies

## Product Discovery vs. Delivery

The two core activities of a product team:
- **Discovery**: Learning what to build (is this the right thing?)
- **Delivery**: Building it correctly (are we building it right?)

Most teams over-invest in delivery and under-invest in discovery, shipping things that customers don't use. The ratio should be roughly 20-30% of team capacity on discovery continuously.

## Teresa Torres: Continuous Discovery

Teresa Torres (*Continuous Discovery Habits*, 2021) defines continuous discovery as "a weekly cadence of small research activities in pursuit of a desired outcome."

### Core Principles
1. **Outcome over output**: Teams should be measured on outcomes (user behavior change, revenue, retention) not features shipped
2. **Weekly touchpoint**: Product teams should talk to customers at least once per week — not a quarterly research sprint but a continuous habit
3. **Assumption testing**: Every product idea is a collection of assumptions. Identify and test the riskiest assumptions first before building.

### Opportunity Solution Tree (OST)
A visual framework for connecting outcomes to opportunities to solutions to experiments:

```
Desired Outcome
    ├── Opportunity 1 (customer need/pain/desire)
    │     ├── Solution A
    │     │     └── Experiment: prototype / test
    │     └── Solution B
    └── Opportunity 2
          └── Solution C
```

**Opportunity**: A customer need, pain, or desire — discovered through interviews and observation. Not a solution. Not a feature. "Users can't find their purchase history" is an opportunity. "Add a search bar" is a solution.

**How to use**: The OST is a living document. Update it every week as you learn. It prevents the team from jumping straight to solutions and helps prioritize based on opportunity size.

### Jobs-to-Be-Done (JTBD)
Originated by Clayton Christensen, popularized by Bob Moesta and Chris Spiek. Core insight: customers "hire" products to make progress in specific circumstances.

**JTBD format**: "When [situation], I want to [motivation], so I can [outcome]."

Example: "When I'm on a business trip and forgot a gift, I want to quickly buy something local and respectable, so I can show appreciation without embarrassment."

**How it's used**: Interview customers about their decision to buy (or switch). Ask about the moment they decided to look for a solution, what they tried before, what triggered the switch. Surface the real job underneath the surface request.

**JTBD vs. User Stories**: User stories describe features ("As a user, I want X"). JTBD describes the progress customers seek — it guides what features to build, not what features look like.

## Agile / Scrum

### Sprint-Based Development
- 2-week sprints are standard; 1-week is fast/lean; 3+ weeks loses urgency
- **Sprint Planning**: Team pulls from refined backlog, commits to sprint goal (outcome-focused, not a list of tickets)
- **Daily Standup**: 15 minutes, for the team, not the manager. What did I do? What am I doing? What's blocking me?
- **Sprint Review**: Demo to stakeholders — show working software, gather feedback
- **Retrospective**: What went well? What didn't? One commitment to improve next sprint.

### Backlog Grooming / Refinement
- Held 1-2x per week, 1 hour each
- Purpose: ensure top of backlog is always well-defined and ready to pull
- Each ticket should have: clear acceptance criteria, reasonable size estimate, no open dependencies

### Scrum Pitfalls
- **Velocity as the success metric**: Velocity (story points/sprint) measures throughput, not value. Teams will game it by inflating estimates.
- **Scrum theater**: Going through the motions without the purpose. Retrospectives become complaints sessions with no action. Standups become status reports to the PM.
- **Sprint commitment becomes a promise**: Sprint goals should be commitments to try, not contracts to deliver. Unexpected complexity is normal.

## Kanban

Flow-based, no sprints, pull-based work. Better suited to:
- Operations/support teams with unpredictable work
- Teams maintaining systems with high interrupt load
- When sprint cadence creates artificial urgency

**Key Kanban metrics**:
- **Cycle time**: From "started" to "done" for a work item
- **Throughput**: Items completed per week
- **WIP (Work in Progress)**: Number of items actively being worked
- **WIP limits**: Explicitly cap concurrent work per column (e.g., "In Progress" max 3 items per person). Forces finishing before starting.

**Why WIP limits matter**: Context switching is expensive. When WIP is unbounded, engineers multitask across 5+ things, leading to slow completion of all of them. WIP limits force a choice: finish something or don't start.

## Shape Up (Basecamp / 37signals)

Ryan Singer, *Shape Up* (2019, free at basecamp.com/shapeup). The methodology 37signals uses internally:

### Six-Week Cycles
Work happens in 6-week chunks — long enough to build something meaningful, short enough that the deadline stays tangible. No sprints within cycles; teams have full autonomy on HOW they work within the cycle.

### The Shaping Process
Before a project enters a cycle, it is "shaped" by a small senior group (typically product + senior engineer):
- **Problem**: What are we solving and why does it matter?
- **Appetite**: How much time are we willing to spend? (Not "how long will it take?")
- **Solution sketch**: Rough concept, not wireframes. Enough to communicate the key insight.
- **Rabbit holes**: Specific risky parts to avoid, known unknowns to address
- **Off-limits**: What is explicitly excluded from scope

**Appetite** is the key innovation: instead of estimating work and then committing, you set how much the idea is worth, then design a solution that fits. This inverts the typical "scope creep due to fixed spec" problem.

### The Betting Table
A meeting held in the 2-week cooldown between cycles. Senior leadership bets on which pitches to execute in the next cycle. Key properties:
- Nothing is automatically on the schedule; everything must be bet on freshly
- No backlog: unbet pitches don't carry forward — they can be re-pitched but start fresh
- The "circuit breaker": if a project isn't done in the 6 weeks, it doesn't automatically get more time. You decide whether to re-bet or abandon.

### Cooldown (2 weeks between cycles)
- Teams fix bugs, do small improvements, explore ideas
- Shapers prepare new pitches for the next betting table
- No one is assigned to ongoing projects; it's loose, exploratory time

### When Shape Up Works
- Teams that are mature and self-organizing
- Companies that have identified the "what to build" problem is harder than the "how to build" problem
- Leaders willing to trust teams with full execution autonomy

### When Shape Up Doesn't Work
- Teams that need tight coordination across many dependent teams
- Regulatory environments requiring detailed planning and audit trails
- Early-stage companies still figuring out their core product

## Roadmaps

### The Three Horizons
- **Now** (0-3 months): Committed work in current quarter, high confidence
- **Next** (3-6 months): Directional, subject to change as we learn
- **Later** (6-18 months): Strategic bets, not commitments — communicate as intent

**Rule**: Never communicate the "Later" horizon as a plan. Communicate it as the direction you expect to move if current bets pay off.

### Roadmap Communication
- Different audiences need different views: Engineering (technical dependencies, sequencing), Product (features and timelines), Executive (outcomes and strategic alignment), Sales/Customer Success (customer-relevant features, dates)
- Don't promise dates externally without engineering buy-in
- Outcome-based roadmaps ("help customers X" not "build feature Y") reduce customer anchoring on solutions

### Stakeholder Management
- Engineering's job is to make trade-offs transparent, not to say yes to everything
- When stakeholders want to add scope, show what gets de-prioritized
- "If we do this, what do we not do?" is the most powerful stakeholder question

## Sources
- *Continuous Discovery Habits* — Teresa Torres (2021), Product Talk
- *Shape Up* — Ryan Singer (2019), 37signals/Basecamp (free online)
- *Competing Against Luck* — Clayton Christensen (2016), JTBD framework
- *Scrum: The Art of Doing Twice the Work in Half the Time* — Jeff Sutherland (2014)
- *Inspired: How to Create Tech Products Customers Love* — Marty Cagan (2017)
- ProductTalk.org — Teresa Torres continuous discovery resources
