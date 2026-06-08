# Engineering Management Best Practices

## The 1-on-1

The 1-on-1 is the manager's primary tool for building trust, diagnosing problems, and developing people. Done badly, it destroys both.

**Structure**: 30 minutes weekly for direct reports (60 min biweekly acceptable for senior ICs). Belongs to the report, not the manager — their agenda first.

**High-leverage agenda items**:
- What's blocking you that I can help with?
- What are you learning? What do you wish you were doing more of?
- How are things going with [specific project]?
- Is there anything about how the team is working that's frustrating you?
- Career: where do you want to be in 2 years? Are we building toward that?

**Anti-patterns to avoid**:
- Status updates (that's what standups are for)
- Manager monologue about strategy
- Skipping 1-on-1s when busy (that's when they matter most)
- Not taking notes / not following up on commitments

**Diagnostic signal**: In your first 4 weeks at a new team, use 1-on-1s to listen only — diagnose the team's pain points before proposing solutions. If people won't give honest answers in 1-on-1s, you have a psychological safety problem.

## Psychological Safety

**Definition (Amy Edmondson, Harvard, 1999)**: "A belief that one will not be punished or humiliated for speaking up with ideas, questions, concerns, or mistakes."

**Google Project Aristotle findings (2012-2016)**: Studied 180 teams across engineering and sales, 250 attributes, two years of analysis. The single strongest predictor of high performance was psychological safety — not team composition, IQ, or seniority. It was a prerequisite for the other four success factors: dependability, structure and clarity, meaning, and impact.

**Behavioral markers of high-safety teams**:
- Members speak in roughly equal proportions in meetings
- Disagreement is stated directly and without personal charge
- People admit mistakes publicly without fear
- New ideas are welcomed before being critiqued

**DORA research confirms**: Teams with high psychological safety have lower deployment failure rates, faster recovery times, and higher deployment frequency. The culture comes first, the metrics follow.

**How to build it**:
1. Model vulnerability — admit your own mistakes and uncertainties openly
2. Respond to bad news with curiosity, not blame ("What did we learn?")
3. Explicitly invite dissent ("Who sees this differently?")
4. Run blameless postmortems (see devops-sre.md)
5. Normalize "I don't know" and "I was wrong"

**Warning sign**: If your team only tells you good news, you do not have psychological safety.

## Career Ladders: IC and Management Tracks

### Why Dual Tracks Matter
Companies like Google, Meta, Stripe, Dropbox, and Shopify all built parallel IC and management ladders because technical leadership and people leadership are fundamentally different disciplines requiring different skills. Without a clear IC track, senior engineers are forced into management to grow — damaging both the person and the team.

**Rule of parity**: The IC track must have equal compensation, influence, and prestige to the management track. If engineers believe management is the "real" leadership path, the IC track erodes.

### Google-Style Levels (widely adapted across industry)

| Level | Title | Scope |
|-------|-------|-------|
| L3 | Software Engineer (new grad) | Works on defined tasks with guidance |
| L4 | Software Engineer (mid) | Independently delivers features |
| L5 | Senior Software Engineer | Leads features, mentors L3/L4 |
| L6 | Staff Engineer | Leads cross-team technical direction |
| L7 | Senior Staff Engineer | Sets org-level technical strategy |
| L8 | Principal Engineer | Company-wide technical impact |
| L9 | Distinguished Engineer | Industry-recognized, rare |
| L10 | Fellow | Foundational industry contributions |

**Key inflection point — L5 to L6**: The jump from Senior to Staff is the hardest. Senior = great individual execution. Staff = multiplying others' execution through technical leadership. Many engineers plateau at Senior because they don't shift from "doing" to "enabling."

### IC Track Descriptions

**Staff Engineer** (L6): Leads technical direction for a product area or platform. Writes the technical strategy, drives architecture reviews, unblocks other engineers. Has influence without authority. Primary concern is the team's long-term technical health.

**Principal Engineer** (L8): Company-wide scope. Often involved in the most critical architectural decisions, security decisions, and engineering-wide standards. Frequently represents engineering in external-facing contexts.

### Management Track

| Level | Title | Typical Scope |
|-------|-------|---------------|
| M1 | Engineering Manager | 5-8 ICs |
| M2 | Senior EM / Group EM | 2-3 teams (~15-25 engineers) |
| M3 | Director of Engineering | 3-5 EMs, 30-60 engineers |
| M4 | Senior Director | Larger org, multi-director |
| M5 | VP of Engineering | Full engineering function |

**Camille Fournier's insight** (*The Manager's Path*): Ladders fail when they reward output instead of scope and influence. A senior engineer who ships a lot of code is not the same as one who multiplies the output of five other engineers.

### Building a Career Ladder

Key principles:
1. Define each level in terms of **scope and impact**, not activity or time-in-role
2. Calibration sessions: have managers review levels for their reports together, using example behaviors to normalize interpretation
3. Public frameworks: companies like Dropbox, GitLab, and Stripe have open-sourced theirs (see progression.fyi)
4. Don't create more levels than you can differentiate — 6-8 levels is typical for IC, 4-5 for management

## OKRs for Engineering Teams

**Origin**: Andy Grove (Intel) → John Doerr → Google → everywhere. *Measure What Matters* (Doerr, 2018) codified it.

### Structure
- **Objective**: Qualitative, inspiring, time-bound. "O" answers "where are we going?"
- **Key Result**: Quantitative, measurable, outcome-based. "KR" answers "how do we know we arrived?"

### Engineering OKR Examples

**Good** (outcome-based):
- O: Customers trust our platform's reliability
  - KR: Reduce P1 incident count from 8/month to 2/month
  - KR: Achieve 99.9% API uptime (measured by external monitoring)
  - KR: Mean time to recover (MTTR) drops from 2h to 30 min

**Bad** (output/activity-based):
- O: Improve platform
  - KR: Complete 5 infrastructure tickets
  - KR: Migrate to new database version
  - KR: Write 10 unit tests

### Critical Pitfalls
1. **Task lists masquerading as KRs**: If it's a to-do item, it's not a KR.
2. **Metric selection bias**: Teams pick what's easy to measure (velocity, ticket counts) over what matters (lead time, user activation, error budget consumption).
3. **Linking OKRs to compensation**: Causes sandbagging — people set safe targets they know they'll hit. Keep OKRs and reviews separate.
4. **Quarterly mismatch**: Software work often spans multi-quarter horizons (migrations, rewrites). Use annual objectives with quarterly KR cadences.
5. **90% completion = "good"**: OKRs are designed to stretch. 0.7/1.0 scoring is considered healthy. If you always hit 1.0, your goals aren't ambitious enough.

### OKR Cadence
- Set quarterly (align with company OKRs)
- Review weekly in team standups (not just at quarter-end)
- Calibrate monthly: is the KR still the right measure? Are we blocked by something outside our control?
- Score at quarter-end: 0.0-1.0 scale, 0.7 = success, 0.4-0.6 = learning, <0.4 = investigate

### Strategic Alignment
Align engineering OKRs with product OKRs with a ~70% overlap and ~30% engineering-specific items (tech debt, reliability, platform investment). The overlap ensures alignment; the 30% gives engineering space to invest in the foundation.

## Performance Reviews

### Common Frameworks

**Stack ranking** (forced distribution): Used by early Microsoft, widely abandoned. Creates internal competition, destroys collaboration. Do not use.

**Calibration-based** (recommended): Managers review their reports together using a shared rubric tied to career levels. Reduces manager bias, creates consistent standards.

**360 reviews**: Gather upward, peer, and self-feedback. Most useful as a developmental input, not a performance rating. Don't tie 360 scores directly to compensation — it creates political behavior.

### What Good Performance Reviews Include
1. Assessment against career level expectations (not against other people)
2. Specific behavioral examples — not "Alice is a great communicator" but "Alice led the incident retrospective and synthesized 8 team inputs into a clear action plan"
3. Growth areas with concrete development suggestions
4. Career trajectory discussion: what's the gap between current state and next level?

### Common Errors
- Recency bias: reviewing only the last 2 months instead of the full period
- Halo/horn effect: one positive/negative trait colors the entire review
- Vague feedback: "needs to improve communication" without specific examples or actionable guidance
- No follow-through: development plans created in reviews are never revisited

## Code Review Culture

Code review is a high-leverage practice for quality, knowledge sharing, and mentorship. It can also be a bottleneck and source of team friction if done poorly.

**Healthy norms**:
- Reviews should be completed within 24 hours (not blocked over weekends)
- Comment with the intent: nitpick, optional, blocker (use prefixes like "nit:", "optional:", "blocking:")
- Authors explain WHY in their PR description, not just WHAT
- Small PRs (<400 lines changed) that are easy to review — large PRs are rarely reviewed well
- Reviewers are not gatekeepers; they are collaborators

**Anti-patterns**:
- Review by committee (too many required reviewers)
- Senior engineer bottleneck (all PRs need approval from 1 person)
- Style debates in reviews (use linters and formatters to automate)
- Nitpicking without acknowledging the value of the PR

**Trunk-based development**: Correlates strongly with high DORA performance. Teams commit to main/trunk frequently (at least daily), using feature flags instead of long-lived branches. Eliminates merge hell, forces small incremental changes.

## Sources
- *The Manager's Path* — Camille Fournier (2017), O'Reilly
- *High Output Management* — Andy Grove (1983), Random House
- *Measure What Matters* — John Doerr (2018), Portfolio/Penguin
- *An Elegant Puzzle* — Will Larson (2019), Stripe Press
- Google Project Aristotle research (rework.withgoogle.com)
- Amy Edmondson, Harvard Business School, Psychological Safety research
- DORA State of DevOps Report 2024
- progression.fyi (open-source career ladder collection)
- Jellyfish Engineering Manager Ratio data (2024)
