# Hiring & Talent for Tech Companies

## Technical Interview Design

A strong interview process has three components: coding/technical, system design, and behavioral/values. Each tests different things and should be designed deliberately.

### Coding Interviews
**Purpose**: Assess problem-solving ability, coding quality, and communication under constraint.

**Industry standard**: 45-60 minute LeetCode-style problems. FAANG/MAANG companies weight heavily on graph algorithms, dynamic programming, and tree traversal (these account for ~40% of questions per 2024 data). Array manipulation and string processing are also common.

**Best practice for companies not competing on algorithmic complexity**:
- Use take-home projects or work-sample tests over pure algorithms
- Pair programming exercises closer to actual job work
- Code review exercises: give them a PR to review
- Debug exercises: give them broken code to fix

**Candidate experience rule**: Your interview is also a signal to candidates about how you work. Long, unclear processes drive away good candidates who have options.

### System Design Interviews
**Purpose**: Evaluate architectural thinking, trade-off reasoning, scalability awareness, and communication of technical decisions.

**Format**: 45-60 minutes, whiteboard or shared doc. Prompt: "Design [Twitter feed / URL shortener / distributed cache / recommendation system]."

**What good candidates demonstrate**:
1. Clarify requirements before diving in (functional + non-functional)
2. Capacity estimation: users, read/write ratio, storage needs
3. High-level design: components, data flow, APIs
4. Deep dive: specific component tradeoffs (SQL vs NoSQL, sync vs async, etc.)
5. Failure modes: what breaks, how you detect it, how you recover

**2025 shift**: System design interviews now increasingly ask about AI-era infrastructure — "Design ChatGPT's serving layer," "Design a real-time ML pipeline." Expect this to continue spreading beyond FAANG.

### Behavioral Interviews
**Purpose**: Assess values fit, leadership behaviors, collaboration style, and how candidates handle adversity.

**STAR method**: Situation → Task → Action → Result. Train interviewers to probe for specifics.

**High-signal questions**:
- "Tell me about a time you disagreed with a technical decision and how you handled it."
- "Describe a project that failed. What did you learn?"
- "Tell me about a time you had to influence without authority."
- "How have you handled a direct report who was underperforming?"

**Structured behavioral interviews**: Use a predefined question bank with rubrics. Two interviewers ask about the same competencies independently. Reduces bias, improves prediction of job performance.

## Interview Process Design

### Anti-Patterns That Hurt Hiring
- **Loop too long**: >5 rounds drives away candidates with other offers
- **No feedback loop**: If you can't tell candidates why they were rejected, your process has no rubric
- **Inconsistent loop**: Every candidate has a different experience (can't compare candidates fairly)
- **"Culture fit" as a veto**: Often proxies for "looks like me." Replace with "values alignment" with defined criteria.
- **Ghosting candidates**: Kills employer brand — candidates tell their networks

### Hiring Bar Calibration
- Hold calibration sessions where interviewers align on what "strong yes" vs. "yes" vs. "no" looks like
- Debrief sessions: all interviewers share their signal before seeing others' ratings (prevents anchoring)
- Track hiring bar over time: if 60% of hires are "strong yes", your bar is well-calibrated; if only 30%, you may be too selective or moving too slowly

### Time-to-Hire Benchmarks
- Top candidates are off the market in 10-14 days (sometimes less)
- Full loop (phone screen → onsite → decision) should take <2 weeks
- Offer → acceptance should close in <1 week; after 1 week, probability of acceptance drops significantly

## Compensation Benchmarking

### Tools
- **Levels.fyi**: Crowdsourced, highly detailed. Breaks down by company, level, location, skills, team. Best for real-time market data. Used for candidate negotiation and offer benchmarking. Provides base, equity, and bonus separately.
- **Radford (now Aon)**: Survey-based, industry standard for formal HR benchmarking. Expensive but comprehensive, used by most large tech companies' HR teams.
- **Mercer**: Similar to Radford, common for non-tech companies entering tech hiring.
- **Glassdoor**: Lower fidelity than Levels.fyi for tech roles; useful for sentiment.
- **Blind**: Anecdotal but useful for understanding candidate market perception.

### Compensation Components (US Tech)
1. **Base salary**: Cash paid regardless of performance or company performance
2. **Annual bonus**: Performance-linked, typically 10-20% of base for engineering
3. **Equity**: Stock options (pre-IPO) or RSUs (public companies)
   - RSUs vest over 4 years, typically with 1-year cliff
   - FAANG equity grants can exceed base salary at senior levels
4. **Signing bonus**: One-time payment to offset leaving unvested equity or golden handcuffs

**Total comp (TC) = base + bonus + annual equity value (grant / vesting period)**

Candidates increasingly negotiate on TC, not just base. Levels.fyi normalizes to TC for comparison.

### 2024 US Engineering Compensation Ranges (Levels.fyi data)

| Level | Tier | TC Range |
|-------|------|----------|
| L3/New grad | FAANG | $160K-$220K TC |
| L4/Mid | FAANG | $200K-$320K TC |
| L5/Senior | FAANG | $280K-$450K TC |
| L6/Staff | FAANG | $400K-$650K TC |
| Senior/Mid | Mid-market tech | $120K-$180K TC |
| Senior | Mid-market tech | $160K-$240K TC |

**Regional adjustments**: San Francisco and New York command ~20-30% premium over Seattle. Austin, Denver, Boston are 10-15% below SF. Remote-first companies increasingly offer location-independent pay (Stripe model) or location-adjusted pay (typical big tech model).

## Fully-Loaded Engineer Cost

The total cost to the company of a software engineer is significantly higher than the salary.

### Cost Components
- **Salary**: $100K-$180K average US engineer (senior specialists higher)
- **Benefits**: +20-30% of salary (health insurance, 401K match, dental, vision, disability, PTO)
- **Payroll taxes**: ~7.65% of salary (FICA, etc.)
- **Equipment**: $2,500-$5,000 year 1 (laptop, monitors, peripherals), amortized
- **Software licenses**: $100-$300/month (GitHub, Slack, cloud tools, IDEs)
- **Office/remote stipend**: $0-$12K/year
- **Recruiting cost**: 15-25% of first-year salary for external recruiter; 5-10% for internal
- **Onboarding/ramp time**: 3-6 months of reduced productivity (~$15-30K opportunity cost)
- **Management overhead**: Allocated share of EM, HR, legal, finance time

### Practical Fully-Loaded Estimates (2024-2025, US)

| Role | Salary | Fully-Loaded Annual | Fully-Loaded Monthly |
|------|--------|--------------------|--------------------|
| Mid-level SWE | $130K | $195K-$220K | $16K-$18K |
| Senior SWE | $165K | $240K-$270K | $20K-$22.5K |
| Staff SWE | $210K | $300K-$340K | $25K-$28K |

**Rule of thumb**: Fully-loaded cost is ~1.5-1.7x base salary.

### Attrition Cost
- Losing an engineer costs 50-200% of annual salary in replacement costs
- A senior engineer ($165K salary) departure costs $82K-$330K total (lost productivity, recruiting, hiring, onboarding)
- This is why retention investment (career development, competitive pay, good management) has enormous ROI

## Retention Strategies

### What Drives Attrition (in order of frequency)
1. Poor management (the #1 reason people leave — "people leave managers, not companies")
2. Compensation below market (people leave when they feel undervalued, or find out they're underpaid)
3. Lack of growth / career development
4. Boring work / no technical challenge
5. Poor culture / toxic teammates
6. Overwork and burnout

### High-Leverage Retention Actions
- **Regular compensation reviews**: At least annually, compare against market benchmarks. Proactively adjust before people feel they need to ask.
- **Career development investment**: Pay for conferences, training, certifications, internal transfers to new roles
- **Manager quality**: Poor managers drive attrition more than anything else. Invest in manager training and remove bad managers quickly.
- **Internal mobility**: Give engineers options to move teams, try new tech, change product areas without leaving the company
- **Recognition**: Public recognition of significant contributions. Engineers who feel invisible leave.

## Remote vs. Hybrid Strategy

### 2024 State of Remote Work
No single "right" answer — but the choice has major talent implications:

| Model | Talent Pool | Culture | Cost |
|-------|-------------|---------|------|
| Fully remote | Global, largest pool | Hard to build, requires intentional async culture | Lower office cost, higher tool cost |
| Hybrid (3 days in office) | Local + commute radius | Natural, less effort to maintain | Full office cost |
| Fully in-office | Local radius only | Easiest to maintain | Highest cost |

**Employer branding**: Remote-first companies can hire from anywhere, widening the talent pool dramatically. However, top candidates sometimes prefer in-person culture (especially for mentorship and collaboration). Hybrid without clear norms ("2 days, choose your own") often produces the worst of both worlds.

**GitLab model** (fully remote, 2000+ employees): Documentation-first, async-by-default. Metrics show 37% fewer meeting hours. Requires cultural discipline to implement.

### Remote Engineering Team Best Practices
- Clear documentation culture: decisions, ADRs, meeting notes all written and searchable
- Overlap hours: For globally distributed teams, establish 2-4 hours of overlap where everyone is available
- Annual in-person gathering: Even fully remote teams benefit from once-yearly in-person meetups for trust and culture
- Async-first communication: Default to written, threaded discussion (Notion, Confluence, Linear) before synchronous meetings
- Camera norms: Default cameras on for small-group discussions; camera optional for large meetings

## Employer Branding for Engineers

Engineers research companies through:
- Engineering blogs (Netflix Tech Blog, Airbnb Engineering, Stripe blog — all high signal)
- GitHub activity and open-source contributions
- Conference talks from engineering leaders
- Levels.fyi and Glassdoor reviews
- Referral networks / LinkedIn

**High-leverage branding investments**:
- Publish real engineering blog posts (actual architecture decisions, not marketing)
- Open-source internal tools when safe to do so
- Have senior engineers speak at conferences (QCon, Velocity, local meetups)
- Respond to Glassdoor reviews

## Sources
- Levels.fyi compensation data (real-time, 2024-2025)
- TechInterviewHandbook.org
- MIT CAPD — Salary Negotiation Guide
- Fast Company — Levels.fyi feature (2021)
- DontHireDevs.com — "Real Cost of Hiring a Software Engineer 2026"
- GlenCoyne.com — Fully Loaded Cost Analysis
- DORA State of DevOps 2024
- DesignGurus.io — FAANG interview evolution 2025-2026
- GitLab Handbook — All-Remote Guide (handbook.gitlab.com)
