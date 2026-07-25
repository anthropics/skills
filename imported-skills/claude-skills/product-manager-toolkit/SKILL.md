---
name: "product-manager-toolkit"
description: Comprehensive toolkit for product managers including RICE prioritization, customer interview analysis, PRD templates, discovery frameworks, and go-to-market strategies. Use when prioritizing features, synthesizing user research, writing requirement documentation, or developing product strategy.
---

# Product Manager Toolkit

Essential tools and frameworks for modern product management, from discovery to delivery.

---

## Table of Contents

- [Quick Start](#quick-start)
- [Core Workflows](#core-workflows)
  - [Feature Prioritization](#feature-prioritization-process)
  - [Customer Discovery](#customer-discovery-process)
  - [PRD Development](#prd-development-process)
- [Tools Reference](#tools-reference)
  - [RICE Prioritizer](#rice-prioritizer)
  - [Customer Interview Analyzer](#customer-interview-analyzer)
- [Input/Output Examples](#inputoutput-examples)
- [Integration Points](#integration-points)
- [Common Pitfalls](#common-pitfalls-to-avoid)

---

## Quick Start

### For Feature Prioritization
```bash
# Create sample data file
python scripts/rice_prioritizer.py sample

# Run prioritization with team capacity
python scripts/rice_prioritizer.py sample_features.csv --capacity 15
```

### For Interview Analysis
```bash
python scripts/customer_interview_analyzer.py interview_transcript.txt
```

### For PRD Creation
1. Choose template from `references/prd_templates.md`
2. Fill sections based on discovery work
3. Review with engineering for feasibility
4. Version control in project management tool

---

## Core Workflows

### Feature Prioritization Process

```
Gather → Score → Analyze → Plan → Validate → Execute
```

#### Step 1: Gather Feature Requests
- Customer feedback (support tickets, interviews)
- Sales requests (CRM pipeline blockers)
- Technical debt (engineering input)
- Strategic initiatives (leadership goals)

#### Step 2: Score with RICE
```bash
# Input: CSV with features
python scripts/rice_prioritizer.py features.csv --capacity 20
```

See `references/frameworks.md` for RICE formula and scoring guidelines.

#### Step 3: Analyze Portfolio
Review the tool output for:
- Quick wins vs big bets distribution
- Effort concentration (avoid all XL projects)
- Strategic alignment gaps

#### Step 4: Generate Roadmap
- Quarterly capacity allocation
- Dependency identification
- Stakeholder communication plan

#### Step 5: Validate Results
**Before finalizing the roadmap:**
- [ ] Compare top priorities against strategic goals
- [ ] Run sensitivity analysis (what if estimates are wrong by 2x?)
- [ ] Review with key stakeholders for blind spots
- [ ] Check for missing dependencies between features
- [ ] Validate effort estimates with engineering

#### Step 6: Execute and Iterate
- Share roadmap with team
- Track actual vs estimated effort
- Revisit priorities quarterly
- Update RICE inputs based on learnings

---

### Customer Discovery Process

```
Plan → Recruit → Interview → Analyze → Synthesize → Validate
```

#### Step 1: Plan Research
- Define research questions
- Identify target segments
- Create interview script (see `references/frameworks.md`)

#### Step 2: Recruit Participants
- 5-8 interviews per segment
- Mix of power users and churned users
- Incentivize appropriately

#### Step 3: Conduct Interviews
- Use semi-structured format
- Focus on problems, not solutions
- Record with permission
- Take minimal notes during interview

#### Step 4: Analyze Insights
```bash
python scripts/customer_interview_analyzer.py transcript.txt
```

Extracts:
- Pain points with severity
- Feature requests with priority
- Jobs to be done patterns
- Sentiment and key themes
- Notable quotes

#### Step 5: Synthesize Findings
- Group similar pain points across interviews
- Identify patterns (3+ mentions = pattern)
- Map to opportunity areas using Opportunity Solution Tree
- Prioritize opportunities by frequency and severity

#### Step 6: Validate Solutions
**Before building:**
- [ ] Create solution hypotheses (see `references/frameworks.md`)
- [ ] Test with low-fidelity prototypes
- [ ] Measure actual behavior vs stated preference
- [ ] Iterate based on feedback
- [ ] Document learnings for future research

---

### PRD Development Process

```
Scope → Draft → Review → Refine → Approve → Track
```

#### Step 1: Choose Template
Select from `references/prd_templates.md`:

| Template | Use Case | Timeline |
|----------|----------|----------|
| Standard PRD | Complex features, cross-team | 6-8 weeks |
| One-Page PRD | Simple features, single team | 2-4 weeks |
| Feature Brief | Exploration phase | 1 week |
| Agile Epic | Sprint-based delivery | Ongoing |

#### Step 2: Draft Content
- Lead with problem statement
- Define success metrics upfront
- Explicitly state out-of-scope items
- Include wireframes or mockups

#### Step 3: Review Cycle
- Engineering: feasibility and effort
- Design: user experience gaps
- Sales: market validation
- Support: operational impact

#### Step 4: Refine Based on Feedback
- Address technical constraints
- Adjust scope to fit timeline
- Document trade-off decisions

#### Step 5: Approval and Kickoff
- Stakeholder sign-off
- Sprint planning integration
- Communication to broader team

#### Step 6: Track Execution
**After launch:**
- [ ] Compare actual metrics vs targets
- [ ] Conduct user feedback sessions
- [ ] Document what worked and what didn't
- [ ] Update estimation accuracy data
- [ ] Share learnings with team

---

## Tools Reference

### RICE Prioritizer

Advanced RICE framework implementation with portfolio analysis.

**Features:**
- RICE score calculation with configurable weights
- Portfolio balance analysis (quick wins vs big bets)
- Quarterly roadmap generation based on capacity
- Multiple output formats (text, JSON, CSV)

**CSV Input Format:**
```csv
name,reach,impact,confidence,effort,description
User Dashboard Redesign,5000,high,high,l,Complete redesign
Mobile Push Notifications,10000,massive,medium,m,Add push support
Dark Mode,8000,medium,high,s,Dark theme option
```

**Commands:**
```bash
# Create sample data
python scripts/rice_prioritizer.py sample

# Run with default capacity (10 person-months)
python scripts/rice_prioritizer.py features.csv

# Custom capacity
python scripts/rice_prioritizer.py features.csv --capacity 20

# JSON output for integration
python scripts/rice_prioritizer.py features.csv --output json

# CSV output for spreadsheets
python scripts/rice_prioritizer.py features.csv --output csv
```

---

### Customer Interview Analyzer

NLP-based interview analysis for extracting actionable insights.

**Capabilities:**
- Pain point extraction with severity assessment
- Feature request identification and classification
- Jobs-to-be-done pattern recognition
- Sentiment analysis per section
- Theme and quote extraction
- Competitor mention detection

**Commands:**
```bash
# Analyze interview transcript
python scripts/customer_interview_analyzer.py interview.txt

# JSON output for aggregation
python scripts/customer_interview_analyzer.py interview.txt json
```

---

## Input/Output Examples
→ See references/input-output-examples.md for details

## Integration Points

Compatible tools and platforms:

| Category | Platforms |
|----------|-----------|
| **Analytics** | Amplitude, Mixpanel, Google Analytics |
| **Roadmapping** | ProductBoard, Aha!, Roadmunk, Productplan |
| **Design** | Figma, Sketch, Miro |
| **Development** | Jira, Linear, GitHub, Asana |
| **Research** | Dovetail, UserVoice, Pendo, Maze |
| **Communication** | Slack, Notion, Confluence |

**JSON export enables integration with most tools:**
```bash
# Export for Jira import
python scripts/rice_prioritizer.py features.csv --output json > priorities.json

# Export for dashboard
python scripts/customer_interview_analyzer.py interview.txt json > insights.json
```

---

## Common Pitfalls to Avoid

| Pitfall | Description | Prevention |
|---------|-------------|------------|
| **Solution-First** | Jumping to features before understanding problems | Start every PRD with problem statement |
| **Analysis Paralysis** | Over-researching without shipping | Set time-boxes for research phases |
| **Feature Factory** | Shipping features without measuring impact | Define success metrics before building |
| **Ignoring Tech Debt** | Not allocating time for platform health | Reserve 20% capacity for maintenance |
| **Stakeholder Surprise** | Not communicating early and often | Weekly async updates, monthly demos |
| **Metric Theater** | Optimizing vanity metrics over real value | Tie metrics to user value delivered |

---

## Best Practices

**Writing Great PRDs:**
- Start with the problem, not the solution
- Include clear success metrics upfront
- Explicitly state what's out of scope
- Use visuals (wireframes, flows, diagrams)
- Keep technical details in appendix
- Version control all changes

**Effective Prioritization:**
- Mix quick wins with strategic bets
- Consider opportunity cost of delays
- Account for dependencies between features
- Buffer 20% for unexpected work
- Revisit priorities quarterly
- Communicate decisions with context

**Customer Discovery:**
- Ask "why" five times to find root cause
- Focus on past behavior, not future intentions
- Avoid leading questions ("Wouldn't you love...")
- Interview in the user's natural environment
- Watch for emotional reactions (pain = opportunity)
- Validate qualitative with quantitative data

---

## Quick Reference

```bash
# Prioritization
python scripts/rice_prioritizer.py features.csv --capacity 15

# Interview Analysis
python scripts/customer_interview_analyzer.py interview.txt

# Generate sample data
python scripts/rice_prioritizer.py sample

# JSON outputs
python scripts/rice_prioritizer.py features.csv --output json
python scripts/customer_interview_analyzer.py interview.txt json
```

---

## Reference Documents

- `references/prd_templates.md` - PRD templates for different contexts
- `references/frameworks.md` - Detailed framework documentation (RICE, MoSCoW, Kano, JTBD, etc.)
