# Root Cause Analysis (RCA) Frameworks Guide

## Overview

This guide provides detailed instructions for applying various Root Cause Analysis frameworks during Post-Incident Reviews. Each framework offers a different perspective and approach to identifying underlying causes of incidents.

## Framework Selection Guidelines

| Incident Type | Recommended Framework | Why |
|---------------|----------------------|-----|
| **Process Failure** | 5 Whys | Simple, direct cause-effect chain |
| **Complex System Failure** | Fishbone + Timeline | Multiple contributing factors |
| **Human Error** | Fishbone | Systematic analysis of contributing factors |
| **Extended Incidents** | Timeline Analysis | Understanding decision points |
| **High-Risk Incidents** | Bow Tie | Comprehensive barrier analysis |
| **Recurring Issues** | 5 Whys + Fishbone | Deep dive into systemic issues |

---

## 5 Whys Analysis Framework

### Purpose
Iteratively drill down through cause-effect relationships to identify root causes.

### When to Use
- Simple, linear cause-effect chains
- Time-pressured analysis
- Process-related failures
- Individual component failures

### Process Steps

#### Step 1: Problem Statement
Write a clear, specific problem statement.

**Good Example:**
> "The payment API returned 500 errors for 2 hours on March 15, affecting 80% of checkout attempts."

**Poor Example:**
> "The system was broken."

#### Step 2: First Why
Ask why the problem occurred. Focus on immediate, observable causes.

**Example:**
- **Why 1:** Why did the payment API return 500 errors?
- **Answer:** The database connection pool was exhausted.

#### Step 3: Subsequent Whys
For each answer, ask "why" again. Continue until you reach a root cause.

**Example Chain:**
- **Why 2:** Why was the database connection pool exhausted?
- **Answer:** The application was creating more connections than usual.

- **Why 3:** Why was the application creating more connections?
- **Answer:** A new feature wasn't properly closing connections.

- **Why 4:** Why wasn't the feature properly closing connections?
- **Answer:** Code review missed the connection leak pattern.

- **Why 5:** Why did code review miss this pattern?
- **Answer:** We don't have automated checks for connection pooling best practices.

#### Step 4: Validation
Verify that addressing the root cause would prevent the original problem.

### Best Practices

1. **Ask at least 3 "whys"** - Surface causes are rarely root causes
2. **Focus on process failures, not people** - Avoid blame, focus on system improvements
3. **Use evidence** - Support each answer with data or observations
4. **Consider multiple paths** - Some problems have multiple root causes
5. **Test the logic** - Work backwards from root cause to problem

### Common Pitfalls

- **Stopping too early** - First few whys often reveal symptoms, not causes
- **Single-cause assumption** - Complex systems often have multiple contributing factors
- **Blame focus** - Focusing on individual mistakes rather than system failures
- **Vague answers** - Use specific, actionable answers

### 5 Whys Template

```markdown
## 5 Whys Analysis

**Problem Statement:** [Clear description of the incident]

**Why 1:** [First why question]
**Answer:** [Specific, evidence-based answer]
**Evidence:** [Supporting data, logs, observations]

**Why 2:** [Second why question]
**Answer:** [Specific answer based on Why 1]
**Evidence:** [Supporting evidence]

[Continue for 3-7 iterations]

**Root Cause(s) Identified:**
1. [Primary root cause]
2. [Secondary root cause if applicable]

**Validation:** [Confirm that addressing root causes would prevent recurrence]
```

---

## Fishbone (Ishikawa) Diagram Framework

### Purpose
Systematically analyze potential causes across multiple categories to identify contributing factors.

### When to Use
- Complex incidents with multiple potential causes
- When human factors are suspected
- Systemic or organizational issues
- When 5 Whys doesn't reveal clear root causes

### Categories

#### People (Human Factors)
- **Training and Skills**
  - Insufficient training on new systems
  - Lack of domain expertise
  - Skill gaps in team
  - Knowledge not shared across team

- **Communication**
  - Poor communication between teams
  - Unclear responsibilities
  - Information not reaching right people
  - Language/cultural barriers

- **Decision Making**
  - Decisions made under pressure
  - Insufficient information for decisions
  - Risk assessment inadequate
  - Approval processes bypassed

#### Process (Procedures and Workflows)
- **Documentation**
  - Outdated procedures
  - Missing runbooks
  - Unclear instructions
  - Process not documented

- **Change Management**
  - Inadequate change review
  - Rushed deployments
  - Insufficient testing
  - Rollback procedures unclear

- **Review and Approval**
  - Code review gaps
  - Architecture review skipped
  - Security review insufficient
  - Performance review missing

#### Technology (Systems and Tools)
- **Architecture**
  - Single points of failure
  - Insufficient redundancy
  - Scalability limitations
  - Tight coupling between systems

- **Monitoring and Alerting**
  - Missing monitoring
  - Alert fatigue
  - Inadequate thresholds
  - Poor alert routing

- **Tools and Automation**
  - Manual processes prone to error
  - Tool limitations
  - Automation gaps
  - Integration issues

#### Environment (External Factors)
- **Infrastructure**
  - Hardware failures
  - Network issues
  - Capacity limitations
  - Geographic dependencies

- **Dependencies**
  - Third-party service failures
  - External API changes
  - Vendor issues
  - Supply chain problems

- **External Pressure**
  - Time pressure from business
  - Resource constraints
  - Regulatory changes
  - Market conditions

### Process Steps

#### Step 1: Define the Problem
Place the incident at the "head" of the fishbone diagram.

#### Step 2: Brainstorm Causes
For each category, brainstorm potential contributing factors.

#### Step 3: Drill Down
For each factor, ask what caused that factor (sub-causes).

#### Step 4: Identify Primary Causes
Mark the most likely contributing factors based on evidence.

#### Step 5: Validate
Gather evidence to support or refute each suspected cause.

### Fishbone Template

```markdown
## Fishbone Analysis

**Problem:** [Incident description]

### People
**Training/Skills:**
- [Factor 1]: [Evidence/likelihood]
- [Factor 2]: [Evidence/likelihood]

**Communication:**
- [Factor 1]: [Evidence/likelihood]

**Decision Making:**
- [Factor 1]: [Evidence/likelihood]

### Process
**Documentation:**
- [Factor 1]: [Evidence/likelihood]

**Change Management:**
- [Factor 1]: [Evidence/likelihood]

**Review/Approval:**
- [Factor 1]: [Evidence/likelihood]

### Technology
**Architecture:**
- [Factor 1]: [Evidence/likelihood]

**Monitoring:**
- [Factor 1]: [Evidence/likelihood]

**Tools:**
- [Factor 1]: [Evidence/likelihood]

### Environment
**Infrastructure:**
- [Factor 1]: [Evidence/likelihood]

**Dependencies:**
- [Factor 1]: [Evidence/likelihood]

**External Factors:**
- [Factor 1]: [Evidence/likelihood]

### Primary Contributing Factors
1. [Factor with highest evidence/impact]
2. [Second most significant factor]
3. [Third most significant factor]

### Root Cause Hypothesis
[Synthesized explanation of how factors combined to cause incident]
```

---

## Timeline Analysis Framework

### Purpose
Analyze the chronological sequence of events to identify decision points, missed opportunities, and process gaps.

### When to Use
- Extended incidents (> 1 hour)
- Complex multi-phase incidents
- When response effectiveness is questioned
- Communication or coordination failures

### Analysis Dimensions

#### Detection Analysis
- **Time to Detection:** How long from onset to first alert?
- **Detection Method:** How was the incident first identified?
- **Alert Effectiveness:** Were the right people notified quickly?
- **False Negatives:** What signals were missed?

#### Response Analysis
- **Time to Response:** How long from detection to first response action?
- **Escalation Timing:** Were escalations timely and appropriate?
- **Resource Mobilization:** How quickly were the right people engaged?
- **Decision Points:** What key decisions were made and when?

#### Communication Analysis
- **Internal Communication:** How effective was team coordination?
- **External Communication:** Were stakeholders informed appropriately?
- **Communication Gaps:** Where did information flow break down?
- **Update Frequency:** Were updates provided at appropriate intervals?

#### Resolution Analysis
- **Mitigation Strategy:** Was the chosen approach optimal?
- **Alternative Paths:** What other options were considered?
- **Resource Allocation:** Were resources used effectively?
- **Verification:** How was resolution confirmed?

### Process Steps

#### Step 1: Event Reconstruction
Create comprehensive timeline with all available events.

#### Step 2: Phase Identification
Identify distinct phases (detection, triage, escalation, mitigation, resolution).

#### Step 3: Gap Analysis
Identify time gaps and analyze their causes.

#### Step 4: Decision Point Analysis
Examine key decision points and alternative paths.

#### Step 5: Effectiveness Assessment
Evaluate the overall effectiveness of the response.

### Timeline Template

```markdown
## Timeline Analysis

### Incident Phases
1. **Detection** ([start] - [end], [duration])
2. **Triage** ([start] - [end], [duration])
3. **Escalation** ([start] - [end], [duration])
4. **Mitigation** ([start] - [end], [duration])
5. **Resolution** ([start] - [end], [duration])

### Key Decision Points
**[Timestamp]:** [Decision made]
- **Context:** [Situation at time of decision]
- **Alternatives:** [Other options considered]
- **Outcome:** [Result of decision]
- **Assessment:** [Was this optimal?]

### Communication Timeline
**[Timestamp]:** [Communication event]
- **Channel:** [Slack/Email/Phone/etc.]
- **Audience:** [Who was informed]
- **Content:** [What was communicated]
- **Effectiveness:** [Assessment]

### Gaps and Delays
**[Time Period]:** [Description of gap]
- **Duration:** [Length of gap]
- **Cause:** [Why did gap occur]
- **Impact:** [Effect on incident response]

### Response Effectiveness
**Strengths:**
- [What went well]
- [Effective decisions/actions]

**Weaknesses:**
- [What could be improved]
- [Missed opportunities]

### Root Causes from Timeline
1. [Process-based root cause]
2. [Communication-based root cause]
3. [Decision-making root cause]
```

---

## Bow Tie Analysis Framework

### Purpose
Analyze both preventive measures (left side) and protective measures (right side) around an incident.

### When to Use
- High-severity incidents (SEV1)
- Security incidents
- Safety-critical systems
- When comprehensive barrier analysis is needed

### Components

#### Hazards
What conditions create the potential for incidents?

**Examples:**
- High traffic loads
- Software deployments
- Human interactions with critical systems
- Third-party dependencies

#### Top Event
What actually went wrong? This is the center of the bow tie.

**Examples:**
- "Database became unresponsive"
- "Payment processing failed"
- "User authentication service crashed"

#### Threats (Left Side)
What specific causes could lead to the top event?

**Examples:**
- Code defects in new deployment
- Database connection pool exhaustion
- Network connectivity issues
- DDoS attack

#### Consequences (Right Side)
What are the potential impacts of the top event?

**Examples:**
- Revenue loss
- Customer churn
- Regulatory violations
- Brand damage
- Data loss

#### Barriers
What controls exist (or could exist) to prevent threats or mitigate consequences?

**Preventive Barriers (Left Side):**
- Code reviews
- Automated testing
- Load testing
- Input validation
- Rate limiting

**Protective Barriers (Right Side):**
- Circuit breakers
- Failover systems
- Backup procedures
- Customer communication
- Rollback capabilities

### Process Steps

#### Step 1: Define the Top Event
Clearly state what went wrong.

#### Step 2: Identify Threats
Brainstorm all possible causes that could lead to the top event.

#### Step 3: Identify Consequences
List all potential impacts of the top event.

#### Step 4: Map Existing Barriers
Identify current controls for each threat and consequence.

#### Step 5: Assess Barrier Effectiveness
Evaluate how well each barrier worked (or failed).

#### Step 6: Recommend Additional Barriers
Identify new controls needed to prevent recurrence.

### Bow Tie Template

```markdown
## Bow Tie Analysis

**Top Event:** [What went wrong]

### Threats (Potential Causes)
1. **[Threat 1]**
   - Likelihood: [High/Medium/Low]
   - Current Barriers: [Preventive controls]
   - Barrier Effectiveness: [Assessment]

2. **[Threat 2]**
   - Likelihood: [High/Medium/Low]
   - Current Barriers: [Preventive controls]
   - Barrier Effectiveness: [Assessment]

### Consequences (Potential Impacts)
1. **[Consequence 1]**
   - Severity: [High/Medium/Low]
   - Current Barriers: [Protective controls]
   - Barrier Effectiveness: [Assessment]

2. **[Consequence 2]**
   - Severity: [High/Medium/Low]
   - Current Barriers: [Protective controls]
   - Barrier Effectiveness: [Assessment]

### Barrier Analysis
**Effective Barriers:**
- [Barrier that worked well]
- [Why it was effective]

**Failed Barriers:**
- [Barrier that failed]
- [Why it failed]
- [How to improve]

**Missing Barriers:**
- [Needed preventive control]
- [Needed protective control]

### Recommendations
**Preventive Measures:**
1. [New barrier to prevent threat]
2. [Improvement to existing barrier]

**Protective Measures:**
1. [New barrier to mitigate consequence]
2. [Improvement to existing barrier]
```

---

## Framework Comparison

| Framework | Time Required | Complexity | Best For | Output |
|-----------|---------------|------------|----------|---------|
| **5 Whys** | 30-60 minutes | Low | Simple, linear causes | Clear cause chain |
| **Fishbone** | 1-2 hours | Medium | Complex, multi-factor | Comprehensive factor map |
| **Timeline** | 2-3 hours | Medium | Extended incidents | Process improvements |
| **Bow Tie** | 2-4 hours | High | High-risk incidents | Barrier strategy |

## Combining Frameworks

### 5 Whys + Fishbone
Use 5 Whys for initial analysis, then Fishbone to explore contributing factors.

### Timeline + 5 Whys
Use Timeline to identify key decision points, then 5 Whys on critical failures.

### Fishbone + Bow Tie
Use Fishbone to identify causes, then Bow Tie to develop comprehensive prevention strategy.

## Quality Checklist

- [ ] Root causes address systemic issues, not symptoms
- [ ] Analysis is backed by evidence, not assumptions  
- [ ] Multiple perspectives considered (technical, process, human)
- [ ] Recommendations are specific and actionable
- [ ] Analysis focuses on prevention, not blame
- [ ] Findings are validated against incident timeline
- [ ] Contributing factors are prioritized by impact
- [ ] Root causes link clearly to preventive actions

## Common Anti-Patterns

- **Human Error as Root Cause** - Dig deeper into why human error occurred
- **Single Root Cause** - Complex systems usually have multiple contributing factors
- **Technology-Only Focus** - Consider process and organizational factors
- **Blame Assignment** - Focus on system improvements, not individual fault
- **Generic Recommendations** - Provide specific, measurable actions
- **Surface-Level Analysis** - Ensure you've reached true root causes

---

**Last Updated:** February 2026  
**Next Review:** August 2026  
**Owner:** SRE Team + Engineering Leadership