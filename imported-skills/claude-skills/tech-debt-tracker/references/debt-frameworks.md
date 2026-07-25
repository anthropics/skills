# tech-debt-tracker reference

## Technical Debt Classification Framework

### 1. Code Debt
Code-level issues that make the codebase harder to understand, modify, and maintain.

**Indicators:**
- Long functions (>50 lines for complex logic, >20 for simple operations)
- Deep nesting (>4 levels of indentation)
- High cyclomatic complexity (>10)
- Duplicate code patterns (>3 similar blocks)
- Missing or inadequate error handling
- Poor variable/function naming
- Magic numbers and hardcoded values
- Commented-out code blocks

**Impact:**
- Increased debugging time
- Higher defect rates
- Slower feature development
- Knowledge silos (only original author understands the code)

**Detection Methods:**
- AST parsing for structural analysis
- Pattern matching for common anti-patterns
- Complexity metrics calculation
- Duplicate code detection algorithms

### 2. Architecture Debt
High-level design decisions that seemed reasonable at the time but now limit scalability or maintainability.

**Indicators:**
- Monolithic components that should be modular
- Circular dependencies between modules
- Violation of separation of concerns
- Inconsistent data flow patterns
- Over-engineering or under-engineering for current scale
- Tightly coupled components
- Missing abstraction layers

**Impact:**
- Difficult to scale individual components
- Cascading changes required for simple modifications
- Testing becomes complex and brittle
- Onboarding new team members takes longer

**Detection Methods:**
- Dependency analysis
- Module coupling metrics
- Component size analysis
- Interface consistency checks

### 3. Test Debt
Inadequate or missing test coverage, poor test quality, and testing infrastructure issues.

**Indicators:**
- Low test coverage (<80% for critical paths)
- Missing unit tests for complex logic
- No integration tests for key workflows
- Flaky tests that pass/fail intermittently
- Slow test execution (>10 minutes for unit tests)
- Tests that don't test meaningful behavior
- Missing test data management strategy

**Impact:**
- Fear of refactoring ("don't touch it, it works")
- Regression bugs in production
- Slow feedback cycles during development
- Difficulty validating complex business logic

**Detection Methods:**
- Coverage report analysis
- Test execution time monitoring
- Test failure pattern analysis
- Test code quality assessment

### 4. Documentation Debt
Missing, outdated, or poor-quality documentation that makes the system harder to understand and maintain.

**Indicators:**
- Missing API documentation
- Outdated README files
- No architectural decision records (ADRs)
- Missing code comments for complex algorithms
- No onboarding documentation for new team members
- Inconsistent documentation formats
- Documentation that contradicts actual implementation

**Impact:**
- Increased onboarding time for new team members
- Knowledge loss when team members leave
- Miscommunication between teams
- Repeated questions in team channels

**Detection Methods:**
- Documentation coverage analysis
- Freshness checking (last modified dates)
- Link validation
- Comment density analysis

### 5. Dependency Debt
Issues related to external libraries, frameworks, and system dependencies.

**Indicators:**
- Outdated packages with known security vulnerabilities
- Dependencies with incompatible licenses
- Unused dependencies bloating the build
- Version conflicts between packages
- Deprecated APIs still in use
- Heavy dependencies for simple tasks
- Missing dependency pinning

**Impact:**
- Security vulnerabilities
- Build instability
- Longer build times
- Legal compliance issues
- Difficulty upgrading core frameworks

**Detection Methods:**
- Vulnerability scanning
- License compliance checking
- Usage analysis
- Version compatibility checking

### 6. Infrastructure Debt
Operations and deployment-related technical debt.

**Indicators:**
- Manual deployment processes
- Missing monitoring and alerting
- Inadequate logging
- No disaster recovery plan
- Inconsistent environments (dev/staging/prod)
- Missing CI/CD pipelines
- Infrastructure as code gaps

**Impact:**
- Deployment risks and downtime
- Difficult troubleshooting
- Inconsistent behavior across environments
- Manual work that should be automated

**Detection Methods:**
- Infrastructure audit checklists
- Configuration drift detection
- Monitoring coverage analysis
- Deployment process documentation review

## Severity Scoring Framework

Each piece of tech debt is scored on multiple dimensions to determine overall severity:

### Impact Assessment (1-10 scale)

**Development Velocity Impact**
- 1-2: Negligible impact on development speed
- 3-4: Minor slowdown, workarounds available
- 5-6: Moderate impact, affects some features
- 7-8: Significant slowdown, affects most work
- 9-10: Critical blocker, prevents new development

**Quality Impact**
- 1-2: No impact on defect rates
- 3-4: Minor increase in minor bugs
- 5-6: Moderate increase in defects
- 7-8: Regular production issues
- 9-10: Critical reliability problems

**Team Productivity Impact**
- 1-2: No impact on team morale or efficiency
- 3-4: Occasional frustration
- 5-6: Regular complaints from developers
- 7-8: Team actively avoiding the area
- 9-10: Causing developer turnover

**Business Impact**
- 1-2: No customer-facing impact
- 3-4: Minor UX degradation
- 5-6: Moderate performance impact
- 7-8: Customer complaints or churn
- 9-10: Revenue-impacting issues

### Effort Assessment

**Size (Story Points or Hours)**
- XS (1-4 hours): Simple refactor or documentation update
- S (1-2 days): Minor architectural change
- M (3-5 days): Moderate refactoring effort
- L (1-2 weeks): Major component restructuring
- XL (3+ weeks): System-wide architectural changes

**Risk Level**
- Low: Well-understood change with clear scope
- Medium: Some unknowns but manageable
- High: Significant unknowns, potential for scope creep

**Skill Requirements**
- Junior: Can be handled by any team member
- Mid: Requires experienced developer
- Senior: Needs architectural expertise
- Expert: Requires deep system knowledge

## Interest Rate Calculation

Technical debt accrues "interest" - the additional cost of leaving it unfixed. This interest rate helps prioritize which debt to pay down first.

### Interest Rate Formula

```
Interest Rate = (Impact Score × Frequency of Encounter) / Time Period
```

Where:
- **Impact Score**: Average severity score (1-10)
- **Frequency of Encounter**: How often developers interact with this code
- **Time Period**: Usually measured per sprint or month

### Cost of Delay Calculation

```
Cost of Delay = Interest Rate × Time Until Fix × Team Size Multiplier
```

### Example Calculation

**Scenario**: Legacy authentication module with poor error handling

- Impact Score: 7 (causes regular production issues)
- Frequency: 15 encounters per sprint (3 developers × 5 times each)
- Team Size: 8 developers
- Current sprint: 1, planned fix: sprint 4

```
Interest Rate = 7 × 15 = 105 points per sprint
Cost of Delay = 105 × 3 × 1.2 = 378 total cost points
```

This debt item should be prioritized over lower-cost items.

## Debt Inventory Management

### Data Structure

Each debt item is tracked with the following attributes:

```json
{
  "id": "DEBT-2024-001",
  "title": "Legacy user authentication module",
  "category": "code",
  "subcategory": "error_handling",
  "location": "src/auth/legacy_auth.py:45-120",
  "description": "Authentication error handling uses generic exceptions",
  "impact": {
    "velocity": 7,
    "quality": 8,
    "productivity": 6,
    "business": 5
  },
  "effort": {
    "size": "M",
    "risk": "medium",
    "skill_required": "mid"
  },
  "interest_rate": 105,
  "cost_of_delay": 378,
  "priority": "high",
  "created_date": "2024-01-15",
  "last_updated": "2024-01-20",
  "assigned_to": null,
  "status": "identified",
  "tags": ["security", "user-experience", "maintainability"]
}
```

### Status Lifecycle

1. **Identified** - Debt detected but not yet analyzed
2. **Analyzed** - Impact and effort assessed
3. **Prioritized** - Added to backlog with priority
4. **Planned** - Assigned to specific sprint/release
5. **In Progress** - Actively being worked on
6. **Review** - Implementation complete, under review
7. **Done** - Debt resolved and verified
8. **Won't Fix** - Consciously decided not to address

## Prioritization Frameworks

### 1. Cost-of-Delay vs Effort Matrix

Plot debt items on a 2D matrix:
- X-axis: Effort (XS to XL)
- Y-axis: Cost of Delay (calculated value)

**Priority Quadrants:**
- High Cost, Low Effort: **Immediate** (quick wins)
- High Cost, High Effort: **Planned** (major initiatives)
- Low Cost, Low Effort: **Opportunistic** (during related work)
- Low Cost, High Effort: **Backlog** (consider for future)

### 2. Weighted Shortest Job First (WSJF)

```
WSJF Score = (Business Value + Time Criticality + Risk Reduction) / Effort
```

Where each component is scored 1-10:
- **Business Value**: Direct impact on customer value
- **Time Criticality**: How much value decreases over time
- **Risk Reduction**: How much risk is mitigated by fixing this debt

### 3. Technical Debt Quadrant

Based on Martin Fowler's framework:

**Quadrant 1: Reckless & Deliberate**
- "We don't have time for design"
- Highest priority for remediation

**Quadrant 2: Prudent & Deliberate**  
- "We must ship now and deal with consequences"
- Schedule for near-term resolution

**Quadrant 3: Reckless & Inadvertent**
- "What's layering?"
- Focus on education and process improvement

**Quadrant 4: Prudent & Inadvertent**
- "Now we know how we should have done it"
- Normal part of learning, lowest priority

## Refactoring Strategies

### 1. Strangler Fig Pattern
Gradually replace old system by building new functionality around it.

**When to use:**
- Large, monolithic systems
- High-risk changes to critical paths
- Long-term architectural migrations

**Implementation:**
1. Identify boundaries for extraction
2. Create abstraction layer
3. Route new features to new implementation
4. Gradually migrate existing features
5. Remove old implementation

### 2. Branch by Abstraction
Create abstraction layer to allow parallel implementations.

**When to use:**
- Need to support old and new systems simultaneously
- High-risk changes with rollback requirements
- A/B testing infrastructure changes

**Implementation:**
1. Create abstraction interface
2. Implement abstraction for current system
3. Replace direct calls with abstraction calls
4. Implement new version behind same abstraction
5. Switch implementations via configuration
6. Remove old implementation

### 3. Feature Toggles
Use configuration flags to control code execution.

**When to use:**
- Gradual rollout of refactored components
- Risk mitigation during large changes
- Experimental refactoring approaches

**Implementation:**
1. Identify decision points in code
2. Add toggle checks at decision points
3. Implement both old and new paths
4. Test both paths thoroughly
5. Gradually move toggle to new implementation
6. Remove old path and toggle

### 4. Parallel Run
Run old and new implementations simultaneously to verify correctness.

**When to use:**
- Critical business logic changes
- Data processing pipeline changes
- Algorithm improvements

**Implementation:**
1. Implement new version alongside old
2. Run both versions with same inputs
3. Compare outputs and log discrepancies
4. Investigate and fix discrepancies
5. Build confidence through parallel execution
6. Switch to new implementation
7. Remove old implementation

## Sprint Allocation Recommendations

### Debt-to-Feature Ratio

Maintain healthy balance between new features and debt reduction:

**Team Velocity < 70% of capacity:**
- 60% tech debt, 40% features
- Focus on removing major blockers

**Team Velocity 70-85% of capacity:**
- 30% tech debt, 70% features  
- Balanced maintenance approach

**Team Velocity > 85% of capacity:**
- 15% tech debt, 85% features
- Opportunistic debt reduction only

### Sprint Planning Integration

**Story Point Allocation:**
- Reserve 20% of sprint capacity for tech debt
- Prioritize debt items with highest interest rates
- Include "debt tax" in feature estimates when working in high-debt areas

**Debt Budget Tracking:**
- Track debt points completed per sprint
- Monitor debt interest rate trend
- Alert when debt accumulation exceeds team's paydown rate

### Quarterly Planning

**Debt Initiatives:**
- Identify 1-2 major debt themes per quarter
- Allocate dedicated sprints for large-scale refactoring
- Plan debt work around major feature releases

**Success Metrics:**
- Debt interest rate reduction
- Developer velocity improvements
- Defect rate reduction
- Code review cycle time improvement

## Stakeholder Reporting

### Executive Dashboard

**Key Metrics:**
- Overall tech debt health score (0-100)
- Debt trend direction (improving/declining)
- Cost of delayed fixes (in development days)
- High-risk debt items count

**Monthly Report Structure:**
1. **Executive Summary** (3 bullet points)
2. **Health Score Trend** (6-month view)
3. **Top 3 Risk Items** (business impact focus)
4. **Investment Recommendation** (resource allocation)
5. **Success Stories** (debt reduced last month)

### Engineering Team Dashboard

**Daily Metrics:**
- New debt items identified
- Debt items resolved
- Interest rate by team/component
- Debt hotspots (most problematic areas)

**Sprint Reviews:**
- Debt points completed vs. planned
- Velocity impact from debt work
- Newly discovered debt during feature work
- Team sentiment on code quality

### Product Manager Reports

**Feature Impact Analysis:**
- How debt affects feature development time
- Quality risk assessment for upcoming features
- Debt that blocks planned features
- Recommendations for feature sequence planning

**Customer Impact Translation:**
- Debt that affects performance
- Debt that increases bug rates
- Debt that limits feature flexibility
- Investment required to maintain current quality
