---
name: "senior-pm"
description: Senior Project Manager for enterprise software, SaaS, and digital transformation projects. Specializes in portfolio management, quantitative risk analysis, resource optimization, stakeholder alignment, and executive reporting. Uses advanced methodologies including EMV analysis, Monte Carlo simulation, WSJF prioritization, and multi-dimensional health scoring. Use when a user needs help with project plans, project status reports, risk assessments, resource allocation, project roadmaps, milestone tracking, team capacity planning, portfolio health reviews, program management, or executive-level project reporting — especially for enterprise-scale initiatives with multiple workstreams, complex dependencies, or multi-million dollar budgets.
---

# Senior Project Management Expert

## Overview

Strategic project management for enterprise software, SaaS, and digital transformation initiatives. Provides portfolio management capabilities, quantitative analysis tools, and executive-level reporting frameworks for complex, multi-project portfolios.

### Core Expertise Areas

**Portfolio Management & Strategic Alignment**
- Multi-project portfolio optimization using advanced prioritization models (WSJF, RICE, ICE, MoSCoW)
- Strategic roadmap development aligned with business objectives and market conditions
- Resource capacity planning and allocation optimization across portfolio
- Portfolio health monitoring with multi-dimensional scoring frameworks

**Quantitative Risk Management**
- Expected Monetary Value (EMV) analysis for financial risk quantification
- Monte Carlo simulation for schedule risk modeling and confidence intervals
- Risk appetite framework implementation with enterprise-level thresholds
- Portfolio risk correlation analysis and diversification strategies

**Executive Communication & Governance**
- Board-ready executive reports with RAG status and strategic recommendations
- Stakeholder alignment through sophisticated RACI matrices and escalation paths
- Financial performance tracking with risk-adjusted ROI and NPV calculations
- Change management strategies for large-scale digital transformations

## Methodology & Frameworks

### Three-Tier Analysis Approach

**Tier 1: Portfolio Health Assessment**
Uses `project_health_dashboard.py` to provide comprehensive multi-dimensional scoring:

```bash
python3 scripts/project_health_dashboard.py assets/sample_project_data.json
```

**Health Dimensions (Weighted Scoring):**
- **Timeline Performance** (25% weight): Schedule adherence, milestone achievement, critical path analysis
- **Budget Management** (25% weight): Spend variance, forecast accuracy, cost efficiency metrics
- **Scope Delivery** (20% weight): Feature completion rates, requirement satisfaction, change control
- **Quality Metrics** (20% weight): Code coverage, defect density, technical debt, security posture
- **Risk Exposure** (10% weight): Risk score, mitigation effectiveness, exposure trends

**RAG Status Calculation:**
- 🟢 Green: Composite score >80, all dimensions >60
- 🟡 Amber: Composite score 60-80, or any dimension 40-60
- 🔴 Red: Composite score <60, or any dimension <40

**Tier 2: Risk Matrix & Mitigation Strategy**
Leverages `risk_matrix_analyzer.py` for quantitative risk assessment:

```bash
python3 scripts/risk_matrix_analyzer.py assets/sample_project_data.json
```

**Risk Quantification Process:**
1. **Probability Assessment** (1-5 scale): Historical data, expert judgment, Monte Carlo inputs
2. **Impact Analysis** (1-5 scale): Financial, schedule, quality, and strategic impact vectors
3. **Category Weighting**: Technical (1.2x), Resource (1.1x), Financial (1.4x), Schedule (1.0x)
4. **EMV Calculation**:

```python
# EMV and risk-adjusted budget calculation
def calculate_emv(risks):
    category_weights = {"Technical": 1.2, "Resource": 1.1, "Financial": 1.4, "Schedule": 1.0}
    total_emv = 0
    for risk in risks:
        score = risk["probability"] * risk["impact"] * category_weights[risk["category"]]
        emv = risk["probability"] * risk["financial_impact"]
        total_emv += emv
        risk["score"] = score
    return total_emv

def risk_adjusted_budget(base_budget, portfolio_risk_score, risk_tolerance_factor):
    risk_premium = portfolio_risk_score * risk_tolerance_factor
    return base_budget * (1 + risk_premium)
```

**Risk Response Strategies (by score threshold):**
- **Avoid** (>18): Eliminate through scope/approach changes
- **Mitigate** (12-18): Reduce probability or impact through active intervention
- **Transfer** (8-12): Insurance, contracts, partnerships
- **Accept** (<8): Monitor with contingency planning

**Tier 3: Resource Capacity Optimization**
Employs `resource_capacity_planner.py` for portfolio resource analysis:

```bash
python3 scripts/resource_capacity_planner.py assets/sample_project_data.json
```

**Capacity Analysis Framework:**
- **Utilization Optimization**: Target 70-85% for sustainable productivity
- **Skill Matching**: Algorithm-based resource allocation to maximize efficiency
- **Bottleneck Identification**: Critical path resource constraints across portfolio
- **Scenario Planning**: What-if analysis for resource reallocation strategies

### Advanced Prioritization Models

Apply each model in the specific context where it provides the most signal:

**Weighted Shortest Job First (WSJF)** — Resource-constrained agile portfolios with quantifiable cost-of-delay
```python
def wsjf(user_value, time_criticality, risk_reduction, job_size):
    return (user_value + time_criticality + risk_reduction) / job_size
```

**RICE** — Customer-facing initiatives where reach metrics are quantifiable
```python
def rice(reach, impact, confidence_pct, effort_person_months):
    return (reach * impact * (confidence_pct / 100)) / effort_person_months
```

**ICE** — Rapid prioritization during brainstorming or when analysis time is limited
```python
def ice(impact, confidence, ease):
    return (impact + confidence + ease) / 3
```

**Model Selection — Use this decision logic:**
```
if resource_constrained and agile_methodology and cost_of_delay_quantifiable:
    → WSJF
elif customer_facing and reach_metrics_available:
    → RICE
elif quick_prioritization_needed or ideation_phase:
    → ICE
elif multiple_stakeholder_groups_with_differing_priorities:
    → MoSCoW
elif complex_tradeoffs_across_incommensurable_criteria:
    → Multi-Criteria Decision Analysis (MCDA)
```

Reference: `references/portfolio-prioritization-models.md`

### Risk Management Framework

Reference: `references/risk-management-framework.md`

**Step 1: Risk Classification by Category**
- Technical: Architecture, integration, performance
- Resource: Availability, skills, retention
- Schedule: Dependencies, critical path, external factors
- Financial: Budget overruns, currency, economic factors
- Business: Market changes, competitive pressure, strategic shifts

**Step 2: Three-Point Estimation for Monte Carlo Inputs**
```python
def three_point_estimate(optimistic, most_likely, pessimistic):
    expected = (optimistic + 4 * most_likely + pessimistic) / 6
    std_dev = (pessimistic - optimistic) / 6
    return expected, std_dev
```

**Step 3: Portfolio Risk Correlation**
```python
import math

def portfolio_risk(individual_risks, correlations):
    # individual_risks: list of risk EMV values
    # correlations: list of (i, j, corr_coefficient) tuples
    sum_sq = sum(r**2 for r in individual_risks)
    sum_corr = sum(2 * c * individual_risks[i] * individual_risks[j]
                   for i, j, c in correlations)
    return math.sqrt(sum_sq + sum_corr)
```

**Risk Appetite Framework:**
- **Conservative**: Risk scores 0-8, 25-30% contingency reserves
- **Moderate**: Risk scores 8-15, 15-20% contingency reserves
- **Aggressive**: Risk scores 15+, 10-15% contingency reserves

## Assets & Templates

### Project Charter Template
Reference: `assets/project_charter_template.md`

**Comprehensive 12-section charter including:**
- Executive summary with strategic alignment
- Success criteria with KPIs and quality gates
- RACI matrix with decision authority levels
- Risk assessment with mitigation strategies
- Budget breakdown with contingency analysis
- Timeline with critical path dependencies

### Executive Report Template
Reference: `assets/executive_report_template.md`

**Board-level portfolio reporting with:**
- RAG status dashboard with trend analysis
- Financial performance vs. strategic objectives
- Risk heat map with mitigation status
- Resource utilization and capacity analysis
- Forward-looking recommendations with ROI projections

### RACI Matrix Template
Reference: `assets/raci_matrix_template.md`

**Enterprise-grade responsibility assignment featuring:**
- Detailed stakeholder roster with decision authority
- Phase-based RACI assignments (initiation through deployment)
- Escalation paths with timeline and authority levels
- Communication protocols and meeting frameworks
- Conflict resolution processes with governance integration

### Sample Portfolio Data
Reference: `assets/sample_project_data.json`

**Realistic multi-project portfolio including:**
- 4 projects across different phases and priorities
- Complete financial data (budgets, actuals, forecasts)
- Resource allocation with utilization metrics
- Risk register with probability/impact scoring
- Quality metrics and stakeholder satisfaction data
- Dependencies and milestone tracking

### Expected Output Examples
Reference: `assets/expected_output.json`

**Demonstrates script capabilities with:**
- Portfolio health scores and RAG status
- Risk matrix visualization and mitigation priorities
- Resource capacity analysis with optimization recommendations
- Integration examples showing how outputs complement each other

## Implementation Workflows

### Portfolio Health Review (Weekly)

1. **Data Collection & Validation**
   ```bash
   python3 scripts/project_health_dashboard.py current_portfolio.json
   ```
   ⚠️ If any project composite score <60 or a critical data field is missing, STOP and resolve data integrity issues before proceeding.

2. **Risk Assessment Update**
   ```bash
   python3 scripts/risk_matrix_analyzer.py current_portfolio.json
   ```
   ⚠️ If any risk score >18 (Avoid threshold), STOP and initiate escalation to project sponsor before proceeding.

3. **Capacity Analysis**
   ```bash
   python3 scripts/resource_capacity_planner.py current_portfolio.json
   ```
   ⚠️ If any team utilization >90% or <60%, flag for immediate reallocation discussion before step 4.

4. **Executive Summary Generation**
   - Synthesize outputs into executive report format
   - Highlight critical issues and recommendations
   - Prepare stakeholder communications

### Monthly Strategic Review

1. **Portfolio Prioritization Review**
   - Apply WSJF/RICE/ICE models to evaluate current priorities
   - Assess strategic alignment with business objectives
   - Identify optimization opportunities

2. **Risk Portfolio Analysis**
   - Update risk appetite and tolerance levels
   - Review portfolio risk correlation and concentration
   - Adjust risk mitigation investments

3. **Resource Optimization Planning**
   - Analyze capacity constraints across upcoming quarter
   - Plan resource reallocation and hiring strategies
   - Identify skill gaps and training needs

4. **Stakeholder Alignment Session**
   - Present portfolio health and strategic recommendations
   - Gather feedback on prioritization and resource allocation
   - Align on upcoming quarter priorities and investments

### Quarterly Portfolio Optimization

1. **Strategic Alignment Assessment**
   - Evaluate portfolio contribution to business objectives
   - Assess market and competitive position changes
   - Update strategic priorities and success criteria

2. **Financial Performance Review**
   - Analyze risk-adjusted ROI across portfolio
   - Review budget performance and forecast accuracy
   - Optimize investment allocation for maximum value

3. **Capability Gap Analysis**
   - Identify emerging technology and skill requirements
   - Plan capability building investments
   - Assess make vs. buy vs. partner decisions

4. **Portfolio Rebalancing**
   - Apply three horizons model for innovation balance
   - Optimize risk-return profile using efficient frontier
   - Plan new initiatives and sunset decisions

## Integration Strategies

### Atlassian Integration
- **Jira**: Portfolio dashboards, cross-project metrics, risk tracking
- **Confluence**: Strategic documentation, executive reports, knowledge management
- Use MCP integrations to automate data collection and report generation

### Financial Systems Integration
- **Budget Tracking**: Real-time spend data for variance analysis
- **Resource Costing**: Hourly rates and utilization for capacity planning
- **ROI Measurement**: Value realization tracking against projections

### Stakeholder Management
- **Executive Dashboards**: Real-time portfolio health visualization
- **Team Scorecards**: Individual project performance metrics
- **Risk Registers**: Collaborative risk management with automated escalation

## Handoff Protocols

### TO Scrum Master
**Context Transfer:**
- Strategic priorities and success criteria
- Resource allocation and team composition
- Risk factors requiring sprint-level attention
- Quality standards and acceptance criteria

**Ongoing Collaboration:**
- Weekly velocity and health metrics review
- Sprint retrospective insights for portfolio learning
- Impediment escalation and resolution support
- Team capacity and utilization feedback

### TO Product Owner
**Strategic Context:**
- Market prioritization and competitive analysis
- User value frameworks and measurement criteria
- Feature prioritization aligned with portfolio objectives
- Resource and timeline constraints

**Decision Support:**
- ROI analysis for feature investments
- Risk assessment for product decisions
- Market intelligence and customer feedback integration
- Strategic roadmap alignment and dependencies

### FROM Executive Team
**Strategic Direction:**
- Business objective updates and priority changes
- Budget allocation and resource approval decisions
- Risk appetite and tolerance level adjustments
- Market strategy and competitive response decisions

**Performance Expectations:**
- Portfolio health and value delivery targets
- Timeline and milestone commitment expectations
- Quality standards and compliance requirements
- Stakeholder satisfaction and communication standards

## Success Metrics & KPIs

Reference: `references/portfolio-kpis.md` for full definitions and measurement guidance.

### Portfolio Performance
- On-time Delivery Rate: >80% within 10% of planned timeline
- Budget Variance: <5% average across portfolio
- Quality Score: >85 composite rating
- Risk Mitigation Coverage: >90% risks with active plans
- Resource Utilization: 75-85% average

### Strategic Value
- ROI Achievement: >90% projects meeting projections within 12 months
- Strategic Alignment: >95% investment aligned with business priorities
- Innovation Balance: 70% operational / 20% growth / 10% transformational
- Stakeholder Satisfaction: >8.5/10 executive average
- Time-to-Value: <6 months average post-completion

### Risk Management
- Risk Exposure: Maintain within approved appetite ranges
- Resolution Time: <30 days (medium), <7 days (high)
- Mitigation Cost Efficiency: <20% of total portfolio risk EMV
- Risk Prediction Accuracy: >70% probability assessment accuracy

## Continuous Improvement Framework

### Portfolio Learning Integration
- Capture lessons learned from completed projects
- Update risk probability assessments based on historical data
- Refine estimation accuracy through retrospective analysis
- Share best practices across project teams

### Methodology Evolution
- Regular review of prioritization model effectiveness
- Update risk frameworks based on industry best practices
- Integrate new tools and technologies for analysis efficiency
- Benchmark against industry portfolio performance standards

### Stakeholder Feedback Integration
- Quarterly stakeholder satisfaction surveys
- Executive interview feedback on decision support quality
- Team feedback on process efficiency and effectiveness
- Customer impact assessment of portfolio decisions

## Related Skills

- **Product Strategist** (`product-team/product-strategist/`) — Product OKRs align with portfolio objectives
- **Scrum Master** (`project-management/scrum-master/`) — Sprint velocity data feeds project health dashboards
