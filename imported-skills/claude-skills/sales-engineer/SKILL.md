---
name: "sales-engineer"
description: Analyzes RFP/RFI responses for coverage gaps, builds competitive feature comparison matrices, and plans proof-of-concept (POC) engagements for pre-sales engineering. Use when responding to RFPs, bids, or proposal requests; comparing product features against competitors; planning or scoring a customer POC or sales demo; preparing a technical proposal; or performing win/loss competitor analysis. Handles tasks described as 'RFP response', 'bid response', 'proposal response', 'competitor comparison', 'feature matrix', 'POC planning', 'sales demo prep', or 'pre-sales engineering'.
---

# Sales Engineer Skill

## 5-Phase Workflow

### Phase 1: Discovery & Research

**Objective:** Understand customer requirements, technical environment, and business drivers.

**Checklist:**
- [ ] Conduct technical discovery calls with stakeholders
- [ ] Map customer's current architecture and pain points
- [ ] Identify integration requirements and constraints
- [ ] Document security and compliance requirements
- [ ] Assess competitive landscape for this opportunity

**Tools:** Run `rfp_response_analyzer.py` to score initial requirement alignment.

```bash
python scripts/rfp_response_analyzer.py assets/sample_rfp_data.json --format json > phase1_rfp_results.json
```

**Output:** Technical discovery document, requirement map, initial coverage assessment.

**Validation checkpoint:** Coverage score must be >50% and must-have gaps ≤3 before proceeding to Phase 2. Check with:
```bash
python scripts/rfp_response_analyzer.py assets/sample_rfp_data.json --format json | python -c "import sys,json; r=json.load(sys.stdin); print('PROCEED' if r['coverage_score']>50 and r['must_have_gaps']<=3 else 'REVIEW')"
```

---

### Phase 2: Solution Design

**Objective:** Design a solution architecture that addresses customer requirements.

**Checklist:**
- [ ] Map product capabilities to customer requirements
- [ ] Design integration architecture
- [ ] Identify customization needs and development effort
- [ ] Build competitive differentiation strategy
- [ ] Create solution architecture diagrams

**Tools:** Run `competitive_matrix_builder.py` using Phase 1 data to identify differentiators and vulnerabilities.

```bash
python scripts/competitive_matrix_builder.py competitive_data.json --format json > phase2_competitive.json

python -c "import json; d=json.load(open('phase2_competitive.json')); print('Differentiators:', d['differentiators']); print('Vulnerabilities:', d['vulnerabilities'])"
```

**Output:** Solution architecture, competitive positioning, technical differentiation strategy.

**Validation checkpoint:** Confirm at least one strong differentiator exists per customer priority before proceeding to Phase 3. If no differentiators found, escalate to Product Team (see Integration Points).

---

### Phase 3: Demo Preparation & Delivery

**Objective:** Deliver compelling technical demonstrations tailored to stakeholder priorities.

**Checklist:**
- [ ] Build demo environment matching customer's use case
- [ ] Create demo script with talking points per stakeholder role
- [ ] Prepare objection handling responses
- [ ] Rehearse failure scenarios and recovery paths
- [ ] Collect feedback and adjust approach

**Templates:** Use `assets/demo_script_template.md` for structured demo preparation.

**Output:** Customized demo, stakeholder-specific talking points, feedback capture.

**Validation checkpoint:** Demo script must cover every must-have requirement flagged in `phase1_rfp_results.json` before delivery. Cross-reference with:
```bash
python -c "import json; rfp=json.load(open('phase1_rfp_results.json')); [print('UNCOVERED:', r) for r in rfp['must_have_requirements'] if r['coverage']=='Gap']"
```

---

### Phase 4: POC & Evaluation

**Objective:** Execute a structured proof-of-concept that validates the solution.

**Checklist:**
- [ ] Define POC scope, success criteria, and timeline
- [ ] Allocate resources and set up environment
- [ ] Execute phased testing (core, advanced, edge cases)
- [ ] Track progress against success criteria
- [ ] Generate evaluation scorecard

**Tools:** Run `poc_planner.py` to generate the complete POC plan.

```bash
python scripts/poc_planner.py poc_data.json --format json > phase4_poc_plan.json

python -c "import json; p=json.load(open('phase4_poc_plan.json')); print('Go/No-Go:', p['recommendation'])"
```

**Templates:** Use `assets/poc_scorecard_template.md` for evaluation tracking.

**Output:** POC plan, evaluation scorecard, go/no-go recommendation.

**Validation checkpoint:** POC conversion requires scorecard score >60% across all evaluation dimensions (functionality, performance, integration, usability, support). If score <60%, document gaps and loop back to Phase 2 for solution redesign.

---

### Phase 5: Proposal & Closing

**Objective:** Deliver a technical proposal that supports the commercial close.

**Checklist:**
- [ ] Compile POC results and success metrics
- [ ] Create technical proposal with implementation plan
- [ ] Address outstanding objections with evidence
- [ ] Support pricing and packaging discussions
- [ ] Conduct win/loss analysis post-decision

**Templates:** Use `assets/technical_proposal_template.md` for the proposal document.

**Output:** Technical proposal, implementation timeline, risk mitigation plan.

---

## Python Automation Tools

### 1. RFP Response Analyzer

**Script:** `scripts/rfp_response_analyzer.py`

**Purpose:** Parse RFP/RFI requirements, score coverage, identify gaps, and generate bid/no-bid recommendations.

**Coverage Categories:** Full (100%), Partial (50%), Planned (25%), Gap (0%).  
**Priority Weighting:** Must-Have 3×, Should-Have 2×, Nice-to-Have 1×.

**Bid/No-Bid Logic:**
- **Bid:** Coverage >70% AND must-have gaps ≤3
- **Conditional Bid:** Coverage 50–70% OR must-have gaps 2–3
- **No-Bid:** Coverage <50% OR must-have gaps >3

**Usage:**
```bash
python scripts/rfp_response_analyzer.py assets/sample_rfp_data.json            # human-readable
python scripts/rfp_response_analyzer.py assets/sample_rfp_data.json --format json  # JSON output
python scripts/rfp_response_analyzer.py --help
```

**Input Format:** See `assets/sample_rfp_data.json` for the complete schema.

---

### 2. Competitive Matrix Builder

**Script:** `scripts/competitive_matrix_builder.py`

**Purpose:** Generate feature comparison matrices, calculate competitive scores, identify differentiators and vulnerabilities.

**Feature Scoring:** Full (3), Partial (2), Limited (1), None (0).

**Usage:**
```bash
python scripts/competitive_matrix_builder.py competitive_data.json              # human-readable
python scripts/competitive_matrix_builder.py competitive_data.json --format json  # JSON output
```

**Output Includes:** Feature comparison matrix, weighted competitive scores, differentiators, vulnerabilities, and win themes.

---

### 3. POC Planner

**Script:** `scripts/poc_planner.py`

**Purpose:** Generate structured POC plans with timeline, resource allocation, success criteria, and evaluation scorecards.

**Default Phase Breakdown:**
- **Week 1:** Setup — environment provisioning, data migration, configuration
- **Weeks 2–3:** Core Testing — primary use cases, integration testing
- **Week 4:** Advanced Testing — edge cases, performance, security
- **Week 5:** Evaluation — scorecard completion, stakeholder review, go/no-go

**Usage:**
```bash
python scripts/poc_planner.py poc_data.json              # human-readable
python scripts/poc_planner.py poc_data.json --format json  # JSON output
```

**Output Includes:** Phased POC plan, resource allocation, success criteria, evaluation scorecard, risk register, and go/no-go recommendation framework.

---

## Reference Knowledge Bases

| Reference | Description |
|-----------|-------------|
| `references/rfp-response-guide.md` | RFP/RFI response best practices, compliance matrix, bid/no-bid framework |
| `references/competitive-positioning-framework.md` | Competitive analysis methodology, battlecard creation, objection handling |
| `references/poc-best-practices.md` | POC planning methodology, success criteria, evaluation frameworks |

## Asset Templates

| Template | Purpose |
|----------|---------|
| `assets/technical_proposal_template.md` | Technical proposal with executive summary, solution architecture, implementation plan |
| `assets/demo_script_template.md` | Demo script with agenda, talking points, objection handling |
| `assets/poc_scorecard_template.md` | POC evaluation scorecard with weighted scoring |
| `assets/sample_rfp_data.json` | Sample RFP data for testing the analyzer |
| `assets/expected_output.json` | Expected output from rfp_response_analyzer.py |

## Integration Points

- **Marketing Skills** - Leverage competitive intelligence and messaging frameworks from `marketing-skill/`
- **Product Team** - Coordinate on roadmap items flagged as "Planned" in RFP analysis from `product-team/`
- **C-Level Advisory** - Escalate strategic deals requiring executive engagement from `c-level-advisor/`
- **Customer Success** - Hand off POC results and success criteria to CSM from `../customer-success-manager/`

---

**Last Updated:** February 2026
**Status:** Production-ready
**Tools:** 3 Python automation scripts
**References:** 3 knowledge base documents
**Templates:** 5 asset files
