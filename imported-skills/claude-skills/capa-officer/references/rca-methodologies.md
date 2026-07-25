# Root Cause Analysis Methodologies

Decision criteria, templates, and implementation guidance for RCA techniques.

---

## Table of Contents

- [Method Selection Matrix](#method-selection-matrix)
- [5 Why Analysis](#5-why-analysis)
- [Fishbone Diagram](#fishbone-diagram)
- [Fault Tree Analysis](#fault-tree-analysis)
- [Human Factors Analysis](#human-factors-analysis)
- [Failure Mode and Effects Analysis](#failure-mode-and-effects-analysis)
- [Selecting the Right Method](#selecting-the-right-method)

---

## Method Selection Matrix

### When to Use Each Method

| Method | Use When | Problem Type | Team Size | Time Required |
|--------|----------|--------------|-----------|---------------|
| 5 Why | Single-cause issues, process deviations | Linear causation | 1-3 people | 30-60 min |
| Fishbone | Multi-factor problems, 3-6 contributing factors | Complex, systemic | 3-8 people | 2-4 hours |
| Fault Tree | Safety-critical failures, reliability issues | System failures | 2-5 people | 4-8 hours |
| Human Factors | Procedure/training-related issues | Human error | 3-6 people | 2-4 hours |
| FMEA | Systematic risk assessment, design review | Potential failures | 4-10 people | 8-16 hours |

### Quick Selection Decision Tree

```
Is the issue safety-critical or involves system reliability?
├── Yes → Use FAULT TREE ANALYSIS
└── No → Is human error the suspected primary cause?
    ├── Yes → Use HUMAN FACTORS ANALYSIS
    └── No → How many potential contributing factors?
        ├── 1-2 factors → Use 5 WHY ANALYSIS
        ├── 3-6 factors → Use FISHBONE DIAGRAM
        └── Unknown/Many → Use FMEA (proactive) or Fishbone (reactive)
```

---

## 5 Why Analysis

### Overview

Simple, iterative technique asking "why" repeatedly (typically 5 times) to drill from symptoms to root cause.

### When to Use

- Single-cause issues with linear causation
- Process deviations with clear failure point
- Quick investigations requiring rapid resolution
- Problems where symptoms clearly link to cause

### When NOT to Use

- Complex multi-factor problems
- Safety-critical incidents requiring comprehensive analysis
- Issues with multiple interacting causes
- When systemic factors are suspected

### 5 Why Template

```
PROBLEM STATEMENT:
[Clear, specific description of what happened, when, where, and impact]

WHY 1: Why did [problem] occur?
BECAUSE: [First-level cause]
EVIDENCE: [Data/observation supporting this cause]

WHY 2: Why did [first-level cause] occur?
BECAUSE: [Second-level cause]
EVIDENCE: [Data/observation supporting this cause]

WHY 3: Why did [second-level cause] occur?
BECAUSE: [Third-level cause]
EVIDENCE: [Data/observation supporting this cause]

WHY 4: Why did [third-level cause] occur?
BECAUSE: [Fourth-level cause]
EVIDENCE: [Data/observation supporting this cause]

WHY 5: Why did [fourth-level cause] occur?
BECAUSE: [Root cause - typically systemic or management system failure]
EVIDENCE: [Data/observation supporting this cause]

ROOT CAUSE VALIDATION:
- [ ] Can the root cause be verified with evidence?
- [ ] If root cause is eliminated, would problem recur?
- [ ] Is the root cause within organizational control?
- [ ] Does the root cause explain all symptoms?
```

### Example: Calibration Overdue

```
PROBLEM: pH meter (EQ-042) found 2 months overdue for calibration

WHY 1: Why was calibration overdue?
BECAUSE: The equipment was not on the calibration schedule
EVIDENCE: Calibration schedule reviewed, EQ-042 not listed

WHY 2: Why was it not on the calibration schedule?
BECAUSE: The schedule was not updated when equipment was purchased
EVIDENCE: Purchase date 2023-06-15, schedule dated 2023-01-01

WHY 3: Why was the schedule not updated?
BECAUSE: No process requires schedule update at equipment purchase
EVIDENCE: Equipment procedure SOP-EQ-001 reviewed, no such requirement

WHY 4: Why is there no requirement to update the schedule?
BECAUSE: The procedure was written before equipment tracking was centralized
EVIDENCE: SOP-EQ-001 last revised 2019, equipment system implemented 2021

WHY 5: Why has the procedure not been updated?
BECAUSE: Periodic procedure review did not assess compatibility with new systems
EVIDENCE: No documented review of SOP-EQ-001 against new equipment system

ROOT CAUSE: Procedure review process does not assess compatibility
with organizational systems implemented after original procedure creation
```

---

## Fishbone Diagram

### Overview

Also called Ishikawa or cause-and-effect diagram. Organizes potential causes into categories branching from the problem statement.

### Standard Categories (6M)

| Category | Focus Areas | Typical Causes |
|----------|-------------|----------------|
| **Man** (People) | Training, competency, workload | Skill gaps, fatigue, communication |
| **Machine** (Equipment) | Calibration, maintenance, age | Wear, malfunction, inadequate capacity |
| **Method** (Process) | Procedures, work instructions | Unclear steps, missing controls |
| **Material** | Specifications, suppliers, storage | Out-of-spec, degradation, contamination |
| **Measurement** | Calibration, methods, interpretation | Instrument error, wrong method |
| **Mother Nature** (Environment) | Temperature, humidity, cleanliness | Environmental excursions |

### Fishbone Template

```
PROBLEM STATEMENT: [Effect being investigated]

                    ┌── Man ────────────────┐
                    │  ├─ [Cause 1]         │
                    │  ├─ [Cause 2]         │
                    │  └─ [Cause 3]         │
                    │                       │
┌── Machine ────────┤                       ├── Method ──────────┐
│  ├─ [Cause 1]     │                       │  ├─ [Cause 1]      │
│  ├─ [Cause 2]     │     PROBLEM           │  ├─ [Cause 2]      │
│  └─ [Cause 3]     ├───────────────────────┤  └─ [Cause 3]      │
│                   │                       │                    │
├── Material ───────┤                       ├── Measurement ─────┤
│  ├─ [Cause 1]     │                       │  ├─ [Cause 1]      │
│  ├─ [Cause 2]     │                       │  ├─ [Cause 2]      │
│  └─ [Cause 3]     │                       │  └─ [Cause 3]      │
                    │                       │
                    └── Environment ────────┘
                       ├─ [Cause 1]
                       ├─ [Cause 2]
                       └─ [Cause 3]

CAUSE PRIORITIZATION:
| Cause | Category | Likelihood | Evidence | Priority |
|-------|----------|------------|----------|----------|
| [Cause A] | Method | High | [Evidence] | 1 |
| [Cause B] | Man | Medium | [Evidence] | 2 |

ROOT CAUSES IDENTIFIED:
1. [Primary root cause with supporting evidence]
2. [Contributing cause with supporting evidence]
```

### Facilitation Guidelines

1. Assemble cross-functional team (3-8 people)
2. Define problem statement clearly before starting
3. Brainstorm causes without judgment first
4. Organize into categories after brainstorming
5. Drill down on each major cause (sub-causes)
6. Prioritize based on evidence and likelihood
7. Validate top causes with data

---

## Fault Tree Analysis

### Overview

Top-down, deductive analysis starting with undesired event and systematically identifying all potential causes using Boolean logic (AND/OR gates).

### When to Use

- Safety-critical system failures
- Complex system reliability analysis
- Events with multiple failure pathways
- Regulatory-required investigations (FDA, MDR)

### FTA Symbols

| Symbol | Name | Meaning |
|--------|------|---------|
| Rectangle | Top Event / Intermediate Event | Undesired event or intermediate fault |
| Circle | Basic Event | Primary fault requiring no further analysis |
| Diamond | Undeveloped Event | Event not fully analyzed (data limitation) |
| AND Gate | Requires all inputs | All child events must occur for parent |
| OR Gate | Requires any input | Any child event causes parent |

### FTA Template

```
TOP EVENT: [Undesired event under investigation]

LEVEL 1 (Immediate Causes):
[Top Event]
    │
    └── OR GATE ──┬── [Cause 1.1]
                  ├── [Cause 1.2]
                  └── [Cause 1.3]

LEVEL 2 (Contributing Causes):
[Cause 1.1]
    │
    └── AND GATE ──┬── [Cause 2.1]
                   └── [Cause 2.2]

MINIMAL CUT SETS:
(Combinations of basic events that cause top event)
1. {Basic Event A, Basic Event B}  ← Both required (AND)
2. {Basic Event C}  ← Single point failure (OR)
3. {Basic Event D, Basic Event E}  ← Both required (AND)

CRITICAL PATH ANALYSIS:
Most likely failure pathway: [Description]
Single points of failure: [List]

RECOMMENDATIONS:
- Address single points of failure first
- Add redundancy where AND gates show vulnerability
- Prioritize controls on highest probability paths
```

### Cut Set Analysis

Minimal cut sets identify the smallest combination of basic events causing the top event:

- **Single-element cut sets**: Single points of failure (highest priority)
- **Two-element cut sets**: Dual failure scenarios
- **Probability calculation**: P(Top Event) = Union of P(Cut Sets)

---

## Human Factors Analysis

### Overview

Systematic analysis of human error focusing on cognitive, physical, and organizational factors contributing to performance failures.

### HFACS Categories

Human Factors Analysis and Classification System:

| Level | Category | Examples |
|-------|----------|----------|
| **Unsafe Acts** | Errors, violations | Skill-based, decision, perceptual errors |
| **Preconditions** | Conditions for unsafe acts | Fatigue, mental state, CRM, physical environment |
| **Unsafe Supervision** | Supervisory failures | Inadequate supervision, planned inappropriate ops |
| **Organizational Influences** | Organizational failures | Resource management, organizational climate |

### Human Error Types

| Type | Description | Example | Mitigation |
|------|-------------|---------|------------|
| Slip | Execution error in routine task | Wrong button pressed | Error-proofing, forcing functions |
| Lapse | Memory failure | Forgot step in procedure | Checklists, reminders |
| Mistake | Planning/decision error | Wrong procedure selected | Training, decision aids |
| Violation | Intentional deviation | Skipped step to save time | Culture change, supervision |

### Human Factors Investigation Template

```
INCIDENT DESCRIPTION:
[What happened, who was involved, when, where]

UNSAFE ACTS ANALYSIS:
Type of Error: [ ] Slip  [ ] Lapse  [ ] Mistake  [ ] Violation
Description: [Specific action or inaction]
Task Being Performed: [Activity at time of error]
Experience Level: [Novice/Intermediate/Expert]

PRECONDITIONS FOR UNSAFE ACTS:
Cognitive Factors:
- [ ] Task complexity exceeded capability
- [ ] Time pressure
- [ ] Distraction/interruption
- [ ] Mental fatigue

Physical Factors:
- [ ] Physical fatigue
- [ ] Inadequate lighting
- [ ] Noise interference
- [ ] Workspace ergonomics

Team Factors:
- [ ] Communication breakdown
- [ ] Coordination failure
- [ ] Inadequate leadership

SUPERVISORY FACTORS:
- [ ] Inadequate supervision
- [ ] Failed to correct known problem
- [ ] Inappropriate staffing
- [ ] Authorized unnecessary risk

ORGANIZATIONAL FACTORS:
- [ ] Resource management deficiency
- [ ] Organizational process issue
- [ ] Organizational culture/climate

ROOT CAUSE(S):
[Human factors root causes identified]

CORRECTIVE ACTIONS:
| Action | Target Factor | Priority |
|--------|---------------|----------|
| [Action 1] | [Factor addressed] | High |
| [Action 2] | [Factor addressed] | Medium |
```

---

## Failure Mode and Effects Analysis

### Overview

Proactive, systematic technique identifying potential failure modes, their causes, and effects before failures occur.

### FMEA Types

| Type | Application | Scope |
|------|-------------|-------|
| Design FMEA (DFMEA) | Product design | Component and system design failures |
| Process FMEA (PFMEA) | Manufacturing process | Process step failures |
| System FMEA | System-level analysis | System interaction failures |

### Risk Priority Number (RPN)

RPN = Severity (S) × Occurrence (O) × Detection (D)

**Severity Scale (1-10):**

| Rating | Effect | Criteria |
|--------|--------|----------|
| 10 | Hazardous | Failure affects safe operation, no warning |
| 8-9 | Very High | Primary function lost, high impact |
| 6-7 | High | Performance degraded, customer dissatisfied |
| 4-5 | Moderate | Some performance loss, moderate impact |
| 2-3 | Low | Minor effect, slight inconvenience |
| 1 | None | No discernible effect |

**Occurrence Scale (1-10):**

| Rating | Likelihood | Failure Rate |
|--------|------------|--------------|
| 10 | Very High | >1 in 10 |
| 7-9 | High | 1 in 20 - 1 in 100 |
| 4-6 | Moderate | 1 in 400 - 1 in 2,000 |
| 2-3 | Low | 1 in 15,000 - 1 in 150,000 |
| 1 | Remote | <1 in 1,500,000 |

**Detection Scale (1-10):**

| Rating | Detection | Criteria |
|--------|-----------|----------|
| 10 | Absolute Uncertainty | No inspection/control, defect will reach customer |
| 7-9 | Very Remote to Remote | Controls unlikely to detect |
| 4-6 | Moderate | Controls may detect |
| 2-3 | High | Controls likely to detect |
| 1 | Almost Certain | Controls will almost certainly detect |

### FMEA Template

```
PROCESS/PRODUCT: [Name]
FMEA TEAM: [Members]
DATE: [Date]

| Item/Step | Failure Mode | Effect | S | Cause | O | Controls | D | RPN | Action |
|-----------|--------------|--------|---|-------|---|----------|---|-----|--------|
| [Item 1] | [How it fails] | [Impact] | 8 | [Why] | 4 | [Current] | 6 | 192 | [Action] |
| [Item 2] | [How it fails] | [Impact] | 6 | [Why] | 3 | [Current] | 4 | 72 | [Action] |

RPN THRESHOLD: Actions required for RPN > [threshold]
HIGH SEVERITY RULE: Actions required for S >= 9 regardless of RPN

ACTION PRIORITIZATION:
1. Address all items with S >= 9 first
2. Address items with highest RPN
3. Focus on reducing Occurrence (prevention)
4. Then improve Detection (inspection)
```

---

## Selecting the Right Method

### Decision Flowchart

```
START: Investigation Required
    │
    ├── Is this a proactive assessment (no failure yet)?
    │   └── Yes → Use FMEA
    │
    ├── Is the issue safety-critical?
    │   └── Yes → Use FAULT TREE ANALYSIS
    │
    ├── Is human error the primary concern?
    │   └── Yes → Use HUMAN FACTORS ANALYSIS
    │
    ├── Are there multiple contributing factors (3+)?
    │   ├── Yes → Use FISHBONE DIAGRAM
    │   └── No → Use 5 WHY ANALYSIS
    │
    └── Uncertain? → Start with 5 WHY, escalate to FISHBONE if needed
```

### Hybrid Approach

For complex investigations, combine methods:

1. **Initial screening**: 5 Why for quick cause identification
2. **Detailed analysis**: Fishbone to explore all categories
3. **Validation**: Fault Tree for critical failure paths
4. **Systemic factors**: Human Factors for people-related causes
5. **Prevention**: FMEA for future risk mitigation

### Documentation Requirements

| Method | Required Outputs | Retention |
|--------|------------------|-----------|
| 5 Why | Completed template with evidence | CAPA record |
| Fishbone | Diagram + prioritized causes | CAPA record |
| Fault Tree | FTA diagram + cut set analysis | DHF/CAPA record |
| Human Factors | HFACS analysis + actions | CAPA record |
| FMEA | FMEA worksheet + action tracking | Design file |
