# Risk Analysis Methods

Systematic techniques for hazard identification and risk analysis in medical device development.

---

## Table of Contents

- [Method Selection Guide](#method-selection-guide)
- [FMEA - Failure Mode and Effects Analysis](#fmea---failure-mode-and-effects-analysis)
- [FTA - Fault Tree Analysis](#fta---fault-tree-analysis)
- [HAZOP - Hazard and Operability Study](#hazop---hazard-and-operability-study)
- [Use Error Analysis](#use-error-analysis)
- [Software Hazard Analysis](#software-hazard-analysis)

---

## Method Selection Guide

### Method Application Matrix

| Method | Best For | Standard | Complexity |
|--------|----------|----------|------------|
| FMEA | Component/process failures | IEC 60812 | Medium |
| FTA | System-level failure analysis | IEC 61025 | High |
| HAZOP | Process deviations | IEC 61882 | Medium |
| PHA | Early hazard screening | - | Low |
| Use FMEA | Use-related hazards | IEC 62366-1 | Medium |
| STPA | Software/system interactions | - | High |

### Selection Decision Tree

```
What is the analysis focus?
        │
        ├── Component failures → FMEA
        │
        ├── System-level failure → FTA
        │
        ├── Process deviations → HAZOP
        │
        ├── User interaction → Use Error Analysis
        │
        └── Software behavior → Software FMEA/STPA
```

### When to Use Each Method

| Project Phase | Recommended Methods |
|---------------|---------------------|
| Concept | PHA, initial FTA |
| Design | FMEA, detailed FTA |
| Development | Use Error Analysis, Software HA |
| Verification | FMEA review, FTA validation |
| Production | Process FMEA |
| Post-Market | Trend analysis, FMEA updates |

---

## FMEA - Failure Mode and Effects Analysis

### FMEA Overview

| Aspect | Description |
|--------|-------------|
| Purpose | Identify potential failure modes and their effects |
| Approach | Bottom-up analysis from component to system |
| Output | Failure mode list with severity, occurrence, detection ratings |
| Standard | IEC 60812 |

### FMEA Process Workflow

1. Define scope and system boundaries
2. Develop functional block diagram
3. Identify failure modes for each component/function
4. Determine effects of each failure mode (local, next level, end)
5. Assign severity rating
6. Identify potential causes
7. Assign occurrence rating
8. Identify current controls (detection)
9. Assign detection rating
10. Calculate Risk Priority Number (RPN) or use risk matrix
11. Determine actions for high-priority items
12. **Validation:** All components analyzed; RPNs calculated; actions assigned for high risks

### FMEA Worksheet Template

```
FMEA WORKSHEET

Product: [Device Name]
Subsystem: [Subsystem]
FMEA Lead: [Name]
Date: [Date]

| ID | Item/Function | Failure Mode | Effect (Local) | Effect (End) | S | Cause | O | Controls | D | RPN | Action |
|----|---------------|--------------|----------------|--------------|---|-------|---|----------|---|-----|--------|
| FM-001 | [Item] | [Mode] | [Local Effect] | [End Effect] | [1-10] | [Cause] | [1-10] | [Detection] | [1-10] | [S×O×D] | [Action] |

S = Severity (1=None, 10=Catastrophic)
O = Occurrence (1=Remote, 10=Frequent)
D = Detection (1=Certain, 10=Cannot Detect)
RPN = Risk Priority Number
```

### Severity Rating Scale

| Rating | Severity | Criteria |
|--------|----------|----------|
| 10 | Hazardous | Death or regulatory non-compliance |
| 9 | Serious | Serious injury, major function loss |
| 8 | Major | Significant injury, major inconvenience |
| 7 | High | Minor injury, significant inconvenience |
| 6 | Moderate | Discomfort, partial function loss |
| 5 | Low | Some performance loss |
| 4 | Very Low | Minor performance degradation |
| 3 | Minor | Noticeable effect, no function loss |
| 2 | Very Minor | Negligible effect |
| 1 | None | No effect |

### Occurrence Rating Scale

| Rating | Occurrence | Probability |
|--------|------------|-------------|
| 10 | Almost Certain | >1 in 2 |
| 9 | Very High | 1 in 3 |
| 8 | High | 1 in 8 |
| 7 | Moderately High | 1 in 20 |
| 6 | Moderate | 1 in 80 |
| 5 | Low | 1 in 400 |
| 4 | Very Low | 1 in 2,000 |
| 3 | Remote | 1 in 15,000 |
| 2 | Very Remote | 1 in 150,000 |
| 1 | Nearly Impossible | <1 in 1,500,000 |

### Detection Rating Scale

| Rating | Detection | Likelihood of Detection |
|--------|-----------|------------------------|
| 10 | Absolute Uncertainty | Cannot detect |
| 9 | Very Remote | Very remote chance |
| 8 | Remote | Remote chance |
| 7 | Very Low | Very low chance |
| 6 | Low | Low chance |
| 5 | Moderate | Moderate chance |
| 4 | Moderately High | Moderately high chance |
| 3 | High | High chance |
| 2 | Very High | Very high chance |
| 1 | Almost Certain | Will detect |

### RPN Action Thresholds

| RPN Range | Priority | Action |
|-----------|----------|--------|
| >200 | Critical | Immediate action required |
| 100-200 | High | Action plan required |
| 50-100 | Medium | Consider action |
| <50 | Low | Monitor |

---

## FTA - Fault Tree Analysis

### FTA Overview

| Aspect | Description |
|--------|-------------|
| Purpose | Determine combinations of events leading to top event |
| Approach | Top-down deductive analysis |
| Output | Fault tree diagram with cut sets |
| Standard | IEC 61025 |

### FTA Process Workflow

1. Define top event (undesired system state)
2. Identify immediate causes using logic gates
3. Continue decomposition to basic events
4. Draw fault tree diagram
5. Identify cut sets (combinations causing top event)
6. Calculate probability if quantitative analysis required
7. Identify single points of failure
8. **Validation:** All branches complete; cut sets identified; single points documented

### Fault Tree Symbols

| Symbol | Name | Meaning |
|--------|------|---------|
| Rectangle | Intermediate Event | Event resulting from other events |
| Circle | Basic Event | Primary event, no further development |
| Diamond | Undeveloped Event | Not analyzed further |
| House | House Event | Event expected to occur (condition) |
| AND Gate | AND | All inputs required for output |
| OR Gate | OR | Any input causes output |

### FTA Worksheet Template

```
FAULT TREE ANALYSIS

Top Event: [Description of undesired state]
System: [System name]
Analyst: [Name]
Date: [Date]

BASIC EVENTS:
| ID | Event | Description | Probability | Control |
|----|-------|-------------|-------------|---------|
| BE-001 | [Event] | [Description] | [P] | [Control] |

CUT SETS:
| Cut Set | Events | Order | Probability |
|---------|--------|-------|-------------|
| CS-001 | BE-001 | 1 | [P] |
| CS-002 | BE-001, BE-002 | 2 | [P] |

SINGLE POINTS OF FAILURE:
| Event | Risk | Mitigation |
|-------|------|------------|
| [Event] | [Risk assessment] | [Mitigation strategy] |
```

### Cut Set Analysis

| Cut Set Order | Meaning | Criticality |
|---------------|---------|-------------|
| First Order | Single event causes top event | Highest - single point of failure |
| Second Order | Two events required | High |
| Third Order | Three events required | Moderate |
| Higher Order | Four+ events required | Lower |

---

## HAZOP - Hazard and Operability Study

### HAZOP Overview

| Aspect | Description |
|--------|-------------|
| Purpose | Identify deviations from intended operation |
| Approach | Systematic examination using guide words |
| Output | Deviation analysis with consequences and safeguards |
| Standard | IEC 61882 |

### HAZOP Guide Words

| Guide Word | Meaning | Example Application |
|------------|---------|---------------------|
| NO/NOT | Complete negation | No flow, no signal |
| MORE | Quantitative increase | More pressure, more current |
| LESS | Quantitative decrease | Less flow, less voltage |
| AS WELL AS | Qualitative increase | Extra component, contamination |
| PART OF | Qualitative decrease | Missing component |
| REVERSE | Logical opposite | Reverse flow, reverse polarity |
| OTHER THAN | Complete substitution | Wrong material, wrong signal |
| EARLY | Time-related | Early activation |
| LATE | Time-related | Delayed response |

### HAZOP Process Workflow

1. Select study node (process section or component)
2. Describe design intent for the node
3. Apply guide words to identify deviations
4. Determine causes of each deviation
5. Assess consequences
6. Identify existing safeguards
7. Recommend actions if needed
8. **Validation:** All nodes analyzed; all guide words applied; actions assigned

### HAZOP Worksheet Template

```
HAZOP WORKSHEET

System: [System Name]
Node: [Node Description]
Design Intent: [What the node is supposed to do]
Team Lead: [Name]
Date: [Date]

| Guide Word | Deviation | Causes | Consequences | Safeguards | Actions |
|------------|-----------|--------|--------------|------------|---------|
| NO | [No + parameter] | [Causes] | [Consequences] | [Existing] | [Recommendations] |
| MORE | [More + parameter] | [Causes] | [Consequences] | [Existing] | [Recommendations] |
| LESS | [Less + parameter] | [Causes] | [Consequences] | [Existing] | [Recommendations] |
```

---

## Use Error Analysis

### Use Error Analysis Overview

| Aspect | Description |
|--------|-------------|
| Purpose | Identify use-related hazards and mitigations |
| Approach | Task analysis combined with error prediction |
| Output | Use error list with risk controls |
| Standard | IEC 62366-1 |

### Use Error Categories

| Category | Description | Examples |
|----------|-------------|----------|
| Perception Error | Failure to perceive information | Missing alarm, unclear display |
| Cognition Error | Failure to understand | Misinterpretation, wrong decision |
| Action Error | Incorrect physical action | Wrong button, slip, lapse |
| Memory Error | Failure to recall | Forgotten step, omission |

### Use Error Analysis Process

1. Identify user tasks and subtasks
2. Identify potential use errors for each task
3. Determine consequences of each use error
4. Estimate probability of use error
5. Identify design features contributing to error
6. Define risk control measures
7. Verify control effectiveness
8. **Validation:** All critical tasks analyzed; errors identified; controls defined

### Use Error Worksheet Template

```
USE ERROR ANALYSIS

Device: [Device Name]
Task: [Task Description]
User: [User Profile]
Analyst: [Name]
Date: [Date]

| Step | User Action | Potential Use Error | Error Type | Cause | Consequence | S | P | Risk | Control |
|------|-------------|--------------------| -----------|-------|-------------|---|---|------|---------|
| 1 | [Action] | [Error] | [Type] | [Cause] | [Harm] | [S] | [P] | [Level] | [Control] |

Error Types: Perception (P), Cognition (C), Action (A), Memory (M)
```

### Human Factors Risk Controls

| Control Type | Examples |
|--------------|----------|
| Design | Forcing functions, constraints, affordances |
| Feedback | Visual, auditory, tactile confirmation |
| Labeling | Clear instructions, warnings, symbols |
| Training | User education, competency verification |
| Environment | Adequate lighting, noise reduction |

---

## Software Hazard Analysis

### Software Hazard Analysis Overview

| Aspect | Description |
|--------|-------------|
| Purpose | Identify software contribution to hazards |
| Approach | Analysis of software failure modes and behaviors |
| Output | Software hazard list with safety requirements |
| Standard | IEC 62304 |

### Software Safety Classification

| Class | Contribution to Hazard | Rigor Required |
|-------|------------------------|----------------|
| A | No contribution possible | Basic |
| B | Non-serious injury possible | Moderate |
| C | Death or serious injury possible | High |

### Software Hazard Categories

| Category | Description | Examples |
|----------|-------------|----------|
| Omission | Required function not performed | Missing safety check |
| Commission | Incorrect function performed | Wrong calculation |
| Timing | Function at wrong time | Delayed alarm |
| Value | Function with wrong value | Incorrect dose |
| Sequence | Functions in wrong order | Steps reversed |

### Software FMEA Worksheet

```
SOFTWARE FMEA

Software Item: [Module/Function Name]
Safety Class: [A/B/C]
Analyst: [Name]
Date: [Date]

| ID | Function | Failure Mode | Cause | Effect on System | Effect on Patient | S | P | Risk | Mitigation |
|----|----------|--------------|-------|------------------|-------------------|---|---|------|------------|
| SW-001 | [Function] | [Mode] | [Cause] | [System effect] | [Patient effect] | [S] | [P] | [Level] | [Control] |

Failure Mode Types: Omission, Commission, Timing, Value, Sequence
```

### Software Risk Controls

| Control Type | Implementation |
|--------------|----------------|
| Defensive Programming | Input validation, range checking |
| Error Handling | Exception handling, graceful degradation |
| Redundancy | Dual channels, voting logic |
| Watchdog | Timeout monitoring, heartbeat |
| Self-Test | Power-on diagnostics, runtime checks |
| Separation | Independence of safety functions |

### Traceability Requirements

| From | To | Purpose |
|------|------|---------|
| Software Hazard | Software Requirement | Hazard addressed |
| Software Requirement | Architecture | Requirement implemented |
| Architecture | Code | Design realized |
| Code | Test | Verification coverage |
| Test | Hazard | Control verified |
