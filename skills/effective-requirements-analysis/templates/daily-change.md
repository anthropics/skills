# <系统名> Change / Optimization Requirements Analysis Sheet

> Applies to change and optimization requirements on systems already in production / products already released.
> Processing flow: **Reconstruct the requirement → Supplement the requirement → Assess the requirement**.

---

## 1. Original Requirement

| Field | Content | Required |
|---|---|---|
| Requester | | ✅ |
| Department | | |
| Original Description (verbatim) | | ✅ |
| ID | | |

## 2. Problem Clarification

| Field | Content | Required |
|---|---|---|
| Problem to Be Solved | Problem-level requirement: **whose** **what problem** | ✅ |
| Current State | How the problem is handled today (workaround) | |
| Concept Clarification | Definitions in the problem description that need clarification | |
| Mining Similar Problem Scenarios | Results of laterally extrapolating to problems of the same kind | |

**Core elements for reconstructing the requirement: Who (whose requirement), Why (what problem to solve), How (a solution with an appropriate cost).**

A way to think about clarifying the problem: answer in the **past tense** which "what problem" of "whom" this requirement is meant to solve.

**Three mandatory questions**:

1. Are the person raising the requirement and the person using it the same? If not, collect the real feedback from the users
2. Are potential affected parties involved? If a process is involved, managers are affected; if data is involved, upstream/downstream collectors and users are; if rules are involved, risk control and audit are
3. Does this requirement represent the voice of mainstream users? Expert users often propose complex solutions, so you need to find the silent mainstream users to validate

### 2.1 Solution Overview

What solution options exist for this problem, what the pros and cons of each are, which one is recommended, and why. (**Required**)

State the benefits of the solution from the user's point of view — the requirements analyst is a "problem solver", not a "requirement relayer".

## 3. Business Environment Description

| Field | Content | Required |
|---|---|---|
| Who Gets Angry If Not Done | Who is directly affected if it is not implemented | Recommended |
| How Often They Get Angry | How frequently the impact occurs | Recommended |
| Other Non-functional Requirements | Which factors exist that impact non-functional requirements | |

## 4. Business Scenario Description

| Field | Content |
|---|---|
| Scenario Name | In which business scenario this requirement occurs |
| Scenario Description | Recommended to organize in the form of "sub-task + task variant" |

## 5. Business Term Explanation

| Term | Meaning | Composition |
|---|---|---|

---

## 6. Supplementary Requirements

**Only mine problems, never solutions.** Customers are rational when discussing the problem level, but emotional when discussing the solution level.

### 6.1 Lateral Extrapolation of Similar Problems (increase breadth)

Extract the **problem type** from the Why of the requirement, then ask: "Besides the XX problem, have you also encountered other problems of type XX?"

| No. | Similar Problems Mined | Frequency of Occurrence | Consequences of Not Solving |
|---|---|---|---|

### 6.2 Vertical Extrapolation of Related Behaviors (increase depth)

Integrate Who + Why into one business scenario, and list the before / during / after work steps of that scenario.

Core question: **"Do we need to support the related behaviors before, during and after?"**

| No. | Related Behavior | Type (before / during / after) | Support Needed |
|---|---|---|---|

### 6.3 360-Degree Analysis (increase comprehensiveness)

Applies to requirements that occur in key business activities.

1. Identify potential affected parties: upstream steps of the process, downstream steps, the manager of the process, collaborators
2. Analyze the requirements of the affected parties: go through them one by one from their own perspective and identify the problems they care about and the derived requirements

| Affected Party | Problems of Concern | Derived Requirements |
|---|---|---|

## 7. Requirement Assessment

### 7.1 Choose the Assessment Dimensions

Select the **primary assessment dimension** according to the product/system stage:

| Stage | Primary Dimension |
|---|---|
| 0→1 Construction Stage | Business dimension (value-frequency two-dimensional evaluation method) |
| 1→10 Growth Stage | User dimension, competitive dimension |
| 10→100 Maturity Stage | Operations dimension (North Star metric, RFM model) |

Or combine them: for each iteration, complete Business dimension Top 3 + Competitive dimension Top 3 + Operations dimension Top 1.

**Do not assess the four dimensions separately and then take a weighted average** — many requirements score low on one dimension and high on others, and averaging buries them.

### 7.2 Assess Requirement by Requirement

Taking the business dimension as an example:

| Requirement | Owning Business Scenario | Is It a Key Business Scenario | Necessity | Frequency of Problem Occurrence | Impact of Non-implementation (benefit / efficiency) | Conclusion |
|---|---|---|---|---|---|---|

**Frequency determination is a relative concept**: anything **less than 3 levels apart** from the frequency level of its owning business scenario (second-level / multi-second-level / minute-level / multi-minute-level / hour-level / multi-hour-level / day-level / multi-day-level / week-level) counts as high frequency.

### 7.3 Assessment Results

| Conclusion | Requirement List |
|---|---|
| Must Do | |
| Should Do | |
| Could Do | |
| Won't Do | |

### 7.4 Backlog Update

Bring the assessed requirements into the Backlog (a collection of pending requirements), and filter the requirement set to be handled in each development iteration by priority and cost.

| Iteration | Requirement ID | Priority | Estimated Cost | Owner |
|---|---|---|---|---|
