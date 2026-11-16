# Artifact Templates

Each template specifies its columns, filling instructions, and key points. Name files `<系统名>_<产物名>.md`.

Artifact inventory (17 tasks → 13 artifact types):

| # | Artifact | From Task | Required |
|---|---|---|---|
| 1 | Problem Card | Goal/Vision Analysis | ✅ Required |
| 2 | Stakeholder List | Stakeholder Identification | ✅ Required |
| 3 | Stakeholder Profile | Stakeholder Analysis | Required when there are many Stakeholders |
| 4 | Business Subsystem Description | Business Subsystem Partitioning | When the system is complex |
| 5 | Business Interface Analysis | Business Interface Analysis | When there are multiple subsystems |
| 6 | Business Process List | Business Process Identification | ✅ Required |
| 7 | Business Process Diagram Model | Business Process Analysis and Optimization | ✅ Required |
| 8 | Business Scenario Description | Business Scenario Identification | ✅ Required |
| 9 | Business Scenario Analysis | Business Scenario Analysis | ✅ Required |
| 10 | Control Point List and Analysis | Management Requirement Analysis | When there are reporting requirements |
| 11 | Business Report Description | Business Report Analysis | When there are reporting requirements |
| 12 | Maintenance Requirement Description | Maintenance Requirement Analysis | ✅ Required |
| 13 | Domain Class Diagram Segment / Domain Model | Domain Modeling | Required |
| 14 | Business Data Description | Business Data Analysis | Required |
| 15 | Key Quality Requirement List + Quality Scenario Decision Card | Quality Requirement Analysis | ✅ Required |
| 16 | Business Rule Description | Business Rule Analysis | When there are many rules |
| 17 | Project Constraint / Design Constraint | Constraint Analysis | ✅ Required |

---

## 1. Problem Card

**Write one target scenario per card.** If there are multiple scenarios, write multiple cards.

| Field | Filling Instructions | Required |
|---|---|---|
| Problem Description | Describe objectively from both the business fact and the business consequence. Stay in the business domain, be objective, and match the actual situation | ✅ |
| Frequency | How often this problem occurs | |
| Aversion Level | The impact of the resulting consequences | |
| Replaceability | Whether an alternative solution currently exists | |
| Solution Description | Explain the solution from a black-box or grey-box perspective to help the business side build a macro-level understanding | ✅ |
| Expected Outcome | The result the solution can achieve once it goes live | ✅ |
| Value Proposition | A "one-sentence goal" in a measure + effect structure. Can be used as a Requirements Specification subsection title | |

**Key Points for Filling In**

- Frequency is a relative concept: relative to the frequency level of the owning Business Scenario (second-level / multi-second-level / minute-level / multi-minute-level / hour-level / multi-hour-level / day-level / multi-day-level / week-level), anything **less than 3 levels apart** counts as high frequency. Example: "Check-in processing" is at the multi-minute level, so the day level counts as high frequency, and anything above the day level counts as low frequency.
- Do not describe the problem from the system perspective. "The legacy system often produces inconsistent data" is the system perspective; "The various business reports currently generated with the help of systems show inconsistent statistical criteria and inconsistent business-related data" is the business perspective.
- Examples of one-sentence goals:
  - ❌ "Build a materials management system to prevent material disconnection" (the measure is not business-oriented enough, and the effect has no value orientation)
  - ✅ "Prevent material disconnection based on safety stock, laying the logistics foundation for store expansion"

---

## 2. Stakeholder List

| Field | Filling Instructions |
|---|---|
| Type | Sponsor/initiator, user, evaluator, other |
| Name | Usually described by position or role |
| Description | Why this person is a key or important Stakeholder |
| Relevance | High/Medium/Low — Is the project directly related to them? Does it involve their interests or responsibilities? |
| Impact | High/Medium/Low — Do they have strong influence on the project direction and acceptance? |

**Relevance and impact are usually for internal reading by the development team and should not be handed directly to customer representatives**, to avoid the kind of friction that comes with "why do you say my relevance is low".

---

## 3. Stakeholder Profile

**Write one Stakeholder per profile.**

### Basic Information

| Field | Description |
|---|---|
| Name | |
| Category | Same categories as the Stakeholder List |
| Relevance / Impact | Internal use only |
| Responsibilities | Key points of job duties, forming the role basis for understanding their concerns |
| Representative | The representative selected among multiple Stakeholders |
| Contact Information | |

### Core Concerns

Write them out one by one, numbering each for tracking, and rate the importance (High/Medium/Low or Critical/Important/Useful/Normal):

| ID | Concern (Positive Requirement) | Corresponding Functional Requirement | Importance |
|---|---|---|---|

| ID | Resistance Point (Negative Requirement) | Mitigation Measure | Importance |
|---|---|---|---|

**Express Resistance Points indirectly with "avoid…"** so that the customer's mood is not affected when reading.

### Notes

Information that helps understand the Stakeholder, such as professional background and career history.

---

## 4. Business Subsystem Description

Two parts: **the diagram part** (choose a suitable model to present the partitioning result, with a legend) ＋ **the description part**.

### Business Subsystem Description

| Field | Description |
|---|---|
| Business Subsystem | Name |
| Type | New / Modified / Affected / Recommend separate purchase |
| Description | Main user departments and value |

### Service Interface Description

| Field | Description |
|---|---|
| Service Interface | Named with a verb-object phrase |
| Provider | Only one |
| Consumer | May have multiple |
| Description | Main purpose |

---

## 5. Business Interface Analysis

| Field | Description |
|---|---|
| Interface Name | |
| Interface Providing Subsystem | |
| Interface Consuming Subsystem | List one by one: the business purpose, timing, and frequency of using this subsystem |
| Interface Interaction Process | Use a sequence diagram when complex |
| Data Package Description | Refine with a data dictionary |
| Interface Design Constraint | Protocol requirements, performance requirements, environment requirements, others |

---

## 6. Business Process List

**One per business subsystem.**

| Field | Description |
|---|---|
| Type | Main Business Process / Variant Business Process / Supporting Business Process / Management Process |
| Process Name | Find the process by identifying service requests, then convert it into a suitable process name; do not write the service request directly |
| Brief Description | Describes the starting point of the process |
| Priority | Critical / Important / Useful / Normal (optionally "gilded") |

Priority basis: **whether it is a core business process × occurrence frequency**.

---

## 7. Business Process Diagram Model

Draw according to the layering principle: **department-level processes** (collaboration between positions) — requirements analysis is performed at this granularity.

Two self-check questions: Is it unrelated to collaboration? Is it not an independently reportable unit of work? If either applies, it should be pushed down to the individual-level process.

The process must reflect the **eight elements**: division of labor, activity, collaboration, artifact relationships, branching (basic) ＋ approval, rules, exceptions (management).

---

## 8. Business Scenario Description

Naming: **"Role: Business Scenario (verb-object format)"**.

| Field | Description |
|---|---|
| Role Played by the End User | Mapped to the end user |
| Type | New / Modified |
| Use Case Name | |
| Use Case Summary | The core business intent of this Business Scenario |
| Priority | |

Appendix: scenario inventory (organized by user role; it can replace the use case diagram).

---

## 9. Business Scenario Analysis

Three parts: **Scenario Overview**, **Scenario Analysis**, **Key Exceptions**.

### Scenario Overview

| Field | Description |
|---|---|
| Task Name | |
| Task Summary | The business purpose the user intends to achieve by executing this scenario, written as intent in the user's own language |
| Task Preconditions | What state must be checked before execution (preconditions) / what state must be guaranteed before it ends (postconditions); indicate which one it is |
| Task Frequency | |

### Scenario Analysis

| Scenario/Task (Sub-task) | Problem/Challenge | Solution/Required Capability |
|---|---|---|
| Step 1 of the basic event flow | | |
| Step 2 of the basic event flow | | |
| Task variant (extended event flow) 2a | | |
| Task variant (extended event flow) 2b | | |

### Key Exceptions

Special cases that cannot be handled by the steps above and require dedicated functional support. **These are not branches inside the normal execution flow.** Example: a hotel front desk receiving a tour group, compared with "check-in processing".

---

## 10. Control Point List and Analysis

**Control Point List** (one per subsystem)

| Field | Description |
|---|---|
| Type | Operational / Management (may be refined into subcategories) |
| Name | Expresses the intent; **avoid technical verbs such as "count" or "aggregate"** |
| Brief Description | Main users and usage value |
| Priority | Critical / Important / Useful / Normal (optionally "gilded") |

**Control Point Analysis**

| Field | Description |
|---|---|
| Related Stakeholders | Which management-level users will use it; if their reading focus differs, state it in the text |
| Control Point Objective | From a business perspective and in value terms, describe the business objectives each Stakeholder expects to achieve through this Control Point |
| Required Business Reports | Fixed data source and fixed query conditions → solve with a report |
| BI / Data Warehouse / Data Mining Requirements | The parts that reports cannot cover; state the requirements from a black-box perspective |

---

## 11. Business Report Description

| Section | Field |
|---|---|
| Report Overview | Report name, users, business intent, usage frequency |
| Report Implementation Analysis | Report input conditions, report output format requirements (a prototype may be used), report data source analysis (domain class diagram segment), report data item descriptions |
| Report-Related Requirements | Whether printing is needed, chart requirements, whether charts are printed, multi-page handling, subtotals by category, special sorting requirements, explanation of the statistical criteria |

**Report analysis must start from the Control Point**, not from "what reports does the customer want".

---

## 12. Maintenance Requirement Description

Organize by maintenance scenario, not by feature.

| Scenario Category | Specific Scenario | Required Support | Responsible Party |
|---|---|---|---|
| Configuration | User group changes / process changes / data changes / regulation changes | | |
| Runtime (Normal) | Service monitoring / network communication / database / client / data backup | | |
| Runtime (Failure) | Fault localization / troubleshooting / fault recovery / emergency handling | | |
| Other | System initialization / system upgrade / system migration | | |

This section may lean toward technical language; confirm it mainly with the operations team.

---

## 13. Domain Class Diagram Segment / System Domain Model

### Domain Class Diagram Segment

Three parts:

1. **Domain Class Diagram Segment** — the graphical part, with a legend
2. **Business Data Description** — point out aliases and explain the meaning
3. **Data Rules** — the rules related to this data

### System Domain Model

The overall diagram after merging all segments. When merging:

- Merge classes that are "named differently but actually the same"
- Optimize relationships (handle complex relationships such as transitive dependencies in moderation) and add key fields to each domain class

**Four self-check questions**: Is red missing (there can be no action that does not need to be recorded)? Is green missing (people, places, or things are always involved)? Is yellow missing (then it would not be flexible)? Is blue missing (then configurability is too poor)?

---

## 14. Business Data Description

### Data Composition Analysis

| Field Name | Type/Specification | Constraint/Value Range | Description | Whether Non-null/Key/Auto-numbered | Calculation Method |
|---|---|---|---|---|---|

### Relationship Between Data and Process (Data Application Analysis)

| Process | Create | Retrieve | Update | Delete | Portion Used (Data Window) |
|---|---|---|---|---|---|

### Other Notes (Data Characteristic Analysis)

Primary/secondary fields, stable/unstable fields, real-time/historical data, key/auxiliary fields.

---

## 15. Key Quality Requirement List + Quality Scenario Decision Card

### Key Quality Requirement List

| Field | Description |
|---|---|
| Quality Objective Type | Security / Reliability / Usability / Performance / Maintainability / Portability |
| Quality Objective Subtype | e.g. access security, data security, learnability, operability, adaptability |
| Description | Why it matters |

Ordering basis: **risk exposure = threat impact × occurrence frequency** (frequency: frequent 3 / occasional 2 / low probability 1).

### Quality Scenario Decision Card (Target Scenario Decision Card)

| Field | Description |
|---|---|
| Objective | Which quality type it belongs to |
| Scenario | The specific scenario that affects the quality requirement |
| Strategy | The technical measures taken for this scenario |
| Risk | The negative side effects brought by this measure |
| Conflict Balance | Conflicts and trade-offs with the countermeasures of other quality scenarios |

**Every quality scenario must fill in the "Risk" column** — omitting it means the conflict analysis was not performed.

---

## 16. Business Rule Description

Classify twice, by **Scope** (macro/meso/micro) and by **Type** (behavior/data/permission).

| Rule ID | Rule Content | Type | Scope | Business Motivation | Executability Considerations |
|---|---|---|---|---|---|

**The Business Motivation and Executability columns are where the value of this artifact lies**; if you cannot fill them in, you have not truly understood the rule.

---

## 17. Project Constraint / Design Constraint

### Project Constraint Description

| Field | Description |
|---|---|
| Schedule Requirement | The latest delivery date **and the reasoning behind it** (new business go-live? new regulation taking effect? exhibition?) |
| Resource Support | Liaison contacts, development/test environment support |
| Budget Requirement | Usually refers to the contract agreement |

### Design Constraint Description

| Field | Description |
|---|---|
| Technology Selection | State whether it is **non-negotiable** (regulation/policy/internal standards) or **negotiable** (personal preference of the liaison) |
| Deployment Environment | Legacy systems, hardware/software platform, country/cultural region, lifecycle length |
| Development Environment | Usually not clarified during the requirements analysis stage |
