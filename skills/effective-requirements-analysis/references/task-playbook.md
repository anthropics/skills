# Key Execution Points for the 17 Tasks

A panoramic view of organising application-software requirements analysis: two levels (Value Requirement / Detailed Requirement), four tracks (Value / Functional / Data / Non-functional).

**The task board is a tool that helps you understand from which angles to analyse; it is not a form that must have every column filled in.** Once you try to fill in every column, you become a slave to the tool.

## Panoramic View

```
Value Requirement Track   Target Scenario ─→ Stakeholder Concerns ─→ Stakeholder Obstacle Points
                            (Black-box view: what problems the whole system solves for the customer, what opportunities it creates)

Detailed Requirement Track
  Functional Requirement  Business Support ── Business Process ── Business Scenario ── Scenario Analysis
               Management Support ── Control Point ── Business Report
               Maintenance Support ── Maintenance Scenario
  Data Requirement        Scope and Relationships (Domain Modelling) ── Composition and Deduction (Business Data Analysis)
  Non-functional Requirement Key Quality Attribute ── Quality Scenario + Constraints
Supplementary             Business Rules, Constraints
```

**Identify the five minimal requirement units**: business function, business report, business data, quality scenario, business interface.

---

## Value Requirement Track

### 1. Goal / Vision Analysis → "Problem Card"

Answer three essential questions: what problems does the whole system solve for the customer, and what opportunities does it create? Who are the most critical stakeholders? What do they care about and what do they worry about?

- Key: **Requirement = Expectation − Current State**, Goal = Problem + Opportunity
- Three ways to describe a goal: **Qualitative** (hollow, avoid), **Quantitative** (SMART: specific, measurable, achievable, relevant, time-bound), **Scenario-based** (recommended: realistic, easy to understand, verifiable, compelling)
- Three-part structure of a scenario-based description: ① Problem (list real stories) ② Who is affected / what the consequences are (analyse business losses) ③ Solution essentials
- Three essentials for defining a problem: **business framing, objectivity, fit**
- Three essentials for analysing impact: **clear referents (be specific about people, do not use "customers" or "management"), matching perspective, sound reasoning (show the reasoning process)**
- Turn the solution into strategies — write concrete strategies rather than empty phrases, and do not jump straight to functional modules
- Distil a **one-sentence goal**: use a "measure + effect" structure that reflects both the business framing and the value framing
- Example: "Prevent material disconnection based on safety stock, laying a logistics foundation for store expansion" (qualified); "Build a material management system to prevent material disconnection" (not qualified)
- Trimming: mandatory regulatory change, new business launch, adding a new channel → may be skipped, but exercise caution

### 2. Stakeholder Identification → "Stakeholder List"

Identify from the goals + supplement from the risks. **Do not aim for completeness; aim for accuracy.**

Types: sponsor/initiator, users, evaluators (finance, audit, regulation, industry supervision — usually holding a veto), others (development, maintenance, domain experts, technical experts).

Assess **relevance** and **influence** separately. Note that people with low relevance but high influence often have a very low priority of real requirements (marginal feedback raised offhand in a meeting).

### 3. Stakeholder Analysis → "Stakeholder Profile"

Select representatives (representativeness + typicality) → collect through interviews → analyse concerns (positive requirements) and obstacle points (negative requirements) → identify conflicts across concerns horizontally and formulate coping strategies.

Stakeholder profile: basic information (name, category, relevance, influence, responsibilities, representative, contact details) + core concerns (numbered one by one, importance judged) + remarks.

Express obstacle points with "avoid…" wording, so that the customer's reading mood is not affected.

Trimming: when there are few stakeholders and their concerns are simple and clear, the profile can be omitted and written directly in the "Description" column of the list.

### 4. Value Requirement Analysis Summary (Walkthrough)

The three sub-tasks are an organic whole that are **executed at the same time**, not sequentially.

Correct order: **first find the pain points → clarify the facts of the problem → analyse the business consequences → draft a preliminary solution concept → look ahead to the value → then identify stakeholders around this solution → analyse their concerns and obstacle points**.

One round is completed each time a pain point is found; a system usually has several pain points, so the process repeats multiple times.

**Key point**: stakeholder identification unfolds around the pain points and the solution, and does not aim to be exhaustive; a negative requirement is not a "bad requirement" but an impact brought about by building the system, which must be mitigated in the solution and in functional design.

---

## System Decomposition

### 5. Business Subsystem Division → "System Decomposition Model"

The purpose is to **control complexity**, not to decompose for the sake of decomposing. When the system is simple and the user group is uniform, this task may be trimmed.

**Must be divided from the business perspective, not the technical implementation perspective** — the technical perspective prevents users from participating, from building a global view, and from judging completeness.

Division strategies:

| Strategy | Applicable to |
|---|---|
| By business function (departmental function) | The most typical strategy for supporting and management-oriented systems (production, sales, supply, management) |
| By product / service | External service systems; internal platforms may adapt, e.g. by approval type |
| Two dimensions | Complex systems: first divide at level 1 by product/service, then at level 2 by function |
| By key characteristic | Computer-domain thematic systems (security, building automation) — identify key characteristics from the value perspective |
| Analysing the impact on legacy systems | Legacy system transformation: what is added, what is modified, what is affected |

**Identify interfaces and define relationships**: between every pair of subsystems, discuss "what service do we need the other party to provide? What service can we provide for the other party?", name them with a **verb-object structure**, and state who provides and who uses. Wherever there is decomposition, there is an interface.

Presentation: **hierarchy diagram** (vertical decomposition, when relationships are simple), **component diagram** (when there are horizontal service/call relationships, recommended), **data flow diagram** (when the focus is mainly on data sharing and exchange).

> Acceptance test: if your division yields "smart sensor system, video recording system, alarm system", that is the technical perspective; the user perspective should be "anti-theft subsystem, disaster warning subsystem, home monitoring subsystem".

### 6. Business Interface Analysis → "Business Interface Analysis"

A business interface ≠ system interface design. One business interface may be implemented by one or more system interfaces; a business interface only clarifies **Why (purpose and business value), What (interaction process)** and constraints, and does not involve How.

Three questions:

1. **Which subsystem should implement the interface more reasonably** — the "unity of knowledge and action" principle: it should be implemented by the subsystem that "knows" the information the interface needs (e.g. "report material usage" is implemented by the material management subsystem, not by the physical examination business subsystem that reports the materials)
2. **Which subsystems will use it, what business value it delivers, at what moment, at what frequency**
3. **Usage frequency** — give typical frequency values

Use sequence diagrams for interaction processes and a data dictionary for data packets. Constraints: protocol requirements, performance requirements, deployment environment, characteristics of the users.

It must be performed whenever there are multiple business subsystems (including those being modified or affected). When modifying an existing interface, first describe the original interface, then state the modification requirements and the reasons.

---

## Functional Requirement Track · Business Support

### 7. Business Process Identification → "Business Process List"

**Outside-in before inside-out, business before management**:

1. Identify external customers → main, variant and branch processes
2. Identify external staff, internal staff, and the specific times/states that trigger processes → main, variant and branch processes
3. Identify management processes (ex-ante prevention / in-process control / ex-post analysis)
4. Judge process priority (core business × frequency of occurrence → critical / important / useful / ordinary; "gilding" may be added)

The **main / variant / branch** classification only exists to guarantee complete identification; there is no need to agonise over attribution. Variant processes are relatively independent and cannot be merged into one single process diagram.

Angles for identifying management processes: approval control for business go-live; control of people, money and material resources; schedule and exception control.

Trimming: single-user systems centred on human-machine interaction (such as POS) may skip process identification and process analysis and go directly to business scenario identification.

### 8. Business Process Analysis and Optimisation → "Process Diagram Model"

**Layering principle** (key):

| Level | What to draw | Reader |
|---|---|---|
| Organisation-level process | Collaboration across departments | Decision layer |
| Department-level process | Collaboration across positions | Management layer ← **requirements analysis is performed at this granularity** |
| Individual-level process | The work steps of one position | Refined further during business scenario analysis |

Two principles for judging whether a process diagram is drawn too finely: **whether it is unrelated to collaboration**, and **whether it is not an independently reportable unit of work**.

**Eight elements**: five basic elements (division of labour, activity, collaboration, artefact relationships, branching) + three management elements (approval, rules, exceptions).

Three sources of division of labour: **scale, risk, expertise**.

### 9. Business Scenario Identification → "Business Scenario Descriptions within Business Processes"

Split scenarios out of the processes, naming them **"Role: Business Scenario (verb-object format)"**. Each scenario is a relatively independent, pausable, valuable and reportable business activity that is usually not split further.

After identification, sort by process priority + whether the scenario is essential + dependency relationships.

Presentation: use case diagram (recommended — managers see the task-to-task logic, operators see the person-to-task logic, combining the two), business scenario list (when you do not want to use the "use case" concept).

**This task cannot be trimmed** (except for pure data analysis systems); it is the "molecular unit that encapsulates requirements".

### 10. Business Scenario Analysis → "Business Scenario Analysis"

The "scenario—challenge—solution" logic replaces "input—output—processing". Five steps:

1. Outline the business scenario — what business objective the user wants to achieve (state the intent in the user's language), preconditions and postconditions (roughly 30% of scenarios have each), who besides the executor cares about it
2. Refine the business steps — basic event flow, extension event flow, exceptional event flow
3. Traverse the steps to analyse difficulties and derive functions — what difficulties will the user encounter at each step → what functions does the system need to provide; then ask "are there key exceptions that cannot be handled by the above steps"
4. Identify the environment and the rules — performance-related (number of users, typical business volume, peak, density), usability-related (the user's growth path and experience with related systems), deployment-environment-related
5. Analyse the implementation approach and complete the preliminary interaction design — interaction process, static snapshots, design notes (advice or constraint)

**Writing essentials**: write user intent rather than user action; write human-machine interaction rather than human-machine interface; do not use "if… then…" (use extension event flows instead); do not use "repeat execution…" (use sub-event flows instead); number extension points `2a`/`2b`.

**This task cannot be trimmed**.

---

## Functional Requirement Track · Management Support

### 11. Management Requirement Analysis → "Control Point List" "Control Point Analysis"

Management support has three aspects: **ex-ante risk avoidance** (adding management processes), **in-process risk control** (rules and approvals), **ex-post summary and optimisation** (data analysis). The first two are handled uniformly within the business support analysis; data analysis is the core of this task.

Three-layer logic: **Control Point (Why) → Metric → Report/BI/Data Mining (How)**. The metric layer cannot be skipped; it is the bridge between the two. Metrics and Control Points have a **many-to-many** relationship (queuing time can be used both to analyse the reasonableness of business arrangements and to analyse customer satisfaction).

Identification steps: identify the managers (decision layer / management layer, operational type vs managerial type) → identify Control Points → analyse the metric system → clarify the implementation approach and the data collection requirements.

Three identification methods: **responsibility analysis** (position responsibilities and assessment metrics), **problem analysis** (managerial type starts from management problems, operational type from business-operation problems), **case reference** (data analysis applications in peer organisations and related industries).

Metric analysis must think from **both sides**: the positive side asks "what information is needed", the negative side asks "what happens if it is unreasonable, and which data would reveal it".

The implementation approach depends on whether the data source is fixed and whether the query conditions are fixed → if fixed, use a report; otherwise use BI / data warehouse / data mining.

Naming: the name of a Control Point should express the intent; **avoid technical verbs such as "count" or "aggregate"**.

Trimming: systems that do not support management with data analysis may be trimmed; for operational analysis / big data projects it is the top priority.

### 12. Business Report Analysis → "Business Report Description"

Report analysis must start from **Control Points**, not from "what reports does the customer want" — users find it hard to articulate report requirements during the requirements analysis stage.

Three parts:

1. **Report overview** — who uses it (distinguish the report generator from the reader; the generator may falsify data under assessment pressure, which must be addressed at the implementation level), why it is used (trace back to the sub-intent of the Control Point), how frequently it is used (frequency determines performance requirements)
2. **Report content** — input conditions, data sources (which data tables, statistical calibre), data items and their formats and calculation methods
3. **Output requirements** — differences between the print version and the screen version, legibility of charts in black-and-white printing, category subtotals, page numbers and headers across multiple pages, special sorting requirements

---

## Functional Requirement Track · Maintenance Support

### 13. Maintenance Requirement Analysis → "Maintenance Requirement Description"

**Do not enumerate from the perspective of functional implementation; do it from the perspective of maintenance scenarios.** It is not a "logging" function but a "troubleshooting" scenario.

Typical maintenance scenarios:

- **Configuration** — start from what changes: user group changes (positions, permissions → functional permissions / data scope permissions / assignment permissions), process changes, data changes, regulatory changes
- **Runtime (normal)** — run-state monitoring (services, network communication, database, client), data backup (backup content, cycle, remote disaster recovery, restoration)
- **Runtime (failure)** — fault localisation, troubleshooting, fault recovery, emergency measures
- **Other** — system initialisation (installation, initialisation configuration, test tools), system upgrade (remote, automated, version checking), system migration (data migration, dual-system parallel operation)

Maintenance scenarios **can be reused across similar systems**; each project only needs a small number of modifications.

Trimming: temporary or transitional systems with a very short life cycle may be trimmed; in all other cases it is usually mandatory.

---

## Data Requirement Track

### 14. Domain Modelling → "Domain Class Diagram Segments" "System Domain Model"

The Data Requirement Track clarifies the "information flow" within the organisation. Two questions: **which business data should be brought into the system (scope)**, and **what relationships exist among them**.

Method: the **four-colour modelling method**, in the order **Red → Green, Yellow → Blue**:

1. Red — process data (behaviours that need to be stored)
2. Green — natural data (people, places, things); Yellow — role data (multiple identities of the same subject that do not convert into each other)
3. Blue — descriptive data (overview type, rule type)

**Bottom-up**: find all main business processes → draw one domain class diagram segment for each process → merge them into the system domain model. When merging, do two things: merge classes that have "different names but are actually the same"; optimise relationships and add key fields.

**Three essentials for reading a class diagram**: name classes and fields in the user's mother tongue (Chinese); provide a legend for the diagram; **read the diagram in business language**.

> "A customer can place multiple orders; each order has exactly one consignee; an order is composed of order items; because an order involves multiple suppliers, the order must therefore be split into multiple delivery notes……"
> Rather than: "customer and order are a one-to-many relationship, order and consignee are a one-to-one relationship……"

Four relationships between classes are commonly used at the domain modelling stage: association, category (generalisation), aggregation, composition. **To judge aggregation vs composition: can the individual exist independently of the whole** (deleting a department does not delete employees → aggregation; deleting an order deletes its order items → composition). **A relationship is stated with respect to a particular problem domain / system**, so talking about relationships outside the system context is meaningless.

**Situations in which this task must be performed**: the problem domain is unfamiliar to the development team; there are more than 50 business data items; database design is difficult to do directly.

### 15. Business Data Analysis → "Business Data Description"

Perform three kinds of analysis on each business data item:

- **Data usage analysis** — which processes use it, which parts are used, CRUD relationships
- **Data composition analysis** — the type of each field, its specification (length/precision), constraints/value ranges, whether it is non-null / a key / auto-numbered, and the formula of calculated fields
- **Data characteristic analysis** — primary/secondary fields (determine what the list displays), stable/unstable fields (determine the extensibility of the table structure), current/historical data (determine the migration strategy), key/auxiliary fields (determine indexes)

Except for pure computation systems, this task cannot be trimmed.

---

## Non-functional Requirement Track

### 16. Quality Requirement Analysis → "Key Quality Requirement List" "Quality Scenario Decision Card"

**The core is reverse thinking + scenario thinking**, starting from threats.

1. **Identify Key Quality Attributes** — security, reliability, usability, performance, maintainability, portability (further subdivisible, e.g. access security, data security, learnability, operability, adaptability)
2. **Prioritise** — risk exposure = threat impact × frequency of occurrence (frequent 3 / occasional 2 / low probability 1)
3. **Identify Quality Scenarios** — from three angles: user psychological expectations, application scenario constraints, operating environment constraints
4. **Identify conflicts and balance them** — every countermeasure brings new problems; negative side effects must be evaluated and the countermeasure may need to be replaced

**Three failure modes of writing and how to crack them**:

| Failure | Example | How to crack it |
|---|---|---|
| Failure of qualitative description | "Highly reliable, highly usable, highly scalable" | Make it scenario-based: write out the concrete scenarios that will occur. "High scalability" must state which change it addresses (business process / regulation / business model) |
| Harm of quantification | "Mean time between failures 2756 hours" | Quantifying for the sake of quantifying (CMMI assessment) is meaningless. The precondition of quantification is **accumulated historical data**. When you cannot write a precise metric, **writing the usage frequency is more useful than making up a metric out of thin air** |
| Confusion of the global view | "All queries respond within 7 seconds" | Global descriptions inevitably generalise from the particular. Distinguish scenarios; give stricter metrics to high-frequency queries |

Trimming: apart from transitional and demonstration systems, it should not be trimmed away entirely; at least the 3–5 most important quality requirements should be determined.

### 17. Constraint Analysis → "Project Constraint Description" "Design Constraint Description"

Non-functional Requirements contain two categories, **quality** and **constraints**: quality is what is demanded of us, constraints are what limit us.

**Project constraints** (also of concern to the client's decision layer): schedule requirements (and understanding the reasons behind the deadline, so as to guide phased delivery and contingency plans when it cannot be met), resource support (interface contacts, development and test environments; strive to have a business interface contact for every business theme), budget requirements.

**Design constraints** (of concern to the information department): technology selection (distinguish **non-negotiable** regulations/policies/internal standards from **negotiable** personal preferences of interface contacts), deployment environment (legacy systems, hardware and software platforms, national and cultural region, life cycle length), development environment (usually need not be clarified during the requirements analysis stage).

---

## Supplement

### Business Rule Analysis → "Business Rule Description"

When the rules are large in volume and complex, treat them as a separate topic; otherwise analyse them alongside process analysis, scenario analysis and domain modelling.

Classify by **scope of effect** (macro: affects the whole problem domain / meso: affects one process / micro: affects one scenario), then classify a second time by **type** (behaviour type / data type / permission type).

**Most important is to analyse the motivation behind the rules** (business motivation + executability considerations); this often reveals where the rules were insufficiently considered and yields better rule solutions.

### Constraint Analysis (see item 17)

---

## Trimming Quick Reference

| Task | Conditions under which trimming is allowed |
|---|---|
| Goal / Vision Analysis | Mandatory regulatory change / new business launch / new channel added — with caution |
| Stakeholder Identification | **Cannot be trimmed** |
| Stakeholder Analysis | When there are few stakeholders and simple concerns, it can be merged into the "Description" column of the list |
| Business Subsystem Division | The business is simple and the user group is uniform |
| Business Interface Analysis | Must be performed whenever there are multiple business subsystems |
| Business Process Identification / Analysis | Single-user systems centred on human-machine interaction (POS and the like) |
| Business Scenario Identification / Analysis | **Cannot be trimmed** (except for pure data analysis systems) |
| Management Requirement Analysis | When the system contains no data analysis supporting management |
| Business Report Analysis | When the system has no report requirements |
| Maintenance Requirement Analysis | Temporary or transitional systems with a very short life cycle |
| Domain Modelling | Unfamiliar problem domain / more than 50 data items / difficult database design → **must be performed** |
| Business Data Analysis | Pure computation systems (calculators and the like) |
| Quality Requirement Analysis | Transitional and demonstration systems; otherwise at least 3–5 items must be defined |
| Business Rule Analysis | Usually merged into other tasks |
| Constraint Analysis | Generally not trimmed |

## Choosing the Primary Evaluation Dimension by Product Stage

| Stage | Primary dimension |
|---|---|
| 0→1 Build-out stage | Business dimension (value–frequency two-dimensional evaluation method) |
| 1→10 Growth stage | User dimension, competitive dimension |
| 10→100 Maturity stage | Operational dimension (North Star metric, RFM model) |

Or use them in combination: in each iteration complete Business dimension Top 3 + Competitive dimension Top 3 + Operational dimension Top 1.

**Do not evaluate the four dimensions separately and then weight them** — many requirements are of low value in one dimension but of high value in others, and averaging buries them.

Results fall into four levels: **Must do / Should do / Could do / Not needed**.
