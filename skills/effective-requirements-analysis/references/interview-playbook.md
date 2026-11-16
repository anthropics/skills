# Interview Question Playbook

The main output of requirements analysis is **questions**. This file provides the questioning methods that turn "solution-level requirements" back into "problem-level requirements", plus the specific questions for each analysis task.

## The Three Levels of Questions

| Level | Meaning | How to ask |
|---|---|---|
| Solution-level requirement | The capability the user wants (described from a technical implementation angle) | Unreliable — the user is a problem expert, not a solution expert |
| Problem-level requirement | The problem the user wants solved (user's view, business view) | "If we don't build this feature, what impact does it have on the business today?" |
| Human-level requirement | The motivation behind the requirement (common in ToC products) | Rarely used in B2B systems; expand only when needed |

**Problem-level requirements are the analysis baseline of this skill.** Every functional requirement should ultimately trace back to some problem.

---

## 1. Clarification Questions (Mandatory in the First Round, 5–8 Questions)

Answer in the **past tense**: whose "what problem" does this requirement solve?

1. **Who raised it?** — Who made this request? (the requester)
2. **Who uses it?** — Are the requester and the user the same person? If not, did you get the real feedback from the users?
3. **Whose what problem?** — Describe it in the past tense: what happened back when you ran into this problem?
4. **How is it handled today?** — What's the current workaround? Is there a spreadsheet or an offline process?
5. **Who is affected?** — If we don't do this, who is the angriest? How angry?
6. **How often does it happen?** — Once a day / a week / a year?
7. **Who else is affected but didn't raise the request?** — Managers involved in the business process, upstream and downstream parties involved with the data, risk control and audit departments when rules are involved.
8. **Is this the voice of the mainstream users?** — Many requirements come from "expert users", whose proposals tend to be over-engineered; validate them against the silent mainstream users.

---

## 2. Questioning Techniques

### Symptom-vs-Cause Decision Tree (dig out the real cause behind the symptom)

Three steps, for when users state a broad demand like "comprehensively improve XX efficiency":

1. **Restore the symptom** — "How do you usually evaluate XX?"
2. **Share the cause** — "Have you seen anything recently that worried you?"
3. **Co-decide** — "What kind of support would you like the system to give you here?"

### Divide-and-Conquer (decomposing a big theme)

When facing a big and vague theme, break it down into interviewable sub-blocks along these angles:

- Decompose by **KPI** — the manager's core concern; most recommended
- Decompose by **work theme** — e.g. a manager in charge of material supply covers requisition, purchasing, and warehousing
- Decompose by **work stage** — e.g. a sales supervisor splits into pre-sales, in-sales, and after-sales

Two decomposition trees can be combined (e.g. KPI + work theme).

### Horizontal Sweep of Similar Cases (increase breadth)

Users often fall into "whack-a-mole" style point thinking, raising one problem at a time. How to do it:

1. Start from the Why of the requirement and distill it into a **problem type** (e.g. "a customer raises a special request")
2. Follow up: "Besides that, have you run into other problems of the XX type?"

### Vertical Sweep of Related Behaviour (increase depth)

Users often fall into stepwise thinking (solve one step at a time, and only raise related requirements after the solution ships). How to do it:

1. Combine Who + Why into a single Business Scenario (e.g. "the front desk clerk is processing a check-in")
2. List the work steps of that scenario: before → during → after
3. Follow up: "Do you need support for related behaviour before, during, and after?" — Which step does the current requirement fall into? What else happens before and after?

**Contrast**: requirements found by a horizontal sweep are usually unrelated to the original; requirements found by a vertical sweep are usually "the same requirement".

### 360-Degree Analysis (increase completeness)

For relatively important requirements:

1. **Identify potential affected parties** — put the scenario back into the process and find the upstream steps, downstream steps, process owners, and collaborators (e.g. a secretary, back-office staff)
2. **Analyse the affected parties' needs** — go through them one by one, stand in their position and identify the problems they care about and the requirements derived from them

---

## 3. Pick Questions by Task

### Goal / Vision Analysis

First judge how the user's expectation relates to the current state:

- Expectation **above** the current state → the user has already seen the "problem"; the interview alone is enough to surface it
- Expectation **equal to / below** the current state → the user is satisfied with the status quo; you need to **propose a new expectation** to stimulate the requirement (an "opportunity scenario")

Choose a strategy based on what triggered the project:

| Trigger | Strategy | What to ask |
|---|---|---|
| Site visit / study tour | Share the learnings | "What did you take away from the last visit? XX can do so much — where do we stand?" |
| Competitor moves | Competitive analysis | "What are the competitors doing with XX? Where is our gap?" |
| Hot topic / new technology trend | Share the understanding | "How do you understand the XX technology/trend? What could it solve for us?" |

If the project was initiated internally and the sponsor already has a mature idea → mine it with the symptom-vs-cause decision tree.

**Opportunity scenario mining** (when the user is satisfied with the status quo): new business (benchmarking leaders, competing with peers, borrowing from other industries), new technology (get close to real life and think about what it could solve), new user groups (value differences across generations bring new ideas).

When describing a problem, hold to three rules: **business framing** (talk about the business, not the system), **objectivity** (no subjective judgement), **match** (the level matches what senior management cares about).

### Stakeholder Identification

**Identify by goal**: collect the org chart first → mark the departments involved by goal/vision → for co-located offices, take the department head → for branches, add the branch head → senior deputies usually need to be included too.

**Supplement by risk**:

- Many frontline users are negatively affected by the system → list frontline users as key Stakeholders
- There are concerns that can veto the decision (finance, audit, regulation, industry regulators, domain experts) → must be included
- High risk in technical implementation → the development team becomes a key Stakeholder
- Long system lifecycle → the operations and maintenance team becomes a key Stakeholder

**More is not better** — what matters is listing them accurately. Note that relevance and impact are two different things: a Stakeholder with low relevance but high impact (e.g. an offhand remark about a peripheral issue from the first deputy general manager in a meeting) usually has a very low requirement priority.

### Stakeholder Analysis

First pick representatives: **representativeness** (covering the variety of differences) and **typicality** (representing a large proportion of a kind).

Before the interview, use divide-and-conquer to lay out the interview outline (content tree). Then collect **two kinds** of requirements:

- **Concerns (positive requirements)** — what problems they want the system to solve, what business support they want it to provide
- **Obstacle points (negative requirements)** — what negative effects they want the system to avoid

Common types of obstacle points: fear of extra data entry work, fear of getting blocked in a queue, fear of professional judgement being replaced by the system, fear of data being exposed by the system, fear of conflicting with the department's appraisal metrics.

**Writing notes**: write from a business angle; write in the result state; the value must be visible. Express obstacle points indirectly as "avoid …" so the customer's reading mood is not affected.

Finally, organise the **conflicts of concerns** among Stakeholders horizontally and give coping strategies.

### Business Process Identification

First identify **external customers** (the service requests they raise are the origin of the process), then identify external staff, internal staff, and the specific time/state that triggers the process.

For each type of initiator, ask about the three kinds of process — main, variant, supporting:

- Main process — the initiator's most core service request
- Variant process — variants that occur independently and cannot be integrated into the main process diagram (e.g. room change, room extension)
- Supporting process — peripheral, auxiliary business support

Then separately identify the **management processes** (used for pre-vention, in-process control, and post-hoc analysis).

**Two criteria for an end-to-end process**:

- **Completeness** — judge whether the process is complete; stand in the position of the service request and see whether the request is fulfilled or rejected
- **Boundary** — functional boundary (crosses business domains we don't cover) and system boundary (parts the system doesn't concern itself with)

Keep asking "where does this process actually end?" until you reach consensus. The end of a process is often where the misunderstanding is.

### Business Scenario Identification

Break Business Scenarios out of the Business Process; the naming format is **"Role: Business Scenario (verb-object form)"**.

A Business Scenario is usually a relatively independent, pausable, valuable, reportable business activity that normally is not split further.

### Business Scenario Analysis (Scenario — Challenge — Solution)

Replaces the traditional "input — output — processing" model:

1. **Scenario refinement** — expand into event flows: basic event flow (the normal steps the user expects), extended event flow (variations), exceptional event flow (error handling)
2. **Challenge identification** — step by step, stand in the user's position and think about what difficulties come up
3. **Solution derivation** — for each difficulty, think about what capability the system should provide

**Writing notes**:

- Write **user intent**, not user actions; write human-machine interaction, not the human-machine interface
- Don't express branches as "if … then …" → use extended event flows instead
- Don't express loops as "repeat step × to step ×" → use sub-event flows instead
- Number extension points: `2a`, `2b` denote extensions of step 2

### Business Data Analysis

For each core business datum, ask:

- **Data application** — which processes use it, which parts of it they use, and the CRUD relationships
- **Data composition** — each field's type, specification, constraints/value range, nullability, whether it is auto-numbered, and calculation formula
- **Data characteristics** — primary/secondary fields, stable/unstable fields, real-time/historical data, key/auxiliary fields

### Domain Modelling (Four-Colour Modelling)

In the order **Red → Green → Yellow → Blue**:

1. **Red (process data)** — behaviour that needs to be stored: read the process description and find all the "actions to be recorded"
2. **Green (natural data)** — people, places, things
3. **Yellow (role data)** — when the same entity has multiple identities and they **do not convert into each other**, extract the role
4. **Blue (descriptive data)** — overview types (e.g. category, package) and rule types (rules configurable through database tables)

**Key questions**: for each process datum ask "Is there a person on it? Do these people need to be abstracted as roles? Is there a place? Is there a thing?" Anything that can be reached by association from other process data should **not be abstracted again**.

### Quality Requirement Analysis

**Reverse thinking**: stand on the opposite side and think about when it would be unsafe, unreliable, or hard to use. Examples — security threats: too rich (sensitive data), too famous (a well-known organisation is easier to attack), the door left ajar (open network environment); reliability threats: demanding requirements (7×24), complex environments, many non-professional users prone to misoperation; usability threats: high efficiency demands, a weak user base, big gaps from developers; performance threats: high concurrency, complex algorithms and logic.

**Scenario thinking**: bring the quality requirement down to a concrete scenario. Measure the loss in a perceivable way (e.g. repair cost), not with made-up metrics.

**Ranking**: use "risk exposure" = threat impact × frequency of occurrence. Frequency has three levels: frequent (3) / occasional (2) / low probability (1).

**Three angles for identifying quality scenarios**: user psychological expectations, application scenario constraints, runtime environment constraints.

**Quality requirement conflicts**: every countermeasure brings new problems (e.g. a graphical CAPTCHA improves access security but reduces usability). They must be identified and balanced, and when necessary the countermeasure swapped (e.g. graphical CAPTCHA → random letter image).

### Management Requirement Analysis

First identify the **managers**, then identify the **control points** (management intent, the Why).

Data ≠ information. Only by asking "what do you want to see these data for?" can you dig out the control points.

**Control point → metric → report** is a three-layer chain; do not skip the middle layer:

- Example: "employee late-arrival statistics" is a report (a solution); "assessing employee motivation" is the control point (the Why); attendance records, proxy clock-ins, and effective working hours are the metrics

**Identify managers**: at the subsystem level find decision-makers and management-layer users → at the process level find management-layer users → at the whole-system level find decision-layer users. Distinguish the management type (managing people, affairs, and progress) from the business-operation type (managing customers, products, and suppliers).

**Three identification methods**: responsibility analysis (position duties and appraisal metrics), problem analysis (management type starts from management problems, business-operation type starts from business-operation problems), case benchmarking (data-analysis applications by peers and related industries).

**Analyse the metric system**: think from both sides — the positive side, "what information do we need"; the negative side, "what would go wrong if it were unreasonable, and which data would reveal that".

### Business Rule Analysis

Classify by **scope** (macro / meso / micro), then classify a second time by **type**:

- **Behaviour type** — affects process and scenario execution (e.g. "order quantity must be less than stock quantity")
- **Data type** — controls data format and content (e.g. "the product code of an order line must be unique")
- **Permission type** — controls execution and viewing permissions (e.g. "a branch manager may only approve purchase requests within 1 million for their own branch")

**The most critical thing is to understand the motivation behind the rule**, which has two sides:

- **Business motivation** — the rule may be poorly considered (e.g. Dangdang's "one coupon per order" was meant to cap the discount, but in fact it hurts large and loyal customers; a more reasonable rule caps it by total order amount)
- **Enforceability** — the rule looks unreasonable but has a practical reason (e.g. liquids over 100mL are not allowed because volume cannot be measured on the spot; if the system could measure volume, the rule could be optimised)

### Constraint Analysis

**Project constraints**: schedule requirements (and clarify the reason behind the deadline: to launch a new business? to implement a new regulation? for a trade show?), resource support (interface owners, test environments; push for a business interface owner for each business theme), budget requirements.

**Design constraints**: technology selection (distinguish what cannot change — regulations, policies, internal standards — from the personal preferences of interface owners that can be negotiated), deployment environment (legacy systems, software/hardware platform, national and cultural region, expected lifetime), development environment (usually need not be pinned down during the requirements analysis stage).

---

## 4. Interview Rhythm

1. **First round, 5–8 questions** — use the "clarification questions" list, covering Who/Why/current state/frequency/impact surface
2. **Second round, expanded from the answers** — take the specific questions for the tasks that were hit from this file (goal analysis / Stakeholder / process / scenario / data / quality / management / rule / constraint)
3. **Give a summary before each round ends** — confirmed Facts (A-xx), pending Assumptions (S-xx), Term definitions (T-xx); ask the user to confirm or correct them

**Every round must give the user one concrete handle they can answer from memory**, not an abstract checklist.
