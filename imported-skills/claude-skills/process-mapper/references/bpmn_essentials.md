# BPMN Essentials for Business-Process Documentation

A practical reference on BPMN (Business Process Model and Notation) for
process-mapper users. The skill emits text-based swim-lane diagrams that
approximate the BPMN structure without requiring users to install Visio,
Lucidchart, or Camunda. This file explains the canon those diagrams reflect.

## Sources

1. **Object Management Group. (2011). _Business Process Model and Notation (BPMN), Version 2.0._** OMG Document Number formal/2011-01-03. — The normative specification.
2. **Silver, B. (2011). _BPMN Method and Style,_ 2nd ed.** Cody-Cassidy Press. — The canonical practitioner book; defines the "method and style" rules now widely treated as informal BPMN convention.
3. **Allweyer, T. (2010). _BPMN 2.0: Introduction to the Standard for Business Process Modeling._** Books on Demand. — Approachable academic introduction.
4. **Freund, J. & Rücker, B. (2019). _Real-Life BPMN,_ 4th ed.** CreateSpace. — Practical patterns from the Camunda team.
5. **OASIS. (2010). _Web Services Business Process Execution Language (WS-BPEL), Version 2.0._** — Related execution standard; clarifies the interplay between BPMN modeling and BPEL execution.
6. **ISO/IEC 19510:2013. _Information technology — Object Management Group Business Process Model and Notation._** — The international-standard version of OMG BPMN 2.0.
7. **Recker, J. (2010). "Opportunities and constraints: the current struggle with BPMN." _Business Process Management Journal,_ 16(1), 181–201.** — Peer-reviewed analysis of BPMN adoption pain points; sources the "common notation mistakes" list below.
8. **Dumas, M., La Rosa, M., Mendling, J. & Reijers, H. A. (2018). _Fundamentals of Business Process Management,_ 2nd ed.** Springer. — Textbook covering BPMN within the broader BPM lifecycle.

---

## Core BPMN elements

BPMN has hundreds of symbols. In practice, ~80% of useful diagrams use only
~10 of them. The skill's swim-lane output uses precisely these.

### Flow objects

- **Activity (task)** — a unit of work done by one role. Rectangle with rounded
  corners. In the skill's swim-lane: this is a `value-add` or `rework` stage.
- **Event** — something that happens (start, intermediate, end). Circles. The
  skill represents start/end implicitly as the first and last stage.
- **Gateway** — branching / merging point. Diamond. Common types:
  - **Exclusive (XOR)** — one path taken.
  - **Parallel (AND)** — all paths taken.
  - **Inclusive (OR)** — one or more paths taken based on data.

### Connecting objects

- **Sequence flow** — solid arrow inside one pool. The skill renders these as
  `->` between stages in the lane.
- **Message flow** — dashed arrow across pool boundaries. The skill's
  cross-lane handoffs (e.g., Requestor -> Manager) are message-flow-equivalents.
- **Association** — dotted line linking a data object to an activity.

### Swim lanes

- **Pool** — represents a participant (a company, a department, or a system).
  Each pool is independent; communication between pools uses message flow only.
- **Lane** — a sub-partition within a pool, usually a role or sub-team.

The skill maps one stage's `owner` field to one lane. The full diagram is a
single pool with multiple lanes — appropriate for an internal business process
where one organization controls the whole flow.

---

## Method and Style rules (Silver)

Silver's "Method and Style" is a set of practitioner conventions that make
BPMN diagrams readable. The most load-bearing rules:

1. **One start, one end** per pool. Multiple end events are allowed only if
   they represent different end-states (e.g., approved vs. rejected).
2. **Label every flow out of a gateway** with the condition (e.g., "amount >
   $10K"). An unlabeled gateway is unreadable.
3. **Sequence flow stays inside a pool.** Use message flow between pools.
4. **One verb-noun task name.** "Approve PO" beats "Approval step."
5. **Black-box pools** for participants you don't model in detail (e.g., the
   customer). Show only the message exchanges with them.

The skill enforces rule #4 implicitly by encouraging "Stage" names like
"Manager approves request" rather than "Approval."

---

## Common notation mistakes (Recker 2010; Freund/Rücker)

The following errors appear in over half of real-world BPMN diagrams:

| Mistake | Why it's wrong | What to do |
|---------|----------------|------------|
| Using sequence flow across pools | Pools are independent; only messages cross | Use dashed message flow |
| Missing gateway labels | The reader can't tell which path is taken when | Label every outbound flow |
| Multiple unrelated end events | Reader can't tell why a process ends in each spot | Consolidate or label by end-state |
| Conflating role with system | "JIRA" is a system, not a role; "Engineering Manager" is a role | Lanes = roles, not tools |
| Implicit gateways | Diverging sequence flows without a gateway diamond | Add an explicit XOR or parallel gateway |
| Modeling exceptions inline | Cluttered happy path | Use boundary events or a separate exception sub-process |
| No data objects | Reader doesn't know what artifacts move through | Add data-object boxes where they help |

The skill's stage-level `type` field (`value-add` | `wait` | `rework`) captures
the rework case explicitly so it doesn't get hidden inline. Users who want
full BPMN fidelity should export the normalized JSON and ingest it into a
BPMN-aware tool (Camunda Modeler, bpmn.io, Signavio).

---

## When to use BPMN vs. simpler notations

BPMN is appropriate when:

- The process has cross-functional handoffs (multiple lanes).
- The process has branching logic (gateways).
- The diagram will be reviewed by people who don't sit through a walkthrough.

For purely linear processes with no branching, a numbered list or a value
stream map is faster to produce and easier to read. The skill's swim-lane
output deliberately occupies the middle ground: more structured than a list,
less ceremony than full BPMN.

---

## BPMN 2.0 execution semantics

ISO/IEC 19510:2013 specifies executable semantics so that a BPMN diagram can
be loaded into a workflow engine (Camunda, jBPM, Activiti) and run directly.
The skill does not target executable BPMN — its output is for human reading
and constraint analysis. If a user wants to move from documentation to
automation, the normalized JSON is a starting point; mapping to the BPMN 2.0
XML schema is a separate exercise.
