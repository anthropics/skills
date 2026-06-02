---
name: change-management
description: >
  Design organizational change frameworks for schools, nonprofits, higher ed, and government/education
  agencies using evidence-based models (Kotter, ADKAR, Lewin, McKinsey 7-S, Bridges). Produces
  stakeholder engagement plans, communication strategy matrices, implementation roadmaps,
  resistance & risk registers, and change readiness assessments — modularly or as a full plan.

  Always use this skill when a user mentions: change management, rollout plan, stakeholder engagement,
  implementation roadmap, managing resistance, change readiness, getting buy-in, launching an initiative,
  managing a transition, culture shift, or organizational transformation. Also trigger for requests to
  plan/lead/design any change initiative in an education, nonprofit, or government context.
---

# Change Management Skill

## Overview

This skill generates modular, evidence-based change management deliverables for educational and mission-driven organizations. Outputs can be used independently or assembled into a full Change Management Plan.

All deliverables are grounded in established change models. Model selection is context-driven — see **Model Selection** below.

## Model Selection

| Context | Recommended Model | Rationale |
|---|---|---|
| K–12 schools | Kotter 8-Step | Clear urgency and coalition framing |
| Nonprofits | ADKAR | Individual-level adoption focus |
| Higher ed | McKinsey 7-S | Systemic alignment across multiple structures |
| Government / public agencies | Lewin (Unfreeze-Change-Refreeze) | Structured bureaucratic change |
| Large mergers / cultural change | Bridges Transition Model | Emotional/identity transition focus |

If the user does not specify a context, default to **Kotter** for organizational change and **ADKAR** for technology/process rollouts.

## Modules

This skill produces five independent modules. Users may request any one module or a full plan.

### Module A: Change Readiness Assessment

Assess organizational readiness across five dimensions:

| Dimension | Indicators of Readiness | Red Flags |
|---|---|---|
| Leadership alignment | Sponsors identified, vocal, consistent | Divided leadership, passive sponsors |
| Staff capacity | Bandwidth exists; PD built in | Already overloaded staff |
| Culture/trust | History of successful change | Change fatigue, prior failures unaddressed |
| Communication infrastructure | Multi-channel, two-way systems in place | Top-down only, low trust in messaging |
| Data/evidence access | Baseline data exists or is collectable | No data culture, resistance to measurement |

Output: Readiness matrix + narrative summary with recommended adjustments before proceeding.

### Module B: Stakeholder Engagement Plan

Identify and map stakeholders across four quadrants:

**Power-Interest Grid:**
- High power, high interest → Manage closely
- High power, low interest → Keep satisfied
- Low power, high interest → Keep informed
- Low power, low interest → Monitor

For each stakeholder group, produce:
| Stakeholder | Role | Current stance | Desired stance | Engagement strategy | Owner |
|---|---|---|---|---|---|
| [Group] | [Title] | [Support/Neutral/Resist] | [Support] | [Tactic] | [Person] |

Include: board members, senior leaders, middle managers, frontline staff, union reps (if applicable), families/community (if K–12 or nonprofit), funders/grantors (if nonprofit/higher ed).

### Module C: Communication Strategy Matrix

| Message | Audience | Goal | Channel | Timing | Sender | Format |
|---|---|---|---|---|---|---|
| Why this change, why now | All staff | Urgency + context | All-hands + email | Week 1 | Superintendent/ED | Town hall + memo |
| What changes for you | Affected roles | Role clarity | Department meeting | Week 2 | Direct supervisor | FAQ + 1:1 |
| How you'll be supported | Frontline staff | Capacity/fear | PD session | Week 3 | Coach/trainer | Workshop |
| Progress update | All stakeholders | Trust + transparency | Newsletter | Monthly | Change lead | Data dashboard |

**Communication Design Principles (for education/nonprofit contexts):**
Lead with *why*, anchor in mission
Differentiate messages by role and concern, not just title
Build in two-way feedback mechanisms (surveys, office hours, anonymous channels)
Acknowledge loss and difficulty explicitly (Bridges)
Cascade: executive → manager → frontline, not all-broadcast

### Module D: Implementation Roadmap

Produce a phased roadmap. Adapt phase names to the selected change model.

**Standard Phase Structure (Kotter-aligned; adapt labels for other models):**

| Phase | Duration | Key Activities | Milestones | Owner |
|---|---|---|---|---|
| 1. Urgency & Coalition | Weeks 1–4 | Stakeholder meetings, data sharing, coalition building | Guiding coalition formed | Sponsor |
| 2. Vision & Strategy | Weeks 5–8 | Vision drafting, strategy alignment, pilot identification | Vision approved | Leadership team |
| 3. Communication & Buy-in | Weeks 9–12 | Town halls, listening sessions, feedback loops | 70%+ awareness and understanding | Comms lead |
| 4. Enabling & Empowering | Months 4–6 | Training, resource allocation, barrier removal | Staff trained and supported | Ops/HR |
| 5. Short-Term Wins | Months 5–7 | Pilot launch, data collection, recognition | First wins publicly celebrated | Project lead |
| 6. Consolidation | Months 7–10 | Scaling, adjusting, embedding in routines | Widespread adoption visible | Change lead |
| 7. Anchoring | Months 10–12 | Policy/process revisions, succession planning, culture integration | Change institutionalized | Exec sponsor |

Include a Gantt chart scaffold if requested.

### Module E: Resistance & Risk Register

| Risk | Likelihood (H/M/L) | Impact (H/M/L) | Type | Mitigation Strategy | Owner |
|---|---|---|---|---|---|
| Key staff departure | M | H | Capacity | Succession plan, retention incentives | HR |
| Union opposition | H | H | Political | Early engagement, transparency, MOUs | ED/Superintendent |
| Change fatigue | H | M | Cultural | Pace management, celebrate wins, lighter early tasks | Change lead |
| Funder concern | L | H | External | Proactive communication, impact narrative | Dev/Comms |
| Technology failure | M | M | Operational | Pilot testing, IT support plan | IT/Ops |

**Resistance Typology:**
**Cognitive resistance**: Staff don't understand — address through communication and FAQs
**Emotional resistance**: Staff feel loss, fear, threat — address through narrative, voice, and co-design
**Capacity resistance**: Staff are willing but overwhelmed — address through workload relief, phasing, and support
**Political resistance**: Competing agendas, union dynamics, board opposition — address through coalition and negotiation

## Full Plan Assembly

If the user requests a complete plan, assemble all five modules in this order:

Executive Summary (1 page: change rationale, model selected, timeline, sponsor)
Change Readiness Assessment (Module A)
Stakeholder Engagement Plan (Module B)
Communication Strategy Matrix (Module C)
Implementation Roadmap (Module D)
Resistance & Risk Register (Module E)
Evaluation & Sustainability Plan (Kirkpatrick Levels 1–4 applied to change adoption)
Appendices (raw data, stakeholder lists, glossary)

Produce as a structured Markdown document or DOCX file (read SKILL at `/mnt/skills/public/docx/SKILL.md` if DOCX output is requested).

## Quality Standards

For every plan, include:
- A named change model (never generic)
- At least one stakeholder group analysis
- A timeline with phases (not just tasks)
- At least one risk with a mitigation strategy
- Language appropriate for education/nonprofit audiences (avoid corporate jargon)
- Acknowledgment of the human/emotional side of change (required, not optional)

## Constraints

Always **name the change model** being used and explain why it fits the context
Never produce a generic "change plan" without anchoring it to a recognized framework
Always **acknowledge the human side of change** — loss, identity, pace — regardless of change type
Flag if the timeline provided is **unrealistic** for the scope of change described
