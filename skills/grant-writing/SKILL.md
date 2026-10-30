---
name: grant-writing
description: >
  Produces professional grant proposals, logic models, needs statements, budgets with indirect cost (F&A) calculations, and evaluation plans for nonprofit and educational organizations. Use this skill whenever a user mentions grants, RFPs, funding proposals, logic models, needs statements, budget justifications, or evaluation plans — even if they just say "help me apply for funding," "write a proposal," "build a logic model," or "I need an eval plan for a grant." Supports all funder types (Federal, private foundation, state/local, corporate) and org types (K-12, higher ed, nonprofit, government). Always use this skill for any grant-related task.
  ---

  # Grant Writing Skill

  Produces rigorous, funder-aligned grant documents across all major output types. Supports both RFP-extraction and manual funder-priority modes.

  ---

  ## Step 1 — Intake & Mode Selection

  Before writing anything, collect the following. Ask only for what's missing — never repeat questions already answered.

  ### Required inputs
  | Field | Purpose |
  |---|---|
  | Organization name, type, and mission | Grounds all narrative voice |
  | Project title and 1–2 sentence description | Anchors scope |
  | Target population | Needed for needs statement & logic model |
  | Geographic scope | Needed for data sourcing in needs statement |
  | Requested amount (or range) | Drives budget structure |
  | Project period | Affects budget lines and eval timeline |
  | Funder name and type | Drives alignment strategy |

  ### Funder alignment mode — choose one:
  - **RFP Mode**: User pastes RFP/NOFO text → run the **RFP Parser** (see `references/funder-alignment.md`)
  - **Manual Mode**: User describes funder priorities → use the **Priority Mapping Template** (see `references/funder-alignment.md`)

  ---

  ## Step 2 — Output Menu

  After intake, confirm which outputs the user needs. Produce them in this recommended sequence when doing a full proposal:

  ```
  1. Needs Statement
  2. Logic Model
  3. Full Grant Narrative
  4. Evaluation Plan
  5. Budget + Justification
  ```

  Each section can also be produced standalone. Jump directly to the relevant section below.

  ---

  ## Step 3 — Needs Statement

  **Purpose:** Establish urgency using data. Must demonstrate a gap between current and desired state.

  ### Structure
  1. **Population & context** — Who is affected, where, and how many
  2. **Problem data** — 2–4 local/regional statistics (cite source + year)
  3. **Root cause framing** — Why the problem persists (systemic, resource, capacity)
  4. **Gap statement** — What is missing that this project will address
  5. **Consequence of inaction** — What happens without intervention
  6. **Transition** — Bridge to the proposed solution

  ### Quality checks
  - [ ] At least one local or regional data point (not national only)
  - [ ] Statistics are < 5 years old
  - [ ] Gap is specific, not generic ("students lack access to X" not "education is a challenge")
  - [ ] Avoids deficit framing — centers community assets alongside needs

  ### Funder-type calibration
  | Funder | Emphasis |
  |---|---|
  | Federal (Dept of Ed, NSF) | Align gap to program priorities in NOFO; cite NAEP, NCES, Census |
  | Private foundation | Connect to funder's theory of change; use community voice language |
  | State/local | Use state data dashboards, ESSA data, state report cards |
  | Corporate | Frame ROI: workforce, economic mobility, community impact |

  ---

  ## Step 4 — Logic Model (W.K. Kellogg Framework)

  **Framework:** W.K. Kellogg Foundation Logic Model format with Theory of Change narrative.

  ### Template

  | Component | Definition | Produce for this project |
  |---|---|---|
  | **Situation** | Problem/need driving the work | Pull from Needs Statement |
  | **Inputs** | Staff, funds, partners, data, facilities | List all committed resources |
  | **Activities** | What the program does | 4–8 specific, verb-led actions |
  | **Outputs** | Direct products of activities | Countable: # trained, # sessions, # materials |
  | **Short-term outcomes** | Changes in knowledge/skill (0–1 yr) | 2–3 SMART outcomes |
  | **Medium-term outcomes** | Changes in behavior/practice (1–3 yr) | 2–3 SMART outcomes |
  | **Long-term outcomes** | Systems/condition change (3–5 yr) | 1–2 aspirational outcomes |
  | **Assumptions** | Conditions required for logic to hold | List 3–5 |
  | **External factors** | Contextual risks outside program control | List 3–5 |

  ### Theory of Change narrative
  After the table, write a 2–3 sentence "if-then" causal chain:
  > "If [inputs] are deployed through [activities], then [outputs] will generate [short-term outcomes], which will lead to [long-term impact] because [assumption]."

  ---

  ## Step 5 — Full Grant Narrative

  Produce sections in funder's required order if specified. Default structure:

  ### 5.1 Executive Summary / Abstract (1 page max)
  - Organization, project title, amount, period, population, core strategy, primary outcome

  ### 5.2 Organizational Capacity
  - Mission alignment, track record, relevant prior grants, key personnel credentials
  - Include 1–2 measurable past results ("In 2023, X served Y participants achieving Z")

  ### 5.3 Project Design / Program Plan
  - Derive directly from logic model activities
  - Use timeline table: Month | Activity | Lead | Milestone
  - Address: evidence base for approach, equity strategy, sustainability plan

  ### 5.4 Partnerships & Community Engagement
  - Named partners with roles and MOUs if available
  - Community voice: how target population shaped the design

  ### 5.5 Evaluation Plan
  → Defer to Step 6 (Evaluation Plan section)

  ### 5.6 Dissemination / Sustainability
  - How results will be shared and how the program continues post-grant

  ### Narrative voice rules
  - Write in active voice; subject = the organization or the participants
  - Use specific, concrete language — never vague ("comprehensive," "innovative," "holistic" without evidence)
  - Mirror funder's language from RFP verbatim where strategic (signal alignment)
  - Page limits: respect them; flag to user if content exceeds limit

  ---

  ## Step 6 — Evaluation Plan

  Read `references/evaluation-frameworks.md` to select the appropriate framework. Decision guide:

  | Use case | Recommended framework |
  |---|---|
  | Training / professional development | **Kirkpatrick** (4 levels) |
  | Public health or behavior change program | **RE-AIM** (5 dimensions) |
  | Community development / capacity building | **W.K. Kellogg Logic Model** (already in Step 4) |
  | Emerging, complex, or adaptive programs | **Developmental Evaluation** (Patton) |
  | Federal education grants (Dept of Ed) | Kirkpatrick or RE-AIM depending on program type |

  ### Minimum evaluation plan components
  1. **Evaluation questions** — 3–5, mapped to outcomes in logic model
  2. **Data sources** — for each question (survey, assessment, admin data, focus group)
  3. **Data collection timeline** — baseline, midpoint, endline
  4. **Evaluator role** — internal vs. external; justify
  5. **Framework-specific section** — (see `references/evaluation-frameworks.md`)
  6. **Reporting plan** — to funder and to participants

  ---

  ## Step 7 — Budget & Budget Justification

  Read `references/budget-templates.md` for line-item templates and indirect cost guidance.

  ### Budget structure

  **Personnel** (largest category — typically 50–70% of budget)
  - List each position: Title | % FTE | Annual Salary | Grant-Funded % | Grant Amount
  - Include fringe benefits as separate line (use actual rate or 25–30% if unknown)

  **Non-Personnel categories**
  | Category | Examples |
  |---|---|
  | Consultants / Subcontracts | Evaluator, trainer, subject matter expert |
  | Travel | Mileage, airfare, per diem (use GSA rates for federal) |
  | Equipment | > $5,000 per unit (federal threshold) |
  | Supplies | Curriculum materials, technology < $5,000 |
  | Indirect / F&A | See below |
  | Other Direct Costs | Participant incentives, printing, subscriptions |

  ### Indirect Cost (F&A) calculation

  ```
  Indirect Cost = Direct Cost Base × Negotiated Rate

  Federal rate options:
  - Use organization's negotiated rate (NICRA) if available
  - De minimis rate: 10% of Modified Total Direct Costs (MTDC) — available to any org without a negotiated rate (2 CFR §200.414)
  - MTDC excludes: equipment, capital, patient care, subcontract amounts > $25K, tuition

  Private foundations: Many cap indirect at 10–15%; always check funder policy.
  State grants: Vary — check state regulations.
  ```

  ### Budget justification format
  For each line item write 2–3 sentences:
  1. What it is and who/what it supports
  2. How the cost was calculated
  3. Why it is necessary for project success

  ### Budget narrative quality checks
  - [ ] All costs are allowable, allocable, and reasonable (2 CFR §200 for federal)
  - [ ] Indirect rate source is cited
  - [ ] No double-counting across cost categories
  - [ ] Cost-share / match requirements noted if applicable

  ---

  ## Step 8 — Final Quality Review

  Before delivering any output, run this checklist:

  - [ ] Funder priorities mirrored in narrative (from RFP parser or manual map)
  - [ ] Logic model outputs connect to evaluation questions
  - [ ] Budget totals match narrative cost references
  - [ ] All statistics cited with source and year
  - [ ] Outcomes are SMART (Specific, Measurable, Achievable, Relevant, Time-bound)
  - [ ] Equity lens present in needs statement, design, and evaluation
  - [ ] Page/word limits respected
  - [ ] No unsupported superlatives ("first," "unique," "only") without evidence

  ---

  ## Reference Files

  Load these only when working on the relevant section:

  | File | When to read |
  |---|---|
  | `references/funder-alignment.md` | Step 1 — RFP parsing or manual priority mapping |
  | `references/evaluation-frameworks.md` | Step 6 — Selecting and building evaluation plan |
  | `references/budget-templates.md` | Step 7 — Budget line items and F&A calculation |
  | `references/funder-alignment.md` | Step 1 — RFP parsing or manual priority mapping |
  | `references/evaluation-frameworks.md` | Step 6 — Selecting and building evaluation plan |
  | `references/budget-templates.md` | Step 7 — Budget line items and F&A calculation |
