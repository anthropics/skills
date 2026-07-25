# 5W2H SOP Canon

Standard Operating Procedure (SOP) authoring discipline for company processes — what every SOP must contain, why, and where the discipline comes from. Eight authoritative sources cited.

## What 5W2H is

5W2H is a structured checklist for documenting *any* repeatable process by answering seven questions:

| Letter | Question | Section in `sop_generator.py` output |
|---|---|---|
| Who | Who is responsible, accountable, consulted, informed? | RACI |
| What | What is the process — inputs, outputs, scope? | Process spec |
| When | When does it run — trigger, frequency, blocking deps? | Trigger + cadence |
| Where | Where does it run — system of record, supporting tools? | System map |
| Why | Why does it exist — business purpose, regulatory basis? | Purpose + compliance |
| How | How is it executed — step-by-step procedure? | Procedure |
| How-much | How much does it cost — time, money per execution? | Cost model |

Two SOPs covering the same process can be wildly different in length and quality. They cannot be different in *coverage* if both follow 5W2H — every section is mandatory.

## Why 5W2H specifically

Three properties make 5W2H the right scaffold for an ops org:

1. **Audit-friendly.** ISO 9001 and FDA 21 CFR Part 211 auditors look for the same seven attributes whether or not they call it "5W2H". Adopting the scaffold up front means SOPs ship audit-ready.
2. **Operator-friendly.** A new ops hire reading the SOP can locate "who do I call" (Who), "when does this run" (When), and "what tells me I'm done" (How / observable success signals) without having to scan the entire doc.
3. **Author-friendly.** Empty 5W2H sections are visually obvious. "How-much" is the section authors most often forget; the scaffold prevents that.

## Eight authoritative sources

### 1. Kaoru Ishikawa — *Guide to Quality Control* (1985, Asian Productivity Organization)

Origin of the 5W1H quality-control method. The seventh question (How-much) was added by Toyota in subsequent standard-work documentation. Ishikawa's central claim: *no process description is complete until you can answer all seven questions in writing*. Anything less is tribal knowledge.

### 2. Jeffrey Liker — *The Toyota Way* (2003, McGraw-Hill)

Chapter 6 on standard work codifies the Toyota convention that every SOP documents (a) takt time, (b) work sequence, (c) standard inventory. The "How-much" anchor maps directly to takt time. Liker's argument: *standard work is the baseline from which improvement is measured*; an undocumented process cannot be improved because there is no baseline.

### 3. Atul Gawande — *The Checklist Manifesto* (2009, Metropolitan Books)

Gawande's hospital surgical-checklist research found that simple, well-owned checklists reduced surgical mortality by 47% in a 2008 WHO study across eight hospitals on four continents. Two principles transfer directly to ops SOPs: (a) *checklists must have a named owner* who is accountable for upkeep, or they rot inside 12 months, and (b) *checklist items must be observable* — "verify the patient is breathing" is bad; "pulse oximeter shows SpO2 > 92%" is good.

### 4. Atlassian — *Confluence SOP best practices* (Atlassian Team Playbook, 2023 ed.)

Atlassian's published guidance on SOP authoring in Confluence emphasizes three operational practices: (a) every SOP must declare a `last-reviewed` date; (b) the review cadence is written into the page itself; (c) "owner: alex@company.com" goes in YAML frontmatter so tooling can find SOPs with no owner. The KB hygiene anti-patterns reference draws from the same source.

### 5. ISO 9001:2015 — *Quality management systems — Requirements*

Clause 7.5.3 ("Control of documented information") requires that controlled documents include: identification (title, ID, version), format (markdown, PDF, etc.), review and approval for suitability, retention and disposition rules, and protection (access control, change history). The `regulated` profile in `sop_generator.py` adds these sections explicitly.

### 6. ITIL v4 — *Service Operation* practice guide (Axelos, 2019)

ITIL's distinction between *procedures* (the SOP — repeatable and largely unchanged) and *work instructions* (the runbook — the specific commands and observable signals at execution time) is the same distinction this skill makes. Both artifacts coexist. An SOP without a paired runbook for the steps that mutate state is incomplete.

### 7. FDA 21 CFR Part 211.100 — *Written procedures; deviations*

For pharmaceutical and medical-device-adjacent companies, Part 211.100 makes SOPs legally required. Requirements: (a) written approval before issue, (b) deviation control (any departure from the SOP must be documented and approved), (c) annual review at minimum. The `--profile regulated` flag attaches these requirements.

### 8. Project Management Institute — *PMBOK Guide* (7th ed., 2021)

PMBOK §4 on integration management defines SOP-equivalent artifacts as "organizational process assets" and requires named accountability. The RACI matrix convention (Responsible / Accountable / Consulted / Informed) used in this skill's "Who" section is the PMBOK convention.

## Anti-pattern: prose-only SOPs

A 1500-word prose SOP without the 5W2H scaffolding looks thorough and is usually missing 2-3 mandatory sections (most commonly: How-much, Why-regulatory, observable success signals). Use the generator. Edit its output. Do not write SOPs from a blank page.

## How this skill applies the canon

- `sop_generator.py` enforces all seven 5W2H sections; missing inputs are flagged in stderr.
- `--profile regulated` attaches ISO 9001 §7.5.3 + FDA Part 211 metadata (version, signoff, change history).
- Regulatory overlays (`SOC2`, `HIPAA`, `ISO13485`, `GDPR`, `SOX`) attach the specific compliance preamble each requires.
- The forcing-question library in `SKILL.md` asks the canon-anchored questions Gawande, ISO 9001, and Part 211 require before code runs.
