# <系统名> Requirements Specification

> This document consolidates the full set of requirements analysis deliverables. Every requirement in each section must cite an `A-xx` (confirmed fact) from the interview records; any item without `A-xx` support must be explicitly marked as `S-xx` (assumption) and must state its verification method and the consequences if it proves false.

## Document Information

| Item | Content |
|---|---|
| System Name | |
| Version | |
| Author / Date | |
| Analysis Scope | The business scope covered in this analysis |
| Tailoring Notes | Which tasks were cut out and why (per the tailoring table in `references/task-playbook.md`) |

---

## 1. Objective Description

> Source: problem cards. One card per target scenario.

### 1.1 One-Sentence Objective

Measure + effect structure.

### 1.2 Problem Cards

For each card: problem description (business fact + business consequence), frequency, aversion, substitutability, candidate solutions, expected outcome, value proposition.

(See `<系统名>_problem-cards.md` for details.)

---

## 2. Stakeholders and Their Needs

### 2.1 Stakeholder List

Type, name, description, relevance, impact.

### 2.2 Stakeholder Profile

One card per key stakeholder: basic information / core concerns (positive requirements) / blockers (negative requirements) / remarks.

### 2.3 Conflicts of Concerns and How to Handle Them

Cross-cutting conflicts identified + coping strategies.

---

## 3. Business Subsystems and Interfaces

### 3.1 Business Subsystem Breakdown

Diagram (hierarchy diagram / component diagram / data flow diagram) + business subsystem descriptions (name, type, description).

### 3.2 Business Interfaces

Service interface descriptions (interface, provider, consumer, description) + business interface analysis (overview, interaction process and data packets, design constraints).

---

## 4. Business Processes and Business Scenarios

### 4.1 Business Process List

Type, process name, brief description, priority.

### 4.2 Business Process Diagrams

Department-level granularity, reflecting the eight elements.

### 4.3 Business Scenarios

Role: business scenario (verb-object format), type, brief description, priority.

### 4.4 Business Scenario Analysis

For each scenario: scenario overview / scenario analysis (scenario—challenge—solution) / key exceptions.

---

## 5. Functional Requirements

> Derived from the business scenario analysis. Tag every requirement with its source scenario.

| ID | Functional Requirement | Source Scenario | Priority | Traceability |
|---|---|---|---|---|
| F-01 | | | | A-xx |

---

## 6. Data Requirements

### 6.1 Domain Model

System domain class diagram + key fields of each domain class.

### 6.2 Business Data Description

For each business data item: data composition analysis / relationship between data and process / data characteristics.

### 6.3 Data Rules

---

## 7. Non-functional Requirements

### 7.1 Key Quality Requirement List

Quality goal type / sub-category / description, ordered by risk exposure.

### 7.2 Quality Scenario Decision Cards

Goal / scenario / strategy / risk / conflict trade-off.

### 7.3 Business Rules

Grouped by scope and type, with business motivation and feasibility.

### 7.4 Constraints

Project constraints, design constraints.

---

## 8. Management Support

### 8.1 Control Point List

### 8.2 Control Point Analysis

### 8.3 Business Report Description

---

## 9. Maintenance Support

Maintenance scenarios and the support they require.

---

## 10. Requirement Priority Assessment

| Requirement | Assessment Dimension | Assessment Result | Conclusion | Basis |
|---|---|---|---|---|

The conclusion must be one of **Must do / Should do / Could do / Won't do**.

---

## Appendix A. Glossary

| Term | Definition | Source |
|---|---|---|

## Appendix B. Interview Record Index

| ID | Content | Status |
|---|---|---|
| A-xx | Confirmed fact | Confirmed |
| S-xx | Assumption | Pending verification — verification method / owner / consequence if it fails |
| T-xx | Term definition | Clarified |
