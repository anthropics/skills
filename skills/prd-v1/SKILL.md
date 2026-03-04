---
name: prd-v1
description: What? Generate a PRD (Product Requirements Document) for a feature (functionality) that should be built. When? Asked to generate (create) a PRD with the information that is provided, Product Strategy Document, Scope Document, Feature Document, or similar requests.
license: Complete terms in LICENSE.txt
metadata:
  version: '1.0.0'
  release-date: '2026-02-02'
---

# PRD Generator

Generate a PRD (Product Requirements Document) for a feature (functionality) that should be built.

## When to Use This Skill

Use this skill when:

- Asked to generate (create) a PRD with the information that is provided, Product Strategy Document, Scope Document, Feature Document, or similar requests.

## Role

You, agent, are an experienced product manager (product owner) who can write professional PRD (Product Requirements Document) for a feature (functionality) that should be built in a frontend/backend workspace.

## Prerequisites

**Mandatory Prerequisites**
The following prerequisite(s) are MANDATORY to check. **If not met, you MUST ask the user to provide them and STOP until provided.**

- A clear **feature description** or relevant supporting documents.

## Mandatory Agent Instructions

- You MUST use the official template structure and section order exactly as provided in the template reference.
- Do NOT add, remove, or rename sections.
- If a step (or sub step) requires user input or confirmation, you MUST ask and wait for a response before proceeding.
- Do NOT merge, skip, or improvise steps. Follow the workflow strictly.

## Workflow

1. Analyse
2. Generate Draft
3. Update Draft
4. Validate Draft
   - Review Checklist
   - Validation Process (Iterative Loop)
5. Summary

### 1. Analyse

Analyse the following documents:

- [PRD Template Reference](./references/template.md) to understand what sections the PRD should have, and also read the guidelines and descriptions mentioned in it to help you prepare the PRD draft better and fill different sections more accurately.

- User's provided 'feature description' to understand how to map it to the template.
  **If any section lacks sufficient info, specify which and request more details.**

### 2. Generate Draft

**Where to save the draft? Ask the user** for:

- Target directory. e.g., `/docs/agents/funs/`.
- File name. e.g., `PRD_{functionality-name}.md`.
  **If the file already exists, notify the user before overwriting.**

### 3. Update Draft

Update the draft using available 'feature description' and PRD template.

### 4. Validate Draft

#### Review Checklist

**Before finalization, you MUST verify the following checklist:**

Review each item and confirm that it is satisfied:

- [ ] **Do CRITICAL section(s) in the template exist in the draft**
  - ✅ Exists: "Overview" section and sub sections?
  - ✅ Exists: "Users" section and sub sections?
  - ✅ Exists: "Permissions & Security" section and sub sections?
  - ✅ Exists: "Data Requirements" section and sub sections?
  - ✅ Exists: "Functional Requirements" section and sub sections?
  - ✅ Exists: "User Experience & Flows" section and sub sections?
  - ✅ Exists: "Business Rule Breakdown" section and sub sections?
  - ✅ Exists: "Analytics & Tracking" section and sub sections?
  - ✅ Exists: "Acceptance Criteria (High‑Level)" section and sub sections?

#### Validation Process (Iterative Loop)

1. **Check all items** - Go through the entire checklist above
2. **If ANY item which required 'CRITICAL section(s) in the template to exist in the draft' is NOT checked ✅:**
   - Stop and edit the draft to fill the missing section(s)
   - **Return to step 1** (re-check the entire checklist)
3. **If ALL items are checked ✅:**
   - Present summary: "I have confirmed all requirements are met. Ready to generate the final draft."
   - Proceed to step 4 (Generate Draft)

> ⚠️ **IMPORTANT:** Do NOT proceed to Generate Draft until this validation loop confirms ALL items are ✅.

### 5. Summary

1. Present the draft to the user for review.
2. Provide a structured summary of any side-effects or follow-up actions (if any).
3. Incorporate any requested changes until the user confirms satisfaction.
