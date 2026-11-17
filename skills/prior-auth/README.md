# Prior Authorization Review Skill

Automate payer review of prior authorization requests using AI-powered clinical reasoning and coverage policy matching to aid the payer's determination and workflow.

## Overview

This Claude Code skill helps automate the health insurance payer professional's prior authorization (PA) review process. It processes incoming PA requests from healthcare providers, validates medical necessity against coverage policies, and generates proposed authorization decisions with complete documentation for the professional's review and sign-off.

**Target Users:** Health insurance payer organizations (Medicare Advantage, Commercial, Medicaid MCOs)

**Value Proposition:**

- Consistent, auditable decision-making
- Structured documentation for review processes
- Free clinical reviewers to focus on complex cases

## Important Disclaimers

> **DRAFT RECOMMENDATIONS ONLY:** This skill generates draft recommendations only. The payer organization remains fully responsible for all final authorization decisions.
>
> **HUMAN REVIEW REQUIRED:** All AI-generated recommendations require review and confirmation by appropriate professionals before becoming final decisions. Users may accept, reject, or override any recommendation with documented justification.
>
> **AI DECISION BEHAVIOR:** In default mode, AI recommends APPROVE or PEND only - never recommends DENY. Decision logic is configurable in the skill's rubric.md file.
>
> **COVERAGE POLICY LIMITATIONS:** Coverage policies are sourced from Medicare LCDs/NCDs via CMS Coverage MCP Connector. If this review is for a commercial or Medicare Advantage plan, payer-specific policies may differ and were not applied.

## Subskill 1: Intake & Assessment

**Purpose:** Collect prior authorization request information, validate credentials and codes, extract clinical data, identify applicable coverage policies, assess medical necessity, and generate approval recommendation.

**What it does:**

- Collects PA request details (member, service, provider, clinical documentation)
- Validates provider credentials via NPI MCP Connector
- Validates ICD-10 codes via ICD-10 MCP Connector (batch validation)
- Validates CPT/HCPCS codes via WebFetch to CMS Fee Schedule
- Searches coverage policies via CMS Coverage MCP Connector
- Extracts structured clinical data from documentation
- Maps clinical evidence to policy criteria
- Performs medical necessity assessment
- Generates recommendation (APPROVE/PEND)

**Output:** `waypoints/assessment.json` - Consolidated assessment with recommendation

**Human Decision Point:** After assessment is generated, the professional reviews the AI recommendation and supporting evidence before proceeding to the decision phase.

## Subskill 2: Decision & Notification

**Purpose:** Finalize authorization decision with human oversight and generate provider notification.

**What it does:**

- Loads assessment from Subskill 1
- Presents recommendation for human review
- Human actively confirms, rejects, or overrides the recommendation
- Generates authorization number (if approved) or documentation requests (if pended)
- Creates provider notification letter
- Documents complete audit trail

**Output:**

- `waypoints/decision.json` - Final decision record
- `outputs/notification_letter.txt` - Provider notification

**Human Decision Point:** The professional must explicitly confirm, reject, or override the AI recommendation. No decision is finalized without human action.

## Installation

See [SKILL.md](SKILL.md) for complete installation and usage instructions.

## Sample Data

Sample case files are included in `assets/sample/` for demonstration purposes. When using sample files, the skill operates in demo mode which:

- Skips NPI MCP lookup for the sample provider only
- Executes all other MCP calls (ICD-10, CMS Coverage) normally
- Demonstrates the complete workflow with a pre-configured lung biopsy case
