# Clinical Trial Protocol Skill

Generate clinical trial protocols for medical devices or drugs (phase 2 or 3). Modular waypoint-based architecture with interactive sample size calculation and research-driven recommendations.

## Overview

This Claude Code skill generates comprehensive clinical trial protocols based on NIH/FDA guidelines and similar trials research. It supports both medical devices (IDE pathway) and drugs (IND pathway) with appropriate regulatory terminology.

**Target Users:** Clinical researchers, regulatory affairs professionals, protocol writers

**Key Features:**

- Device & Drug Support - Handles both medical devices (IDE) and drugs (IND)
- Token-Efficient - Modular protocol development to stay within output limits
- Resume from Any Step - Interrupted workflows can continue from any step
- Sample Size Calculation - Interactive statistical power analysis
- Research-Driven - Leverages ClinicalTrials.gov and FDA guidance documents

## Disclaimers

> **PRELIMINARY PROTOCOL ONLY:** This protocol generation tool provides preliminary clinical study protocols based on NIH/FDA guidelines and similar trials. It does NOT constitute official FDA or IRB determination or approval.
>
> **NOT MEDICAL/LEGAL/REGULATORY ADVICE:** Generated protocols do not substitute for professional biostatistician review, FDA Pre-Submission meetings, or legal review.
>
> **PROFESSIONAL CONSULTATION REQUIRED:** Clinical trial protocols are complex, high-stakes documents requiring expertise across multiple disciplines. Professional consultation with clinical trial experts, biostatisticians, and regulatory affairs specialists is essential.

**REQUIRED before proceeding with clinical study:**

- Biostatistician review and sample size validation
- FDA Pre-Submission meeting (Q-Submission for devices, Pre-IND for drugs)
- IRB review and approval
- Clinical expert and regulatory consultant engagement
- Legal review of protocol and informed consent

## Workflow Steps

| Step | Name | Description | Output |
| ---- | ---- | ----------- | ------ |
| 0 | Initialize | Collect intervention info (device/drug, indication) | `intervention_metadata.json` |
| 1 | Research | Search ClinicalTrials.gov, find FDA guidance | `01_clinical_research_summary.json` |
| 2 | Foundation | Sections 1-6: Summary, Objectives, Design, Population | `02_protocol_foundation.md` |
| 3 | Intervention | Sections 7-8: Administration, Dose Modifications | `03_protocol_intervention.md` |
| 4 | Operations | Sections 9-12: Assessments, Statistics, Regulatory | `04_protocol_operations.md` |
| 5 | Concatenate | Combine all sections into final protocol | `protocol_complete.md` |

## Requirements

- **Python Dependencies** - `scipy`, `numpy` for sample size calculations
- **ClinicalTrials.gov MCP Server** - For searching similar trials
- **WebSearch** - For FDA guidance documents

## Getting Started

See [SKILL.md](SKILL.md) for complete installation and usage instructions.
