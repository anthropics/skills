---
name: ninth-circuit-brief-body
description: "Generate Ninth Circuit appellate brief body sections. This skill should be used when assembling brief sections (jurisdictional statement, issues presented, statement of case, argument, etc.) from evidence and facts. Each section is built separately and assembled into a complete brief. NO REWORDING of source material."
---

# Ninth Circuit Brief Body Generator

## Overview

Assemble appellate brief sections from evidence pool data. Each section is generated separately, validated, then combined. **CRITICAL: All text comes from source files - NO AI rewording.**

## Brief Sections (FRAP 28 Order)

| #   | Section                   | Required | Source                                  |
| --- | ------------------------- | -------- | --------------------------------------- |
| 1   | Corporate Disclosure      | Yes*     | `case_info.json`                        |
| 2   | Table of Contents         | Yes      | Auto-generated                          |
| 3   | Table of Authorities      | Yes      | `authorities.json`                      |
| 4   | Jurisdictional Statement  | Yes      | `case_info.json`                        |
| 5   | Issues Presented          | Yes      | `issues_presented.json`                 |
| 6   | Statement of the Case     | Yes      | `evidence_pool.json`                    |
| 7   | Summary of Argument       | Yes      | `arguments.json`                        |
| 8   | Argument                  | Yes      | `evidence_pool.json` + `arguments.json` |
| 9   | Conclusion                | Yes      | Template                                |
| 10  | Certificate of Compliance | Yes      | Word count                              |
| 11  | Certificate of Service    | Yes      | Template                                |

*Pro se appellants exempt from corporate disclosure

## Data Files Location

```
legal_brief_system/data/
├── case_info.json          # Case details, parties, dates
├── evidence_pool.json      # Facts with citations (EXACT TEXT)
├── authorities.json        # Cases, statutes, rules cited
├── arguments.json          # Argument structure
├── issues_presented.json   # Issues for appeal
├── timeline.json           # Chronological events
└── frap_compliance_rules.json  # Formatting rules
```

## Section Generation Workflow

### Step 1: Validate Data
```bash
python "d:\Nineth Circuit\CLAUDE_COPILOT HLP\NINTH CIR5\legal_brief_system\validate_brief.py"
```

### Step 2: Build from Evidence
```bash
python "d:\Nineth Circuit\CLAUDE_COPILOT HLP\NINTH CIR5\legal_brief_system\build_from_evidence.py"
```

### Step 3: Generate Complete Brief
```bash
python "d:\Nineth Circuit\CLAUDE_COPILOT HLP\NINTH CIR5\legal_brief_system\generate_brief.py"
```

## CRITICAL: NO REWORDING RULES

```
┌─────────────────────────────────────────────────────────────┐
│  SOURCE FILES (exact text) → ASSEMBLY ONLY → OUTPUT        │
│                                                             │
│  ✓ Read from JSON files                                     │
│  ✓ Place text in correct sections                          │
│  ✓ Add citation formatting                                  │
│  ✓ Create footnotes from cross-references                  │
│                                                             │
│  ✗ DO NOT reword facts                                      │
│  ✗ DO NOT "improve" writing                                 │
│  ✗ DO NOT summarize then expand                             │
│  ✗ DO NOT have subprocesses modify text                    │
└─────────────────────────────────────────────────────────────┘
```

## Evidence Pool Structure

Each fact in `evidence_pool.json`:
```json
{
    "id": "F001",
    "category": "arrest",
    "date": "2022-03-06",
    "statement": "EXACT TEXT - never modify",
    "record_cite": "ER-12",
    "supporting_evidence": ["E001", "E002"],
    "cross_references": ["F003", "F010"],
    "used_in_sections": ["statement_of_case", "argument_I"]
}
```

## Output Naming Convention

Files saved to: `legal_brief_system/output/`

Format: `Case_[number]_[section]_[date].docx`

Example: `Case_25-6461_Statement_of_Case_20251206.docx`

## Subprocess Rules

When using subagents or subprocesses:

1. **READ-ONLY access** to evidence files
2. Subprocesses receive **COPIES** of data, not originals
3. Output must be **VALIDATED** against source before acceptance
4. Any modification to original text = **REJECT**

## References

- `references/frap_rules.md` - FRAP formatting requirements
- `references/ninth_circuit_rules.md` - Local rules
- `references/brief_shell.md` - Section templates
