#!/usr/bin/env python3
"""
Spec Generator - Generates a feature specification template from a name and description.

Produces a complete spec document with all required sections pre-filled with
guidance prompts. Output can be markdown or structured JSON.

No external dependencies - uses only Python standard library.
"""

import argparse
import json
import sys
import textwrap
from datetime import date
from pathlib import Path
from typing import Dict, Any, Optional


SPEC_TEMPLATE = """\
# Spec: {name}

**Author:** [your name]
**Date:** {date}
**Status:** Draft
**Reviewers:** [list reviewers]
**Related specs:** [links to related specs, or "None"]

---

## Context

{context_prompt}

---

## Functional Requirements

_Use RFC 2119 keywords: MUST, MUST NOT, SHOULD, SHOULD NOT, MAY._
_Each requirement is a single, testable statement. Number sequentially._

- FR-1: The system MUST [describe required behavior].
- FR-2: The system MUST [describe another required behavior].
- FR-3: The system SHOULD [describe recommended behavior].
- FR-4: The system MAY [describe optional behavior].
- FR-5: The system MUST NOT [describe prohibited behavior].

---

## Non-Functional Requirements

### Performance
- NFR-P1: [Operation] MUST complete in < [threshold] (p95) under [conditions].
- NFR-P2: [Operation] SHOULD handle [throughput] requests per second.

### Security
- NFR-S1: All data in transit MUST be encrypted via TLS 1.2+.
- NFR-S2: The system MUST rate-limit [operation] to [limit] per [period] per [scope].

### Accessibility
- NFR-A1: [UI component] MUST meet WCAG 2.1 AA standards.
- NFR-A2: Error messages MUST be announced to screen readers.

### Scalability
- NFR-SC1: The system SHOULD handle [number] concurrent [entities].

### Reliability
- NFR-R1: The [service] MUST maintain [percentage]% uptime.

---

## Acceptance Criteria

_Write in Given/When/Then (Gherkin) format._
_Each criterion MUST reference at least one FR-* or NFR-*._

### AC-1: [Descriptive name] (FR-1)
Given [precondition]
When [action]
Then [expected result]
And [additional assertion]

### AC-2: [Descriptive name] (FR-2)
Given [precondition]
When [action]
Then [expected result]

### AC-3: [Descriptive name] (NFR-S2)
Given [precondition]
When [action]
Then [expected result]
And [additional assertion]

---

## Edge Cases

_For every external dependency (API, database, file system, user input), specify at least one failure scenario._

- EC-1: [Input/condition] -> [expected behavior].
- EC-2: [Input/condition] -> [expected behavior].
- EC-3: [External service] is unavailable -> [expected behavior].
- EC-4: [Concurrent/race condition] -> [expected behavior].
- EC-5: [Boundary value] -> [expected behavior].

---

## API Contracts

_Define request/response shapes using TypeScript-style notation._
_Cover all endpoints referenced in functional requirements._

### [METHOD] [endpoint]

Request:
```typescript
interface [Name]Request {{
  field: string;       // Description, constraints
  optional?: number;   // Default: [value]
}}
```

Success Response ([status code]):
```typescript
interface [Name]Response {{
  id: string;
  field: string;
  createdAt: string;   // ISO 8601
}}
```

Error Response ([status code]):
```typescript
interface [Name]Error {{
  error: "[ERROR_CODE]";
  message: string;
}}
```

---

## Data Models

_Define all entities referenced in requirements._

### [Entity Name]
| Field | Type | Constraints |
|-------|------|-------------|
| id | UUID | Primary key, auto-generated |
| [field] | [type] | [constraints] |
| createdAt | timestamp | UTC, immutable |
| updatedAt | timestamp | UTC, auto-updated |

---

## Out of Scope

_Explicit exclusions prevent scope creep. If someone asks for these during implementation, point them here._

- OS-1: [Feature/capability] — [reason for exclusion or link to future spec].
- OS-2: [Feature/capability] — [reason for exclusion].
- OS-3: [Feature/capability] — deferred to [version/sprint].

---

## Open Questions

_Track unresolved questions here. Each must be resolved before status moves to "Approved"._

- [ ] Q1: [Question] — Owner: [name], Due: [date]
- [ ] Q2: [Question] — Owner: [name], Due: [date]
"""


def generate_context_prompt(description: str) -> str:
    """Generate a context section prompt based on the provided description."""
    if description:
        return textwrap.dedent(f"""\
            {description}

            _Expand this context section to include:_
            _- Why does this feature exist? What problem does it solve?_
            _- What is the business motivation? (link to user research, support tickets, metrics)_
            _- What is the current state? (what exists today, what pain points exist)_
            _- 2-4 paragraphs maximum._""")
    return textwrap.dedent("""\
        _Why does this feature exist? What problem does it solve? What is the business
        motivation? Include links to user research, support tickets, or metrics that
        justify this work. 2-4 paragraphs maximum._""")


def generate_spec(name: str, description: str) -> str:
    """Generate a spec document from name and description."""
    context_prompt = generate_context_prompt(description)
    return SPEC_TEMPLATE.format(
        name=name,
        date=date.today().isoformat(),
        context_prompt=context_prompt,
    )


def generate_spec_json(name: str, description: str) -> Dict[str, Any]:
    """Generate structured JSON representation of the spec template."""
    return {
        "spec": {
            "title": f"Spec: {name}",
            "metadata": {
                "author": "[your name]",
                "date": date.today().isoformat(),
                "status": "Draft",
                "reviewers": [],
                "related_specs": [],
            },
            "context": description or "[Describe why this feature exists]",
            "functional_requirements": [
                {"id": "FR-1", "keyword": "MUST", "description": "[describe required behavior]"},
                {"id": "FR-2", "keyword": "MUST", "description": "[describe another required behavior]"},
                {"id": "FR-3", "keyword": "SHOULD", "description": "[describe recommended behavior]"},
                {"id": "FR-4", "keyword": "MAY", "description": "[describe optional behavior]"},
                {"id": "FR-5", "keyword": "MUST NOT", "description": "[describe prohibited behavior]"},
            ],
            "non_functional_requirements": {
                "performance": [
                    {"id": "NFR-P1", "description": "[operation] MUST complete in < [threshold]"},
                ],
                "security": [
                    {"id": "NFR-S1", "description": "All data in transit MUST be encrypted via TLS 1.2+"},
                ],
                "accessibility": [
                    {"id": "NFR-A1", "description": "[UI component] MUST meet WCAG 2.1 AA"},
                ],
                "scalability": [
                    {"id": "NFR-SC1", "description": "[system] SHOULD handle [N] concurrent [entities]"},
                ],
                "reliability": [
                    {"id": "NFR-R1", "description": "[service] MUST maintain [N]% uptime"},
                ],
            },
            "acceptance_criteria": [
                {
                    "id": "AC-1",
                    "name": "[descriptive name]",
                    "references": ["FR-1"],
                    "given": "[precondition]",
                    "when": "[action]",
                    "then": "[expected result]",
                },
            ],
            "edge_cases": [
                {"id": "EC-1", "condition": "[input/condition]", "behavior": "[expected behavior]"},
            ],
            "api_contracts": [
                {
                    "method": "[METHOD]",
                    "endpoint": "[/api/path]",
                    "request_fields": [{"name": "field", "type": "string", "constraints": "[description]"}],
                    "success_response": {"status": 200, "fields": []},
                    "error_response": {"status": 400, "fields": []},
                },
            ],
            "data_models": [
                {
                    "name": "[Entity]",
                    "fields": [
                        {"name": "id", "type": "UUID", "constraints": "Primary key, auto-generated"},
                    ],
                },
            ],
            "out_of_scope": [
                {"id": "OS-1", "description": "[feature/capability]", "reason": "[reason]"},
            ],
            "open_questions": [],
        },
        "metadata": {
            "generated_by": "spec_generator.py",
            "feature_name": name,
            "feature_description": description,
        },
    }


def main():
    parser = argparse.ArgumentParser(
        description="Generate a feature specification template from a name and description.",
        epilog="Example: python spec_generator.py --name 'User Auth' --description 'OAuth 2.0 login flow'",
    )
    parser.add_argument(
        "--name",
        required=True,
        help="Feature name (used as spec title)",
    )
    parser.add_argument(
        "--description",
        default="",
        help="Brief feature description (used to seed the context section)",
    )
    parser.add_argument(
        "--output",
        "-o",
        default=None,
        help="Output file path (default: stdout)",
    )
    parser.add_argument(
        "--format",
        choices=["md", "json"],
        default="md",
        help="Output format: md (markdown) or json (default: md)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        dest="json_flag",
        help="Shorthand for --format json",
    )

    args = parser.parse_args()

    output_format = "json" if args.json_flag else args.format

    if output_format == "json":
        result = generate_spec_json(args.name, args.description)
        output = json.dumps(result, indent=2)
    else:
        output = generate_spec(args.name, args.description)

    if args.output:
        out_path = Path(args.output)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(output, encoding="utf-8")
        print(f"Spec template written to {out_path}", file=sys.stderr)
    else:
        print(output)

    sys.exit(0)


if __name__ == "__main__":
    main()
