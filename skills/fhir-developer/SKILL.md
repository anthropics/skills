---
license: Provided under Anthropic's Terms of Service (not the Apache-2.0 LICENSE.txt used by most skills in this repo) — see NOTICE.md
source: https://github.com/anthropics/healthcare/tree/main/plugins/healthcare/skills/fhir-developer
name: fhir-developer-skill
description: >
  FHIR API development guide for building healthcare endpoints. Use when: (1) Creating
  FHIR REST endpoints (Patient, Observation, Encounter, Condition, MedicationRequest),
  (2) Validating FHIR resources and returning proper HTTP status codes and error responses,
  (3) Implementing SMART on FHIR authorization and OAuth scopes, (4) Working with Bundles,
  transactions, batch operations, or search pagination. Covers FHIR R4 resource structures,
  required fields, value sets (status codes, gender, intent), coding systems (LOINC, SNOMED,
  RxNorm, ICD-10), and OperationOutcome error handling.
---

# FHIR Developer Skill

## Quick Reference

### HTTP Status Codes
| Code | When to Use |
|------|-------------|
| `200 OK` | Successful read, update, or search |
| `201 Created` | Successful create (include `Location` header) |
| `204 No Content` | Successful delete |
| `400 Bad Request` | Malformed JSON, wrong resourceType |
| `401 Unauthorized` | Missing, expired, revoked, or malformed token (RFC 6750) |
| `403 Forbidden` | Valid token but insufficient scopes |
| `404 Not Found` | Resource doesn't exist |
| `412 Precondition Failed` | If-Match ETag mismatch (NOT 400!) |
| `422 Unprocessable Entity` | Missing required fields, invalid enum values, business rule violations |

### Required Fields by Resource (FHIR R4)
| Resource | Required Fields | Everything Else |
|----------|-----------------|-----------------|
| Patient | *(none)* | All optional |
| Observation | `status`, `code` | Optional |
| Encounter | `status`, `class` | Optional (including `subject`, `period`) |
| Condition | `subject` | Optional (including `code`, `clinicalStatus`) |
| MedicationRequest | `status`, `intent`, `medication[x]`, `subject` | Optional |
| Medication | *(none)* | All optional |
| Bundle | `type` | Optional |

---

## Required vs Optional Fields (CRITICAL)

**Only validate fields with cardinality starting with "1" as required.**

| Cardinality | Required? |
|-------------|-----------|
| `0..1`, `0..*` | NO |
| `1..1`, `1..*` | YES |

**Common mistake**: Making `subject` or `period` required on Encounter. They are 0..1 (optional).

---

## Value Sets (Enum Values)

Invalid enum values must return `422 Unprocessable Entity`.

### Patient.gender
`male | female | other | unknown`

### Observation.status
`registered | preliminary | final | amended | corrected | cancelled | entered-in-error | unknown`

### Encounter.status
`planned | arrived | triaged | in-progress | onleave | finished | cancelled | entered-in-error | unknown`

### Encounter.class (Common Codes)
| Code | Display | Use |
|------|---------|-----|
| `AMB` | ambulatory | Outpatient visits |
| `IMP` | inpatient encounter | Hospital admissions |
| `EMER` | emergency | Emergency department |
| `VR` | virtual | Telehealth |

### Condition.clinicalStatus
`active | recurrence | relapse | inactive | remission | resolved`

### Condition.verificationStatus
`unconfirmed | provisional | differential | confirmed | refuted | entered-in-error`

### MedicationRequest.status
`active | on-hold | cancelled | completed | entered-in-error | stopped | draft | unknown`

### MedicationRequest.intent
`proposal | plan | order | original-order | reflex-order | filler-order | instance-order | option`

### Bundle.type
`document | message | transaction | transaction-response | batch | batch-response | history | searchset | collection`

---

## Validation Pattern

**Python/FastAPI:**
```python
from fastapi import FastAPI
from fastapi.responses import JSONResponse

app = FastAPI()

def operation_outcome(severity: str, code: str, diagnostics: str):
    return {
        "resourceType": "OperationOutcome",
        "issue": [{"severity": severity, "code": code, "diagnostics": diagnostics}]
    }

VALID_OBS_STATUS = {"registered", "preliminary", "final", "amended",
                    "corrected", "cancelled", "entered-in-error", "unknown"}

@app.post("/Observation", status_code=201)
async def create_observation(data: dict):
    if not data.get("status"):
        return JSONResponse(status_code=422, content=operation_outcome(
            "error", "required", "Observation.status is required"
        ), media_type="application/fhir+json")

    if data["status"] not in VALID_OBS_STATUS:
        return JSONResponse(status_code=422, content=operation_outcome(
            "error", "value", f"Invalid status '{data['status']}'"
        ), media_type="application/fhir+json")
    # ... create resource
```

**TypeScript/Express:**
```typescript
const VALID_OBS_STATUS = new Set(['registered', 'preliminary', 'final', 'amended',
  'corrected', 'cancelled', 'entered-in-error', 'unknown']);

app.post('/Observation', (req, res) => {
  if (!req.body.status) {
    return res.status(422).contentType('application/fhir+json')
      .json(operationOutcome('error', 'required', 'Observation.status is required'));
  }
  if (!VALID_OBS_STATUS.has(req.body.status)) {
    return res.status(422).contentType('application/fhir+json')
      .json(operationOutcome('error', 'value', `Invalid status '${req.body.status}'`));
  }
  // ... create resource
});
```

**Pydantic v2 Models** (use `Literal`, not `const=True`):
```python
from typing import Literal
from pydantic import BaseModel

class Patient(BaseModel):
    resourceType: Literal["Patient"] = "Patient"
    id: str | None = None
    gender: Literal["male", "female", "other", "unknown"] | None = None
```

---

## Coding Systems (URLs)

| System | URL |
|--------|-----|
| LOINC | `http://loinc.org` |
| SNOMED CT | `http://snomed.info/sct` |
| RxNorm | `http://www.nlm.nih.gov/research/umls/rxnorm` |
| ICD-10 | `http://hl7.org/fhir/sid/icd-10` |
| v3-ActCode | `http://terminology.hl7.org/CodeSystem/v3-ActCode` |
| Observation Category | `http://terminology.hl7.org/CodeSystem/observation-category` |
| Condition Clinical | `http://terminology.hl7.org/CodeSystem/condition-clinical` |
| Condition Ver Status | `http://terminology.hl7.org/CodeSystem/condition-ver-status` |

### Common LOINC Codes (Vital Signs)
| Code | Description |
|------|-------------|
| `8867-4` | Heart rate |
| `8480-6` | Systolic blood pressure |
| `8462-4` | Diastolic blood pressure |
| `8310-5` | Body temperature |
| `2708-6` | Oxygen saturation (SpO2) |

---

## Data Type Patterns

### Coding (direct) vs CodeableConcept (wrapped)

**Coding** - Used by `Encounter.class`:
```json
{"system": "http://terminology.hl7.org/CodeSystem/v3-ActCode", "code": "AMB"}
```

**CodeableConcept** - Used by `Observation.code`, `Condition.code`:
```json
{"coding": [{"system": "http://loinc.org", "code": "8480-6"}], "text": "Systolic BP"}
```

### Reference
```json
{"reference": "Patient/123", "display": "John Smith"}
```

### Identifier
```json
{"system": "http://hospital.example.org/mrn", "value": "12345"}
```

---

## Common Mistakes

| Mistake | Correct Approach |
|---------|------------------|
| Making `subject` or `period` required on Encounter | Both are 0..1 (optional). Only `status` and `class` are required |
| Using CodeableConcept for `Encounter.class` | `class` uses Coding directly: `{"system": "...", "code": "AMB"}` |
| Returning 400 for ETag mismatch | Use `412 Precondition Failed` for If-Match failures |
| Returning 400 for invalid enum values | Use `422 Unprocessable Entity` for validation errors |
| Forgetting Content-Type header | Always set `Content-Type: application/fhir+json` |
| Missing Location header on create | Return `Location: /Patient/{id}` with 201 Created |

---

## Resource Structures

For complete JSON examples of all resources, see **[references/resource-examples.md](references/resource-examples.md)**.

Quick reference for error responses:

```json
{
  "resourceType": "OperationOutcome",
  "issue": [{"severity": "error", "code": "not-found", "diagnostics": "Patient/123 not found"}]
}
```

---

## RESTful Endpoints

```
POST   /[ResourceType]              # Create (returns 201 + Location header)
GET    /[ResourceType]/[id]         # Read
PUT    /[ResourceType]/[id]         # Update
DELETE /[ResourceType]/[id]         # Delete (returns 204)
GET    /[ResourceType]?param=value  # Search (returns Bundle)
GET    /metadata                    # CapabilityStatement
POST   /                            # Bundle transaction/batch
```

---

## Conditional Operations

**If-Match** (optimistic locking):
- Client sends: `If-Match: W/"1"`
- Mismatch returns `412 Precondition Failed`

**If-None-Exist** (conditional create):
- Client sends: `If-None-Exist: identifier=http://mrn|12345`
- Match exists: return existing (200)
- No match: create new (201)

---

## Reference Files

For detailed guidance, see:

- **[Resource Examples](references/resource-examples.md)**: Complete JSON structures for Patient, Observation, Encounter, Condition, MedicationRequest, OperationOutcome, CapabilityStatement
- **[SMART on FHIR Authorization](references/smart-auth.md)**: OAuth flows, scope syntax (v1/v2), backend services, scope enforcement
- **[Pagination](references/pagination.md)**: Search result pagination, `_count`/`_offset` parameters, link relations
- **[Bundle Operations](references/bundles.md)**: Transaction vs batch semantics, atomicity, processing order

---

## Implementation Checklist

1. Set `Content-Type: application/fhir+json` on all responses
2. Return `meta.versionId` and `meta.lastUpdated` on resources
3. Return `Location` header on create: `/Patient/{id}`
4. Return `ETag` header: `W/"{versionId}"`
5. Use OperationOutcome for all error responses
6. Validate required fields → 422 for missing
7. Validate enum values → 422 for invalid
8. Search returns Bundle with `type: "searchset"`

---

## Quick Start Script

To scaffold a new FHIR API project with correct Pydantic v2 patterns:

```bash
python scripts/setup_fhir_project.py my_fhir_api
```

Creates a FastAPI project with correct models, OperationOutcome helpers, and Patient CRUD endpoints.
