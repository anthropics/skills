# FHIR Resource Structure Examples

Complete JSON examples for common FHIR R4 resources.

## Table of Contents
- [Patient](#patient)
- [Observation (Vital Signs)](#observation-vital-signs)
- [Encounter](#encounter)
- [Condition](#condition)
- [MedicationRequest](#medicationrequest)
- [Medication](#medication)
- [OperationOutcome](#operationoutcome)
- [CapabilityStatement](#capabilitystatement)

## Patient

No required fields. All elements are optional.

```json
{
  "resourceType": "Patient",
  "id": "example",
  "meta": {"versionId": "1", "lastUpdated": "2024-01-15T10:30:00Z"},
  "identifier": [{"system": "http://hospital.example.org/mrn", "value": "12345"}],
  "name": [{"family": "Smith", "given": ["John"]}],
  "gender": "male",
  "birthDate": "1990-05-15"
}
```

## Observation (Vital Signs)

Required: `status`, `code`

```json
{
  "resourceType": "Observation",
  "status": "final",
  "category": [{"coding": [{"system": "http://terminology.hl7.org/CodeSystem/observation-category", "code": "vital-signs"}]}],
  "code": {"coding": [{"system": "http://loinc.org", "code": "8480-6", "display": "Systolic blood pressure"}]},
  "subject": {"reference": "Patient/123"},
  "effectiveDateTime": "2024-01-15T10:30:00Z",
  "valueQuantity": {"value": 120, "unit": "mmHg", "system": "http://unitsofmeasure.org", "code": "mm[Hg]"}
}
```

## Encounter

Required: `status`, `class`

**Note**: `class` uses Coding directly (NOT CodeableConcept). `subject` and `period` are optional (0..1).

```json
{
  "resourceType": "Encounter",
  "status": "in-progress",
  "class": {"system": "http://terminology.hl7.org/CodeSystem/v3-ActCode", "code": "AMB", "display": "ambulatory"},
  "subject": {"reference": "Patient/123"},
  "period": {"start": "2024-01-15T09:00:00Z"}
}
```

## Condition

Required: `subject`

**Note**: `code` and `clinicalStatus` are optional.

```json
{
  "resourceType": "Condition",
  "clinicalStatus": {"coding": [{"system": "http://terminology.hl7.org/CodeSystem/condition-clinical", "code": "active"}]},
  "verificationStatus": {"coding": [{"system": "http://terminology.hl7.org/CodeSystem/condition-ver-status", "code": "confirmed"}]},
  "code": {"coding": [{"system": "http://snomed.info/sct", "code": "73211009", "display": "Diabetes mellitus"}]},
  "subject": {"reference": "Patient/123"},
  "onsetDateTime": "2020-03-15"
}
```

## MedicationRequest

Required: `status`, `intent`, `medication[x]`, `subject`

```json
{
  "resourceType": "MedicationRequest",
  "status": "active",
  "intent": "order",
  "medicationCodeableConcept": {
    "coding": [{"system": "http://www.nlm.nih.gov/research/umls/rxnorm", "code": "1049502", "display": "Acetaminophen 325 MG"}]
  },
  "subject": {"reference": "Patient/456"},
  "authoredOn": "2024-01-15",
  "dosageInstruction": [{
    "text": "Take 2 tablets every 6 hours as needed",
    "timing": {"repeat": {"frequency": 4, "period": 1, "periodUnit": "d"}},
    "doseAndRate": [{"doseQuantity": {"value": 2, "unit": "tablet"}}]
  }]
}
```

Alternative using reference:
```json
{
  "resourceType": "MedicationRequest",
  "status": "active",
  "intent": "order",
  "medicationReference": {"reference": "Medication/123"},
  "subject": {"reference": "Patient/456"}
}
```

## Medication

No required fields.

```json
{
  "resourceType": "Medication",
  "id": "123",
  "code": {
    "coding": [{"system": "http://www.nlm.nih.gov/research/umls/rxnorm", "code": "1049502", "display": "Acetaminophen 325 MG"}]
  },
  "form": {
    "coding": [{"system": "http://snomed.info/sct", "code": "385055001", "display": "Tablet"}]
  }
}
```

## OperationOutcome

Used for all error responses.

```json
{
  "resourceType": "OperationOutcome",
  "issue": [{
    "severity": "error",
    "code": "not-found",
    "diagnostics": "Patient/999 not found"
  }]
}
```

**Severity values**: `fatal | error | warning | information`

**Code values**: `invalid | required | value | not-found | conflict | exception | processing | security | business-rule`

### Multiple Issues

```json
{
  "resourceType": "OperationOutcome",
  "issue": [
    {"severity": "error", "code": "required", "diagnostics": "Observation.status is required", "expression": ["Observation.status"]},
    {"severity": "error", "code": "required", "diagnostics": "Observation.code is required", "expression": ["Observation.code"]}
  ]
}
```

## CapabilityStatement

Returned by `/metadata` endpoint.

```json
{
  "resourceType": "CapabilityStatement",
  "status": "active",
  "date": "2024-01-15",
  "kind": "instance",
  "fhirVersion": "4.0.1",
  "format": ["json"],
  "rest": [{
    "mode": "server",
    "security": {
      "service": [{"coding": [{"system": "http://terminology.hl7.org/CodeSystem/restful-security-service", "code": "SMART-on-FHIR"}]}],
      "extension": [{
        "url": "http://fhir-registry.smarthealthit.org/StructureDefinition/oauth-uris",
        "extension": [
          {"url": "authorize", "valueUri": "https://auth.example.org/authorize"},
          {"url": "token", "valueUri": "https://auth.example.org/token"}
        ]
      }]
    },
    "resource": [{
      "type": "Patient",
      "interaction": [{"code": "read"}, {"code": "create"}, {"code": "update"}, {"code": "delete"}, {"code": "search-type"}],
      "searchParam": [
        {"name": "name", "type": "string"},
        {"name": "identifier", "type": "token"},
        {"name": "birthdate", "type": "date"}
      ]
    }]
  }]
}
```
