# FHIR Bundle Operations: Batch vs Transaction

## Table of Contents
- [Key Differences](#key-differences)
- [Transaction Bundle](#transaction-bundle)
- [Batch Bundle](#batch-bundle)
- [Processing Order](#processing-order)

## Key Differences

| Feature | Transaction | Batch |
|---------|-------------|-------|
| Atomicity | **All-or-nothing** | Independent entries |
| Failure handling | Entire bundle fails | Partial success allowed |
| Use case | Related data that must succeed together | Independent operations |
| Response | Single success/failure | Per-entry status |

## Transaction Bundle

All entries succeed together, or all fail. Use for related data.

**Request:**
```json
{
  "resourceType": "Bundle",
  "type": "transaction",
  "entry": [
    {
      "fullUrl": "urn:uuid:patient-1",
      "resource": {
        "resourceType": "Patient",
        "name": [{"family": "Smith", "given": ["John"]}]
      },
      "request": {
        "method": "POST",
        "url": "Patient"
      }
    },
    {
      "fullUrl": "urn:uuid:observation-1",
      "resource": {
        "resourceType": "Observation",
        "status": "final",
        "code": {"coding": [{"system": "http://loinc.org", "code": "8480-6"}]},
        "subject": {"reference": "urn:uuid:patient-1"}
      },
      "request": {
        "method": "POST",
        "url": "Observation"
      }
    }
  ]
}
```

**Success Response (200 OK):**
```json
{
  "resourceType": "Bundle",
  "type": "transaction-response",
  "entry": [
    {
      "fullUrl": "https://fhir.example.org/Patient/123",
      "response": {
        "status": "201 Created",
        "location": "Patient/123/_history/1",
        "etag": "W/\"1\""
      }
    },
    {
      "fullUrl": "https://fhir.example.org/Observation/456",
      "response": {
        "status": "201 Created",
        "location": "Observation/456/_history/1",
        "etag": "W/\"1\""
      }
    }
  ]
}
```

**Failure Response (400 Bad Request):** Entire transaction rolled back
```json
{
  "resourceType": "OperationOutcome",
  "issue": [{
    "severity": "error",
    "code": "required",
    "diagnostics": "Observation.status is required",
    "expression": ["Bundle.entry[1].resource"]
  }]
}
```

## Batch Bundle

Each entry processed independently. Partial success allowed.

**Request:**
```json
{
  "resourceType": "Bundle",
  "type": "batch",
  "entry": [
    {
      "request": {"method": "GET", "url": "Patient/123"}
    },
    {
      "request": {"method": "GET", "url": "Patient/999"}
    },
    {
      "resource": {
        "resourceType": "Observation",
        "status": "final",
        "code": {"coding": [{"system": "http://loinc.org", "code": "8480-6"}]}
      },
      "request": {"method": "POST", "url": "Observation"}
    }
  ]
}
```

**Response (200 OK with mixed results):**
```json
{
  "resourceType": "Bundle",
  "type": "batch-response",
  "entry": [
    {
      "resource": {"resourceType": "Patient", "id": "123"},
      "response": {"status": "200 OK"}
    },
    {
      "response": {
        "status": "404 Not Found",
        "outcome": {
          "resourceType": "OperationOutcome",
          "issue": [{"severity": "error", "code": "not-found"}]
        }
      }
    },
    {
      "response": {
        "status": "201 Created",
        "location": "Observation/789/_history/1"
      }
    }
  ]
}
```

## Processing Order

Transactions are processed in this order (regardless of entry order):
1. DELETE
2. POST
3. PUT/PATCH
4. GET

This allows references to work correctly within a transaction.
