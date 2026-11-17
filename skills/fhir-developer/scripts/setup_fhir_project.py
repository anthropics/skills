#!/usr/bin/env python3
"""FHIR API Project Scaffold - Creates a working FHIR API structure with correct patterns."""

import argparse
import subprocess
import sys
from pathlib import Path

def create_project(project_dir: Path):
    """Create FHIR API project structure with correct Pydantic v2 patterns."""

    # Create directories
    (project_dir / "app" / "models").mkdir(parents=True, exist_ok=True)
    (project_dir / "app" / "routes").mkdir(parents=True, exist_ok=True)
    (project_dir / "tests").mkdir(parents=True, exist_ok=True)

    # requirements.txt
    (project_dir / "requirements.txt").write_text(
        "fastapi>=0.100.0\nuvicorn>=0.23.0\npydantic>=2.0.0\nhttpx>=0.24.0\npytest>=7.0.0\n"
    )

    # app/__init__.py
    (project_dir / "app" / "__init__.py").touch()
    (project_dir / "app" / "models" / "__init__.py").touch()
    (project_dir / "app" / "routes" / "__init__.py").touch()

    # Core FHIR types with Pydantic v2 syntax
    (project_dir / "app" / "models" / "fhir_types.py").write_text('''"""FHIR R4 Base Types - Pydantic v2"""
from typing import Literal
from pydantic import BaseModel, Field
from datetime import datetime
import uuid

class Meta(BaseModel):
    versionId: str = "1"
    lastUpdated: str = Field(default_factory=lambda: datetime.utcnow().isoformat() + "Z")

class HumanName(BaseModel):
    family: str | None = None
    given: list[str] | None = None

class Coding(BaseModel):
    system: str | None = None
    code: str | None = None
    display: str | None = None

class CodeableConcept(BaseModel):
    coding: list[Coding] | None = None
    text: str | None = None

class Reference(BaseModel):
    reference: str | None = None
    display: str | None = None

class Quantity(BaseModel):
    value: float | None = None
    unit: str | None = None
    system: str | None = "http://unitsofmeasure.org"
    code: str | None = None

class Patient(BaseModel):
    resourceType: Literal["Patient"] = "Patient"
    id: str | None = Field(default_factory=lambda: str(uuid.uuid4()))
    meta: Meta | None = None
    name: list[HumanName] | None = None
    gender: Literal["male", "female", "other", "unknown"] | None = None
    birthDate: str | None = None

class Observation(BaseModel):
    resourceType: Literal["Observation"] = "Observation"
    id: str | None = Field(default_factory=lambda: str(uuid.uuid4()))
    meta: Meta | None = None
    status: Literal["registered", "preliminary", "final", "amended", "corrected", "cancelled", "entered-in-error", "unknown"]
    category: list[CodeableConcept] | None = None
    code: CodeableConcept
    subject: Reference | None = None
    valueQuantity: Quantity | None = None

class BundleEntry(BaseModel):
    fullUrl: str | None = None
    resource: dict | None = None

class Bundle(BaseModel):
    resourceType: Literal["Bundle"] = "Bundle"
    type: Literal["searchset", "batch", "transaction", "batch-response", "transaction-response", "collection", "document", "message", "history"]
    total: int | None = None
    entry: list[BundleEntry] | None = None

class OperationOutcomeIssue(BaseModel):
    severity: Literal["fatal", "error", "warning", "information"]
    code: str
    diagnostics: str | None = None

class OperationOutcome(BaseModel):
    resourceType: Literal["OperationOutcome"] = "OperationOutcome"
    issue: list[OperationOutcomeIssue]
''')

    # Helpers
    (project_dir / "app" / "helpers.py").write_text('''"""FHIR Response Helpers"""
from fastapi.responses import JSONResponse
from app.models.fhir_types import OperationOutcome, OperationOutcomeIssue

def operation_outcome(status_code: int, severity: str, code: str, diagnostics: str) -> JSONResponse:
    """Return a FHIR OperationOutcome error response."""
    return JSONResponse(
        status_code=status_code,
        content=OperationOutcome(
            issue=[OperationOutcomeIssue(severity=severity, code=code, diagnostics=diagnostics)]
        ).model_dump(exclude_none=True),
        media_type="application/fhir+json"
    )

def fhir_response(content: dict, status_code: int = 200, headers: dict = None) -> JSONResponse:
    """Return a FHIR JSON response with correct content-type."""
    return JSONResponse(
        status_code=status_code,
        content=content,
        headers=headers,
        media_type="application/fhir+json"
    )
''')

    # Main app
    (project_dir / "app" / "main.py").write_text('''"""FHIR R4 API Server"""
from fastapi import FastAPI
from app.routes import patient

app = FastAPI(title="FHIR R4 API", version="1.0.0")
app.include_router(patient.router)

@app.get("/metadata")
def capability_statement():
    return {
        "resourceType": "CapabilityStatement",
        "status": "active",
        "kind": "instance",
        "fhirVersion": "4.0.1",
        "format": ["json"],
        "rest": [{"mode": "server", "resource": [
            {"type": "Patient", "interaction": [{"code": "read"}, {"code": "create"}, {"code": "update"}, {"code": "delete"}, {"code": "search-type"}]}
        ]}]
    }
''')

    # Patient routes
    (project_dir / "app" / "routes" / "patient.py").write_text('''"""Patient CRUD Endpoints"""
from fastapi import APIRouter, Response, status
from app.models.fhir_types import Patient, Bundle, BundleEntry, Meta
from app.helpers import operation_outcome, fhir_response

router = APIRouter()
patients: dict[str, Patient] = {}

@router.post("/Patient", status_code=status.HTTP_201_CREATED)
def create_patient(patient: Patient, response: Response):
    patient.meta = Meta()
    patients[patient.id] = patient
    response.headers["Location"] = f"/Patient/{patient.id}"
    response.headers["ETag"] = f'W/"{patient.meta.versionId}"'
    return fhir_response(patient.model_dump(exclude_none=True), 201)

@router.get("/Patient/{patient_id}")
def read_patient(patient_id: str):
    if patient_id not in patients:
        return operation_outcome(404, "error", "not-found", f"Patient/{patient_id} not found")
    return fhir_response(patients[patient_id].model_dump(exclude_none=True))

@router.put("/Patient/{patient_id}")
def update_patient(patient_id: str, patient: Patient):
    if patient_id not in patients:
        return operation_outcome(404, "error", "not-found", f"Patient/{patient_id} not found")
    patient.id = patient_id
    patient.meta = Meta(versionId=str(int(patients[patient_id].meta.versionId) + 1))
    patients[patient_id] = patient
    return fhir_response(patient.model_dump(exclude_none=True))

@router.delete("/Patient/{patient_id}", status_code=status.HTTP_204_NO_CONTENT)
def delete_patient(patient_id: str):
    if patient_id not in patients:
        return operation_outcome(404, "error", "not-found", f"Patient/{patient_id} not found")
    del patients[patient_id]

@router.get("/Patient")
def search_patients(name: str = None, gender: str = None):
    results = list(patients.values())
    if name:
        results = [p for p in results if any(name.lower() in (n.family or "").lower() for n in (p.name or []))]
    if gender:
        results = [p for p in results if p.gender == gender]
    return fhir_response(Bundle(
        type="searchset", total=len(results),
        entry=[BundleEntry(fullUrl=f"/Patient/{p.id}", resource=p.model_dump(exclude_none=True)) for p in results]
    ).model_dump(exclude_none=True))
''')

    # Basic test
    (project_dir / "tests" / "test_patient.py").write_text('''"""Patient API Tests"""
from fastapi.testclient import TestClient
from app.main import app

client = TestClient(app)

def test_create_patient():
    r = client.post("/Patient", json={"resourceType": "Patient", "name": [{"family": "Smith"}], "gender": "male"})
    assert r.status_code == 201
    assert "Location" in r.headers

def test_read_not_found():
    r = client.get("/Patient/nonexistent")
    assert r.status_code == 404
    assert r.json()["resourceType"] == "OperationOutcome"

def test_search():
    r = client.get("/Patient")
    assert r.status_code == 200
    assert r.json()["resourceType"] == "Bundle"
''')

    print(f"Created FHIR API project: {project_dir}")
    print(f"\nNext steps:")
    print(f"  cd {project_dir}")
    print(f"  python -m venv venv && source venv/bin/activate")
    print(f"  pip install -r requirements.txt")
    print(f"  uvicorn app.main:app --reload")
    print(f"\nOpen http://localhost:8000/docs for API docs")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Create FHIR API project scaffold")
    parser.add_argument("project_name", nargs="?", default="fhir_api", help="Project directory name")
    args = parser.parse_args()
    create_project(Path(args.project_name))
