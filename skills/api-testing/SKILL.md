---
name: api-testing
description: Generate integration tests for REST and GraphQL APIs from API docs (OpenAPI/Swagger/Postman),
  covering HTTP methods, status codes, auth, and parameter validation.
allowed-tools: Read, Write, Edit, Bash, Grep, Glob
---

# API Testing Skill

## Purpose

This skill generates integration tests for APIs, covering all HTTP methods, success/error status codes, auth and auth failure, request/response validation, and error handling.

## Use Cases

- **Generate tests from API docs**: Generate tests for REST APIs; supports OpenAPI 2.0/3.x (Swagger), Postman Collection — use scripts in this directory's `scripts/` to obtain endpoint inventory first
- Generate tests for GraphQL queries and mutations
- Validate request/response contracts
- Validate auth, auth failure, and status codes

## Test Coverage

Each endpoint should cover:

- ✅ **Success scenarios** (200, 201, 204)
- ✅ **Parameter/validation errors** (400, 422)
- ✅ **Unauthenticated** (401)
- ✅ **Forbidden** (403)
- ✅ **Not Found** (404)
- ✅ **Conflict** (409)
- ✅ **Server error** (500)
- ✅ **Request body/query parameter validation**
- ✅ **Response structure validation**

---

## Real-World Scenarios and Test Data

To let tests **catch API behavior issues** (e.g. returning 200 when 400 is expected), design for real scenarios and use **strict assertions**.

### Test Data Setup

- **Endpoints that depend on resources** (e.g. "get/update/delete a pipeline"): In fixture or class/session-level setup, **call the create endpoint first** to obtain real `id` (e.g. `pipeline_id`, `file_id`), then use that ID in subsequent tests.
- **Example**: Create pipeline via `POST /studio/pipelines` → use returned `pipeline_id` to test `GET /studio/pipelines/{pipeline_id}`, `POST .../run`, `DELETE .../files/{file_id}`, etc.
- Optional: Delete created resources in teardown, or use a dedicated test account/project to avoid polluting the environment.

### Assertion Strictness

- **Assert exactly one expected status code per scenario** (e.g. success → `assert response.status_code == 200`, invalid params → `assert response.status_code == 400`, not found → `assert response.status_code == 404`).
- **Do not write loose assertions like "accept 200 or 400"**: they hide bugs such as "should return 400 but returned 200", making it hard for QA to find issues.
- Response structure: besides status code in success scenarios, validate fields defined in the docs (e.g. `code`, `data`, `meta`, `pipeline_id`).

### Two Test Modes

| Mode | When to use | Assertion | Purpose |
|------|-------------|-----------|---------|
| **Contract/real scenario** | Controllable data or Mock | One expected status code + response structure per scenario | Catch API behavior bugs; suitable for QA |
| **Smoke/connectivity** | No data, direct external API | May accept multiple status codes (e.g. 200/404/401) | Quick reachability check; no strict validation |

Prefer generating **contract/real scenario** tests; if data cannot be set up yet, mark as smoke tests (e.g. `@pytest.mark.smoke`) and document accordingly.

### Mock Files (Multiple Formats)

For **upload and file-related endpoints** that need file bodies, use **mock files** to provide in-memory content in multiple formats — **no mock server**, no real disk files — suitable for CI and environments without file dependencies.

- **Use**: Upload endpoints (e.g. `POST .../upload`), endpoints that depend on `file_id` (upload mock file first to get `file_id`, then test).
- **Design**:
  - Provide a shared module in the test project (e.g. `tests/mock_files.py`) with minimal valid or placeholder bytes per format (e.g. minimal PDF, 1×1 PNG, JPEG header, txt/csv/json).
  - Provide `get_mock_file_bytes(format)` returning `bytes`, and `get_mock_upload_tuple(format [, filename])` returning `(filename, BytesIO(bytes), content_type)` for use with `requests`'s `files=`.
  - Supported formats example: `pdf`, `png`, `jpg`/`jpeg`, `gif`, `txt`, `csv`, `json`, `xml`; extend per API docs.
- **In conftest**: Provide `mock_upload_file(format)` factory or fixtures like `mock_pdf_file`, `mock_png_file` for test injection.
- **Test strategy**: Prefer **mock files** for upload-success and delete-success tests; if the server only accepts real files (e.g. magic bytes validation), fall back to real project files (if any) or skip with a note.

Example (upload mock PNG):

```python
from tests.mock_files import get_mock_upload_tuple

file_tuple = get_mock_upload_tuple("png")  # ("mock.png", BytesIO(...), "image/png")
payload = {"files": file_tuple, "pipeline_id": (None, pipeline_id)}
resp = api_client("POST", f"/studio/pipelines/{pipeline_id}/upload", files=payload)
```

---

## Supported API Doc Formats

When APIs are defined by **API docs**, use these formats and the scripts in this skill's `scripts/` to get endpoint inventory:

| Format | Description | Script |
|--------|-------------|--------|
| **OpenAPI 3.x** | OpenAPI 3.0/3.1 JSON or YAML | `scripts/parse_openapi.py <doc path>` |
| **OpenAPI 2.0 (Swagger)** | Swagger 2.0 JSON or YAML | `scripts/parse_openapi.py <doc path>` |
| **Postman Collection 2.x** | Postman-exported JSON | `scripts/parse_postman.py <doc path>` |

- **OpenAPI/Swagger**: From project root run `python .cursor/skills/api-testing/scripts/parse_openapi.py path/to/openapi.json` (or `.yaml`). Optional: `--output inventory.txt`, `--base-url https://api.example.com`. YAML requires `pyyaml`.
- **Postman**: Run `python .cursor/skills/api-testing/scripts/parse_postman.py path/to/collection.json`. Optional: `--output inventory.txt`, `--base-url https://api.example.com`.

Output is a "method path - summary" text inventory, i.e. the **deliverable** for workflow step 1. See this directory's `scripts/README.md` for script usage.

---

## Workflow

### 1. Get Endpoint Inventory from API Docs

Use scripts in this directory's `scripts/` to extract endpoints from OpenAPI / Swagger / Postman docs:

```bash
# OpenAPI 3.x or Swagger 2.0 (JSON/YAML)
python .cursor/skills/api-testing/scripts/parse_openapi.py path/to/openapi.json --output inventory.txt

# Postman Collection 2.x
python .cursor/skills/api-testing/scripts/parse_postman.py path/to/collection.json --output inventory.txt
```

From the generated inventory and doc content, organize per endpoint: path, method, parameters, request body, response, auth requirements. Base URL comes from `--base-url` or OpenAPI `servers` / Postman variables.

**Endpoint inventory example:**

```
GET    /api/users              - User list (public)
GET    /api/users/:id          - User detail (public)
POST   /api/users              - Create user (admin only)
PUT    /api/users/:id          - Update user (login required, self or admin)
DELETE /api/users/:id          - Delete user (login required, self or admin)
```

**Deliverable:** API endpoint inventory (script output).

**Test environment:** If the target is an **external HTTP service** (described by OpenAPI/Postman, called via HTTP), tests typically use `requests` with a configurable base_url (and optional auth headers), not an in-process TestClient and database. Provide `api_client`, `base_url` etc. in `conftest.py`; do not provide DB fixtures when there is no local app/DB. For **real scenario** tests, create data via create endpoints in fixtures (e.g. create pipeline), then write tests with real IDs and strict status assertions (see "Real-World Scenarios and Test Data" above).

---

### 2. Generate REST API Tests

- **Structure**: One class per endpoint (e.g. `TestGetUsers`, `TestCreateUser`), with `test_xxx` per scenario; use Arrange-Act-Assert; include both positive (success codes) and negative (400/401/403/404/409) cases.
- **Assertions**: **Assert exactly one expected status code per scenario** (e.g. success 200, invalid params 400, not found 404), aligned with doc `responses`; do not write loose "accept 200 or 400" assertions, or QA cannot reliably find API bugs.
- **Data**: For resource-dependent endpoints, create resources in fixture/setup first (see "Real-World Scenarios and Test Data"), then write tests with real IDs.
- **Example code**: See `examples/rest_api_test_example.py` in this directory.
- **Status code examples**: See `examples/http_status_codes_example.py`.

**Deliverable:** Full REST API test file (e.g. `tests/test_xxx_api.py`).

---

### 3. Generate GraphQL API Tests

- **Structure**: Separate tests for queries and mutations; assert `response.status_code == 200` and `response.json()["data"]` structure.
- **Example code**: See `examples/graphql_test_example.py` in this directory.

**Deliverable:** GraphQL API test file.

---

## HTTP Status Codes

Status codes to cover are illustrated in `examples/http_status_codes_example.py`, including:

- 200 (GET/PUT/PATCH success), 201 (POST create), 204 (DELETE success)
- 400 (parameter/validation error), 401 (unauthorized), 403 (forbidden), 404 (not found), 409 (conflict), 422 (unprocessable), 500 (server error)

---

## Best Practices

1. Cover all endpoints and HTTP methods
2. Test both success and error status codes; **assert exactly one expected status code per scenario** (no "or" over multiple codes)
3. For resource-dependent endpoints: **create data first, then test** (create in fixture/setup, then use real ID)
4. For upload/file endpoints: **prefer mock files** (in-memory multi-format content, no real files, no mock server); fall back or skip if server only accepts real files
5. Validate request body: required fields, format, constraints
6. Validate response body: structure, fields, types (match API doc schemas/examples)
7. Test auth: with/without token, expired token
8. Test authorization: different roles and permissions
9. Test boundaries: empty list, null, max limits
10. When DB exists, validate persistence; when testing external APIs with created data, validate behavior accordingly
11. Clear test names; one scenario per test
12. Organize by endpoint; tests are independent

---

## Quality Checklist

Before finishing tests, confirm:

- [ ] All endpoints covered (inventory from API docs)
- [ ] All HTTP methods covered
- [ ] Success scenarios (200, 201, 204) covered, **with exactly one expected status code per scenario** (no loose 200 or 400)
- [ ] Error scenarios (400, 401, 403, 404, 409) covered, **with exactly one expected status code per scenario**
- [ ] Resource-dependent endpoints **create data first** in fixture/setup, then test with real ID (real scenario)
- [ ] Request validation tested
- [ ] Response structure validated (matches docs)
- [ ] Auth tested (if required)
- [ ] Authorization tested (if required)
- [ ] Edge cases covered
- [ ] Persistence validated when DB exists; when testing external API with created data, assert real scenario
- [ ] Tests run independently and all pass

---

## Integration with Test Process

**Input:** API doc files (OpenAPI/Swagger/Postman).  
**Process:** Analyze (optionally with this directory's `scripts/`) → generate tests → run and fix.  
**Output:** Complete API test suite.  
**Next:** Integrate with CI, docs, or deployment.

---

## Remember

- Cover all endpoints and HTTP methods
- Test both success and error scenarios; **assert exactly one expected status code per scenario** (so QA can catch API bugs)
- Resource-dependent endpoints: **create data first, then test**, use real IDs, no loose "accept multiple status codes" assertions
- Upload/file endpoints: **prefer mock files** (in-memory multi-format), no real files, no mock server
- Validate request and response structure (match API docs)
- Test auth and authorization
- Validate persistence when DB exists
- One scenario per test
- Tests as documentation; keep them readable
