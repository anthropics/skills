---
name: robot-framework-py
description: Guide for authoring and refactoring Robot Framework test automation with Python-based libraries. Use when Claude needs to create or modify `.robot` suites, `.resource` files, RequestsLibrary API tests, or custom Python keyword libraries for service and API testing workflows.
license: Complete terms in LICENSE.txt
---

# Robot Framework (Python)

Create deterministic, maintainable Robot Framework automation for API and service-level testing.

## Use this default project layout

```text
tests/
resources/
libraries/
variables/
```

- Store suite files in `tests/`.
- Store reusable keywords in `resources/`.
- Store custom Python keyword libraries in `libraries/`.
- Store environment-specific variable files in `variables/`.

## Generate valid Robot Framework sections

For `.robot` suite files, use:

- `*** Settings ***`
- `*** Variables ***` (when needed)
- `*** Test Cases ***`
- `*** Keywords ***` (only when local keywords are needed)

For `.resource` files, use:

- `*** Settings ***`
- `*** Variables ***` (optional)
- `*** Keywords ***`

Use BuiltIn assertions (`Should Be Equal`, `Should Contain`, `Should Be True`, `Should Not Be Empty`) instead of ad-hoc assertion logic.

## Prioritize reuse and maintainability

- Keep test cases short and move repeated flows into resource keywords.
- Use `Suite Setup` and `Suite Teardown` for shared lifecycle steps.
- Apply consistent tags (`smoke`, `api`, `regression`, domain tags).
- Keep secrets out of suite files; load from environment variables or secure variable files.

## Use libraries deliberately

- Use BuiltIn for assertions, logging, and control flow.
- Use OperatingSystem for file and environment checks.
- Use Collections, String, Process, and XML only when required by the test flow.
- Declare all imported libraries explicitly in `*** Settings ***`.

Do not add SeleniumLibrary, Browser, Appium, or other UI automation stacks unless the user explicitly asks for them.

## Follow this RequestsLibrary path for API tests

- Install with `pip install robotframework-requests`.
- Create sessions with `Create Session`.
- Reuse sessions for related requests.
- Build auth headers and shared request data in reusable keywords.
- Assert both HTTP status and business-critical response fields.

### Minimal RequestsLibrary example

```robotframework
*** Settings ***
Library    RequestsLibrary

*** Variables ***
${BASE_URL}    https://api.example.com

*** Test Cases ***
Get Health Endpoint
    Create Session    api    ${BASE_URL}
    ${resp}=    GET On Session    api    /health
    Should Be Equal As Integers    ${resp.status_code}    200
```

## Implement Python keyword libraries safely

- Keep each keyword focused on one responsibility.
- Return simple serializable types where possible.
- Raise clear assertion failures for invalid state or input.

### Module-style keyword library

```python
from robot.api.deco import keyword

@keyword("Normalize Text")
def normalize_text(value: str) -> str:
    return " ".join(value.split()).strip().lower()
```

### Class-style keyword library

```python
from robot.api.deco import keyword

class MathKeywords:
    @keyword("Add Integers")
    def add_integers(self, left: int, right: int) -> int:
        return int(left) + int(right)
```

## Prevent hallucinations

- State which library provides each non-trivial keyword pattern.
- If a keyword or library is external and not explicitly requested, label it as optional.
- Do not present unknown keywords as built-in Robot Framework keywords.

## Execution checklist

1. Identify output type (`.robot` suite, `.resource`, or Python library module).
2. Identify required libraries (BuiltIn, OperatingSystem, RequestsLibrary, custom library).
3. Decide variable and secret handling.
4. Generate deterministic assertions and reusable keywords.
5. Refactor duplicate steps into resource files.
6. Add run commands only when requested.

## References

- Robot Framework User Guide: https://robotframework.org/robotframework/latest/RobotFrameworkUserGuide.html
- Standard libraries overview: https://docs.robotframework.org/docs/different_libraries/standard
- BuiltIn library docs: https://robotframework.org/robotframework/latest/libraries/BuiltIn.html
- OperatingSystem library docs: https://robotframework.org/robotframework/latest/libraries/OperatingSystem.html
- Python library extension guide: https://docs.robotframework.org/docs/extending_robot_framework/custom-libraries/python_library
- Robot Framework API docs: https://robot-framework.readthedocs.io/
- RequestsLibrary docs: https://docs.robotframework.org/docs/different_libraries/requests
