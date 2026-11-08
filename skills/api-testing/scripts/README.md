# Scripts

This directory contains helper scripts for the **api-testing** skill. They extract endpoint inventory from API docs for use in the SKILL workflow step "Get endpoint inventory from API docs".

## Dependencies

- Python 3.7+
- For YAML OpenAPI: `pip install pyyaml`

## Paths

Scripts live under the skill directory: `.cursor/skills/api-test-generator/scripts/`. When run from the **project root**, doc paths are relative to the project root.

## Usage

### OpenAPI / Swagger

Supports **OpenAPI 2.0 (Swagger)** and **OpenAPI 3.x**, and `.json` / `.yaml` / `.yml`.

```bash
# Output to terminal
python .cursor/skills/api-test-generator/scripts/parse_openapi.py path/to/openapi.json
python .cursor/skills/api-test-generator/scripts/parse_openapi.py path/to/openapi.yaml

# Output to file
python .cursor/skills/api-test-generator/scripts/parse_openapi.py path/to/openapi.json --output inventory.txt
python .cursor/skills/api-test-generator/scripts/parse_openapi.py path/to/openapi.json --base-url https://api.example.com
```

### Postman Collection

Supports **Postman Collection 2.x** JSON export.

```bash
# Output to terminal
python .cursor/skills/api-test-generator/scripts/parse_postman.py path/to/collection.json

# Output to file
python .cursor/skills/api-test-generator/scripts/parse_postman.py path/to/collection.json --output inventory.txt --base-url https://api.example.com
```

## Output Example

```
# API Name (version 1.0)
# Base URL: https://api.example.com

GET    /api/users              - Get user list
GET    /api/users/{id}         - Get user detail
POST   /api/users              - Create user
PUT    /api/users/{id}         - Update user
DELETE /api/users/{id}         - Delete user
```

Use this inventory as the **API endpoint inventory** input in the workflow, then generate positive/negative test cases per endpoint.
