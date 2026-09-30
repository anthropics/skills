# Examples

This directory contains test code examples for the **api-testing** skill, for reference when generating test cases.

| File | Description |
|------|-------------|
| `rest_api_test_example.py` | REST API test structure: one class per endpoint, positive/negative cases, Arrange-Act-Assert |
| `graphql_test_example.py` | GraphQL query/mutation test examples |
| `http_status_codes_example.py` | Assertion examples for HTTP status codes (200/201/204/400/401/403/404/409/422/500) |

Usage: Based on endpoint inventory and business logic, use the above structure to write or generate `tests/test_xxx_api.py`, and provide `client`, `db`, `admin_headers` etc. via project `conftest.py`.
