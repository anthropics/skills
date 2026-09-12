# Root CLAUDE.md Template

Use this template for the root-level CLAUDE.md file.
Target: ~50-100 lines containing ONLY global conventions.

---

```markdown
# CLAUDE.md - [Project Name] Conventions

**Version**: X.Y.Z | **Updated**: YYYY-MM-DD

## Context
[2-3 line project description - what it does, who it's for]

## Stack
- **Framework**: [e.g., Spring Boot 3.2, Java 17]
- **Database**: [e.g., PostgreSQL, MongoDB]
- **Auth**: [e.g., JWT, OAuth2]
- **Integrations**: [Key external services]

## Critical Architecture
[ONLY include if there's a pattern that MUST be followed everywhere]

Example for multi-tenant system:
```java
// CORRECT - Always use tenant-specific client
Client client = clientFactory.getClientForTenant(tenantId);

// WRONG - Never use static client
```

## Code Conventions

### Controller Pattern
```java
@PostMapping("/endpoint")
public ResponseEntity<Response<T>> method(@RequestBody Request req) {
    return ResponseEntity.ok(Response.ok(service.operation(req)));
}
```

### Error Handling
```java
throw ErrorUtils.createValidationException("ERR001");
// Exception handler catches → always HTTP 200 with error payload
```

### Layer Structure
```
Controller → Service → Repository
```

## Feature Flags
```properties
FEATURE_X_ENABLED=false
FEATURE_Y_ENABLED=true
```

## Build
```bash
mvn clean package -DskipTests    # Requires Java 17
java -jar target/app.jar
```

## Documentation

| Area | Location |
|------|----------|
| **Service Details** | `component/CLAUDE.md` |
| **API Reference** | `component/docs/API.md` |
| **Integrations** | `docs/integrations/` |
| **Changelog** | `CHANGELOG.md` |

## Commit Format
```
type(scope): description

Types: feat, fix, refactor, docs, test, chore
Scope: [component names]
```

## Security
- Required header: `Authorization: Bearer {token}`
- Never commit: `.env`, credentials, API keys
- JWT validation: Delegated to gateway
```

---

## Guidelines

1. **Keep it short**: If > 100 lines, move details to component CLAUDE.md
2. **No implementation details**: Workflows, endpoints, error codes go in component files
3. **No changelog**: History belongs in CHANGELOG.md only
4. **No analysis/fixes**: Those are temporary docs, delete when done
5. **Links over content**: Reference other files instead of duplicating
