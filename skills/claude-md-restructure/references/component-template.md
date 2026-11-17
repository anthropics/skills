# Component CLAUDE.md Template

Use this template for component/service-level CLAUDE.md files.
These files are lazy-loaded only when working in that directory.
Target: ~100-200 lines with component-specific details.

---

```markdown
# CLAUDE.md - [Component Name]

[One-line description of what this component does]

## Workflows

### Primary Workflow: [Name]
```
[Endpoint or trigger]
Body: { field1, field2 }

→ Step 1
→ Step 2
   ├─ Sub-step A
   └─ Sub-step B
→ Step 3

→ Response: ResponseDTO
   └─ List<ItemDTO> items
      ├─ field1 (type)
      └─ field2 (type)
```

### Secondary Workflow: [Name]
[Similar structure]

## Status/State Machine

| Code | Name | Description |
|------|------|-------------|
| 1 | STATE_A | Description |
| 2 | STATE_B | Description |
| 3 | STATE_C | Description |

```java
// Reading status
Status status = Status.fromValue(entity.getStatus().getId());

// Writing status
EntityStatus newStatus = new EntityStatus();
newStatus.setId(Status.STATE_B.getValue());
entity.setStatus(newStatus);
```

## Data Schema

### Input Format (e.g., Excel/CSV)

| Col | Field | Required | Resolution |
|-----|-------|----------|------------|
| 0 | field_a | Yes | Direct mapping |
| 1 | field_b | No | From external service |
| 2 | field_c | Yes | Computed from field_a |

## Endpoints

### Category A
- `POST /api/resource` - Create
- `GET /api/resource/{id}` - Get by ID
- `POST /api/resource/search` - Search with filters

### Category B
- `PUT /api/resource/{id}` - Update
- `DELETE /api/resource/{id}` - Delete

## Error Codes

### Validation Errors
| Code | Description |
|------|-------------|
| ERR001 | Field X missing |
| ERR002 | Invalid format |

### Business Errors
| Code | Description | Retry |
|------|-------------|-------|
| ERR010 | Resource not found | No |
| ERR011 | Duplicate entry | No |
| ERR012 | External service error | Yes |

## Utility Classes

| Class | Responsibility |
|-------|----------------|
| `Parser` | Parse input files |
| `Validator` | Business validation |
| `Resolver` | External ID resolution |
| `ErrorClassifier` | Error categorization |

## Configuration

### Environment Variables
```properties
# Database
DB_URL=...
DB_USERNAME=...

# External Services
SERVICE_X_ENABLED=true
SERVICE_X_ENDPOINT=https://...
```

### Per-Environment Settings
| Setting | Local | Production |
|---------|-------|------------|
| Context Path | `/app` | `/prod-app` |
| Log Level | DEBUG | INFO |

## Related Documentation
- `docs/API.md` - Full API reference
- `docs/INTEGRATION.md` - External service integration
```

---

## Guidelines

1. **Component-specific only**: Don't repeat root CLAUDE.md conventions
2. **Workflows first**: Lead with how the component is used
3. **Tables for reference**: Error codes, states, config in tables
4. **Code examples**: Show patterns specific to this component
5. **Link to detailed docs**: Reference docs/ files for deep dives
