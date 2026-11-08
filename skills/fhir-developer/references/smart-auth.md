# SMART on FHIR Authorization

SMART on FHIR is the standard authorization framework for FHIR APIs, built on OAuth 2.0.

## Table of Contents
- [Discovery Endpoint](#discovery-endpoint)
- [Scope Syntax](#scope-syntax)
- [Launch Context](#launch-context)
- [Authorization Flow](#authorization-flow)
- [Backend Services](#backend-services)
- [Enforcing Scopes](#enforcing-scopes)

## Discovery Endpoint

Servers MUST publish authorization configuration at:
```
GET /.well-known/smart-configuration
```

**Response:**
```json
{
  "authorization_endpoint": "https://auth.example.org/authorize",
  "token_endpoint": "https://auth.example.org/token",
  "token_endpoint_auth_methods_supported": ["client_secret_basic", "private_key_jwt"],
  "scopes_supported": ["openid", "fhirUser", "launch", "launch/patient",
                       "patient/*.rs", "user/*.cruds", "offline_access"],
  "capabilities": ["launch-ehr", "launch-standalone", "client-public",
                   "client-confidential-symmetric", "permission-v2", "sso-openid-connect"]
}
```

## Scope Syntax

**SMART v2 (Current Standard):**
```
<context>/<resource>.<permissions>

context: patient | user | system
resource: Patient | Observation | * (wildcard)
permissions: c (create) | r (read) | u (update) | d (delete) | s (search)
```

**Examples:**
| Scope | Meaning |
|-------|---------|
| `patient/Patient.rs` | Read and search Patient for current patient context |
| `patient/Observation.rs` | Read and search Observations for current patient |
| `patient/*.rs` | Read and search all resources for current patient |
| `user/Encounter.cruds` | Full CRUD + search on Encounters the user can access |
| `system/*.rs` | Backend service: read/search all resources |

**SMART v1 (Legacy - still widely used):**
```
<context>/<resource>.<read|write|*>
```
| v1 Scope | Equivalent v2 |
|----------|---------------|
| `patient/Patient.read` | `patient/Patient.rs` |
| `patient/Patient.write` | `patient/Patient.cud` |
| `patient/Patient.*` | `patient/Patient.cruds` |

### Scope Types

| Scope Type | Use Case | Context Required |
|------------|----------|------------------|
| `patient/` | Patient-facing apps | `patient` launch context |
| `user/` | Provider-facing apps | User's access permissions |
| `system/` | Backend services | Pre-configured policy |

## Launch Context

| Scope | Provides | In Token Response |
|-------|----------|-------------------|
| `launch` | EHR launch context | `patient`, `encounter` |
| `launch/patient` | Standalone patient selection | `patient` |
| `launch/encounter` | Standalone encounter selection | `encounter` |
| `openid fhirUser` | User identity | `id_token` with `fhirUser` claim |
| `offline_access` | Refresh token (persistent) | `refresh_token` |
| `online_access` | Refresh token (session-bound) | `refresh_token` |

## Authorization Flow (EHR Launch)

```
1. EHR redirects to app with launch parameter:
   GET https://app.example.com/launch?iss=https://fhir.hospital.org&launch=abc123

2. App discovers authorization endpoints:
   GET https://fhir.hospital.org/.well-known/smart-configuration

3. App redirects to authorization:
   GET https://auth.hospital.org/authorize?
     response_type=code&
     client_id=my-app&
     redirect_uri=https://app.example.com/callback&
     scope=launch patient/Patient.rs patient/Observation.rs&
     state=xyz789&
     aud=https://fhir.hospital.org&
     launch=abc123

4. User authenticates & authorizes

5. Authorization server redirects back:
   GET https://app.example.com/callback?code=auth_code_here&state=xyz789

6. App exchanges code for token:
   POST https://auth.hospital.org/token
   Content-Type: application/x-www-form-urlencoded

   grant_type=authorization_code&
   code=auth_code_here&
   redirect_uri=https://app.example.com/callback&
   client_id=my-app

7. Token response includes context:
   {
     "access_token": "eyJ...",
     "token_type": "Bearer",
     "expires_in": 3600,
     "scope": "launch patient/Patient.rs patient/Observation.rs",
     "patient": "123",
     "encounter": "456"
   }
```

## Backend Services (System-to-System)

For automated systems without user interaction:

```python
import jwt
import time
import requests

# 1. Create signed JWT assertion
now = int(time.time())
claims = {
    "iss": CLIENT_ID,
    "sub": CLIENT_ID,
    "aud": TOKEN_ENDPOINT,
    "exp": now + 300,
    "jti": str(uuid.uuid4())
}
assertion = jwt.encode(claims, PRIVATE_KEY, algorithm="RS384")

# 2. Exchange for access token
response = requests.post(TOKEN_ENDPOINT, data={
    "grant_type": "client_credentials",
    "scope": "system/*.rs",
    "client_assertion_type": "urn:ietf:params:oauth:client-assertion-type:jwt-bearer",
    "client_assertion": assertion
})
token = response.json()["access_token"]

# 3. Use token in FHIR requests
headers = {"Authorization": f"Bearer {token}"}
patients = requests.get(f"{FHIR_BASE}/Patient", headers=headers)
```

## Enforcing Scopes

**Python/FastAPI Middleware:**
```python
from fastapi import Request, HTTPException
import re

def parse_smart_scopes(token_scopes: str) -> dict:
    """Parse SMART scopes into a permissions structure."""
    permissions = {}
    for scope in token_scopes.split():
        match = re.match(r'(patient|user|system)/(\w+|\*)\.([cruds]+|read|write|\*)', scope)
        if match:
            context, resource, perms = match.groups()
            if perms == 'read': perms = 'rs'
            elif perms == 'write': perms = 'cud'
            elif perms == '*': perms = 'cruds'

            if resource not in permissions:
                permissions[resource] = set()
            permissions[resource].update(perms)
    return permissions

async def check_scope(request: Request, resource_type: str, action: str):
    """Verify the token has required scope for the action."""
    token_scopes = request.state.token_scopes
    permissions = parse_smart_scopes(token_scopes)

    action_map = {'create': 'c', 'read': 'r', 'update': 'u', 'delete': 'd', 'search': 's'}
    required = action_map.get(action, action)

    allowed = permissions.get(resource_type, set()) | permissions.get('*', set())

    if required not in allowed:
        raise HTTPException(status_code=403, detail=f"Insufficient scope. Required: {resource_type}.{required}")
```

## Common Authorization Errors

| Status | Error | When |
|--------|-------|------|
| `401` | `invalid_token` | Token expired, malformed, or revoked |
| `403` | `insufficient_scope` | Valid token but missing required scope |
| `403` | `access_denied` | Resource outside patient compartment |
