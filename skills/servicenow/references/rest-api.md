# ServiceNow REST API Patterns

## Table API

### GET — Query Records
```bash
# Get active incidents, limit 10
GET /api/now/table/incident?sysparm_query=active=true&sysparm_limit=10&sysparm_fields=number,short_description,state,priority&sysparm_display_value=true

# Pagination
GET /api/now/table/incident?sysparm_query=active=true&sysparm_limit=100&sysparm_offset=200

# Order by
GET /api/now/table/incident?sysparm_query=active=true^ORDERBYDESCsys_created_on
```

### GET — Single Record
```bash
GET /api/now/table/incident/{sys_id}?sysparm_fields=number,short_description,state&sysparm_display_value=all
# display_value=all returns both value and display_value for each field
```

### POST — Create Record
```bash
POST /api/now/table/incident
Content-Type: application/json

{
    "short_description": "Cannot access email",
    "caller_id": "user_sys_id",
    "category": "software",
    "impact": "2",
    "urgency": "2"
}
```

### PUT — Replace Record (all fields)
```bash
PUT /api/now/table/incident/{sys_id}
Content-Type: application/json

{
    "state": "6",
    "close_code": "Solved (Permanently)",
    "close_notes": "Resolved by resetting credentials"
}
```

### PATCH — Update Specific Fields
```bash
PATCH /api/now/table/incident/{sys_id}
Content-Type: application/json

{
    "assigned_to": "user_sys_id",
    "state": "2"
}
```

### DELETE
```bash
DELETE /api/now/table/incident/{sys_id}
```

### Authentication

```bash
# Basic Auth from environment variables
curl --user "$SN_USER:$SN_PASS" \
  https://instance.service-now.com/api/now/table/incident

# OAuth2 Bearer Token
curl -H "Authorization: Bearer $SN_ACCESS_TOKEN" \
  https://instance.service-now.com/api/now/table/incident

# OAuth2 Token Request (prefer a secure client flow, not inline hardcoded secrets)
POST /oauth_token.do
Content-Type: application/x-www-form-urlencoded

grant_type=client_credentials&client_id=$SN_CLIENT_ID&client_secret=$SN_CLIENT_SECRET
```

### Pagination Pattern (Python example)
```python
import os
import requests

base_url = "https://instance.service-now.com/api/now/table/incident"
headers = {
    "Accept": "application/json",
    "Authorization": f"Bearer {os.environ['SN_ACCESS_TOKEN']}",
}

offset = 0
limit = 100
all_records = []

while True:
    params = {
        "sysparm_query": "active=true",
        "sysparm_limit": limit,
        "sysparm_offset": offset,
        "sysparm_fields": "number,short_description,state"
    }
    resp = requests.get(base_url, headers=headers, params=params, timeout=30)
    resp.raise_for_status()
    data = resp.json()["result"]
    
    if not data:
        break
    
    all_records.extend(data)
    offset += limit

    # Also check X-Total-Count header
    total = int(resp.headers.get("X-Total-Count", 0))
    if offset >= total:
        break
```

## Scripted REST API

### Creating a Custom API Endpoint

1. Navigate to **System Web Services > Scripted REST APIs**
2. Create new API: Name, API ID (namespace), Base API path

### Resource Script (GET single record)
```javascript
(function process(/*RESTAPIRequest*/ request, /*RESTAPIResponse*/ response) {
    
    var id = request.pathParams.id;
    
    // Validate input
    if (gs.nil(id)) {
        response.setStatus(400);
        return { error: 'Missing required parameter: id' };
    }
    
    var gr = new GlideRecord('incident');
    if (!gr.get(id)) {
        response.setStatus(404);
        return { error: 'Incident not found', id: id };
    }
    
    // Check permissions
    if (!gr.canRead()) {
        response.setStatus(403);
        return { error: 'Insufficient permissions' };
    }
    
    return {
        sys_id: gr.getUniqueValue(),
        number: gr.getValue('number'),
        short_description: gr.getValue('short_description'),
        state: gr.getValue('state'),
        priority: gr.getValue('priority'),
        assigned_to: gr.getDisplayValue('assigned_to'),
        created: gr.getValue('sys_created_on')
    };
    
})(request, response);
```

### Resource Script (POST with validation)
```javascript
(function process(/*RESTAPIRequest*/ request, /*RESTAPIResponse*/ response) {
    
    var body = request.body.data;
    
    // Validate required fields
    var required = ['short_description', 'caller_id', 'category'];
    var missing = [];
    for (var i = 0; i < required.length; i++) {
        if (gs.nil(body[required[i]])) missing.push(required[i]);
    }
    if (missing.length > 0) {
        response.setStatus(400);
        return { error: 'Missing required fields', fields: missing };
    }
    
    var gr = new GlideRecord('incident');
    gr.initialize();
    gr.setValue('short_description', body.short_description);
    gr.setValue('caller_id', body.caller_id);
    gr.setValue('category', body.category);
    gr.setValue('description', body.description || '');
    gr.setValue('impact', body.impact || '3');
    gr.setValue('urgency', body.urgency || '3');
    
    var sys_id = gr.insert();
    
    if (sys_id) {
        response.setStatus(201);
        response.setHeader('Location', '/api/x_myapp/v1/incidents/' + sys_id);
        return {
            sys_id: sys_id,
            number: gr.getValue('number')
        };
    } else {
        response.setStatus(500);
        return { error: 'Failed to create incident' };
    }
    
})(request, response);
```

### Versioned API Pattern
```
Base path: /api/x_myapp/incidents
Resources:
  /v1/incidents         — GET (list), POST (create)
  /v1/incidents/{id}    — GET (read), PATCH (update), DELETE
  /v2/incidents         — GET (enhanced list with pagination metadata)
```

### Query Parameters in Scripted REST
```javascript
// Access query parameters
var limit = parseInt(request.queryParams.limit) || 20;
var offset = parseInt(request.queryParams.offset) || 0;
var query = request.queryParams.query || 'active=true';

// Access headers
var apiKey = request.getHeader('X-API-Key');
var contentType = request.getHeader('Content-Type');
```

## Outbound REST (RESTMessageV2)

### Basic GET Request
```javascript
try {
    var rm = new sn_ws.RESTMessageV2('My REST Message', 'GET');
    rm.setStringParameterNoEscape('endpoint', 'https://api.example.com/data');
    rm.setRequestHeader('Accept', 'application/json');
    
    var response = rm.execute();
    var statusCode = response.getStatusCode();
    var body = response.getBody();
    
    if (statusCode == 200) {
        var data = JSON.parse(body);
        gs.info('Got ' + data.results.length + ' records');
    } else {
        gs.error('REST call failed: ' + statusCode + ' - ' + body);
    }
} catch(e) {
    gs.error('REST exception: ' + e.message);
}
```

### POST with OAuth2
```javascript
var rm = new sn_ws.RESTMessageV2();
rm.setEndpoint('https://api.example.com/create');
rm.setHttpMethod('POST');

// Preferred: configure auth on the REST Message method record.
// Alternate: keep the profile name in a property rather than hardcoding it.
var oauthProfile = gs.getProperty('x_scope.outbound.oauth_profile', 'x_scope.default_oauth_profile');
rm.setAuthenticationProfile('oauth2', oauthProfile);

rm.setRequestHeader('Content-Type', 'application/json');
rm.setRequestBody(JSON.stringify({
    name: 'Test',
    description: 'Created from ServiceNow'
}));

var response = rm.execute();
```

### Async REST (Mid Server)
```javascript
var rm = new sn_ws.RESTMessageV2('External API', 'GET');
rm.setMIDServer('my_mid_server');
rm.setEccTopic('MyIntegration');

// Execute asynchronously through MID
var response = rm.executeAsync();
var eccQueueId = response.getBody(); // ECC queue sys_id

// Response comes back via ECC queue — handle in a Business Rule on ecc_queue
```

### Retry Pattern
```javascript
function callWithRetry(rmName, method, maxRetries) {
    var retries = 0;
    while (retries < maxRetries) {
        try {
            var rm = new sn_ws.RESTMessageV2(rmName, method);
            var response = rm.execute();
            var code = response.getStatusCode();
            
            if (code >= 200 && code < 300) return response;
            if (code == 429 || code >= 500) {
                retries++;
                gs.sleep(1000 * retries); // exponential-ish backoff
                continue;
            }
            return response; // 4xx — don't retry
        } catch(e) {
            retries++;
            if (retries >= maxRetries) throw e;
            gs.sleep(1000 * retries);
        }
    }
    return null;
}
```

## Import Sets + Transform Maps via API

### POST to Import Set Table
```bash
POST /api/now/import/u_my_import_set
Content-Type: application/json

{
    "u_name": "John Doe",
    "u_email": "john@example.com",
    "u_department": "IT"
}
# Response includes transform result
```

### Bulk Import via Attachment
```bash
# Upload CSV/Excel to import set
POST /api/now/attachment/upload
Content-Type: multipart/form-data
table_name=u_my_import_set&table_sys_id=...

# Then trigger transform via API
POST /api/now/table/sys_transform_map
```

## Batch API

```bash
POST /api/now/batch
Content-Type: application/json

{
    "batch_request_id": "batch_001",
    "rest_requests": [
        {
            "id": "req_1",
            "method": "GET",
            "url": "/api/now/table/incident/sys_id_1",
            "headers": [{"name": "Accept", "value": "application/json"}]
        },
        {
            "id": "req_2",
            "method": "PATCH",
            "url": "/api/now/table/incident/sys_id_2",
            "headers": [{"name": "Content-Type", "value": "application/json"}],
            "body": "{\"state\": \"2\"}"
        }
    ]
}
```

## Error Handling Pattern (Scripted REST)

```javascript
(function process(request, response) {
    try {
        // ... main logic ...
        
        return { result: data };
        
    } catch(e) {
        gs.error('API Error: ' + e.message + '\nStack: ' + e.stack);
        
        response.setStatus(500);
        return {
            error: {
                message: 'Internal server error',
                detail: gs.getProperty('glide.appcreator.env') == 'development' ? e.message : undefined
            }
        };
    }
})(request, response);
```

## Attachment API

```bash
# Upload attachment
POST /api/now/attachment/file?table_name=incident&table_sys_id={sys_id}&file_name=document.pdf
Content-Type: application/pdf
[binary data]

# Get attachment metadata
GET /api/now/attachment?sysparm_query=table_sys_id={sys_id}

# Download attachment
GET /api/now/attachment/{attachment_sys_id}/file
```

## CORS and Security

```javascript
// In Scripted REST API properties:
// - Requires authentication: true (default)
// - Requires ACL authorization: Check for row-level security
// - Allowed request headers: Authorization, Content-Type, Accept

// For CORS: System Properties
// glide.rest.cors.enabled = true  
// glide.rest.cors.rule.* — configure per-origin rules
```
