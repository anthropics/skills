# ServiceNow Security

## ACL Rules (Access Control)

### ACL Evaluation Order
1. Table-level ACL (e.g., `incident.*`)
2. Field-level ACL (e.g., `incident.short_description`)
3. Most restrictive wins — ALL applicable ACLs must pass

### Row-Level ACL (record access)
```
Name: incident (read)
Type: record
Operation: read
Table: incident
Condition: active=true
Script:
  // Advanced condition — return true to allow access
  answer = current.getValue('assignment_group') != '' && 
           gs.getUser().isMemberOf(current.getValue('assignment_group'));
Roles: itil, incident_manager
// Role OR script must pass (depends on "Requires role" checkbox)
```

### Field-Level ACL
```
Name: incident.close_notes (write)
Type: record
Operation: write
Table: incident
Field: close_notes
Condition: state=6^ORstate=7
Script:
  answer = gs.hasRole('itil');
```

### Common ACL Patterns

```javascript
// Only allow assigned group members to write
answer = gs.hasRole('admin') || 
         gs.getUser().isMemberOf(current.getValue('assignment_group'));

// Only allow assignee or manager to close
answer = current.getValue('assigned_to') == gs.getUserID() || 
         gs.hasRole('incident_manager');

// Restrict based on caller's company (multi-tenant)
answer = current.caller_id.company == gs.getUser().getCompanyID();

// Time-based restriction
var gdt = new GlideDateTime(current.getValue('sys_created_on'));
var now = new GlideDateTime();
var diff = GlideDateTime.subtract(gdt, now);
answer = diff.getNumericValue() < 86400000; // within 24 hours
```

### ACL Debugging
```
Navigate: System Security > Debugging
Enable: Session Debug > Security (ACL)

// In scripts:
gs.setProperty('glide.security.debug', true); // TEMP only!

// Check ACL in script
var gr = new GlideRecord('incident');
if (gr.get(sys_id)) {
    gs.info('Can read: ' + gr.canRead());
    gs.info('Can write: ' + gr.canWrite());
    gs.info('Can delete: ' + gr.canDelete());
}
```

## Role Management

### Role Hierarchy
```
admin
├── security_admin
├── incident_manager
│   └── itil
│       └── sn_incident_read
├── problem_manager
│   └── itil
├── change_manager
│   └── itil
└── knowledge_manager
    └── knowledge
```

### Creating Custom Roles
```
Navigate: User Administration > Roles

Name: x_myapp.incident_resolver
Description: Can resolve incidents in MyApp scope
Elevated privilege: false (check only for sensitive operations)

// Contains roles (inherited):
itil

// Contained by roles (grants this role):
x_myapp.admin
```

### Checking Roles in Scripts
```javascript
// Server-side
gs.hasRole('itil');                    // exact role
gs.hasRole('itil,incident_manager');   // any of these roles

// Check role for specific user
var gr = new GlideRecord('sys_user_has_role');
gr.addQuery('user', userId);
gr.addQuery('role.name', 'itil');
gr.addQuery('state', 'active');
gr.query();
var hasRole = gr.hasNext();

// Client-side (via g_user)
var isAdmin = g_user.hasRole('admin');
var isItil = g_user.hasRole('itil');
```

## Scoped Application Security

### Access Control for Scoped Apps
```
Navigate: System Applications > Application Access

Application: My Custom App (x_myapp)
Settings:
  - Can read: All application scopes
  - Can create/update/delete: This application scope only
  - Accessible from: All scopes / This scope only
  - Caller Access: Restrict which scopes can call Script Includes
```

### Cross-Scope Access
```javascript
// Calling a Script Include from another scope
// The target Script Include must have "Accessible from: All application scopes"

// From scope x_app_a, calling x_app_b.UtilityClass:
var util = new x_app_b.UtilityClass();  // prefix with scope namespace
var result = util.myMethod(param);

// If Script Include is NOT accessible cross-scope:
// → Results in "Security restricted: Script Include not accessible" error
```

### Privileged Script Include
```javascript
// Mark as "Protection policy: Read-only" to prevent modification
// Mark as "Accessible from: All application scopes" for cross-scope use

// For accessing tables outside your scope:
var si = new global.SomeGlobalUtil(); // access global scope utilities
```

### Application Properties (scoped)
```javascript
// Define in: System Properties > Application Properties
// Name: x_myapp.max_records
// Value: 500

// Access (within scope):
var maxRec = gs.getProperty('x_myapp.max_records', '100');

// Other scopes can read if "Can read" is set to "All application scopes"
```

## Data Encryption

### Column-Level Encryption
```
Navigate: System Security > Column Level Security

Table: sys_user
Fields: 
  - social_security_number (Edge Encrypted)
  - bank_account (Edge Encrypted)

Edge Encryption:
  - Data encrypted at rest AND in transit
  - Decrypted only at edge (browser)
  - Not searchable when encrypted
  - Requires Edge Encryption plugin
```

### Encryption in Scripts
```javascript
// Encrypt a value
var encryptor = new GlideEncrypter();
var encrypted = encryptor.encrypt('sensitive data');

// Decrypt
var decrypted = encryptor.decrypt(encrypted);

// For password fields (one-way hash)
var gr = new GlideRecord('my_table');
if (gr.get(sys_id)) {
    gr.setValue('password_field', 'new_password'); // auto-hashed
    gr.update();
}
```

## Security Best Practices

### Input Validation
```javascript
// NEVER trust user input in encoded queries
var userInput = request.queryParams.filter;
// BAD: gr.addEncodedQuery(userInput); // SQL injection risk!

// GOOD: Validate and sanitize
var allowedFields = ['number', 'state', 'priority'];
var field = allowedFields.indexOf(userInput) >= 0 ? userInput : 'number';
gr.addQuery(field, sanitizedValue);
```

### Prevent Script Injection
```javascript
// Never use eval()
// eval(userInput); // NEVER!

// Never construct queries from raw user input
// gr.addEncodedQuery(userInput); // DANGEROUS!

// Use parameterized approaches
var gr = new GlideRecord('incident');
gr.addQuery('number', userProvidedNumber); // safe — single field query
gr.query();
```

### Impersonation
```javascript
// Check if user is impersonating
var impersonating = gs.isInteractive() && gs.getImpersonatingUserName() != '';

// Impersonate in script (requires admin)
var impersonator = new GlideImpersonate();
impersonator.impersonate(targetUserSysId);
// ... perform actions as target user
impersonator.unimpersonate();
```

### Delegation
```
Navigate: System Security > Delegated Administration

// Delegate group management
// Delegate approval authority
// Time-bound delegation (start/end date)
// Delegate specific roles only
```

## Security Operations (SecOps) Integration

```
Key tables:
- sn_si_incident — Security Incidents
- sn_vul_vulnerable_item — Vulnerabilities
- sn_ti_indicator — Threat Indicators

Integration points:
- SIEM (Splunk, QRadar) → Security Incident Response
- Vulnerability scanners (Qualys, Tenable) → Vulnerability Response
- Threat intel feeds → Threat Intelligence
```

## Audit & Compliance

```javascript
// Check audit history
var gr = new GlideRecord('sys_audit');
gr.addQuery('tablename', 'incident');
gr.addQuery('documentkey', incidentSysId);
gr.orderByDesc('sys_created_on');
gr.setLimit(50);
gr.query();
while (gr.next()) {
    gs.info(gr.getValue('fieldname') + ': ' + 
            gr.getValue('oldvalue') + ' → ' + gr.getValue('newvalue'));
}
```
