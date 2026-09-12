# ServiceNow Testing & Debugging

## Automated Test Framework (ATF)

### Creating a Test

Navigate: **Automated Test Framework > Tests**

### Server-Side Test Steps

```
Test: Verify Incident Auto-Assignment

Step 1: Create Record
  Table: incident
  Values:
    short_description: ATF Test Incident
    category: network
    caller_id: [ATF test user]
  Save as: incident_record

Step 2: Assert Field Value  
  Record: {incident_record}
  Field: assignment_group
  Expected: Network Operations
  Assertion: Equals

Step 3: Assert Field Value
  Record: {incident_record}
  Field: state
  Expected: New
  Assertion: Equals

Step 4: Update Record
  Record: {incident_record}
  Values:
    state: In Progress
    assigned_to: [ATF test user]

Step 5: Assert Condition
  Condition: {incident_record}.state == 2
  
Step 6: Delete Record (cleanup)
  Record: {incident_record}
```

### Parameterized Tests
```
Test: Verify Priority Matrix

Parameters:
  | impact | urgency | expected_priority |
  |--------|---------|-------------------|
  | 1      | 1       | 1                 |
  | 1      | 2       | 2                 |
  | 2      | 1       | 2                 |
  | 2      | 2       | 3                 |
  | 3      | 3       | 5                 |

Step 1: Create Record
  Table: incident
  Values:
    impact: {parameter.impact}
    urgency: {parameter.urgency}
    short_description: Priority Matrix Test

Step 2: Assert Field Value
  Field: priority
  Expected: {parameter.expected_priority}
```

### Server Script Step
```javascript
// Custom assertion logic
(function(outputs, steps, params, stepResult, assertEqual) {
    
    var gr = new GlideRecord('incident');
    gr.addQuery('short_description', 'CONTAINS', 'ATF Test');
    gr.addActiveQuery();
    gr.query();
    
    var count = 0;
    while (gr.next()) count++;
    
    assertEqual({
        name: 'Active test incidents should be zero after cleanup',
        shouldbe: 0,
        value: count
    });
    
    stepResult.setOutputMessage('Found ' + count + ' remaining test records');
    
})(outputs, steps, params, stepResult, assertEqual);
```

### REST Step (test API endpoints)
```
Step: REST Request
  Method: POST
  URL: /api/now/table/incident
  Body: {
    "short_description": "ATF REST Test",
    "category": "software"
  }
  Expected Status: 201
  
Step: Assert JSON Body
  Response field: result.number
  Assertion: Starts with "INC"
```

## Client-Side ATF Tests

### Testing Client Scripts
```
Step: Open Form
  Table: incident
  Record: {created_record}
  View: Default

Step: Set Field Value
  Field: category
  Value: network

Step: Assert Field Property
  Field: cmdb_ci
  Property: mandatory
  Expected: true

Step: Assert Field Property
  Field: u_network_segment
  Property: visible
  Expected: true

Step: Set Field Value
  Field: priority
  Value: 1 - Critical

Step: Click UI Action
  Button: Escalate to Major

Step: Assert Form Message
  Type: info
  Contains: "escalated"
```

### Client Script Step (custom client assertions)
```javascript
// Custom client-side test step
(function(outputs, steps, params, stepResult, assertEqual) {
    
    var priority = g_form.getValue('priority');
    var isMandatory = g_form.isMandatory('cmdb_ci');
    
    assertEqual({
        name: 'CI should be mandatory for P1',
        shouldbe: true,
        value: isMandatory
    });
    
    // Check field messages
    var fieldMsg = document.querySelector('[data-field="caller_id"] .field-msg');
    assertEqual({
        name: 'VIP message should be displayed',
        shouldbe: true,
        value: fieldMsg !== null
    });
    
})(outputs, steps, params, stepResult, assertEqual);
```

## Test Suites

### Creating a Test Suite
```
Navigate: Automated Test Framework > Suites

Name: ITSM Regression Suite
Tests:
  1. Incident Auto-Assignment (order: 100)
  2. Incident Priority Matrix (order: 200)
  3. Incident Resolution Validation (order: 300)
  4. Problem Creation from Incident (order: 400)
  5. Change Request Approval Flow (order: 500)

Schedule: Weekly, Sunday 2:00 AM
Notification: Email on failure to dev-team@company.com
```

### Suite Properties
```
Run order: Ordered (respect test sequence) vs Unordered (parallel-friendly)
Abort on failure: true (stop suite if a test fails)
Browser: Chrome, Firefox (for client-side tests)
Test runner user: atf_test_user (dedicated service account)
```

## Mock Data & Test Data Management

### ATF Test Data
```javascript
// Setup script (runs before test)
(function(outputs, steps, params, stepResult) {
    
    // Create test user
    var user = new GlideRecord('sys_user');
    user.initialize();
    user.setValue('user_name', 'atf_test_user_' + gs.generateGUID());
    user.setValue('first_name', 'ATF');
    user.setValue('last_name', 'TestUser');
    user.setValue('email', 'atf@test.com');
    user.setValue('active', true);
    outputs.test_user_id = user.insert();
    
    // Create test group
    var group = new GlideRecord('sys_user_group');
    group.initialize();
    group.setValue('name', 'ATF Test Group ' + gs.generateGUID());
    outputs.test_group_id = group.insert();
    
    // Add user to group
    var member = new GlideRecord('sys_user_grmember');
    member.initialize();
    member.setValue('user', outputs.test_user_id);
    member.setValue('group', outputs.test_group_id);
    member.insert();
    
})(outputs, steps, params, stepResult);
```

### Cleanup Script (runs after test)
```javascript
(function(outputs, steps, params, stepResult) {
    
    // Clean up in reverse order of creation
    var tables = ['sys_user_grmember', 'sys_user_group', 'sys_user', 'incident'];
    var fields = ['user', 'sys_id', 'sys_id', 'sys_id'];
    var values = [
        steps.setup.test_user_id,
        steps.setup.test_group_id,
        steps.setup.test_user_id,
        steps.create_incident.sys_id
    ];
    
    for (var i = 0; i < tables.length; i++) {
        var gr = new GlideRecord(tables[i]);
        gr.addQuery(fields[i], values[i]);
        gr.deleteMultiple();
    }
    
})(outputs, steps, params, stepResult);
```

## Instance Scan

### Running Instance Scan
```
Navigate: Instance Scan > Scan Results

Checks include:
- Performance: slow queries, missing indexes, N+1 patterns
- Security: hardcoded credentials, eval() usage, XSS risks
- Best practices: deprecated API usage, global scope violations
- Upgrade safety: customizations on OOB records
```

### Custom Scan Checks
```
Navigate: Instance Scan > Scan Checks

Name: Check for hardcoded sys_ids
Type: Script Include scan
Table: sys_script_include
Script:
(function(engine) {
    var pattern = /[a-f0-9]{32}/g;
    var script = engine.getValue('script');
    var matches = script.match(pattern);
    if (matches && matches.length > 0) {
        engine.finding({
            description: 'Found ' + matches.length + ' potential hardcoded sys_ids',
            severity: 'warning'
        });
    }
})(engine);
```

## Debugging

### Session Debug Modules
```
Navigate: System Diagnostics > Session Debug

Enable (per session):
- Debug Business Rule — shows which BRs fire
- Debug Security — shows ACL evaluation
- Debug SQL — shows database queries  
- Debug Workflow — shows workflow execution (legacy)
- Debug Flow — shows Flow Designer execution

Output: System Logs > Session Debug Log
```

### Script Debugger
```
Navigate: System Diagnostics > Script Debugger

Features:
- Set breakpoints in Business Rules, Script Includes
- Step through code line by line
- Inspect variables and GlideRecord values
- Watch expressions
- Call stack inspection

// Programmatic breakpoint:
gs.breakpoint(); // triggers debugger if session debug enabled
```

### Transaction Log
```
Navigate: System Logs > Transactions

Key fields:
- URL — what was accessed
- Response time — total ms
- SQL count — number of DB queries
- Business rule count — BRs executed

// Filter for slow transactions:
response_time > 5000 (> 5 seconds)
```

### Debugging Business Rules
```javascript
// Temporary debug logging (remove before prod!)
(function executeRule(current, previous) {
    gs.info('[DEBUG] BR fired on ' + current.getValue('number'));
    gs.info('[DEBUG] State change: ' + previous.getValue('state') + ' → ' + current.getValue('state'));
    gs.info('[DEBUG] Changed fields: ' + current.getChangedFields());
    
    // ... actual logic
    
})(current, previous);
```

### Debugging Client Scripts
```javascript
// Browser console (F12)
function onChange(control, oldValue, newValue, isLoading) {
    jslog('onChange fired: ' + oldValue + ' → ' + newValue);
    console.log('Debug: field value = ', g_form.getValue('state'));
    
    // Check client-side errors in browser DevTools > Console
}
```

### Debugging REST API Calls
```javascript
// In Scripted REST API:
(function process(request, response) {
    gs.info('[REST DEBUG] Method: ' + request.getHeader('X-HTTP-Method'));
    gs.info('[REST DEBUG] Path params: ' + JSON.stringify(request.pathParams));
    gs.info('[REST DEBUG] Query params: ' + JSON.stringify(request.queryParams));
    gs.info('[REST DEBUG] Body: ' + JSON.stringify(request.body.data));
    
    // ... process request
})(request, response);
```

## Performance Testing

### Load Testing Approach
```
1. Use ATF to create realistic test scenarios
2. Run multiple test suites in parallel
3. Monitor: System Diagnostics > Stats
4. Check: Transaction times, semaphore waits, query times
5. Identify bottlenecks: slow queries, BR execution time

// Key metrics to monitor:
// - Average transaction response time
// - p95 response time
// - Database query count per transaction
// - Business Rule execution time per transaction
// - Cache hit/miss ratio
```

## Testing Best Practices

1. **Isolate tests** — each test creates AND cleans up its own data
2. **Use dedicated ATF user** — don't run as admin (tests ACLs)
3. **Test Business Rules independently** — create record, assert result
4. **Test client scripts with ATF client steps** — not manual browser testing
5. **Run suites on schedule** — catch regressions early
6. **Test edge cases** — null values, empty strings, max lengths
7. **Test security** — impersonate non-admin user, verify ACL enforcement
8. **Version control tests** — include in scoped app / update set
9. **Don't test platform** — test YOUR customizations, not OOB behavior
10. **Clean up** — ALWAYS delete test data, even on failure (use finally blocks)
