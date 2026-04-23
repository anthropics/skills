# Flow Designer & Process Automation

## Flow Triggers

### Record-Based Triggers
- **Created** — fires when record is inserted
- **Updated** — fires when record is updated (with optional conditions)
- **Created or Updated** — combination
- **Deleted** — fires on record deletion

```
Trigger: Record → Created or Updated
Table: incident
Condition: Priority is Critical AND State changes to In Progress
Run: For each unique change (deduplicate)
```

### Scheduled Triggers
- **Daily / Weekly / Monthly** — recurring schedule
- **Once** — one-time execution
- **Repeat** — custom interval

### Application Triggers
- **Inbound email** — fire on email receipt
- **REST** — fire from external REST call
- **Service Catalog** — catalog item submission
- **MetricBase** — threshold alerts

## Actions

### Built-in Actions (most common)
| Action | Use |
|--------|-----|
| Create Record | Insert a new record |
| Update Record | Modify existing record |
| Delete Record | Remove a record |
| Look Up Records | Query and return records |
| Ask for Approval | Create approval request |
| Send Email | Send notification |
| Send Notification | Use notification record |
| Create Task | Create a task record |
| Run Script | Execute server-side JavaScript |
| Log | Add to flow execution log |
| Wait for Condition | Pause until condition met |

### Look Up Records Action
```
Table: sys_user_grmember
Conditions: group = [Data Pill: Trigger.assignment_group]
Return: Multiple records (First 100)
Fields to return: user, user.email, user.name
```

### Run Script Action
```javascript
(function execute(inputs, outputs) {
    var ga = new GlideAggregate('incident');
    ga.addQuery('assignment_group', inputs.group_id);
    ga.addActiveQuery();
    ga.addAggregate('COUNT');
    ga.query();
    
    outputs.count = 0;
    if (ga.next()) {
        outputs.count = parseInt(ga.getAggregate('COUNT'), 10);
    }
})(inputs, outputs);

// Inputs: group_id (Reference: sys_user_group)
// Outputs: count (Integer)
```

## Subflows (Reusable)

### Creating a Reusable Approval Subflow
```
Name: Standard Approval Process
Inputs:
  - record (Reference: task)
  - approval_type (String: "manager" | "group")
  - approval_group (Reference: sys_user_group, optional)

Steps:
  1. IF approval_type == "manager"
     → Look Up Record: Get manager of record.opened_by
     → Ask for Approval: manager, Due in 3 days
  2. ELSE
     → Ask for Approval: approval_group, Due in 5 days
  3. IF Approval.state == "approved"
     → Update Record: record.state = "Work in Progress"
     → Output: approved = true
  4. ELSE
     → Update Record: record.state = "On Hold"  
     → Output: approved = false

Outputs:
  - approved (Boolean)
  - approver (Reference: sys_user)
```

### Calling a Subflow from a Flow
```
Step: Subflow → Standard Approval Process
  record: [Trigger Record]
  approval_type: "manager"
  
IF [Subflow Output: approved] == true
  → Continue processing
ELSE
  → Send Email to requester: "Request denied"
```

## Error Handling

### Try/Catch in Flows
```
1. Try
   └── Step 1: Call REST API
   └── Step 2: Process Response
2. Catch
   └── Step 3: Log Error
   └── Step 4: Create Incident for integration failure
   └── Step 5: Send notification to integration team
```

### Error Handling in Script Action
```javascript
(function execute(inputs, outputs) {
    try {
        var rm = new sn_ws.RESTMessageV2('ExternalAPI', 'POST');
        rm.setStringParameterNoEscape('data', JSON.stringify(inputs.payload));
        var response = rm.execute();
        
        outputs.status_code = response.getStatusCode();
        outputs.response_body = response.getBody();
        outputs.success = (outputs.status_code >= 200 && outputs.status_code < 300);
        
    } catch(e) {
        outputs.success = false;
        outputs.error_message = e.message;
    }
})(inputs, outputs);
```

## Parallel Execution

```
Parallel Block:
  Branch 1: Look up CI details (CMDB)
  Branch 2: Get user's recent incidents
  Branch 3: Check SLA status

After Parallel:
  → Use all three results in assignment logic
```

## Flow Variables & Data Pills

### Variable Types
- **String, Integer, Boolean** — primitives
- **Reference** — link to a record
- **Record** — full GlideRecord
- **Date/Time** — temporal values
- **Array** — list of values (limited support)

### Using Data Pills
```
Trigger Record → caller_id.email     (dot-walking through reference)
Step 1 Output → records[0].number    (first record from lookup)
Flow Variable → approval_count       (custom variable)
```

### Transform Data Pills
```
String: [Trigger.number] + " - " + [Trigger.short_description]
Condition: [Step1.count] > 10
Reference: [Lookup.record.sys_id]
```

## Custom Spoke Actions

### Creating a Custom Action
```
Name: Send Slack Message
Category: Custom Integrations
Application: My Scoped App

Inputs:
  - channel (String, mandatory)
  - message (String, mandatory)
  - webhook_url (String, mandatory)

Script Step:
(function execute(inputs, outputs) {
    var rm = new sn_ws.RESTMessageV2();
    rm.setEndpoint(inputs.webhook_url);
    rm.setHttpMethod('POST');
    rm.setRequestHeader('Content-Type', 'application/json');
    rm.setRequestBody(JSON.stringify({
        channel: inputs.channel,
        text: inputs.message
    }));
    
    var response = rm.execute();
    outputs.status = response.getStatusCode();
    outputs.success = (outputs.status == 200);
})(inputs, outputs);

Outputs:
  - status (Integer)
  - success (Boolean)
```

## Decision Tables

```
Decision Table: Incident Auto-Assignment
Inputs: category, subcategory, location

Rules:
  | Category | Subcategory | Location    | → Assignment Group     |
  |----------|-------------|-------------|------------------------|
  | network  | *           | Building A  | Network Team - East    |
  | network  | *           | Building B  | Network Team - West    |
  | software | email       | *           | Email Support          |
  | software | *           | *           | General Software Team  |
  | hardware | *           | *           | Hardware Team          |
  | *        | *           | *           | Service Desk           |

Usage in Flow:
  Step: Decision Table → Incident Auto-Assignment
    category: [Trigger.category]
    subcategory: [Trigger.subcategory]  
    location: [Trigger.caller_id.location]
  Output: assignment_group → use in Update Record step
```

## Flow Best Practices

1. **Name flows descriptively** — "Auto-assign Critical Incidents" not "Flow 1"
2. **Use subflows** for any logic reused in 2+ flows
3. **Add error handling** (Try/Catch) for all external calls
4. **Set run-as** to a service account, not admin
5. **Use conditions on triggers** to filter early — don't query in flow
6. **Limit lookups** — get only fields you need
7. **Test with Flow Execution** details view for debugging
8. **Avoid infinite loops** — watch for flows that update records which trigger the same flow
9. **Use Flow Variables** to reduce repeated lookups
10. **Document complex flows** with Log actions explaining each section

## Process Automation Designer (PAD) Connection

PAD / Playbooks use Flow Designer actions under the hood:
- Playbook activities can call Subflows
- Custom actions are reusable in both Flows and Playbooks
- See `playbooks.md` for Playbook-specific patterns
