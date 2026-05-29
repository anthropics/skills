# Advanced ServiceNow Topics

## Predictive Intelligence

### Classification Model
```
Navigate: Predictive Intelligence > Prediction Definitions

Use case: Auto-classify incident category/assignment group

Configuration:
  Table: incident
  Training filter: active=false^resolved_atISNOTEMPTY (closed incidents)
  
  Input fields (features):
    - short_description (NLP)
    - description (NLP)
    - category
    - caller_id.department
    
  Prediction field: assignment_group
  
  Training schedule: Weekly
  Minimum records: 5,000+ for good accuracy
  Confidence threshold: 0.7 (70%)
```

### Similarity Model
```
Navigate: Predictive Intelligence > Similarity Definitions

Use case: Find similar incidents for faster resolution

Configuration:
  Table: incident
  Active filter: active=true
  
  Similarity fields:
    - short_description (weight: 5)
    - description (weight: 3)
    - category (weight: 2)
    - cmdb_ci (weight: 4)
    
  Max similar results: 5
  Minimum score: 0.6
```

### Using Predictions in Scripts
```javascript
// Check prediction result
var gr = new GlideRecord('incident');
if (!gr.get(incidentSysId)) {
    gs.warn('Incident not found: ' + incidentSysId);
    return;
}

// Prediction fills ml_prediction field
var prediction = gr.getValue('ml_prediction');
var confidence = gr.getValue('ml_confidence');

if (parseFloat(confidence) > 0.8) {
    // Auto-assign if high confidence
    gr.setValue('assignment_group', prediction);
    gr.update();
}
```

### Now Assist (GenAI) — Xanadu+
```
Features:
- Summarize incident/case
- Generate resolution notes
- Suggest knowledge articles
- Code assist for developers
- Virtual Agent conversation improvement

Configuration:
  Navigate: Now Assist > Setup
  Enable: per-table, per-use-case
  Model: ServiceNow LLM or bring-your-own (Azure OpenAI, etc.)
```

## Virtual Agent

### NLU Model Setup
```
Navigate: Virtual Agent > NLU Workbench

Model: My IT Support NLU
Intents:
  - Reset Password
    Utterances:
      "I need to reset my password"
      "forgot my password"
      "can't log in to my account"
      "password expired"
      "change my password"
      
  - Report Outage
    Utterances:
      "service is down"
      "system is not working"
      "email is broken"
      "can't access the VPN"

Entities:
  - Application (software, email, VPN, SAP, etc.)
  - Priority (urgent, critical, normal, low)
  - Location (office, remote, building names)

Training: Requires 15+ utterances per intent for good accuracy
```

### Topic Design
```
Topic: Reset Password
Trigger: NLU Intent = "Reset Password"

Flow:
  1. Bot: "I can help you reset your password. Which system?"
     → Collect: Application entity
     
  2. Bot: "Let me verify your identity. What's your employee ID?"
     → Collect: employee_id (text input)
     
  3. Automation: Call Subflow "Verify Identity"
     → Input: employee_id
     → Output: verified (boolean)
     
  4. Decision: verified?
     → Yes: 
        Automation: Call Subflow "Reset Password"
        Bot: "Your password has been reset. Check your email for instructions."
     → No:
        Bot: "I couldn't verify your identity. Let me connect you with an agent."
        → Transfer to Live Agent (queue: Password Reset)
```

### Virtual Agent Script Block
```javascript
// Server-side script in VA topic
(function execute(inputs, outputs) {
    var userId = inputs.employee_id;
    
    var gr = new GlideRecord('sys_user');
    gr.addQuery('employee_number', userId);
    gr.setLimit(1);
    gr.query();
    
    if (gr.next()) {
        outputs.user_found = true;
        outputs.user_name = gr.getValue('name');
        outputs.user_sys_id = gr.getUniqueValue();
    } else {
        outputs.user_found = false;
    }
})(inputs, outputs);
```

## CMDB Best Practices

### CI Lifecycle
```
States: Ordered → Received → In Stock → In Use → In Maintenance → Retired → Absent

Key tables:
  cmdb_ci                    — Base CI class
  cmdb_ci_server            — Servers
  cmdb_ci_app_server        — Application servers
  cmdb_ci_service           — Business services
  cmdb_ci_db_instance       — Database instances
  cmdb_ci_network_adapter   — Network devices
  cmdb_rel_ci               — CI relationships
```

### CMDB Query Patterns
```javascript
// Find all CIs in a service map
var gr = new GlideRecord('cmdb_rel_ci');
gr.addQuery('parent', businessServiceSysId);
gr.addQuery('type.name', 'Depends on::Used by');
gr.query();
while (gr.next()) {
    var childCI = gr.getDisplayValue('child');
    var relType = gr.getDisplayValue('type');
    gs.info(childCI + ' (' + relType + ')');
}

// Find all incidents related to a CI (including children)
var cis = new SNC.CMDBUtil().getAllChildren(ciSysId); // includes self
var gr = new GlideRecord('incident');
gr.addQuery('cmdb_ci', 'IN', cis);
gr.addActiveQuery();
gr.query();
```

### CMDB Health Dashboard
```
Navigate: CMDB > CMDB Health

Metrics:
- Completeness: % of required fields populated
- Compliance: CIs following naming standards
- Relationships: orphaned CIs, missing dependencies
- Staleness: CIs not updated by discovery in X days
- Duplicates: potential duplicate CIs

Health Checks:
  Navigate: CMDB Health > CMDB Health Checks
  - Missing relationships
  - Orphan CIs (no service mapping)
  - Stale CIs (no recent discovery)
  - Duplicate detection rules
```

### Discovery & Service Mapping
```
Key components:
- Discovery: Auto-populate CMDB from network scans
- Service Mapping: Map CI relationships (application dependencies)
- MID Server: On-premise proxy for discovery

// Trigger discovery programmatically
var discovery = new SNC.DiscoveryAPI();
discovery.discoverIP('10.0.0.1');

// Check last discovery
var gr = new GlideRecord('cmdb_ci_server');
if (gr.get(serverSysId)) {
    gs.info('Last discovered: ' + gr.getValue('last_discovered'));
}
```

## Agent Workspace Configuration

### Custom Record Page
```
Navigate: Workspace Experience > Workspace Configuration > [workspace]

Record Page layout:
  Primary tab:
    - Form fields (configurable sections)
    - Related lists
  
  Contextual sidebar:
    - Activity Stream (default)
    - Similar Records (Predictive Intelligence)
    - AI-generated summary (Now Assist)
    - Related CIs
    - Playbook panel

Configurable per table:
  incident, problem, change_request, sc_request, etc.
```

### Agent Assist
```
Features (Xanadu+):
- Recommended knowledge articles
- Similar incident resolutions
- Auto-generated summaries
- Suggested next actions

Configuration:
  Navigate: Agent Workspace > Agent Assist Configuration
  Enable per table/workspace
  Configure recommendation sources
```

## Employee Center

### Content Management
```
Navigate: Employee Center > Content Management

Content types:
  - Announcements
  - Knowledge articles
  - Quick links
  - Catalog items
  - Video content

Content blocks:
  - Rich text
  - Image carousel
  - Catalog category browser
  - Knowledge search
  - My requests/approvals widget
```

### Custom Catalog Items
```
Navigate: Service Catalog > Catalog Items

Item: Request New Laptop
Variables:
  - Laptop model (Select Box: Standard, Performance, Executive)
  - Business justification (Multi-line text, mandatory)
  - Preferred delivery date (Date)
  - Manager approval required: true

Workflow/Flow:
  1. Manager approval
  2. IT approval (if Executive model)
  3. Create procurement task
  4. Delivery scheduling
  5. Asset assignment
```

## Domain Separation

### Key Concepts
```
- Domain: logical partition of data (e.g., Company A, Company B)
- Domain visibility: which domains a user can see
- Domain context: current working domain
- Global domain: visible to all domains

Configuration:
  Navigate: System Properties > Domain Support
  Enable: glide.sys.domain.enable = true (instance-level setting)

Tables:
  domain — Domain definitions
  sys_user.sys_domain — User's primary domain
  [any table].sys_domain — Record's domain
```

### Scripting with Domains
```javascript
// Get current domain
var currentDomain = gs.getSession().getCurrentDomainID();

// Query within domain (automatic if domain separation is on)
var gr = new GlideRecord('incident');
gr.addQuery('sys_domain', domainSysId);
gr.query();

// Create record in specific domain
var gr = new GlideRecord('incident');
gr.initialize();
gr.setValue('sys_domain', targetDomainSysId);
gr.setValue('short_description', 'Domain-specific incident');
gr.insert();
```

## Upgrade Planning

### Pre-Upgrade Checklist
```
1. Instance Scan — identify customizations on OOB records
2. Skipped records report — review sys_update_xml where remote_update_name is populated
3. Custom table review — check for deprecated API usage
4. Plugin compatibility — verify installed plugins are supported
5. Integration testing — test all external integrations
6. Performance baseline — document current metrics for comparison
```

### Upgrade-Safe Development Patterns
```javascript
// DON'T modify OOB Business Rules — create new ones
// DON'T modify OOB Script Includes — extend them
// DON'T modify OOB ACLs — add new ACLs

// DO: Extend OOB Script Includes
var MyIncidentUtils = Class.create();
MyIncidentUtils.prototype = Object.extendsObject(IncidentUtils, {
    // Add your custom methods here
    myCustomMethod: function() {
        // Custom logic that won't be overwritten on upgrade
    },
    type: 'MyIncidentUtils'
});

// DO: Use sys_properties instead of hardcoding values
var threshold = gs.getProperty('x_myapp.escalation_threshold', '4');

// DO: Use update sets for ALL changes
// DO: Test upgrades in sub-prod first
// DO: Document all customizations
```

## Multi-Instance Architecture

```
Patterns:
  - Dev → Test → Staging → Prod (standard pipeline)
  - Hub-and-spoke (central instance + departmental instances)
  - Geo-distributed (regional instances with data sync)

Data replication:
  - Update sets: configuration deployment
  - Data replication (replication_queue): runtime data sync
  - MID Server: on-premise connectivity for each instance
  - IntegrationHub: cross-instance API calls
```

## Delegated Development

```
App Engine Studio:
  Navigate: App Engine Studio
  
  Low-code development for:
  - Tables and fields
  - Forms and lists
  - Flows and automation
  - Workspaces
  - Dashboards
  
  Guard rails:
  - Template-based development
  - Admin review before publish
  - Scoped application only
  - Cannot modify OOB tables
  - Limited scripting capability
```
