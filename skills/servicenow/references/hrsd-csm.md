# HRSD & CSM

## HRSD (HR Service Delivery)

### Core Tables
```
sn_hr_core_case          — HR Case (main record)
sn_hr_core_case_operation — Case operations/tasks
sn_hr_le_lifecycle_event — Lifecycle Events
sn_hr_core_template      — Document templates
sn_hr_core_service       — HR Services
sn_hr_core_topic         — Topics/Categories
```

### HR Case Management
```
HR Case lifecycle:
  Draft → Open → Work in Progress → Pending → Resolved → Closed

Case types:
  - General Inquiry
  - Benefits
  - Payroll
  - Leave of Absence
  - Employee Relations
  - Onboarding / Offboarding
  - Document Requests

Creating cases:
  - Employee Center portal
  - Virtual Agent
  - Email inbound action
  - Walk-up / phone (agent creates)
  - Lifecycle Event auto-generation
```

### HR Case Scripting
```javascript
// Business Rule: Auto-assign HR case based on topic
(function executeRule(current, previous) {
    var topic = current.getValue('hr_topic');
    
    var topicGr = new GlideRecord('sn_hr_core_topic');
    if (topicGr.get(topic)) {
        var group = topicGr.getValue('assignment_group');
        if (group) {
            current.setValue('assignment_group', group);
        }
    }
    
    // Set SLA based on case type
    var caseType = current.getValue('hr_service');
    if (caseType) {
        var svcGr = new GlideRecord('sn_hr_core_service');
        if (svcGr.get(caseType) && svcGr.getValue('sla')) {
            current.setValue('sla', svcGr.getValue('sla'));
        }
    }
})(current, previous);
```

### Lifecycle Events
```
Lifecycle Events automate multi-step HR processes triggered 
by employee milestones.

Examples:
  - New Hire Onboarding → generates 15-20 tasks across departments
  - Promotion → update role, salary, badge access
  - Transfer → notify both managers, update location
  - Leave of Absence → suspend access, notify benefits
  - Offboarding → collect equipment, revoke access, final pay

Structure:
  Lifecycle Event
  ├── Activity Set 1: IT Tasks
  │   ├── Provision laptop
  │   ├── Create email account
  │   └── Set up VPN access
  ├── Activity Set 2: Facilities
  │   ├── Assign desk/badge
  │   └── Parking pass
  ├── Activity Set 3: HR
  │   ├── Benefits enrollment
  │   ├── Policy acknowledgment
  │   └── Emergency contacts
  └── Activity Set 4: Manager
      ├── Assign buddy/mentor
      └── Schedule orientation

Triggering lifecycle events:
```
```javascript
// Script to trigger a lifecycle event
var le = new sn_hr_le.LifecycleEventAPI();
var params = {
    subject_person: userSysId,      // Employee
    lifecycle_event: leSysId,        // Lifecycle Event definition
    opened_for: userSysId,
    source_record_table: 'sys_user',
    source_record_id: userSysId
};
var caseId = le.createLifecycleEventCase(params);
```

### Document Templates
```
Navigate: HR Service Delivery > Document Templates

Use case: Auto-generate offer letters, tax forms, policy docs

Template variables:
  ${employee.name}, ${employee.title}, ${employee.department}
  ${employee.manager.name}, ${employee.location}
  ${effective_date}, ${salary}, ${start_date}
  
Generate document via script:
```
```javascript
// Generate document from template
var docGen = new sn_hr_core.HRDocumentGeneration();
var templateSysId = 'abc123...';
var caseSysId = current.sys_id.toString();
var result = docGen.generateDocument(templateSysId, caseSysId);
```

### Employee Center
```
Employee Center is the self-service portal for HR:
  - Topic categories (browse by life event)
  - Knowledge articles
  - Request HR services (catalog items)
  - View my HR cases
  - Virtual Agent integration
  
Customization:
  - Branding, layout via Employee Center Designer
  - Content Blocks for announcements
  - Audience targeting (by department, location, role)
```

### HRSD Best Practices
1. **Lifecycle Events** for repeatable processes — don't manually create tasks
2. **Topic taxonomy** should mirror how employees think, not HR org structure
3. **Virtual Agent** as first contact — deflect common queries (PTO balance, pay dates)
4. **Document templates** for anything requiring employee signatures
5. **Sensitive fields** — use ACLs to restrict PII visibility (SSN, salary)
6. **COE (Center of Excellence)** model — shared services with specialized tiers

---

## CSM (Customer Service Management)

### Core Tables
```
sn_customerservice_case  — Customer Case
csm_consumer             — Consumer (B2C)
customer_account         — Account (B2B)
customer_contact         — Contact (person at an account)
csm_product              — Product
csm_asset                — Installed Product/Asset
sn_customerservice_community — Community forums
```

### Customer Case Management
```
Case lifecycle:
  New → Open → In Progress → Pending (customer/vendor) → Resolved → Closed

Case channels:
  - Customer Portal (self-service)
  - Email inbound
  - Phone (agent creates)
  - Chat (Agent Chat / Virtual Agent)
  - Social media (Twitter, Facebook integration)
  - Community forums (case from post)
  - API (partner systems)
  
Matching:
  - Email → Contact → Account (auto-match)
  - Phone → CTI integration → Contact lookup
  - Portal → Authenticated user → Contact record
```

### CSM Scripting Patterns
```javascript
// Business Rule: Auto-set account and entitlement on case creation
(function executeRule(current, previous) {
    // Look up contact's account
    if (!gs.nil(current.getValue('contact')) && gs.nil(current.getValue('account'))) {
        var contact = new GlideRecord('customer_contact');
        if (contact.get(current.getValue('contact'))) {
            current.setValue('account', contact.getValue('account'));
        }
    }
    
    // Check entitlement (SLA eligibility)
    if (!gs.nil(current.getValue('account'))) {
        var entGr = new GlideRecord('service_entitlement');
        entGr.addQuery('account', current.getValue('account'));
        entGr.addActiveQuery();
        entGr.addQuery('end_date', '>', new GlideDateTime());
        entGr.orderByDesc('priority');
        entGr.setLimit(1);
        entGr.query();
        if (entGr.next()) {
            current.setValue('entitlement', entGr.getUniqueValue());
        }
    }
})(current, previous);
```

### Account & Contact Management
```javascript
// Script Include: Customer lookup utility
var CustomerUtils = Class.create();
CustomerUtils.prototype = {
    initialize: function() {},
    
    getAccountHealth: function(accountSysId) {
        var result = {
            open_cases: 0,
            escalated_cases: 0,
            avg_resolution_hours: 0,
            csat_score: 0
        };
        
        // Open cases
        var ga = new GlideAggregate('sn_customerservice_case');
        ga.addQuery('account', accountSysId);
        ga.addActiveQuery();
        ga.addAggregate('COUNT');
        ga.query();
        if (ga.next()) {
            result.open_cases = parseInt(ga.getAggregate('COUNT'));
        }
        
        // Escalated cases
        ga = new GlideAggregate('sn_customerservice_case');
        ga.addQuery('account', accountSysId);
        ga.addQuery('escalation', '>', 0);
        ga.addActiveQuery();
        ga.addAggregate('COUNT');
        ga.query();
        if (ga.next()) {
            result.escalated_cases = parseInt(ga.getAggregate('COUNT'));
        }
        
        return result;
    },
    
    type: 'CustomerUtils'
};
```

### Entitlements & SLAs
```
Entitlements define what support a customer receives:
  - Support level (Gold, Silver, Bronze)
  - Response time SLAs
  - Number of cases per month
  - Available channels (phone, email, chat)
  
Tables:
  - service_entitlement: entitlement definitions
  - sla: SLA definitions
  - task_sla: SLA instances on records

SLA setup:
  Navigate: Service Level Management > SLA > SLA Definitions
  
  Example SLA:
    Name: Gold - P1 Response
    Table: sn_customerservice_case
    Conditions: entitlement.name = Gold AND priority = 1
    Duration: 1 hour
    Type: Response (time to first contact)
```

### Customer Portal
```
CSM Portal (Service Portal-based):
  - Knowledge base browsing
  - Case submission and tracking
  - Community forums
  - Product documentation
  - Chat with agent / Virtual Agent
  - Asset/product registration
  
Customization:
  - Branded per account (multi-tenant)
  - Role-based content visibility
  - Custom widgets for product-specific features
```

### Community Forums
```
Navigate: Customer Service > Community

Features:
  - Forum categories
  - Q&A format (mark best answer)
  - Moderation tools
  - Auto-create case from unresolved posts
  - Knowledge article linking
  - Gamification (points, badges)
  
Scripting — create case from forum post:
```
```javascript
// Scheduled job or Business Rule on community post
var post = new GlideRecord('sn_customerservice_community_post');
post.addQuery('resolved', false);
post.addQuery('sys_created_on', '<', gs.daysAgoStart(7)); // Unresolved 7+ days
post.query();
while (post.next()) {
    var caseGr = new GlideRecord('sn_customerservice_case');
    caseGr.initialize();
    caseGr.setValue('short_description', 'Community post: ' + post.getValue('title'));
    caseGr.setValue('description', post.getValue('body'));
    caseGr.setValue('contact', post.getValue('author'));
    caseGr.setValue('category', 'community_escalation');
    caseGr.insert();
    
    // Link case to post
    post.setValue('case', caseGr.getUniqueValue());
    post.update();
}
```

### CSM Best Practices
1. **Account hierarchy** — parent/child accounts for enterprise customers
2. **Entitlements before SLAs** — define what each customer gets first
3. **Omni-channel** — same case regardless of how customer contacts you
4. **Auto-match contacts** — email domain matching to accounts
5. **Major Issue Management** — group related cases under a major case
6. **Proactive support** — monitor products, create cases before customer reports
7. **Community deflection** — encourage self-service before case creation
8. **CSAT surveys** — automate after case closure
9. **Asset-based support** — link cases to specific products/serials
10. **Knowledge from cases** — every resolved case is a potential KB article
