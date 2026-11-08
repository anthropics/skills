# ITSM (IT Service Management)

## Core ITSM Tables

```
incident              — Incident Management
problem               — Problem Management
change_request        — Change Management
change_task           — Change Tasks
sc_request            — Service Request (RITM parent)
sc_req_item           — Requested Item (RITM)
sc_task               — Catalog Tasks
kb_knowledge          — Knowledge Management
task_sla              — SLA instances on records
cmdb_ci               — Configuration Items
cmdb_rel_ci           — CI Relationships
```

## Incident Management

### Incident Lifecycle
```
State flow:
  1 - New
  2 - In Progress
  3 - On Hold
  6 - Resolved
  7 - Closed
  8 - Canceled

Priority matrix (auto-calculated):
  Impact × Urgency = Priority
  
  Impact:    1-High  2-Medium  3-Low
  Urgency:   1-High  2-Medium  3-Low
  
  1×1=P1(Critical)  1×2=P2(High)    1×3=P3(Moderate)
  2×1=P2(High)      2×2=P3(Moderate) 2×3=P4(Low)
  3×1=P3(Moderate)  3×2=P4(Low)     3×3=P5(Planning)
```

### Incident Scripting Patterns
```javascript
// Auto-assign incident based on category + location
// Business Rule: Before Insert on incident
(function executeRule(current, previous) {
    if (!current.assignment_group) {
        var category = current.getValue('category');
        var location = current.getValue('location');
        
        var rules = new GlideRecord('x_assignment_rule');
        rules.addQuery('category', category);
        rules.addQuery('location', location);
        rules.addActiveQuery();
        rules.orderBy('order');
        rules.setLimit(1);
        rules.query();
        
        if (rules.next()) {
            current.setValue('assignment_group', rules.getValue('assignment_group'));
        }
    }
})(current, previous);
```

```javascript
// Reopen incident if customer responds after resolution
// Business Rule: Before Update on incident
(function executeRule(current, previous) {
    if (current.getValue('state') == '6' && current.comments.changes()) {
        // Check if comment is from caller (not agent)
        var lastComment = current.comments.getJournalEntry(1);
        if (lastComment.indexOf(current.caller_id.getDisplayValue()) > -1) {
            current.setValue('state', '2'); // In Progress
            current.setValue('work_notes', 'Reopened: customer added comments after resolution');
        }
    }
})(current, previous);
```

```javascript
// Escalation script — auto-escalate overdue P1 incidents
// Scheduled Job: runs every 15 minutes
(function() {
    var gr = new GlideRecord('incident');
    gr.addQuery('priority', 1);
    gr.addQuery('state', 'IN', '1,2'); // New or In Progress
    gr.addQuery('escalation', 0); // Not yet escalated
    
    // SLA breached or about to breach
    var slaGr = new GlideRecord('task_sla');
    slaGr.addQuery('task.priority', 1);
    slaGr.addQuery('stage', 'IN', 'breached,warning');
    slaGr.addQuery('active', true);
    slaGr.query();
    
    var incidentIds = [];
    while (slaGr.next()) {
        incidentIds.push(slaGr.getValue('task'));
    }
    
    if (incidentIds.length > 0) {
        gr.addQuery('sys_id', 'IN', incidentIds.join(','));
        gr.query();
        while (gr.next()) {
            gr.setValue('escalation', '1');
            gr.setValue('work_notes', 'Auto-escalated: SLA breached or in warning state');
            gr.update();
            
            // Notify management
            gs.eventQueue('incident.escalated', gr, 
                gr.assignment_group.manager.toString(), '');
        }
    }
})();
```

### Major Incident Management
```
Major Incident Process:
  1. Declare major incident (set major_incident_state = accepted)
  2. Create communication channels (bridge call, Slack/Teams)
  3. Assign Incident Commander
  4. Track child incidents (parent_incident field)
  5. Regular stakeholder updates (communication plan)
  6. Resolve → Post-Incident Review → Problem record

Key fields on incident:
  - major_incident_state: none, proposed, accepted, rejected, closed
  - parent_incident: links child incidents to major
  - business_impact: free text for executive communication

Communication plan script:
```
```javascript
// Script Include: Major Incident Communications
var MajorIncidentComms = Class.create();
MajorIncidentComms.prototype = {
    initialize: function(incidentGr) {
        this.incident = incidentGr;
    },
    
    sendStakeholderUpdate: function(updateText) {
        // Get all affected CIs' business service owners
        var stakeholders = this._getStakeholders();
        
        // Create communication task
        var commTask = new GlideRecord('task');
        commTask.initialize();
        commTask.setValue('short_description', 'Major Incident Update: ' +
            this.incident.getValue('number'));
        commTask.setValue('description', updateText);
        commTask.setValue('parent', this.incident.getUniqueValue());
        commTask.insert();
        
        // Fire notification event
        gs.eventQueue('major.incident.update', this.incident,
            stakeholders.join(','), updateText);
    },
    
    _getStakeholders: function() {
        var users = [];
        // Get business service owners for affected CIs
        var rel = new GlideRecord('cmdb_rel_ci');
        rel.addQuery('child', this.incident.getValue('cmdb_ci'));
        rel.addQuery('type.name', 'Depends on::Used by');
        rel.query();
        while (rel.next()) {
            var svc = new GlideRecord('cmdb_ci_service');
            if (svc.get(rel.getValue('parent'))) {
                if (svc.getValue('owned_by')) {
                    users.push(svc.getValue('owned_by'));
                }
            }
        }
        return users;
    },
    
    type: 'MajorIncidentComms'
};
```

## Problem Management

### Problem Lifecycle
```
States:
  1 - New (Open)
  2 - Assessed / Known Error
  3 - Root Cause Identified  
  4 - Fix in Progress
  5 - Resolved
  7 - Closed
  
Key fields:
  - known_error: boolean (is this a known error?)
  - workaround: text (temporary fix)
  - root_cause: text (identified root cause)
  - fix_notes: text (permanent fix details)
  - related_incidents: M2M to incident table
```

### Problem Scripting
```javascript
// Auto-create problem from recurring incidents
// Scheduled Job: runs daily
(function() {
    // Find categories with 5+ incidents in past 7 days
    var ga = new GlideAggregate('incident');
    ga.addQuery('sys_created_on', '>=', gs.daysAgoStart(7));
    ga.addActiveQuery();
    ga.groupBy('category');
    ga.groupBy('cmdb_ci');
    ga.addAggregate('COUNT');
    ga.addHaving('COUNT', '>', 5);
    ga.query();
    
    while (ga.next()) {
        var category = ga.getValue('category');
        var ci = ga.getValue('cmdb_ci');
        var count = ga.getAggregate('COUNT');
        
        // Check if problem already exists
        var existing = new GlideRecord('problem');
        existing.addQuery('category', category);
        existing.addQuery('cmdb_ci', ci);
        existing.addActiveQuery();
        existing.setLimit(1);
        existing.query();
        
        if (!existing.hasNext()) {
            var prob = new GlideRecord('problem');
            prob.initialize();
            prob.setValue('short_description', 'Recurring incidents: ' + category +
                ' (' + count + ' in 7 days)');
            prob.setValue('category', category);
            prob.setValue('cmdb_ci', ci);
            prob.setValue('description', count + ' incidents created in the past 7 days ' +
                'for category ' + category + ' on CI ' + ci.getDisplayValue());
            prob.insert();
            
            gs.info('Auto-created problem: ' + prob.getValue('number'));
        }
    }
})();
```

### Known Error Database (KEDB)
```javascript
// Script Include: Search known errors for matching workarounds
var KEDBSearch = Class.create();
KEDBSearch.prototype = {
    initialize: function() {},
    
    findWorkaround: function(incidentGr) {
        var results = [];
        var prob = new GlideRecord('problem');
        prob.addQuery('known_error', true);
        prob.addQuery('workaround', '!=', '');
        prob.addActiveQuery();
        
        // Match on category + CI
        var category = incidentGr.getValue('category');
        var ci = incidentGr.getValue('cmdb_ci');
        
        if (ci) {
            prob.addQuery('cmdb_ci', ci);
        } else {
            prob.addQuery('category', category);
        }
        
        prob.query();
        while (prob.next()) {
            results.push({
                number: prob.getValue('number'),
                description: prob.getValue('short_description'),
                workaround: prob.getValue('workaround'),
                fix_planned: prob.getValue('fix_notes') != ''
            });
        }
        return results;
    },
    
    type: 'KEDBSearch'
};
```

## Change Management

### Change Types
```
Standard Change:
  - Pre-approved, low-risk
  - Uses templates (std_change_proposal)
  - No CAB approval needed
  - Example: password reset, scheduled patch

Normal Change:
  - Requires assessment and approval
  - Goes through CAB (Change Advisory Board)
  - Full risk assessment
  - Example: server migration, app upgrade

Emergency Change:
  - Expedited approval (post-implementation review)
  - For critical production issues
  - Retrospective documentation required
  - Example: emergency security patch
```

### Change States
```
  -5 - New
  -4 - Assess
  -3 - Authorize (approval phase)
  -2 - Scheduled
  -1 - Implement
   0 - Review
   3 - Closed
   4 - Canceled
```

### Change Risk Assessment
```javascript
// Business Rule: Auto-calculate risk score
// Before Insert/Update on change_request
(function executeRule(current, previous) {
    var riskScore = 0;
    
    // Impact-based scoring
    var impact = parseInt(current.getValue('impact'));
    riskScore += (4 - impact) * 10;  // High impact = more risk
    
    // CI criticality
    if (current.cmdb_ci) {
        var ci = new GlideRecord('cmdb_ci');
        if (ci.get(current.getValue('cmdb_ci'))) {
            var criticality = ci.getValue('busines_criticality');
            if (criticality == '1') riskScore += 30;      // Most critical
            else if (criticality == '2') riskScore += 20;
            else riskScore += 10;
        }
    }
    
    // Time-based risk
    var plannedStart = new GlideDateTime(current.getValue('start_date'));
    var dayOfWeek = plannedStart.getDayOfWeekLocalTime();
    if (dayOfWeek >= 2 && dayOfWeek <= 6) {  // Mon-Fri
        riskScore += 15;  // Business hours = higher risk
    }
    
    // Backout plan exists?
    if (!current.getValue('backout_plan')) {
        riskScore += 20;
    }
    
    // Test plan exists?
    if (!current.getValue('test_plan')) {
        riskScore += 15;
    }
    
    // Set risk level
    if (riskScore >= 60) current.setValue('risk', '1');       // High
    else if (riskScore >= 30) current.setValue('risk', '2');  // Moderate
    else current.setValue('risk', '3');                       // Low
    
    current.setValue('risk_value', riskScore);
})(current, previous);
```

### Change Conflict Detection
```javascript
// Script Include: Check for scheduling conflicts
var ChangeConflict = Class.create();
ChangeConflict.prototype = {
    initialize: function() {},
    
    checkConflicts: function(changeGr) {
        var conflicts = [];
        var start = changeGr.getValue('start_date');
        var end = changeGr.getValue('end_date');
        var ci = changeGr.getValue('cmdb_ci');
        
        // Check overlapping changes on same CI
        var gr = new GlideRecord('change_request');
        gr.addQuery('sys_id', '!=', changeGr.getUniqueValue());
        gr.addQuery('cmdb_ci', ci);
        gr.addQuery('state', 'IN', '-2,-1');  // Scheduled or Implement
        gr.addQuery('start_date', '<=', end);
        gr.addQuery('end_date', '>=', start);
        gr.query();
        
        while (gr.next()) {
            conflicts.push({
                number: gr.getValue('number'),
                description: gr.getValue('short_description'),
                window: gr.getValue('start_date') + ' to ' + gr.getValue('end_date')
            });
        }
        
        // Check blackout windows
        var blackout = new GlideRecord('change_blackout');
        blackout.addActiveQuery();
        blackout.addQuery('start_date', '<=', end);
        blackout.addQuery('end_date', '>=', start);
        blackout.query();
        
        while (blackout.next()) {
            conflicts.push({
                number: 'BLACKOUT',
                description: blackout.getValue('name'),
                window: blackout.getValue('start_date') + ' to ' + 
                    blackout.getValue('end_date')
            });
        }
        
        return conflicts;
    },
    
    type: 'ChangeConflict'
};
```

## SLA Management

### SLA Definition
```
Navigate: Service Level Management > SLA > SLA Definitions
Table: contract_sla

Key fields:
  - Name: descriptive (e.g., "P1 Incident Response - 15 min")
  - Table: target table (incident, sn_customerservice_case, etc.)
  - Type: Response, Resolution, or Custom
  - Duration: SLA target time
  - Schedule: business schedule (e.g., 24x7, 8x5)
  - Conditions: when SLA applies
  - Start condition: when SLA clock starts
  - Pause condition: when clock pauses (e.g., On Hold)
  - Stop condition: when SLA is achieved
  - Reset condition: when SLA resets
```

### SLA Scripting
```javascript
// Script Include: SLA breach prediction
var SLAPredictor = Class.create();
SLAPredictor.prototype = {
    initialize: function() {},
    
    getAtRiskTasks: function(tableName, minutes) {
        // Find tasks with SLA about to breach
        var results = [];
        var sla = new GlideRecord('task_sla');
        sla.addQuery('task.sys_class_name', tableName);
        sla.addQuery('active', true);
        sla.addQuery('stage', 'in_progress');
        
        // Calculate breach time threshold
        var threshold = new GlideDateTime();
        threshold.addSeconds(minutes * 60);
        sla.addQuery('planned_end_time', '<=', threshold);
        
        sla.query();
        while (sla.next()) {
            var remaining = GlideDateTime.subtract(
                new GlideDateTime(), 
                new GlideDateTime(sla.getValue('planned_end_time'))
            );
            
            results.push({
                task: sla.task.getDisplayValue(),
                sla_name: sla.sla.getDisplayValue(),
                breach_in: remaining.getDisplayValue(),
                assigned_to: sla.task.assigned_to.getDisplayValue(),
                priority: sla.task.getValue('priority')
            });
        }
        return results;
    },
    
    type: 'SLAPredictor'
};
```

## Assignment Rules

### Auto-Assignment
```
Navigate: System Policy > Assignment

Assignment rule fields:
  - Table: target table
  - Conditions: when rule applies
  - Group: target assignment group
  - User: specific user (optional)
  - Script: advanced assignment logic (optional)
  - Order: evaluation priority (lower = first)
```

### Round-Robin Assignment
```javascript
// Script Include: Round-robin within a group
var RoundRobin = Class.create();
RoundRobin.prototype = {
    initialize: function() {},
    
    getNextAgent: function(groupSysId) {
        // Get group members
        var members = [];
        var gm = new GlideRecord('sys_user_grmember');
        gm.addQuery('group', groupSysId);
        gm.query();
        while (gm.next()) {
            var user = gm.getValue('user');
            // Check user is active and not on leave
            var userGr = new GlideRecord('sys_user');
            if (userGr.get(user) && userGr.getValue('active') == 'true') {
                members.push(user);
            }
        }
        
        if (members.length == 0) return null;
        
        // Find member with fewest active assignments
        var minCount = 999999;
        var nextAgent = members[0];
        
        for (var i = 0; i < members.length; i++) {
            var ga = new GlideAggregate('incident');
            ga.addQuery('assigned_to', members[i]);
            ga.addActiveQuery();
            ga.addAggregate('COUNT');
            ga.query();
            var count = 0;
            if (ga.next()) {
                count = parseInt(ga.getAggregate('COUNT'));
            }
            if (count < minCount) {
                minCount = count;
                nextAgent = members[i];
            }
        }
        
        return nextAgent;
    },
    
    type: 'RoundRobin'
};
```

## Knowledge Management

### Knowledge Base Structure
```
Tables:
  kb_knowledge_base  — Knowledge Base container
  kb_knowledge       — Knowledge Articles
  kb_category        — Article categories
  kb_feedback        — Article feedback/ratings

Article workflow:
  Draft → Review → Published → Retired

Key fields:
  - Knowledge base, Category
  - Short description, Text (article body)
  - Valid to (expiration date)
  - Workflow state
  - Article type: text, wiki, external
```

### Knowledge API
```javascript
// Script Include: Search knowledge base
var KBSearch = Class.create();
KBSearch.prototype = {
    initialize: function() {},
    
    searchArticles: function(searchTerm, kbSysId, limit) {
        var results = [];
        var gr = new GlideRecord('kb_knowledge');
        gr.addQuery('kb_knowledge_base', kbSysId);
        gr.addQuery('workflow_state', 'published');
        gr.addQuery('active', true);
        
        // Full-text search
        gr.addQuery('123TEXTQUERY321', searchTerm);
        gr.setLimit(limit || 10);
        gr.query();
        
        while (gr.next()) {
            results.push({
                sys_id: gr.getUniqueValue(),
                number: gr.getValue('number'),
                title: gr.getValue('short_description'),
                category: gr.category.getDisplayValue(),
                views: gr.getValue('sys_view_count'),
                rating: gr.getValue('rating')
            });
        }
        return results;
    },
    
    // Link knowledge article to incident
    linkToIncident: function(articleSysId, incidentSysId) {
        var m2m = new GlideRecord('m2m_kb_task');
        m2m.initialize();
        m2m.setValue('kb_knowledge', articleSysId);
        m2m.setValue('task', incidentSysId);
        m2m.insert();
    },
    
    type: 'KBSearch'
};
```

## ITSM Reporting & Metrics

### Key ITSM Metrics
```
Incident:
  - MTTR (Mean Time to Resolve) by priority
  - First Contact Resolution rate
  - Reopen rate
  - SLA compliance % (response + resolution)
  - Incidents by category/CI/group
  - Backlog aging

Problem:
  - Known Error count and resolution time
  - Problems created from incidents (proactive %)
  - Root cause categories

Change:
  - Change success rate (vs failed/unauthorized)
  - Emergency change % (should be <10%)
  - Lead time (submit to implement)
  - CAB approval time
  - Changes causing incidents

Knowledge:
  - Article usage (views, feedback score)
  - Deflection rate (self-service resolution)
  - Knowledge gap analysis
```

### Reporting Script
```javascript
// Script Include: ITSM Dashboard Metrics
var ITSMMetrics = Class.create();
ITSMMetrics.prototype = {
    initialize: function() {},
    
    getIncidentMetrics: function(daysBack) {
        var metrics = {};
        var startDate = gs.daysAgoStart(daysBack);
        
        // Total incidents
        var ga = new GlideAggregate('incident');
        ga.addQuery('sys_created_on', '>=', startDate);
        ga.addAggregate('COUNT');
        ga.query();
        metrics.total = ga.next() ? parseInt(ga.getAggregate('COUNT')) : 0;
        
        // By priority
        ga = new GlideAggregate('incident');
        ga.addQuery('sys_created_on', '>=', startDate);
        ga.groupBy('priority');
        ga.addAggregate('COUNT');
        ga.query();
        metrics.by_priority = {};
        while (ga.next()) {
            metrics.by_priority[ga.getValue('priority')] = 
                parseInt(ga.getAggregate('COUNT'));
        }
        
        // MTTR (resolved incidents)
        ga = new GlideAggregate('incident');
        ga.addQuery('resolved_at', '>=', startDate);
        ga.addQuery('resolved_at', 'ISNOTEMPTY', '');
        ga.addAggregate('AVG', 'calendar_duration');
        ga.query();
        if (ga.next()) {
            var avgSeconds = parseFloat(ga.getAggregate('AVG', 'calendar_duration'));
            metrics.mttr_hours = Math.round(avgSeconds / 3600 * 10) / 10;
        }
        
        // SLA compliance
        var slaGa = new GlideAggregate('task_sla');
        slaGa.addQuery('task.sys_class_name', 'incident');
        slaGa.addQuery('task.sys_created_on', '>=', startDate);
        slaGa.addQuery('active', false);
        slaGa.groupBy('has_breached');
        slaGa.addAggregate('COUNT');
        slaGa.query();
        var met = 0, breached = 0;
        while (slaGa.next()) {
            if (slaGa.getValue('has_breached') == 'true') {
                breached = parseInt(slaGa.getAggregate('COUNT'));
            } else {
                met = parseInt(slaGa.getAggregate('COUNT'));
            }
        }
        metrics.sla_compliance = met + breached > 0 ? 
            Math.round(met / (met + breached) * 100) : 0;
        
        return metrics;
    },
    
    type: 'ITSMMetrics'
};
```

## ITSM Best Practices

1. **Priority = Impact × Urgency** — never let users set priority directly
2. **Assignment groups before users** — assign to groups, let groups manage individual assignment
3. **Mandatory fields per state** — require resolution notes before closing, category before routing
4. **SLAs on everything** — response AND resolution, measured against business schedules
5. **Knowledge-centered service** — every resolved incident should check: can this be a KB article?
6. **Parent-child for major incidents** — track affected users/locations as child incidents
7. **Standard changes for repetitive work** — pre-approved templates reduce CAB load
8. **Post-incident review** — every P1/P2 should create a problem record
9. **Metrics-driven improvement** — track MTTR, reopen rate, SLA compliance monthly
10. **CMDB accuracy** — if your CMDB is wrong, impact analysis and assignment rules will fail
