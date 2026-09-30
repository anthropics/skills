# Playbooks & Process Automation Designer (PAD)

## What Are Playbooks?

Playbooks provide **guided, step-by-step resolution processes** for agents in Agent Workspace. They combine human tasks, automation, and decision logic into a structured workflow that agents follow to resolve issues consistently.

**Key concepts:**
- **Playbook** = overall process definition (like a runbook, but interactive)
- **Activity** = individual step in a playbook (instruction, automation, decision, approval)
- **Lane** = who performs the activity (agent, system, requester, approver)
- **Process Automation Designer (PAD)** = the visual editor for building playbooks

## Where Playbooks Live

- **Agent Workspace** — primary consumption point
- **Process Automation Designer** — build/edit interface
- **Flow Designer** — automation activities use Flow actions

Navigate to: **Process Automation > Process Automation Designer**

## Playbook Structure

```
Playbook: Incident Resolution - Network
├── Stage 1: Triage
│   ├── Activity: Gather Information (Instruction)
│   │   └── "Ask caller for error message and affected systems"
│   ├── Activity: Check CMDB (Automation)
│   │   └── Look up affected CIs and recent changes
│   └── Activity: Classify Issue (Decision)
│       ├── → Hardware Failure → Stage 2A
│       └── → Software Issue → Stage 2B
├── Stage 2A: Hardware Resolution
│   ├── Activity: Create Change Request (Automation)
│   ├── Activity: Notify On-site Team (Automation)
│   └── Activity: Verify Resolution (Instruction)
├── Stage 2B: Software Resolution
│   ├── Activity: Apply Known Fix (Instruction)
│   ├── Activity: Test Connectivity (Automation)
│   └── Activity: Verify Resolution (Instruction)
└── Stage 3: Close
    ├── Activity: Document Resolution (Instruction)
    └── Activity: Customer Satisfaction Survey (Automation)
```

## Activity Types

### Instruction Activity
Tells the agent what to do — human-driven step.
```
Name: Gather Caller Information
Type: Instruction
Assigned to: Agent Lane
Instructions: |
  1. Confirm the caller's contact information
  2. Ask for the specific error message
  3. Determine when the issue started
  4. Check if any recent changes were made
  
Required fields to update:
  - Description (detailed symptoms)
  - Category / Subcategory
  - Configuration Item
```

### Automation Activity
Runs Flow Designer actions automatically.
```
Name: Look Up Recent Changes
Type: Automation
Action: Look Up Records
  Table: change_request
  Conditions: 
    cmdb_ci = [Playbook Context: cmdb_ci]
    state = Closed
    closed_at >= last 7 days
  
Output: Display results to agent in workspace
```

### Decision Activity
Branch the playbook based on conditions.
```
Name: Determine Resolution Path
Type: Decision
Condition: [Playbook Context: category]

Branches:
  "network"  → Go to Network Troubleshooting stage
  "software" → Go to Software Fix stage
  "hardware" → Go to Hardware Replacement stage
  DEFAULT    → Go to General Resolution stage
```

### Approval Activity
Request approval before proceeding.
```
Name: Manager Approval for Emergency Change
Type: Approval
Approver: [Record: opened_by.manager]
Due: 2 hours
On Approve: Continue to next activity
On Reject: Go to "Request Denied" stage
```

### Wait Activity
Pause until a condition is met.
```
Name: Wait for Vendor Response
Type: Wait
Condition: [Record: u_vendor_response] is not empty
Timeout: 48 hours
On Timeout: → Escalation stage
```

## Building ITSM Playbooks

### Incident Playbook Pattern
```
Trigger: Incident created with category = "network"
Context Record: incident

Stages:
1. Initial Assessment (2 activities)
   - Auto-enrich: Pull CMDB data, recent incidents, known errors
   - Triage: Agent reviews enrichment, sets priority/assignment

2. Diagnosis (3 activities)  
   - Run Diagnostics: Automated ping/trace tests via MID Server
   - Check Known Errors: Auto-search knowledge base
   - Decision: Known fix available? → Yes/No branch

3. Resolution (2 activities)
   - Apply Fix: Instructions for agent OR automated remediation
   - Verify: Confirm service restored (auto-check or agent confirm)

4. Closure (2 activities)
   - Document: Agent fills resolution notes
   - Close: Auto-update state, send satisfaction survey
```

### Problem Playbook Pattern
```
Trigger: Problem created
Context: problem

Stages:
1. Root Cause Investigation
   - Gather related incidents (automation)
   - Timeline analysis (instruction)
   - 5-Why analysis template (instruction)
   
2. Solution Development
   - Document root cause (instruction)
   - Propose fix / workaround (instruction)
   - Approval for change (approval activity)
   
3. Implementation
   - Create Change Request (automation)
   - Wait for Change completion (wait activity)
   - Validate fix (instruction)

4. Knowledge
   - Create KB article (automation + instruction)
   - Link to related incidents (automation)
   - Close problem (automation)
```

### Change Playbook Pattern
```
Trigger: Change Request state = "Assess"
Context: change_request

Stages:
1. Planning
   - Risk assessment checklist (instruction)
   - Auto-calculate risk score (automation)
   - Implementation plan template (instruction)
   
2. Approval
   - CAB approval (approval, group-based)
   - Decision: Standard/Normal/Emergency path
   
3. Implementation
   - Pre-implementation checklist (instruction)
   - Execute change tasks (linked to change_task records)
   - Post-implementation verification (instruction)
   
4. Review
   - PIR (Post-Implementation Review) (instruction)
   - Close change (automation)
```

## Custom Playbook Activities

### Creating a Custom Activity
```
Navigate: Process Automation > Activity Definitions

Name: Check Service Health
Category: Custom
Inputs:
  - service_name (String)
  - ci_sys_id (Reference: cmdb_ci)

Action Type: Subflow
  → Calls subflow: "Service Health Check"
  → Inputs mapped from activity inputs
  
Outputs:
  - health_status (String: "healthy" | "degraded" | "down")
  - details (String)
  
Display: Show outputs in Agent Workspace activity panel
```

### Script-Based Activity
```javascript
// Custom activity using Run Script action
(function execute(inputs, outputs) {
    // Check if similar incidents exist
    var ga = new GlideAggregate('incident');
    ga.addQuery('cmdb_ci', inputs.ci_sys_id);
    ga.addQuery('active', true);
    ga.addQuery('sys_id', '!=', inputs.current_incident);
    ga.addAggregate('COUNT');
    ga.query();
    
    outputs.similar_count = 0;
    if (ga.next()) {
        outputs.similar_count = parseInt(ga.getAggregate('COUNT'));
    }
    
    outputs.is_widespread = outputs.similar_count > 3;
    outputs.recommendation = outputs.is_widespread ? 
        'Consider creating a Major Incident' : 
        'Isolated incident - proceed with standard resolution';
})(inputs, outputs);
```

## Playbook Analytics

### Key Metrics
- **Completion Rate** — % of playbooks completed vs abandoned
- **Average Duration** — time to complete each stage/activity
- **Bottleneck Analysis** — which activities take longest
- **Agent Compliance** — are agents following the playbook?

### Accessing Analytics
```
Navigate: Process Automation > Playbook Experience > Analytics
Reports: PA dashboards for playbook execution metrics
Custom: Create reports on sn_playbook_execution table
```

## Agent Workspace Integration

Playbooks appear in the **Activity Stream** panel:
- Current activity is highlighted
- Agent can see upcoming steps
- Automation results display inline
- Agent can add notes to each activity
- Mandatory fields enforce completion before advancing

### Configuring Workspace Display
```
Navigate: Workspace Experience > Workspace Configuration
Add: Playbook component to record page layout
Configure: Activity panel position, auto-expand settings
```

## Best Practices

1. **Keep playbooks focused** — one process, not a mega-workflow
2. **2-4 stages max** — too many stages overwhelm agents
3. **3-5 activities per stage** — granular but not micro-managed
4. **Automate what you can** — reduce agent manual steps
5. **Use decision branches** — not every incident follows the same path
6. **Include context** in instructions — link to KB articles, include screenshots
7. **Set timeouts** on wait activities — don't let playbooks stall forever
8. **Test with real agents** — get feedback on instructions clarity
9. **Version your playbooks** — use publish/draft lifecycle
10. **Monitor analytics** — iterate based on completion rates and duration data
