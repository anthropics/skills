---
name: servicenow
description: "ServiceNow platform engineering assistant. Use when the task is ServiceNow or SNOW development and architecture involving GlideRecord, Business Rules, Flow Designer, Service Portal, UI Builder, CMDB, MID Server, update sets, ServiceNow APIs, ITSM, ITOM, ITAM/SAM, FSM, SPM, SecOps, IntegrationHub, vulnerabilities, security incidents, assets, work orders, or service modeling. Do not use for non-ServiceNow JavaScript."
license: MIT
compatibility: "Works in Claude.ai, Claude Code, and API. Bundled CLI helper requires Python 3.8+."
metadata:
  author: "Jamiu Awoke"
  version: "1.0.0"
  category: "enterprise-development"
  tags: "servicenow, itsm, itom, itam, fsm, spm, secops, gliderecord, flow-designer, service-portal, now-experience"
---

# ServiceNow Developer Skill

ServiceNow development and architecture guidance across classic scripting, platform configuration, workflow automation, workspace UX, domain apps, and enterprise delivery practices.

## Instructions

### Step 1: Triage the request before writing code

Always identify:

1. The product family or workflow domain.
2. Whether the solution is server-side, client-side, Flow Designer, UI Builder, Service Portal, Virtual Agent, or API-driven.
3. Whether the user is working in global scope or a scoped app.
4. The target table, plugins, roles, and release assumptions if they affect the answer.
5. Whether the task is read-only, transactional, or security-sensitive.

Load the minimum set of reference files that matches the task. For cross-cutting work, load 2-3 references and reconcile them before answering.

| Need | Reference File |
|------|---------------|
| Incident, Problem, Change, Knowledge, assignment, SLA, reporting | `references/itsm.md` |
| GlideRecord, GlideAggregate, GlideSystem, GlideAjax, GlideForm, dates | `references/glide-api.md` |
| Business Rules, Script Includes, Client Scripts, UI Policies, UI Actions, jobs | `references/scripting-patterns.md` |
| REST API, Scripted REST, Table API, outbound REST, Import Sets | `references/rest-api.md` |
| Flow Designer, subflows, spokes, script actions, PAD | `references/flow-designer.md` |
| Playbooks and workspace automation patterns | `references/playbooks.md` |
| UI Builder, Now Experience, Workspace components, mobile workspace | `references/now-experience.md` |
| ACLs, roles, scoped security, SecOps, audit/compliance | `references/security.md` |
| Performance, indexing, caching, query tuning, client perf | `references/performance.md` |
| ATF, instance scan, debugging, regression coverage | `references/testing.md` |
| Catalog Items, Record Producers, Order Guides, fulfillment | `references/service-catalog.md` |
| Notifications, mail scripts, inbound email, SMS, push | `references/notifications.md` |
| Update Sets, source control, pipelines, CI/CD APIs | `references/update-sets-cicd.md` |
| Discovery, MID Server, Event Management, Service Mapping, HLA | `references/itom.md` |
| HRSD, CSM, lifecycle events, entitlements, portals | `references/hrsd-csm.md` |
| Service Portal widgets, `$sp`, Angular providers, theming | `references/service-portal.md` |
| App Engine Studio, scoped apps, low-code architecture | `references/app-engine.md` |
| Virtual Agent, NLU, topic design, handoff patterns | `references/virtual-agent.md` |
| CMDB, Predictive Intelligence, Agent Workspace, Employee Center, upgrades | `references/advanced.md` |
| ITAM, HAM, SAM, stockrooms, contracts, reclamation | `references/itam.md` |
| FSM, work orders, dispatch, scheduling, mobile technician flows | `references/fsm.md` |
| IRM, GRC, policy/compliance, vendor risk, SecOps workflows | `references/irm-secops.md` |
| SPM/PPM, demand, portfolios, projects, resource plans, Agile 2.0 | `references/spm.md` |
| Vulnerable items, vulnerability groups, remediation and exception workflows | `references/vulnerability-response.md` |
| Security incidents, containment, eradication, response tasks, forensic workflows | `references/security-incident-response.md` |
| SAM Pro, entitlements, reclamation, normalization, publishers, software models | `references/sam-pro.md` |
| CSDM, service taxonomy, ownership, CMDB governance, health models | `references/csdm-cmdb-governance.md` |
| IntegrationHub, spokes, Connection & Credential Aliases, custom actions, Data Stream Actions | `references/integrationhub.md` |

### Step 2: Apply ServiceNow platform standards

All generated code and recommendations should follow these rules:

1. Use `getValue()` and `setValue()` for GlideRecord or `current` data access and mutation. GlideElement methods like `changes()`, `changesTo()`, `nil()`, and `setDisplayValue()` are acceptable when needed.
2. Never hardcode credentials, OAuth profile sys_ids, or environment-specific secrets. Prefer REST Message records, Connection & Credential Aliases, and system properties.
3. In scoped apps, treat `GlideRecord.get()` as a boolean-returning operation and always check the result before reading fields.
4. Use `GlideAggregate` for counts and aggregates; do not call `addAggregate()` on `GlideRecord`.
5. Use `setLimit()` on exploratory or user-facing queries unless the workflow explicitly needs the full result set.
6. Prefer encoded queries only for static, known-safe complex filters. If any part comes from user input, sanitize it or use discrete `addQuery()` calls.
7. Use async Business Rules, events, or scheduled jobs for heavy work. Do not block the transaction with slow integrations.
8. Avoid `current.update()` in Before Business Rules. If you must update from an After rule or UI Action, explain the recursion risk and use `setWorkflow(false)` deliberately.
9. Use async `GlideAjax` patterns only; never use `getXMLWait()`.
10. Call out required plugins, roles, cross-scope privileges, and release-specific assumptions whenever they matter.
11. For Vulnerability Response, Security Incident Response, SAM Pro, and IntegrationHub, favor data-driven workflows and named configuration records over scripted constants.

### Step 3: Validate before you return anything

Before responding:

- Confirm the code matches the correct execution context.
- Check for recursion, N+1 queries, unbounded queries, and unsafe auth patterns.
- Verify reference-field logic uses internal values for writes and explicit display-value APIs only when needed.
- Include deployment notes if the change depends on plugins, update sets, app repo, or CI/CD.
- Include a test path: ATF, background script smoke test, Flow execution test, or manual validation steps.

### Common gotchas

- `gr.field` returns a GlideElement, not a plain string. Use `getValue()` unless you specifically need GlideElement behavior.
- `g_form`, `g_user`, and `g_list` are client APIs only.
- `getRowCount()` is not a cheap count.
- `addEncodedQuery(userInput)` is an injection risk.
- Business Rules on `sys_dictionary` or `sys_db_object` can destabilize an instance.
- Querying by display value such as `assignment_group.name` is sometimes useful for examples, but sys_id-based queries are safer and faster in production code.
- Record Producers and inbound actions should usually populate `current` and let the platform handle persistence rather than forcing extra updates.
- CSDM guidance should preserve layer boundaries and ownership semantics rather than inventing custom service hierarchies.
- IntegrationHub solutions should specify connection aliases, credential ownership, retries, and rate-limit behavior.

### Fast patterns

Use these without loading a reference file when the request is simple and clearly matches the pattern.

#### Safe GlideRecord query

```javascript
var gr = new GlideRecord('incident');
gr.addActiveQuery();
gr.addQuery('priority', '1');
gr.setLimit(50);
gr.query();

while (gr.next()) {
    gs.info(gr.getValue('number') + ' ' + gr.getValue('short_description'));
}
```

#### Scoped-safe single-record lookup

```javascript
var user = new GlideRecord('sys_user');
if (!user.get(userSysId)) {
    gs.addErrorMessage('User not found');
    return;
}

gs.info(user.getValue('email'));
```

## CLI Helper

```bash
# Generate queries
python3 skills/servicenow/scripts/snow_helper.py query "find active incidents assigned to me"
python3 skills/servicenow/scripts/snow_helper.py query "find all work orders in state Dispatch Pending"

# Generate templates
python3 skills/servicenow/scripts/snow_helper.py template business-rule --table incident --when before --insert --update
python3 skills/servicenow/scripts/snow_helper.py template scripted-rest-api --table incident
python3 skills/servicenow/scripts/snow_helper.py template flow-script-action --table incident
python3 skills/servicenow/scripts/snow_helper.py template atf-server-test --table incident
python3 skills/servicenow/scripts/snow_helper.py template integrationhub-action --table incident

# Lint a script
python3 skills/servicenow/scripts/snow_helper.py lint < myscript.js

# Validate the skill package and bundled references
python3 skills/servicenow/scripts/snow_helper.py validate-skill skills/servicenow
```

## Examples

### Example 1: ITSM query
**User says:** "Write a query to find all P1 incidents opened this week"

**Actions:** Load `references/glide-api.md` and `references/itsm.md`, generate a safe query, and check for limits and boolean `get()` usage.

### Example 2: Scripted REST
**User says:** "Create a REST endpoint that returns user details by employee number"

**Actions:** Load `references/rest-api.md`, return a Scripted REST resource with 400/404 handling, note required ACLs, and include a test call.

### Example 3: ITAM lifecycle
**User says:** "How do I reclaim laptops from terminated employees and update stockroom state?"

**Actions:** Load `references/itam.md` and `references/flow-designer.md`, propose a reclamation flow, asset-state transitions, and HAM role assumptions.

### Example 4: FSM dispatch
**User says:** "Build a flow to auto-assign field work orders by territory and skills"

**Actions:** Load `references/fsm.md` and `references/flow-designer.md`, design dispatch logic, scheduling constraints, and technician/mobile validation.

### Example 5: SecOps / IRM
**User says:** "Create a Vulnerability Response integration that opens exceptions only for approved compensating controls"

**Actions:** Load `references/irm-secops.md`, `references/security.md`, and `references/rest-api.md`, then return data model, approval logic, and audit requirements.

### Example 6: SPM
**User says:** "Model demand intake and project creation with resource plans"

**Actions:** Load `references/spm.md` plus `references/app-engine.md` or `references/flow-designer.md`, then return table/process guidance and portfolio governance notes.

### Example 7: Vulnerability Response
**User says:** "Build triage logic for vulnerable items that routes exceptions to security governance"

**Actions:** Load `references/vulnerability-response.md`, `references/irm-secops.md`, and `references/integrationhub.md`, then return routing logic, exception controls, and audit requirements.

### Example 8: Security Incident Response
**User says:** "Create a security incident workflow for containment and forensic handoff"

**Actions:** Load `references/security-incident-response.md`, `references/flow-designer.md`, and `references/security.md`, then return lifecycle design, task model, and escalation rules.

### Example 9: SAM Pro
**User says:** "Reconcile software entitlements against installs and flag reclaim candidates"

**Actions:** Load `references/sam-pro.md` and `references/itam.md`, then return normalization assumptions, compliance logic, and reclamation workflow.

### Example 10: CSDM / CMDB governance
**User says:** "Model business applications and services using CSDM and clean up ownership gaps"

**Actions:** Load `references/csdm-cmdb-governance.md` and `references/advanced.md`, then return class mapping, governance steps, and validation queries.

### Example 11: IntegrationHub
**User says:** "Create a custom spoke action that streams paginated records from an external API"

**Actions:** Load `references/integrationhub.md` and `references/rest-api.md`, then return the action contract, credential strategy, pagination handling, and retry notes.

## Troubleshooting

| Error | Cause | Solution |
|-------|-------|----------|
| "Record not found" in Scripted REST | `gr.get()` result not checked | Use `if (!gr.get(id)) { ... }` before reading fields |
| Flow script count logic fails | `addAggregate()` called on `GlideRecord` | Replace with `GlideAggregate` |
| REST call works in dev only | Auth or endpoint details hardcoded in script | Move auth and endpoint configuration into REST Message records or properties |
| Record Producer saves duplicate changes | Script mutates `current` and then calls `current.update()` | Set values on `current` and let the producer persist the record |
| Workspace component fails in scoped app | Missing cross-scope access or wrong data resource | Verify scope privileges and UI Builder data-resource config |
| Query is slow in production | Missing index or querying by display value | Move to sys_id/internal values, add indexes where justified, and limit record scans |
| Vulnerability automation keeps misrouting records | Grouping logic ignores state, source, or exception posture | Use vulnerability-grouping rules, explicit exception states, and table-driven routing |
| Security incident process stalls | No clear transition between containment, eradication, and recovery | Model phase ownership explicitly and create response tasks per phase |
| IntegrationHub action works manually but fails in flow | Missing connection alias or action outputs are underspecified | Validate alias binding, outputs, and error contracts in the action definition |

## Release Notes

Treat release behavior as instance-specific. If a feature depends on family release or plugin state, say so explicitly and ask which release the customer is on.

Recent family names often referenced in examples:

- Zurich
- Xanadu
- Washington DC
