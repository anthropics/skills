# App Engine Studio & Low-Code Development

## App Engine Studio (AES)

### Overview
App Engine Studio is the low-code/no-code environment for building custom applications on the ServiceNow platform. It provides a guided experience for creating tables, forms, flows, and portals without deep platform knowledge.

### Getting Started
```
Navigate: App Engine Studio (separate URL: /now/app-engine-studio)

Creating an App:
  1. Click "Create app"
  2. Enter name, description, scope prefix
  3. Choose template (blank, or pre-built starter)
  4. AES creates: scoped app, tables, roles automatically
  
App structure (auto-generated):
  - Scoped application record
  - App-specific roles (user, admin)
  - App menu and modules
  - Default table with standard fields
```

### Table Builder
```
Visual table creation:
  1. Navigate to Data tab in AES
  2. Click "Add a table"
  3. Options:
     - Create from scratch
     - Extend an existing table (e.g., extend task)
     - Upload spreadsheet (auto-create from CSV/Excel)
  
Field types available:
  - String, Integer, Decimal, Boolean
  - Date, Date/Time, Duration
  - Reference (to other tables)
  - Choice (dropdown)
  - HTML, URL, Email
  - Attachment
  - Journal (work notes, comments)
  - Document ID, Conditions
  
Extending task table benefits:
  - Inherits: assignment, state, SLA, approval
  - Works with Flow Designer triggers
  - Works with Playbooks
  - Shows in Agent Workspace
```

### Form Builder
```
Drag-and-drop form designer:
  - Add/remove fields
  - Create sections and tabs
  - Set field properties (mandatory, read-only)
  - Configure related lists
  - Add annotations (instructions, separators)
  
Form layout:
  - 1-column or 2-column sections
  - Section visibility conditions
  - Field-level conditions (show/hide)
  - Formatters (activity stream, process flow)
```

### Experience Builder (Portals)
```
Create user-facing portals:
  1. Navigate to Experience tab in AES
  2. Choose template (Record List, Record Detail, Landing)
  3. Configure pages and navigation
  4. Apply branding (logo, colors, fonts)
  
Page types:
  - Landing page (dashboard/overview)
  - List page (filterable record list)
  - Record page (form view)
  - Custom page (free-form layout)
  
Components:
  - Data tables
  - Charts and reports
  - Rich text blocks
  - Image and video
  - Embedded flows
```

### Logic & Automation in AES
```
Built-in automation:
  - Flow Designer integration (visual flow builder)
  - Business Rules (guided creation)
  - Notifications (template-based)
  - Approval flows (configurable)
  
AES-created flows:
  - Trigger: record insert/update on app table
  - Actions: assignments, notifications, approvals
  - No scripting required for basic workflows
```

## Guided App Creator (GAC)

### Templates
```
Pre-built app templates:
  - Request Management (intake, approval, fulfillment)
  - Case Management (customer cases, tracking)
  - Project Tracking (tasks, milestones, assignments)
  - Approval Workflow (multi-level approval chain)
  - Knowledge Management (articles, categories)
  
Each template includes:
  - Pre-configured tables and fields
  - Standard workflows
  - Basic portal pages
  - Default roles and ACLs
```

## Collaboration & Governance

### Delegated Development
```
App Engine provides development guardrails:
  
Developer roles:
  - sn_app_eng_studio.user — can build apps
  - sn_app_eng_studio.admin — can manage/approve apps
  
Governance:
  - App intake process (request → approve → develop → deploy)
  - Template restrictions (limit what devs can create)
  - Instance scan integration (check quality before deploy)
  - Pipeline deployment (Dev → Test → Prod via CI/CD)
```

### Collaboration Features
```
AES supports team development:
  - Multiple developers per app
  - Source control integration (Git)
  - Version management
  - Branching support
  - Change tracking (who modified what)
  
App Deployment:
  - Publish to App Repository
  - Install via instance CI/CD pipeline
  - Or deploy via Update Sets (legacy)
```

## Scripting in Scoped Apps

### Scoped App Restrictions
```javascript
// Scoped apps have limited API access compared to global scope

// ALLOWED in scoped apps:
var gr = new GlideRecord('my_scoped_table');  // Own tables
gr.addQuery('active', true);
gr.query();

var sys = new GlideSystem();  // Limited GlideSystem methods
gs.info('Scoped log message');
gs.getProperty('x_myco_myapp.my_property');  // Own properties only

// RESTRICTED in scoped apps (need cross-scope access):
// - Direct access to tables in other scopes
// - System properties not in your scope
// - GlideRecord on system tables (need explicit access)

// Cross-scope access pattern:
// 1. Create a Script Include in global scope (or target scope)
// 2. Mark it as "Accessible from: All application scopes"
// 3. Call it from your scoped app
```

### Application Properties
```javascript
// Scoped app properties (editable per-environment)
// Navigate: sys_properties_list.do?sysparm_query=name STARTSWITH x_myco_myapp

// Set property
gs.setProperty('x_myco_myapp.max_retries', '3');

// Get property
var maxRetries = parseInt(gs.getProperty('x_myco_myapp.max_retries', '5'));

// App-specific system property categories
// Navigate: System Properties > Categories
// Create category for your app's properties
```

### Application Menus & Modules
```
Auto-created by AES, but can customize:

Table: sys_app_application (Menu)
Table: sys_app_module (Module)

Module types:
  - List: show table records
  - URL: link to any page
  - Filter: pre-filtered list view
  - Report: link to a report
  - Separator: visual divider
  - Content Page: static content
```

## App Engine Best Practices

1. **Extend task** for any work-tracking table — get SLA, assignment, state machine for free
2. **Use AES for citizen developers** — guided experience prevents platform damage
3. **Governance first** — set up intake/approval before opening AES to developers
4. **Instance scan** every app before deployment — catch issues early
5. **Scoped over global** — always build in a scoped app, never global
6. **Version your apps** — use semantic versioning via source control
7. **Template common patterns** — create custom AES templates for your org
8. **Limit direct table access** — use ACLs even in scoped apps
9. **Test data strategy** — plan how test data moves between instances
10. **Document APIs** — if your app exposes Script Includes for other apps, document them
