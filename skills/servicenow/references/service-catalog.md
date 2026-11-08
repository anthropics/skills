# Service Catalog

## Catalog Structure

```
Service Catalog
├── Catalog Categories
│   ├── Hardware
│   ├── Software
│   ├── Access Requests
│   └── General Services
├── Catalog Items (sc_cat_item)
│   ├── Variables (item_option_new)
│   ├── Variable Sets (item_option_new_set)
│   ├── Catalog UI Policies
│   ├── Catalog Client Scripts
│   └── Workflows / Flows
├── Record Producers (sc_cat_item_producer)
├── Order Guides (sc_cat_item_guide)
└── Content Items (sc_cat_item_content)
```

## Catalog Items

### Creating a Standard Catalog Item
```
Table: sc_cat_item
Key fields:
  - Name, Short description, Description
  - Category (sc_category)
  - Catalogs (many-to-many: sc_cat_item_catalog)
  - Active, Desktop/Mobile/Service Portal
  - Workflow or Flow
  - Template (for task generation)
```

### Variables (Questions)
```
Table: item_option_new
Types:
  - Single Line Text, Multi Line Text
  - Select Box, Lookup Select Box
  - Check Box, Multiple Choice
  - Reference (links to any table)
  - Date, Date/Time
  - Macro (free-form HTML/UI Page)
  - Label (display only)
  - Container Start/End (grouping)
  - Masked (password fields)
  - Requested For (special user picker)

Key attributes:
  - Name (internal), Question Text (display)
  - Type, Default Value
  - Mandatory (yes/no/on condition)
  - Order (display sequence)
  - Read only, Hidden
  - Reference qualifier (for Reference type)
```

### Variable Sets (Reusable Variable Groups)
```
Table: item_option_new_set
Use case: Common questions shared across items
  e.g., "Justification Set" with manager, reason, cost center

Creating:
  1. Create Variable Set record
  2. Add variables to the set
  3. Associate set with catalog items (many-to-many)

Types:
  - Single Row: variables appear inline
  - Multi Row: tabular data entry (e.g., multiple users)
```

## Catalog Client Scripts

### onChange — Dynamic Variable Behavior
```javascript
// Catalog Client Script — onChange
// Applies to: Catalog Item or Variable Set
// Variable: department
function onChange(control, oldValue, newValue, isLoading) {
    if (isLoading || newValue == '') return;
    
    // Show/hide variable based on selection
    if (newValue == 'IT') {
        g_form.setDisplay('it_subcategory', true);
        g_form.setMandatory('it_subcategory', true);
    } else {
        g_form.setDisplay('it_subcategory', false);
        g_form.setMandatory('it_subcategory', false);
    }
}
```

### onLoad — Initialize Form State
```javascript
// Catalog Client Script — onLoad
function onLoad() {
    // Pre-populate variables based on current user
    var user = g_user.userID;
    g_form.setValue('requested_for', user);
    
    // Hide variables initially
    g_form.setDisplay('additional_details', false);
    g_form.setDisplay('manager_approval_required', false);
}
```

### onSubmit — Validate Before Submission
```javascript
// Catalog Client Script — onSubmit
function onSubmit() {
    var cost = parseFloat(g_form.getValue('estimated_cost'));
    
    if (cost > 5000 && g_form.getValue('manager_justification') == '') {
        g_form.addErrorMessage('Manager justification required for items over $5,000');
        g_form.setMandatory('manager_justification', true);
        return false; // Prevent submission
    }
    return true;
}
```

## Catalog UI Policies

```
Table: catalog_ui_policy
Use case: Show/hide/mandatory variables without scripting

Example: Show "Emergency Justification" when Priority = Critical
  Conditions: priority == 1
  Actions:
    - Set "emergency_justification" visible = true
    - Set "emergency_justification" mandatory = true
    
Reverse: When condition no longer met, reverse actions automatically
Order: Lower number = higher priority
```

## Record Producers

Generate task records directly from catalog submissions.

```
Table: sc_cat_item_producer
Key fields:
  - Table name: target table (e.g., incident, hr_case, sc_task)
  - Script: server-side processing after submission

Use cases:
  - "Report an Incident" → creates incident record
  - "HR Case" → creates hr_case record
  - "Facility Request" → creates fm_request record

Server Script (runs after record creation):
```
```javascript
// Record Producer script
// 'current' = the newly created target record
// 'producer' = the catalog item
// Variables accessible via: producer.getVariable('var_name')

current.setValue('short_description', producer.getVariable('issue_summary'));
current.setValue('description', producer.getVariable('detailed_description'));
current.setValue('category', producer.getVariable('category'));
current.setValue('cmdb_ci', producer.getVariable('affected_ci'));
current.setValue('impact', producer.getVariable('impact'));
current.setValue('urgency', producer.getVariable('urgency'));

// Set assignment based on category
var category = current.getValue('category');
if (category == 'network') {
    current.assignment_group.setDisplayValue('Network Operations');
} else if (category == 'database') {
    current.assignment_group.setDisplayValue('Database Administration');
}
```

## Order Guides

Multi-item ordering with a wizard-style interface.

```
Table: sc_cat_item_guide
Use case: "New Employee Onboarding" bundles:
  - Laptop request
  - Software bundle
  - Building access
  - Email account
  - Phone setup

Structure:
  1. Create Order Guide record
  2. Define Rule Base (conditions for including items)
  3. Optional: Script to cascade variables to child items
  
Cascade Script:
```
```javascript
// Order Guide cascade script
// Pass selected department to all child items
var items = current.guide_items;
for (var i = 0; i < items.length; i++) {
    items[i].setVariable('department', current.getVariable('department'));
    items[i].setVariable('location', current.getVariable('office_location'));
}
```

## Fulfillment Workflows

### Flow Designer (Modern)
```
Trigger: Service Catalog item requested
  → Approval (if cost > threshold)
  → Create catalog tasks (parallel or sequential)
  → Notify fulfillment groups
  → Wait for task completion
  → Close RITM
```

### Execution Plans
```
Table: sc_cat_item_delivery_plan
Use case: Multi-step fulfillment without Flow/Workflow

Delivery Plan:
  Task 1: "Provision Account" → Assignment: IT Ops
  Task 2: "Ship Hardware" → Assignment: Logistics (after Task 1)
  Task 3: "Configure Software" → Assignment: Desktop Support (after Task 1)
  Task 4: "User Training" → Assignment: Training Team (after Task 2 & 3)
```

## Pricing & Recurring Costs

```
Catalog Item fields:
  - Price: one-time cost
  - Recurring price: monthly/annual
  - Recurring frequency: monthly, quarterly, annually
  
Variable pricing (dynamic):
  Use pricing implications on variables
  e.g., Laptop model selection changes price
  
Script-based pricing:
```
```javascript
// Pricing script on catalog item
// Runs when item is added to cart
(function calculatePrice(item) {
    var basePrice = 500;
    var ram = item.getVariable('ram_size');
    
    if (ram == '32GB') basePrice += 200;
    if (ram == '64GB') basePrice += 500;
    
    var monitor = item.getVariable('external_monitor');
    if (monitor == 'true') basePrice += 350;
    
    item.price = basePrice;
    return basePrice;
})(current);
```

## Service Portal Catalog

### Widget: SC Catalog Item
```javascript
// Server script — custom catalog widget
(function() {
    var catItemId = $sp.getParameter('sys_id');
    var gr = new GlideRecord('sc_cat_item');
    if (gr.get(catItemId)) {
        data.item = {
            name: gr.getValue('name'),
            short_description: gr.getValue('short_description'),
            description: gr.getValue('description'),
            price: gr.getValue('price'),
            picture: gr.getValue('picture')
        };
    }
    
    // Get variables
    data.variables = [];
    var vars = new GlideRecord('item_option_new');
    vars.addQuery('cat_item', catItemId);
    vars.addActiveQuery();
    vars.orderBy('order');
    vars.query();
    while (vars.next()) {
        data.variables.push({
            name: vars.getValue('name'),
            question_text: vars.getValue('question_text'),
            type: vars.getValue('type'),
            mandatory: vars.getValue('mandatory') == 'true'
        });
    }
})();
```

## Catalog Best Practices

1. **Use Variable Sets** for common questions — DRY principle
2. **Catalog UI Policies > Client Scripts** when possible — no code maintenance
3. **Execution Plans** for simple multi-task — save Flow Designer for complex logic
4. **Test in Service Portal AND Agent Workspace** — behavior can differ
5. **Set fulfillment groups** via catalog tasks, not assignment rules
6. **Use record producers** for incident/case creation — better UX than raw forms
7. **Limit variables per item** to 10-15 — too many overwhelms users
8. **Category hierarchy** max 3 levels deep — navigation gets confusing beyond that
9. **Active = false** instead of deleting — preserve order history
10. **Approval policies** by dollar amount — automate low-cost approvals
