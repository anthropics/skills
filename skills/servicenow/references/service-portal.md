# Service Portal

## Overview

Service Portal is ServiceNow's AngularJS-based framework for building user-facing portals. It provides a widget-based architecture for creating self-service experiences for employees, customers, and partners.

### Portal Structure
```
Service Portal
├── Portal Record (sp_portal)
│   ├── Theme (sp_theme)
│   ├── CSS Variables / SCSS
│   └── Logo, favicon, branding
├── Pages (sp_page)
│   ├── Containers (rows/columns)
│   └── Widget Instances (sp_instance)
├── Widgets (sp_widget)
│   ├── HTML Template
│   ├── Client Script (AngularJS controller)
│   ├── Server Script (Rhino/GlideRecord)
│   ├── CSS/SCSS
│   ├── Link function (advanced DOM)
│   └── Angular Providers (services/factories)
├── Headers & Footers (sp_header_footer)
├── Menus (sp_menu)
└── Search Sources (sp_search_source)
```

## Widget Architecture

### Widget Components
```
Every widget has up to 6 parts:

1. HTML Template — AngularJS template (HTML + ng-directives)
2. CSS — scoped styles (SCSS supported)
3. Client Script — AngularJS controller function
4. Server Script — runs on server, populates data object
5. Link Function — advanced DOM manipulation (rare)
6. Angular Providers — reusable services/factories

Data flow:
  Server Script → data object → Client Script → HTML Template
  Client Script → $http/spUtil → Server Script (via GlideAjax or widget server)
```

### Server Script
```javascript
// Server script — runs on page load
// Available objects: input, data, options, $sp

(function() {
    // Query data for the widget
    var gr = new GlideRecord('incident');
    gr.addQuery('caller_id', gs.getUserID());
    gr.addActiveQuery();
    gr.orderByDesc('sys_created_on');
    gr.setLimit(10);
    gr.query();
    
    data.incidents = [];
    while (gr.next()) {
        data.incidents.push({
            sys_id: gr.getUniqueValue(),
            number: gr.getValue('number'),
            short_description: gr.getValue('short_description'),
            state: gr.state.getDisplayValue(),
            priority: gr.getValue('priority'),
            opened_at: gr.getValue('opened_at')
        });
    }
    
    data.count = data.incidents.length;
    
    // Access widget options
    data.title = options.title || 'My Incidents';
    data.max_display = options.max_display || 5;
    
    // Handle client-side actions (POST back)
    if (input) {
        if (input.action == 'close_incident') {
            var inc = new GlideRecord('incident');
            if (inc.get(input.sys_id)) {
                inc.setValue('state', '7'); // Closed
                inc.setValue('close_notes', input.close_notes || 'Closed via portal');
                inc.update();
                data.message = 'Incident ' + inc.getValue('number') + ' closed.';
            }
        }
    }
})();
```

### Client Script (AngularJS Controller)
```javascript
// Client script — AngularJS controller
// Available: $scope, $http, spUtil, $location, $timeout, snRecordWatcher

api.controller = function($scope, spUtil, snRecordWatcher, $timeout) {
    var c = this;  // 'c' is the controller alias used in HTML
    
    // Data from server script is available as c.data
    c.incidents = c.data.incidents;
    c.title = c.data.title;
    
    // Client-side action — calls server script with input
    c.closeIncident = function(sysId) {
        c.data.action = 'close_incident';
        c.data.sys_id = sysId;
        c.data.close_notes = c.closeNotes;
        
        // POST back to server script
        c.server.update().then(function(response) {
            // Server script runs again with input populated
            c.incidents = response.data.incidents;
            spUtil.addInfoMessage(response.data.message);
        });
    };
    
    // Real-time updates using Record Watcher
    snRecordWatcher.initList('incident', 'caller_id=' + window.NOW.user_id + '^active=true');
    $scope.$on('record.updated', function(event, data) {
        // Refresh widget when incident is updated
        c.server.refresh().then(function(response) {
            c.incidents = response.data.incidents;
        });
    });
    
    // Navigate to a page
    c.viewIncident = function(sysId) {
        $location.url('?id=ticket&table=incident&sys_id=' + sysId);
    };
    
    // Use spUtil for common operations
    c.showForm = function() {
        spUtil.get('widget-form', {
            table: 'incident',
            sys_id: '-1',  // New record
            view: 'sp'
        }).then(function(widget) {
            c.formWidget = widget;
        });
    };
};
```

### HTML Template
```html
<!-- AngularJS template — uses 'c' as controller alias -->
<div class="panel panel-default">
    <div class="panel-heading">
        <h3>{{c.title}} ({{c.data.count}})</h3>
    </div>
    <div class="panel-body">
        <!-- Empty state -->
        <div ng-if="c.incidents.length == 0" class="text-center text-muted">
            <i class="fa fa-check-circle fa-3x"></i>
            <p>No open incidents. You're all set!</p>
        </div>
        
        <!-- Incident list -->
        <div class="list-group">
            <a ng-repeat="inc in c.incidents | limitTo:c.data.max_display" 
               ng-click="c.viewIncident(inc.sys_id)"
               class="list-group-item"
               ng-class="{'list-group-item-danger': inc.priority == '1',
                          'list-group-item-warning': inc.priority == '2'}">
                
                <div class="row">
                    <div class="col-sm-3">
                        <strong>{{inc.number}}</strong>
                    </div>
                    <div class="col-sm-6">
                        {{inc.short_description}}
                    </div>
                    <div class="col-sm-3 text-right">
                        <span class="label" 
                              ng-class="{'label-success': inc.state == 'Resolved',
                                         'label-info': inc.state == 'In Progress',
                                         'label-default': inc.state == 'New'}">
                            {{inc.state}}
                        </span>
                    </div>
                </div>
            </a>
        </div>
        
        <!-- Close incident modal -->
        <div ng-if="c.showCloseModal" class="well">
            <h4>Close Incident</h4>
            <textarea ng-model="c.closeNotes" 
                      class="form-control" 
                      placeholder="Closure notes..."></textarea>
            <br>
            <button class="btn btn-primary" 
                    ng-click="c.closeIncident(c.selectedIncident)">
                Confirm Close
            </button>
            <button class="btn btn-default" 
                    ng-click="c.showCloseModal = false">
                Cancel
            </button>
        </div>
    </div>
</div>
```

### Widget CSS (SCSS)
```scss
// Scoped to widget — won't leak to other widgets
.panel-heading h3 {
    margin: 0;
    font-size: 18px;
    font-weight: 600;
}

.list-group-item {
    cursor: pointer;
    transition: background-color 0.2s;
    
    &:hover {
        background-color: $sp-navbar-divider-color;  // Theme variable
    }
}

.label {
    font-size: 12px;
    padding: 4px 8px;
}

// Responsive
@media (max-width: 768px) {
    .row > div {
        margin-bottom: 5px;
    }
}
```

## $sp API (GlideSPScriptable)

### Server-Side $sp Methods
```javascript
// Available in widget server scripts as $sp

// Get current portal
var portal = $sp.getPortalRecord();
var portalUrl = portal.getValue('url_suffix');

// Get page parameters
var sysId = $sp.getParameter('sys_id');
var table = $sp.getParameter('table');

// Get current user
var userGr = $sp.getUser();  // Returns GlideRecord of sys_user

// Get widget by ID (embed another widget)
var widget = $sp.getWidget('widget-cool-clock', {
    timezone: 'US/Central'
});
data.clockWidget = widget;

// Get catalog item for display
var catItem = $sp.getCatalogItem('sys_id_here');
data.catalogItem = catItem;

// Get Knowledge Base article
var article = $sp.getKBArticle('kb_sys_id');
data.article = article;

// Get record and check ACLs
var record = $sp.getRecord();  // Current page record
var canRead = $sp.canReadRecord('incident', 'sys_id_here');
var canWrite = GlideRecordSecure('incident'); // Respects ACLs

// Build URL
var url = $sp.getPortalUrl() + '?id=form&table=incident&sys_id=' + sysId;
```

## Angular Providers

### Creating a Reusable Service
```javascript
// Angular Provider — shared service across widgets
// Type: Factory

function myPortalService($http, spUtil) {
    var service = {};
    
    service.getRecords = function(table, query, limit) {
        return $http.get('/api/now/table/' + table, {
            params: {
                sysparm_query: query,
                sysparm_limit: limit || 20,
                sysparm_display_value: true
            }
        }).then(function(response) {
            return response.data.result;
        });
    };
    
    service.createRecord = function(table, data) {
        return $http.post('/api/now/table/' + table, data)
            .then(function(response) {
                spUtil.addInfoMessage('Record created: ' + response.data.result.number);
                return response.data.result;
            })
            .catch(function(error) {
                spUtil.addErrorMessage('Error creating record');
                throw error;
            });
    };
    
    service.formatDate = function(dateString) {
        if (!dateString) return '';
        var d = new Date(dateString);
        return d.toLocaleDateString() + ' ' + d.toLocaleTimeString();
    };
    
    return service;
}

// Register: paste into Angular Provider record
// Name: myPortalService
// Type: Factory
```

### Using Providers in Widgets
```javascript
// Client script — inject the provider
api.controller = function($scope, myPortalService) {
    var c = this;
    
    myPortalService.getRecords('incident', 'active=true', 10)
        .then(function(records) {
            c.incidents = records;
        });
    
    c.createIncident = function() {
        myPortalService.createRecord('incident', {
            short_description: c.description,
            urgency: c.urgency
        }).then(function(result) {
            c.newIncidentNumber = result.number;
        });
    };
};
```

## Embedded Widgets

### Embedding Widgets in Other Widgets
```javascript
// Server script — get widget to embed
data.formWidget = $sp.getWidget('widget-form', {
    table: 'incident',
    sys_id: $sp.getParameter('sys_id'),
    view: 'sp'
});

data.approvalWidget = $sp.getWidget('sc-approval-summary', {
    sys_id: $sp.getParameter('sys_id')
});
```

```html
<!-- HTML Template — render embedded widget -->
<sp-widget widget="c.data.formWidget"></sp-widget>

<!-- Conditional embedding -->
<sp-widget ng-if="c.showApproval" widget="c.data.approvalWidget"></sp-widget>
```

## Theming & Branding

### Theme Configuration
```
Navigate: Service Portal > Themes (sp_theme)

Theme components:
  - CSS Variables: brand colors, fonts, spacing
  - Header/Footer: portal-wide header and footer widgets
  - SCSS: global styles compiled into portal CSS
  
Key CSS variables:
  $sp-navbar-bg             — navbar background
  $sp-navbar-text-color     — navbar text
  $sp-body-bg               — page background
  $sp-primary-color         — primary brand color
  $sp-link-color            — link color
  $sp-tagline-color         — subtitle text
  $sp-navbar-divider-color  — divider lines
```

### Custom Theme SCSS
```scss
// Theme SCSS — applies globally to the portal

// Override Bootstrap variables
$brand-primary: #1a73e8;
$brand-success: #34a853;
$brand-danger: #ea4335;
$font-family-base: 'Poppins', 'Helvetica Neue', sans-serif;
$font-size-base: 14px;

// Custom portal styles
.navbar-default {
    box-shadow: 0 2px 4px rgba(0,0,0,0.1);
}

.panel {
    border-radius: 8px;
    border: none;
    box-shadow: 0 1px 3px rgba(0,0,0,0.08);
}

// Catalog item cards
.sc-cat-item {
    transition: transform 0.2s;
    &:hover {
        transform: translateY(-2px);
    }
}

// Service Portal specific utility classes
.sp-hero {
    background: linear-gradient(135deg, $brand-primary, darken($brand-primary, 15%));
    color: white;
    padding: 60px 0;
    text-align: center;
}
```

## Pages & Navigation

### Page Configuration
```
Navigate: Service Portal > Pages (sp_page)

Page record fields:
  - Title: page display name
  - ID: URL identifier (?id=page_id)
  - Internal: hide from public navigation
  - CSS: page-specific styles
  - Roles: restrict access
  
Page layout:
  Container → Row → Column → Widget Instance
  
  Column sizes: 1-12 (Bootstrap grid)
  Row options: full-width, contained
```

### URL Parameters
```javascript
// Server script — access URL parameters
var pageId = $sp.getParameter('id');
var tableName = $sp.getParameter('table');
var recordSysId = $sp.getParameter('sys_id');
var customParam = $sp.getParameter('my_param');

// Client script — navigate with parameters
c.navigateToRecord = function(table, sysId) {
    var url = '?id=form&table=' + table + '&sys_id=' + sysId;
    window.location.href = url;
    // OR using $location:
    // $location.search({id: 'form', table: table, sys_id: sysId});
};
```

### Menu Configuration
```
Navigate: Service Portal > Menus (sp_menu)

Menu items:
  - Label: display text
  - Page: link to portal page
  - URL: external link
  - Sub-items: dropdown children
  - Roles: visibility per role
  - Order: menu position
  - Glyph: Font Awesome icon
```

## Search Sources

### Custom Search Source
```
Navigate: Service Portal > Search Sources (sp_search_source)

Fields:
  - Name: display name
  - Table: source table
  - Conditions: base filter
  - Page: results page ID
  - Fields to display: title, description, image
  - Order: search priority
  
Script-based search:
```
```javascript
// Search source data fetch script
(function(query) {
    var results = [];
    var gr = new GlideRecord('kb_knowledge');
    gr.addQuery('workflow_state', 'published');
    gr.addQuery('123TEXTQUERY321', query);
    gr.setLimit(10);
    gr.query();
    
    while (gr.next()) {
        results.push({
            primary: gr.getValue('short_description'),
            secondary: gr.getValue('kb_knowledge_base').getDisplayValue(),
            tertiary: gr.getValue('sys_view_count') + ' views',
            url: '?id=kb_article&sys_id=' + gr.getUniqueValue(),
            sys_id: gr.getUniqueValue()
        });
    }
    return results;
})(query);
```

## spUtil — Client-Side Utility

```javascript
// spUtil — available in all widget client scripts

// Messages
spUtil.addInfoMessage('Record saved successfully');
spUtil.addErrorMessage('Something went wrong');
spUtil.addTrivialMessage('FYI: System maintenance tonight');

// Get a widget reference
spUtil.get('widget-id', {option: 'value'}).then(function(widget) {
    c.embeddedWidget = widget;
});

// Update widget (calls server script with input)
spUtil.update($scope);  // Shortcut for c.server.update()

// Record watcher — real-time updates
spUtil.recordWatch($scope, 'incident', 'active=true', function(name, data) {
    // Called when record matching filter is inserted/updated
    c.server.refresh();
});

// Create a modal
spUtil.createModal({
    title: 'Confirm Action',
    message: 'Are you sure you want to proceed?',
    buttons: [
        {label: 'Cancel', cancel: true},
        {label: 'Confirm', primary: true}
    ]
}).then(function() {
    // User clicked Confirm
}, function() {
    // User clicked Cancel
});
```

## Performance Optimization

### Widget Performance
```
1. Minimize server script queries
   - Use encoded queries, setLimit(), setFields()
   - Cache data when possible (session/application cache)
   
2. Reduce client-side DOM operations
   - Use ng-if over ng-show for heavy content (ng-if removes from DOM)
   - Limit ng-repeat with | limitTo filter
   - Use track by in ng-repeat: ng-repeat="item in items track by item.sys_id"
   
3. Avoid unnecessary server roundtrips
   - Batch operations in single server.update() call
   - Use Angular providers to cache shared data
   - Client-side filtering when dataset is small
   
4. Image optimization
   - Use thumbnails in lists, full image on detail
   - Lazy load images below the fold
   
5. Use record watcher sparingly
   - Each watcher = active WebSocket connection
   - Unsubscribe when leaving page: $scope.$on('$destroy', ...)
```

### Caching Pattern
```javascript
// Server script — cache expensive queries
(function() {
    var cacheKey = 'sp_catalog_categories_' + gs.getUserID();
    var cached = gs.getSession().getClientData(cacheKey);
    
    if (cached) {
        data.categories = JSON.parse(cached);
        return;
    }
    
    // Expensive query
    var cats = [];
    var gr = new GlideRecord('sc_category');
    gr.addActiveQuery();
    gr.orderBy('title');
    gr.query();
    while (gr.next()) {
        cats.push({
            sys_id: gr.getUniqueValue(),
            title: gr.getValue('title'),
            icon: gr.getValue('icon')
        });
    }
    
    data.categories = cats;
    gs.getSession().putClientData(cacheKey, JSON.stringify(cats));
})();
```

## Common Patterns

### Form Widget with Validation
```javascript
// Server script
(function() {
    if (input && input.action == 'submit') {
        // Validate
        var errors = [];
        if (!input.short_description) errors.push('Description is required');
        if (!input.category) errors.push('Category is required');
        
        if (errors.length > 0) {
            data.errors = errors;
            return;
        }
        
        // Create record
        var gr = new GlideRecord('incident');
        gr.initialize();
        gr.setValue('short_description', input.short_description);
        gr.setValue('description', input.description);
        gr.setValue('category', input.category);
        gr.setValue('caller_id', gs.getUserID());
        gr.insert();
        
        data.success = true;
        data.incidentNumber = gr.getValue('number');
    }
    
    // Load categories for dropdown
    data.categories = [];
    var cat = new GlideRecord('sys_choice');
    cat.addQuery('name', 'incident');
    cat.addQuery('element', 'category');
    cat.addActiveQuery();
    cat.orderBy('sequence');
    cat.query();
    while (cat.next()) {
        data.categories.push({
            value: cat.getValue('value'),
            label: cat.getValue('label')
        });
    }
})();
```

### Pagination Widget
```javascript
// Server script with pagination
(function() {
    var pageSize = options.page_size || 10;
    var currentPage = input && input.page ? input.page : 1;
    var offset = (currentPage - 1) * pageSize;
    
    // Get total count
    var ga = new GlideAggregate('incident');
    ga.addQuery('caller_id', gs.getUserID());
    ga.addAggregate('COUNT');
    ga.query();
    data.totalCount = ga.next() ? parseInt(ga.getAggregate('COUNT')) : 0;
    data.totalPages = Math.ceil(data.totalCount / pageSize);
    data.currentPage = currentPage;
    
    // Get page of records
    var gr = new GlideRecord('incident');
    gr.addQuery('caller_id', gs.getUserID());
    gr.orderByDesc('sys_created_on');
    gr.chooseWindow(offset, offset + pageSize);
    gr.query();
    
    data.records = [];
    while (gr.next()) {
        data.records.push({
            sys_id: gr.getUniqueValue(),
            number: gr.getValue('number'),
            short_description: gr.getValue('short_description'),
            state: gr.state.getDisplayValue()
        });
    }
})();
```

```javascript
// Client script — pagination controls
api.controller = function($scope) {
    var c = this;
    
    c.goToPage = function(page) {
        if (page < 1 || page > c.data.totalPages) return;
        c.data.page = page;
        c.server.update().then(function(response) {
            c.data.records = response.data.records;
            c.data.currentPage = response.data.currentPage;
        });
    };
};
```

## Best Practices

1. **Server script for data, client script for interaction** — never query GlideRecord client-side
2. **Use `c.server.update()`** for client→server communication, not raw `$http` to ServiceNow APIs
3. **Always check ACLs** — use `GlideRecordSecure` or `$sp.canReadRecord()` before displaying data
4. **Scope your CSS** — widget CSS is auto-scoped, but theme CSS isn't
5. **Embed widgets** with `$sp.getWidget()` + `<sp-widget>` — don't duplicate code
6. **Record Watcher for real-time** — but limit active watchers (performance cost)
7. **Test mobile** — Service Portal is responsive but widgets may not be
8. **Options for configurability** — use widget instance options so the same widget works in multiple contexts
9. **Error handling** — always handle server.update() failures with `.catch()` or error state
10. **URL parameters** — use `$sp.getParameter()` server-side, `$location.search()` client-side
