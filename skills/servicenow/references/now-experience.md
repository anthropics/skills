# Now Experience / UI Builder

## UI Builder Overview

UI Builder is the visual editor for creating **Now Experience** pages — modern, responsive UIs that replace Service Portal for new development.

Navigate: **UI Builder** (All > Now Experience > UI Builder)

## Pages & Variants

### Page Structure
```
Page: Incident Overview
├── URL: /x/myapp/incident-overview
├── Variants:
│   ├── Default (desktop)
│   ├── Tablet variant (breakpoint: 768px)
│   └── Mobile variant (breakpoint: 480px)
├── Data Resources:
│   ├── Look Up incident record (GlideRecord)
│   └── Get user preferences (Script)
└── Components:
    ├── Header (Now Heading)
    ├── Record Details (Now Record Fields)
    ├── Activity Stream
    └── Related Lists
```

### Creating a Page
1. Open UI Builder
2. Click **Create** → **Page**
3. Choose **Experience**: Workspace, Portal, or Custom App
4. Set URL path, name, description
5. Add components from the component palette

## Data Resources

### Record Data Resource
```
Type: Look up record
Table: incident
Conditions: sys_id = [Page Parameter: sys_id]
Fields: number, short_description, state, priority, assigned_to, caller_id
```

### GraphQL Data Resource
```
Type: GraphQL
Query:
  query($sysId: String!) {
    GlideRecord_Query {
      incident(queryConditions: { sys_id: { _eq: $sysId } }) {
        number { value displayValue }
        short_description { value }
        state { value displayValue }
        assigned_to { value displayValue }
      }
    }
  }
Variables:
  sysId: [Page Parameter: sys_id]
```

### Script Data Resource
```javascript
// Server-side script data resource
(function(dataResourceParams) {
    var result = {
        incidents: [],
        totalCount: 0
    };
    
    var ga = new GlideAggregate('incident');
    ga.addQuery('assigned_to', gs.getUserID());
    ga.addActiveQuery();
    ga.addAggregate('COUNT');
    ga.query();
    if (ga.next()) {
        result.totalCount = parseInt(ga.getAggregate('COUNT'));
    }
    
    var gr = new GlideRecord('incident');
    gr.addQuery('assigned_to', gs.getUserID());
    gr.addActiveQuery();
    gr.orderByDesc('priority');
    gr.setLimit(10);
    gr.query();
    while (gr.next()) {
        result.incidents.push({
            sys_id: gr.getUniqueValue(),
            number: gr.getValue('number'),
            short_description: gr.getValue('short_description'),
            priority: gr.getValue('priority')
        });
    }
    
    return result;
})(dataResourceParams);
```

## Custom Components (Seismic Framework)

### Component Scaffold (CLI)
```bash
# Install Now CLI
npm install -g @servicenow/cli

# Create component project
snc ui-component create --name x-myapp-incident-card
cd x-myapp-incident-card

# Project structure:
# ├── src/
# │   ├── x-myapp-incident-card/
# │   │   ├── __tests__/
# │   │   ├── index.js          ← main component
# │   │   ├── styles.scss       ← component styles
# │   │   └── actionHandlers.js ← event handlers
# │   └── index.js
# ├── package.json
# └── now-ui.json               ← component metadata
```

### Component Definition
```javascript
// src/x-myapp-incident-card/index.js
import { createCustomElement } from '@servicenow/ui-core';
import snabbdom from '@servicenow/ui-renderer-snabbdom';
import styles from './styles.scss';

const view = (state, { updateState, dispatch }) => {
    const { incidents, loading } = state;
    
    return (
        <div className="incident-card">
            {loading ? (
                <now-loader label="Loading..." />
            ) : (
                <div className="incident-list">
                    {incidents.map(inc => (
                        <div className="incident-item" 
                             key={inc.sys_id}
                             on-click={() => dispatch('INCIDENT_SELECTED', { sys_id: inc.sys_id })}>
                            <span className="number">{inc.number}</span>
                            <span className="desc">{inc.short_description}</span>
                            <now-highlighted-value 
                                label="Priority" 
                                value={inc.priority} 
                                variant={inc.priority === '1' ? 'critical' : 'normal'} />
                        </div>
                    ))}
                </div>
            )}
        </div>
    );
};

createCustomElement('x-myapp-incident-card', {
    renderer: { type: snabbdom },
    view,
    styles,
    properties: {
        assignedTo: { default: '' },
        maxRecords: { default: 10 }
    },
    initialState: {
        incidents: [],
        loading: true
    },
    actionHandlers: {
        'COMPONENT_RENDERED': ({ dispatch, properties }) => {
            dispatch('FETCH_INCIDENTS', { 
                assignedTo: properties.assignedTo,
                limit: properties.maxRecords 
            });
        }
    }
});
```

### Action Handlers (data fetching)
```javascript
// src/x-myapp-incident-card/actionHandlers.js
import { actionTypes } from '@servicenow/ui-core';
import { createHttpEffect } from '@servicenow/ui-effect-http';

export default {
    'FETCH_INCIDENTS': createHttpEffect('/api/now/table/incident', {
        method: 'GET',
        queryParams: {
            sysparm_query: ({ action }) => 
                `assigned_to=${action.payload.assignedTo}^active=true`,
            sysparm_limit: ({ action }) => action.payload.limit,
            sysparm_fields: 'sys_id,number,short_description,priority,state'
        },
        successActionType: 'FETCH_INCIDENTS_SUCCESS',
        errorActionType: 'FETCH_INCIDENTS_ERROR'
    }),
    
    'FETCH_INCIDENTS_SUCCESS': ({ action, updateState }) => {
        updateState({
            incidents: action.payload.result,
            loading: false
        });
    },
    
    'FETCH_INCIDENTS_ERROR': ({ updateState }) => {
        updateState({ loading: false, incidents: [] });
    }
};
```

### Deploy Component
```bash
# Build and deploy to instance
snc ui-component deploy --instance https://myinstance.service-now.com

# Development mode (live reload)
snc ui-component develop --instance https://myinstance.service-now.com
```

## Workspaces

### Agent Workspace Configuration
```
Navigate: Workspace Experience > Workspace Configuration

Key settings:
- Landing page: Dashboard or list view
- Record pages: Layout per table (incident, problem, change)
- Lists: Column configuration, filters
- Contextual sidebar: Related records, activity stream
- Playbook panel: Position and auto-open settings
```

### Workspace Record Page Layout
```
┌─────────────────────────────────────────────────┐
│ Header: Number | State | Priority | Actions      │
├──────────────────────┬──────────────────────────┤
│ Form Fields          │ Contextual Sidebar        │
│ - Short Description  │ - Activity Stream         │
│ - Caller             │ - Related Records         │
│ - Category           │ - Similar Incidents       │
│ - Assignment Group   │ - Playbook Activities     │
│ - Assigned To        │                           │
│ - Description        │                           │
├──────────────────────┴──────────────────────────┤
│ Related Lists / Tabs                              │
│ [Tasks] [Worknotes] [Attachments] [Approvals]    │
└─────────────────────────────────────────────────┘
```

## Declarative Actions

Replace UI Actions in workspaces:
```
Navigate: Now Experience > Declarative Actions

Action: Escalate Incident
Applicable to: incident table
Conditions: state != 6 AND state != 7 (not resolved/closed)
Roles: itil
Action type: Record action
Form: Form button
List: List action

Implementation:
  1. Client action: Show confirmation dialog
  2. Server action: Update record (priority=1, state=2)
  3. Client action: Show success banner
```

## UX Page Properties & State

### Page Parameters
```
Define URL parameters that components can consume:
  /incident-dashboard?group=SYS_ID&view=kanban

Components bind to page parameters:
  Component property: group → Page parameter: group
  Component property: viewType → Page parameter: view
```

### Client State Parameters
```
Share state between components on same page:
  Component A dispatches: UPDATE_CLIENT_STATE_PARAM
    key: selectedIncident
    value: sys_id
    
  Component B listens: CLIENT_STATE_PARAM_CHANGED
    key: selectedIncident
    → Fetches and displays incident detail
```

## Theming & Branding

```
Navigate: Now Experience > Theme Management

Customizable:
- Primary/secondary colors
- Font family and sizes
- Logo and favicon
- Header/navigation colors
- Component-level overrides via CSS custom properties

CSS Variables:
  --now-color--primary-1
  --now-color--secondary-1
  --now-font-family
  --now-button--primary--background-color
```

## Mobile Development

### Configurable Workspace (mobile-responsive)
- Workspaces auto-adapt to mobile breakpoints
- Configure mobile-specific variants in UI Builder
- Simplified navigation: bottom tabs, swipe gestures

### Native Mobile (ServiceNow Mobile App)
```
Navigate: Now Mobile > Mobile App Builder

Applets:
- My Requests
- Approvals
- Agent (for ITSM agents)
- Custom applets via Mobile App Builder

Mobile Cards:
- Configurable list views
- Quick actions (swipe)
- Offline support (limited)
```

## Best Practices

1. **Use UI Builder for new development** — Service Portal is legacy
2. **GraphQL over REST** for data resources — better performance, field selection
3. **Component reuse** — build generic components, configure via properties
4. **Minimize data resources** — combine queries where possible
5. **Test at all breakpoints** — desktop, tablet, mobile
6. **Use Now Design System components** — consistent UX, accessibility
7. **Declarative Actions over UI Actions** for workspaces
8. **Cache static data** — reduce server round-trips
9. **Lazy load** — don't fetch data until component is visible
10. **Accessibility** — use ARIA attributes, keyboard navigation, screen reader support
