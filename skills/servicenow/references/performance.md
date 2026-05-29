# ServiceNow Performance Optimization

## GlideRecord Optimization

### Use setLimit() Always
```javascript
// BAD — fetches ALL records even if you need one
var gr = new GlideRecord('incident');
gr.addQuery('number', 'INC0010001');
gr.query();
if (gr.next()) { /* ... */ }

// GOOD — stops after first match
var gr = new GlideRecord('incident');
gr.addQuery('number', 'INC0010001');
gr.setLimit(1);
gr.query();
if (gr.next()) { /* ... */ }

// BEST — use get() for single record by sys_id
var gr = new GlideRecord('incident');
if (gr.get(sysId)) { /* ... */ }
```

### Use addEncodedQuery for Complex Filters
```javascript
// Encoded query is parsed once and sent to DB — faster than chained addQuery
var gr = new GlideRecord('incident');
gr.addEncodedQuery('active=true^priority=1^state!=6^assignment_groupISNOTEMPTY^sys_created_on>=javascript:gs.daysAgoStart(30)');
gr.query();

// vs chained (slightly slower, more overhead)
gr.addQuery('active', true);
gr.addQuery('priority', '1');
gr.addQuery('state', '!=', '6');
gr.addNotNullQuery('assignment_group');
gr.addQuery('sys_created_on', '>=', gs.daysAgoStart(30));
```

### Select Only Needed Fields
```javascript
// Only fetch fields you need — reduces data transfer
var gr = new GlideRecord('incident');
gr.addActiveQuery();
gr.setLimit(100);
gr.addQuery('priority', '1');
// Restrict returned fields
gr.chooseWindow(0, 100);
gr.query();
// Note: ServiceNow doesn't have a native "select fields" for GlideRecord
// but chooseWindow + setLimit reduces memory footprint
```

### Use GlideAggregate Instead of getRowCount()
```javascript
// BAD — loads ALL records into memory just to count
var gr = new GlideRecord('incident');
gr.addActiveQuery();
gr.query();
var count = gr.getRowCount(); // TERRIBLE for large tables

// GOOD — database-level count
var ga = new GlideAggregate('incident');
ga.addActiveQuery();
ga.addAggregate('COUNT');
ga.query();
var count = 0;
if (ga.next()) count = parseInt(ga.getAggregate('COUNT'));
```

## Avoiding N+1 Queries

```javascript
// BAD — N+1 pattern (1 query + N sub-queries)
var gr = new GlideRecord('incident');
gr.addActiveQuery();
gr.query();
while (gr.next()) {
    var user = new GlideRecord('sys_user');
    user.get(gr.getValue('assigned_to')); // query per incident!
    gs.info(user.getValue('email'));
}

// GOOD — collect IDs, single query
var gr = new GlideRecord('incident');
gr.addActiveQuery();
gr.query();
var userIds = [];
var incidents = [];
while (gr.next()) {
    var userId = gr.getValue('assigned_to');
    if (userId && userIds.indexOf(userId) == -1) userIds.push(userId);
    incidents.push({
        number: gr.getValue('number'),
        assigned_to: userId
    });
}

// Single query for all users
var userMap = {};
if (userIds.length > 0) {
    var ug = new GlideRecord('sys_user');
    ug.addQuery('sys_id', 'IN', userIds.join(','));
    ug.query();
    while (ug.next()) {
        userMap[ug.getUniqueValue()] = ug.getValue('email');
    }
}

// Map results
incidents.forEach(function(inc) {
    inc.email = userMap[inc.assigned_to] || 'unassigned';
});

// ALSO GOOD — use dot-walking (single query, ServiceNow handles join)
var gr = new GlideRecord('incident');
gr.addActiveQuery();
gr.query();
while (gr.next()) {
    var email = gr.getValue('assigned_to.email'); // dot-walk, no extra query
}
```

## Indexing Strategies

### Check Existing Indexes
```
Navigate: System Definition > Tables > [table] > Table Indexes tab

Key indexed fields (incident):
- number (unique)
- sys_id (primary key)
- active + priority (composite)
- assigned_to
- assignment_group
- state
- sys_created_on
```

### Creating Custom Indexes
```
Navigate: System Definition > Tables > [table] > Table Indexes
New Index:
  Table: u_my_custom_table
  Fields: u_status, u_category (composite index)
  Unique: false

// Composite index order matters:
// Index on (category, state) helps: WHERE category='x' AND state='y'
// Does NOT help: WHERE state='y' (wrong order)
```

### When to Add Indexes
- Fields frequently used in `addQuery()` / `addEncodedQuery()`
- Fields used in `orderBy()`
- Reference fields used in joins
- Fields in ACL conditions
- **Don't over-index** — each index slows writes

## Client Script Performance

### Always Use Asynchronous GlideAjax
```javascript
// BAD — blocks UI thread
var ga = new GlideAjax('MyUtil');
ga.addParam('sysparm_name', 'getData');
var result = ga.getXMLWait(); // FREEZES browser!

// GOOD — async callback
var ga = new GlideAjax('MyUtil');
ga.addParam('sysparm_name', 'getData');
ga.getXMLAnswer(function(answer) {
    // Process result without blocking UI
    g_form.setValue('field', answer);
});
```

### Batch GlideAjax Calls
```javascript
// BAD — 3 separate round-trips
var ga1 = new GlideAjax('Util');
ga1.addParam('sysparm_name', 'getA');
ga1.getXMLAnswer(function(a) {
    var ga2 = new GlideAjax('Util');
    ga2.addParam('sysparm_name', 'getB');
    ga2.getXMLAnswer(function(b) {
        // nested callback hell + 3 HTTP requests
    });
});

// GOOD — single round-trip, return all data
var ga = new GlideAjax('Util');
ga.addParam('sysparm_name', 'getAllData');
ga.addParam('sysparm_incident_id', g_form.getUniqueValue());
ga.getXMLAnswer(function(answer) {
    var data = JSON.parse(answer);
    g_form.setValue('field_a', data.a);
    g_form.setValue('field_b', data.b);
    g_form.setValue('field_c', data.c);
});
```

### Minimize Client Script onLoad Work
```javascript
// BAD — heavy work on every form load
function onLoad() {
    // Multiple GlideAjax calls
    // DOM manipulation
    // Complex calculations
}

// GOOD — use Display Business Rule + g_scratchpad
// Server-side (Display BR): pre-compute data
g_scratchpad.precomputedData = computeExpensiveData(current);

// Client-side (onLoad): just read cached data
function onLoad() {
    if (g_scratchpad.precomputedData) {
        g_form.setValue('field', g_scratchpad.precomputedData);
    }
}
```

## Business Rule Performance

### Use Async for Heavy Operations
```javascript
// BEFORE: synchronous — blocks user's save
// After BR: Sync to external system (2-3 second API call)

// AFTER: async — user's save returns immediately
// After BR (async): Sync to external system
// The async BR runs in background worker thread
```

### Minimize Queries in Before Rules
```javascript
// BAD — query in every save
(function executeRule(current, previous) {
    var gr = new GlideRecord('sys_user');
    gr.get(current.getValue('assigned_to'));
    var dept = gr.getValue('department');
    // ... complex logic
})(current, previous);

// GOOD — only run when relevant field changes
// Set Condition: assigned_to changes
(function executeRule(current, previous) {
    if (!current.assigned_to.changes()) return; // double-check
    // ... only runs when needed
})(current, previous);
```

### Avoid current.update() in Business Rules
```javascript
// BAD — causes recursion, double save
(function executeRule(current, previous) {
    current.setValue('description', 'updated');
    current.update(); // triggers all BRs again!
})(current, previous);

// GOOD — in Before rule, just set values (auto-saved)
(function executeRule(current, previous) {
    current.setValue('description', 'updated');
    // No update() needed — system saves automatically
})(current, previous);
```

## Cache Management

```javascript
// Flush specific cache
gs.cacheFlush('sys_properties'); // property cache
gs.cacheFlush('sys_cache_flush'); // general cache flush

// System Properties for caching
// glide.cache.max_size — max cache entries
// glide.db.pooler.connections — DB connection pool size
```

### Script Include Caching Pattern
```javascript
var CachedLookup = Class.create();
CachedLookup.prototype = {
    initialize: function() {
        this.CACHE_KEY = 'x_myapp.cached_config';
    },
    
    getConfig: function() {
        // Check cache first (using system property as simple cache)
        var cached = gs.getProperty(this.CACHE_KEY);
        if (cached) {
            var data = JSON.parse(cached);
            // Check TTL (5 minutes)
            if (new Date().getTime() - data.timestamp < 300000) {
                return data.value;
            }
        }
        
        // Cache miss — query and store
        var config = this._loadConfig();
        gs.setProperty(this.CACHE_KEY, JSON.stringify({
            value: config,
            timestamp: new Date().getTime()
        }));
        return config;
    },
    
    _loadConfig: function() {
        // expensive query here
        return {};
    },
    
    type: 'CachedLookup'
};
```

## Semaphores & Mutual Exclusion

```javascript
// Prevent concurrent execution of critical sections
var sem = new GlideSemaphore();
var lockName = 'my_integration_lock';

if (sem.acquire(lockName, 30)) { // 30 second timeout
    try {
        // Critical section — only one thread at a time
        processIntegration();
    } finally {
        sem.release(lockName);
    }
} else {
    gs.warn('Could not acquire lock: ' + lockName);
}
```

## Slow Query Analysis

```
Navigate: System Diagnostics > Slow Queries

Key metrics:
- Execution time > 1 second = investigate
- Full table scans = add index
- Missing indexes = sys_slow_query_log

// Enable slow query logging
System Property: glide.sql.debug = true (TEMP only!)
System Property: glide.slow_query_threshold = 1000 (ms)
```

## Database Views vs Joins

```javascript
// Database View — pre-joined virtual table (read-only, fast)
// Create via: System Definition > Database Views
// Good for: reporting, dashboards, repeated complex joins

// GlideRecord Join — runtime join (flexible but slower)
var gr = new GlideRecord('incident');
var join = gr.addJoinQuery('sys_user_grmember', 'assigned_to', 'user');
join.addCondition('group.name', 'Network');
gr.query();
// Use addJoinQuery sparingly — database views are faster for repeated patterns
```

## Performance Checklist

1. ✅ `setLimit()` on all queries
2. ✅ `GlideAggregate` for counts, not `getRowCount()`
3. ✅ Async GlideAjax (never `getXMLWait()`)
4. ✅ Async Business Rules for heavy operations
5. ✅ No `current.update()` in Before rules
6. ✅ Avoid N+1 queries — batch lookups
7. ✅ Use encoded queries for complex filters
8. ✅ Index frequently queried fields
9. ✅ Use Display BR + `g_scratchpad` over onLoad GlideAjax
10. ✅ Batch GlideAjax calls — single round-trip
11. ✅ No `eval()` anywhere
12. ✅ `setWorkflow(false)` for bulk data operations
