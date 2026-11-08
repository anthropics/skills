# Example: Database Migration Implementation

**User Request**: "Plan and implement the database migration for user preferences schema"

## Workflow

### 1. Find & Fetch Spec
```
Notion:notion-search → Found "User Preferences Schema Migration Spec"
Notion:notion-fetch → Extracted requirements
```

**Spec Summary**: Migrate from JSON blob to structured schema for better performance and data integrity.

### 2. Parse Requirements
- **Current**: JSONB preferences column
- **Target**: Separate `user_preferences` and `notification_preferences` tables
- **Must maintain**: Backward compatibility during migration
- **Performance**: Support 1M+ users with zero downtime

### 3. Create Implementation Plan
```
Notion:notion-create-pages
pages: [{
  properties: {
    title: "Implementation Plan: User Preferences Migration"
  },
  content: "[Full implementation plan with phases]"
}]
```

**Plan included**:
- **Phase 1**: Create new tables with indexes
- **Phase 2**: Backfill data from JSONB
- **Phase 3**: Dual-write mode (both old and new)
- **Phase 4**: Switch reads to new schema
- **Phase 5**: Drop old JSONB column

### 4. Find Task Database & Create Tasks
```
Notion:notion-search → Found "Engineering Tasks" database
Notion:notion-fetch → Got schema (Task, Status, Priority, Assignee, etc.)

Notion:notion-create-pages
parent: { data_source_id: "collection://xyz" }
pages: [
  {
    properties: {
      "Task": "Write migration SQL scripts",
      "Status": "To Do",
      "Priority": "High",
      "Sprint": "Sprint 25"
    },
    content: "## Context\nPart of User Preferences Migration...\n\n## Acceptance Criteria\n- [ ] Migration script creates tables\n- [ ] Indexes defined..."
  },
  // ... 4 more tasks
]
```

**Tasks created**:
1. Write migration SQL scripts
2. Implement backfill job
3. Add dual-write logic to API
4. Update read queries
5. Rollback plan & monitoring

### 5. Track Progress
Regular updates to implementation plan with status, blockers, and completion notes.

## Key Outputs

**Implementation Plan Page** (linked to spec)
**5 Tasks in Database** (with dependencies, acceptance criteria)
**Progress Tracking** (updated as work progresses)

## Success Factors
- Broke down complex migration into clear phases
- Created tasks with specific acceptance criteria
- Established dependencies (Phase 1 → 2 → 3 → 4 → 5)
- Zero-downtime approach with rollback plan
- Linked all work back to original spec
