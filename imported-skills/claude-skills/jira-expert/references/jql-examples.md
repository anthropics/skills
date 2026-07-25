# JQL Query Examples

## Sprint Queries

**Current sprint issues:**
```jql
sprint IN openSprints() ORDER BY rank
```

**Issues in specific sprint:**
```jql
sprint = "Sprint 23" ORDER BY priority DESC
```

**All sprint work (current and backlog):**
```jql
project = ABC AND issuetype IN (Story, Bug, Task) 
ORDER BY sprint DESC, rank
```

**Unscheduled stories:**
```jql
project = ABC AND issuetype = Story AND sprint IS EMPTY 
AND status != Done ORDER BY priority DESC
```

**Spillover from last sprint:**
```jql
sprint IN closedSprints() AND sprint NOT IN (latestReleasedVersion()) 
AND status != Done ORDER BY created DESC
```

**Sprint completion rate:**
```jql
sprint = "Sprint 23" AND status = Done
```

## User & Team Queries

**My open issues:**
```jql
assignee = currentUser() AND status != Done 
ORDER BY priority DESC, created ASC
```

**Unassigned in my project:**
```jql
project = ABC AND assignee IS EMPTY AND status != Done
ORDER BY priority DESC
```

**Issues I'm watching:**
```jql
watcher = currentUser() AND status != Done
```

**Team workload:**
```jql
assignee IN membersOf("engineering-team") AND status IN ("In Progress", "In Review")
ORDER BY assignee, priority DESC
```

**Issues I reported that are still open:**
```jql
reporter = currentUser() AND status != Done ORDER BY created DESC
```

**Issues commented on by me:**
```jql
comment ~ currentUser() AND status != Done
```

## Date Range Queries

**Created today:**
```jql
created >= startOfDay() ORDER BY created DESC
```

**Updated in last 7 days:**
```jql
updated >= -7d ORDER BY updated DESC
```

**Created this week:**
```jql
created >= startOfWeek() AND created <= endOfWeek()
```

**Created this month:**
```jql
created >= startOfMonth() AND created <= endOfMonth()
```

**Not updated in 30 days:**
```jql
status != Done AND updated <= -30d ORDER BY updated ASC
```

**Resolved yesterday:**
```jql
resolved >= startOfDay(-1d) AND resolved < startOfDay()
```

**Due this week:**
```jql
duedate >= startOfWeek() AND duedate <= endOfWeek() AND status != Done
```

**Overdue:**
```jql
duedate < now() AND status != Done ORDER BY duedate ASC
```

## Status & Workflow Queries

**In Progress issues:**
```jql
project = ABC AND status = "In Progress" ORDER BY assignee
```

**Blocked issues:**
```jql
project = ABC AND labels = blocked AND status != Done
```

**Issues in review:**
```jql
project = ABC AND status IN ("Code Review", "QA Review", "Pending Approval")
ORDER BY updated ASC
```

**Ready for development:**
```jql
project = ABC AND status = "Ready" AND sprint IS EMPTY
ORDER BY priority DESC
```

**Recently done:**
```jql
project = ABC AND status = Done AND resolved >= -7d
ORDER BY resolved DESC
```

**Status changed today:**
```jql
status CHANGED AFTER startOfDay() ORDER BY updated DESC
```

**Long-running in progress:**
```jql
status = "In Progress" AND status CHANGED BEFORE -14d
ORDER BY status CHANGED ASC
```

## Priority & Type Queries

**High priority bugs:**
```jql
issuetype = Bug AND priority IN (Highest, High) AND status != Done
ORDER BY priority DESC, created ASC
```

**Critical blockers:**
```jql
priority = Highest AND status != Done ORDER BY created ASC
```

**All epics:**
```jql
issuetype = Epic ORDER BY status, priority DESC
```

**Stories without acceptance criteria:**
```jql
issuetype = Story AND "Acceptance Criteria" IS EMPTY AND status = Backlog
```

**Technical debt:**
```jql
labels = tech-debt AND status != Done ORDER BY priority DESC
```

## Complex Multi-Condition Queries

**My team's sprint work:**
```jql
sprint IN openSprints() 
AND assignee IN membersOf("engineering-team") 
AND status != Done
ORDER BY assignee, priority DESC
```

**Bugs created this month, not in sprint:**
```jql
issuetype = Bug 
AND created >= startOfMonth() 
AND sprint IS EMPTY 
AND status != Done
ORDER BY priority DESC, created DESC
```

**High-priority work needing attention:**
```jql
project = ABC 
AND priority IN (Highest, High) 
AND status IN ("In Progress", "In Review") 
AND updated <= -3d
ORDER BY priority DESC, updated ASC
```

**Stale issues:**
```jql
project = ABC 
AND status NOT IN (Done, Cancelled) 
AND (assignee IS EMPTY OR updated <= -30d)
ORDER BY created ASC
```

**Epic progress:**
```jql
"Epic Link" = ABC-123 ORDER BY status, rank
```

## Component & Version Queries

**Issues in component:**
```jql
project = ABC AND component = "Frontend" AND status != Done
```

**Issues without component:**
```jql
project = ABC AND component IS EMPTY AND status != Done
```

**Target version:**
```jql
fixVersion = "v2.0" ORDER BY status, priority DESC
```

**Released versions:**
```jql
fixVersion IN releasedVersions() ORDER BY fixVersion DESC
```

## Label & Text Search Queries

**Issues with label:**
```jql
labels = urgent AND status != Done
```

**Multiple labels (AND):**
```jql
labels IN (frontend, bug) AND status != Done
```

**Search in summary:**
```jql
summary ~ "authentication" ORDER BY created DESC
```

**Search in summary and description:**
```jql
text ~ "API integration" ORDER BY created DESC
```

**Issues with empty description:**
```jql
description IS EMPTY AND issuetype = Story
```

## Performance-Optimized Queries

**Good - Specific project first:**
```jql
project = ABC AND status = "In Progress" AND assignee = currentUser()
```

**Bad - User filter first:**
```jql
assignee = currentUser() AND status = "In Progress" AND project = ABC
```

**Good - Use functions:**
```jql
sprint IN openSprints() AND status != Done
```

**Bad - Hardcoded sprint:**
```jql
sprint = "Sprint 23" AND status != Done
```

**Good - Specific date:**
```jql
created >= 2026-01-01 AND created <= 2026-01-31
```

**Bad - Relative with high cost:**
```jql
created >= -365d AND created <= -335d
```

## Reporting Queries

**Velocity calculation:**
```jql
sprint = "Sprint 23" AND status = Done
```
*Then sum story points*

**Bug rate:**
```jql
project = ABC AND issuetype = Bug AND created >= startOfMonth()
```

**Average cycle time:**
```jql
project = ABC AND resolved >= startOfMonth() 
AND resolved <= endOfMonth()
```
*Calculate time from In Progress to Done*

**Stories delivered this quarter:**
```jql
project = ABC AND issuetype = Story 
AND resolved >= startOfYear() AND resolved <= endOfQuarter()
```

**Team capacity:**
```jql
assignee IN membersOf("engineering-team") 
AND sprint IN openSprints()
```
*Sum original estimates*

## Notification & Watching Queries

**Issues I need to review:**
```jql
status = "Pending Review" AND assignee = currentUser()
```

**Issues assigned to me, high priority:**
```jql
assignee = currentUser() AND priority IN (Highest, High) 
AND status != Done
```

**Issues created by me, not resolved:**
```jql
reporter = currentUser() AND status != Done 
ORDER BY created DESC
```

## Advanced Functions

**Issues changed from status:**
```jql
status WAS "In Progress" AND status = "Done" 
AND status CHANGED AFTER startOfWeek()
```

**Assignee changed:**
```jql
assignee CHANGED BY currentUser() AFTER -7d
```

**Issues re-opened:**
```jql
status WAS Done AND status != Done ORDER BY updated DESC
```

**Linked issues:**
```jql
issue IN linkedIssues("ABC-123") ORDER BY issuetype
```

**Parent epic:**
```jql
parent = ABC-123 ORDER BY rank
```

## Saved Filter Examples

**Daily Standup Filter:**
```jql
assignee = currentUser() AND sprint IN openSprints() 
AND status != Done ORDER BY priority DESC
```

**Team Sprint Board Filter:**
```jql
project = ABC AND sprint IN openSprints() ORDER BY rank
```

**Bugs Dashboard Filter:**
```jql
project = ABC AND issuetype = Bug AND status != Done
ORDER BY priority DESC, created ASC
```

**Tech Debt Backlog:**
```jql
project = ABC AND labels = tech-debt AND status = Backlog
ORDER BY priority DESC
```

**Needs Triage:**
```jql
project = ABC AND status = "To Triage" 
AND created >= -7d ORDER BY created ASC
```
