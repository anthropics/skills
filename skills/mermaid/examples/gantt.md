## Instructions

Gantt charts display project schedules, showing tasks, their durations, and dependencies over time.

### Syntax

- Use `gantt` keyword
- Title: `title Project Title`
- Date format: `dateFormat YYYY-MM-DD`
- Sections: `section Section Name`
- Tasks: `Task Name :crit, milestone, done, active, task_id, start_date, end_date`
- Status:
  - `done` - Completed
  - `active` - In progress
  - `crit` - Critical path
  - `milestone` - Milestone marker
- Dependencies: `after task_id, duration`

### Example

```mermaid
gantt
    title Project Timeline
    dateFormat YYYY-MM-DD
    section Phase 1
    Design :done, des1, 2024-01-01, 2024-01-15
    Development :active, dev1, 2024-01-16, 2024-02-15
    section Phase 2
    Testing :test1, after dev1, 10d
    Deployment :milestone, deploy1, after test1, 1d
```
