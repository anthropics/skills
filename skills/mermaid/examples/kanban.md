## Instructions

Kanban diagrams visualize workflow using a board with columns representing different stages of work.

### Syntax

- Use `kanban` keyword
- Columns: `section ColumnName`
- Cards: `Card Title :crit, done, active`
- Status:
  - `done` - Completed
  - `active` - In progress
  - `crit` - Critical
- Cards can be moved between columns

### Example

```mermaid
kanban
    title Project Board
    section To Do
        Task 1
        Task 2
    section In Progress
        Task 3 :active
        Task 4 :crit
    section Done
        Task 5 :done
        Task 6 :done
```
