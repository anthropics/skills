# Pipeline Status Dashboard Template

This template defines the output format for the Progress Dashboard. Switch between language versions based on user language.

---

## English Version

```
+=========================================+
|   Academic Pipeline Status              |
+=========================================+
| Topic: {topic}                          |
+-----------------------------------------+

  Stage 1 RESEARCH    [{status_icon}] {status_text}
    {mode_line}
    {outputs_line}

  Stage 2 WRITE       [{status_icon}] {status_text}
    {mode_line}
    {outputs_line}

  Stage 3 REVIEW      [{status_icon}] {status_text}
    {mode_line}
    {decision_line}

  Stage 4 REVISE      [{status_icon}] {status_text}
    {revision_round_line}
    {addressed_line}

  Stage 3' RE-REVIEW  [{status_icon}] {status_text}
    {loop_count_line}

  Stage 5 FINALIZE    [{status_icon}] {status_text}
    {format_line}

+-----------------------------------------+
| Materials:                              |
|   [{icon}] RQ Brief                     |
|   [{icon}] Methodology Blueprint        |
|   [{icon}] Bibliography                 |
|   [{icon}] Synthesis Report             |
|   [{icon}] Paper Draft                  |
|   [{icon}] Review Reports               |
|   [{icon}] Revision Roadmap             |
|   [{icon}] Revised Draft                |
|   [{icon}] Response to Reviewers        |
|   [{icon}] Final Paper                  |
+-----------------------------------------+
| Revision History:                       |
|   {revision_history}                    |
+-----------------------------------------+
| Next Step: {next_step_suggestion}       |
+=========================================+
```

---

## Field Definitions

### status_icon

| Status | Icon |
|--------|------|
| completed | `v` |
| in_progress | `..` |
| pending | ` ` (space) |
| skipped | `--` |

### status_text

| Status | Text |
|--------|------|
| completed | Completed |
| in_progress | In Progress |
| pending | Pending |
| skipped | Skipped |

### mode_line

Format: `Mode: {mode_name}`
- Only displayed when status is completed or in_progress
- If mode switched (e.g., plan -> full), display the full path

### outputs_line

Format: `Outputs: {output_1}, {output_2}, ...`
- Only displayed when status is completed
- List all deliverables for that stage

### decision_line

Format: `Decision: {Accept/Minor Revision/Major Revision/Reject}`
- Only displayed when Stage 3 or Stage 3' is completed

### revision_round_line

Format: `Revision Round: {current}/{max}`
- Only displayed when Stage 4 is in_progress

### addressed_line

Format: `Addressed: {count}/{total} required revisions`
- Only displayed when Stage 4 is in_progress

### loop_count_line

Format: `Loop: {count}/2`
- Only displayed for Stage 3'

### material icon

| Status | Icon |
|--------|------|
| available | `v` |
| missing | ` ` (space) |

### revision_history

One line per round:
```
Round {n}: {decision} | {addressed}/{total} items addressed
  Pending: {pending_items_summary}
```

If no revision history, display "(No revision history yet)".

### next_step_suggestion

Auto-generated suggestion based on current state:
- Stage 1 completed: "Recommend proceeding to Stage 2 (WRITE) using {recommended_mode} mode"
- Stage 3 completed (Major): "Need to enter Stage 4 (REVISE), {N} required items"
- Stage 4 completed: "Recommend proceeding to Stage 3' (RE-REVIEW) to confirm revision quality"
- Stage 3' completed (Accept): "Congratulations! Proceed to Stage 5 (FINALIZE) to produce final version"
- Pipeline completed: "Pipeline complete! Final paper is ready."

---

## Simplified Version (Auto-appended after stage completion)

One-line progress bar:

```
Pipeline: [v]RESEARCH -> [v]WRITE -> [..]REVIEW -> [ ]REVISE -> [ ]FINALIZE
```
