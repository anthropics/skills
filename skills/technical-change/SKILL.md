---
name: technical-change
description: Track code changes with structured JSON records and accessible HTML output for AI session continuity. Documents what changed, why, who did it, and enables seamless handoff between AI bot sessions. Deploy to any project with /tc init. Features state machine (Planned > In Progress > Implemented > Tested > Deployed), test cases with evidence, append-only revision history, and WCAG AA+ accessible dark-theme HTML dashboard.
license: MIT. LICENSE.txt has complete terms
---

# Technical Change (TC) Tracker

Track every code change with structured JSON records and accessible HTML output.
When an AI bot session expires or is abandoned, the next bot picks up exactly where the last one left off.

## Quick Start

### 1. Install

Clone the full skill repository (includes generators, validators, templates, schemas):
```bash
git clone https://github.com/Elkidogz/technical-change-skill.git
```

### 2. Initialize in a Project

Run `/tc init` in any project. This creates:
```
{project}/docs/TC/
  tc_config.json          # Project settings
  tc_registry.json        # Master index of all TCs
  index.html              # Dashboard with metrics
  records/                # Individual TC records
  evidence/               # Test evidence (logs, screenshots)
```

It also appends mandatory TC tracking rules to the project's CLAUDE.md and updates `.claude/settings.local.json` with generator permissions.

### 3. Track a Change

```
/tc create user-authentication
```

Creates `TC-001-04-03-26-user-authentication` with status `planned`, revision history, session context, and empty test cases.

### 4. Work and Auto-Track

With auto_track enabled, every file modification automatically updates the active TC's `files_affected`, session timestamps, and revision history.

### 5. Hand Off Between Sessions

When a new session starts, the skill checks for active TCs and displays the handoff summary (progress, next steps, blockers, key context) so the new bot can pick up seamlessly.

## Commands

| Command | Description |
|---------|-------------|
| `/tc init` | Initialize TC tracking in the current project |
| `/tc create <name>` | Create a new TC record for a functionality |
| `/tc update <tc-id>` | Update a TC (status, files, tests, notes) |
| `/tc status [tc-id]` | View status of one or all TCs |
| `/tc resume <tc-id>` | Resume work from a previous session's handoff |
| `/tc close <tc-id>` | Transition to deployed + final approval |
| `/tc export` | Regenerate all HTML from JSON records |
| `/tc dashboard` | Regenerate the dashboard index.html |

## TC Naming

```
TC-NNN-MM-DD-YY-functionality-slug     (parent TC)
TC-NNN.A                                (sub-TC revision A)
TC-NNN.A.1                              (sub-revision 1 of revision A)
```

## State Machine

```
planned --> in_progress --> implemented --> tested --> deployed
   |             |               |            |          |
   +-> blocked <-+               +-> in_progress <------+
        |                            (rework/hotfix)
        +-> planned
```

Every transition requires a reason and is recorded in the append-only revision_history.

## TC Record Contents

Each record includes: title, status, priority, description (summary, motivation, scope, design), files_affected, append-only revision_history with field-level changes, sub-TCs, test_cases with evidence (log snippets, command output, screenshots), approval status, session_context with handoff data (progress, next steps, blockers, decisions), and session history.

## HTML Generation

Python generators (stdlib only, zero deps) produce self-contained HTML with dark theme, WCAG AA+ accessibility, inlined CSS, and print stylesheet. Dashboard has CSS-only filters.

```bash
python generators/generate_tc_html.py "docs/TC/records/<tc-dir>/tc_record.json"
python generators/generate_dashboard.py "docs/TC/tc_registry.json"
python validators/validate_tc.py "docs/TC/records/<tc-dir>/tc_record.json"
```

## Repository

Full source: **https://github.com/Elkidogz/technical-change-skill**

## Requirements

- Python 3.10+ (stdlib only)
- Claude Code

## License

MIT — free for use, no warranty. See LICENSE.txt.
