---
name: tc
description: |
  Technical Change tracking skill. Use when user says /tc, /tc init, /tc create, /tc update, /tc status, /tc resume, /tc close, /tc export, /tc dashboard, or /tc retro. Also auto-runs at session start to check for TC initialization and active TCs. Tracks code changes with structured JSON records and accessible HTML output for AI session continuity.
user-invocable: true
tools: Read, Write, Edit, Glob, Grep, Bash
---

# /tc — Technical Change Tracker

Track every code change with structured JSON records and accessible HTML output.
Ensures AI bot sessions can resume seamlessly when previous sessions expire or are abandoned.
Designed for deployment across multiple projects.

## First-Use Detection (MANDATORY — Every Session)

At the start of EVERY session, before doing any work:

1. Check if `docs/TC/tc_config.json` exists in the current working directory
2. **If it EXISTS**: follow the Session Start Protocol in the `/tc resume` section
3. **If it does NOT exist**: prompt the user:
   > TC tracking is not initialized in this project. Would you like to set it up?
   > This enables structured change tracking, AI session handoff, and HTML documentation.
   > Run `/tc init` to get started.
4. Wait for the user's response. If they agree, run `/tc init`.
5. If the user declines, continue without TC tracking for this session.

A global skill is installed at `~/.claude/skills/tc.md` to ensure this check runs
in every project, even those that haven't been initialized yet.

## Overview

Each Technical Change (TC) is a structured record that documents:
- **What** changed (files, code, configuration)
- **Why** it changed (motivation, scope, design decisions)
- **Who** changed it (human or AI bot session)
- **When** it changed (revision history with timestamps)
- **How it was tested** (test cases with evidence from logs)
- **Where work stands** (session handoff data for bot continuity)

### Storage Location
Each project stores TCs at `{project_root}/docs/TC/`:
```
docs/TC/
├── tc_config.json          # Project settings
├── tc_registry.json        # Master index
├── index.html              # Dashboard
├── records/
│   └── TC-001-MM-DD-YY-name/
│       ├── tc_record.json  # System of record
│       └── tc_record.html  # Human-readable
└── evidence/
    └── TC-001/             # Log snippets, screenshots
```

### TC Naming Convention
- **Parent TC**: `TC-NNN-MM-DD-YY-functionality-slug` (e.g., `TC-001-04-03-26-user-authentication`)
- **Sub-TC**: `TC-NNN.A` or `TC-NNN.A.1` (letter = revision, number = sub-revision)
- NNN = sequential number, MM-DD-YY = creation date, slug = kebab-case functionality name

### Implementation States
```
planned → in_progress → implemented → tested → deployed
   │           │              │           │         │
   └→ blocked ←┘              └→ in_progress ←──────┘
        │                        (rework/hotfix)
        └→ planned
```

---

## Commands

### /tc init
Initialize TC tracking in the current project. Run this once per project.

**Steps:**
1. Check if `docs/TC/tc_config.json` exists. If yes, report "Already initialized" with current stats and stop.
2. Detect project name: try CLAUDE.md first heading, then package.json name, then pyproject.toml name, then directory basename. Confirm with user.
3. Create directories: `docs/TC/`, `docs/TC/records/`, `docs/TC/evidence/`
4. Create `tc_config.json`:
   ```json
   {
     "project_name": "<detected>",
     "tc_root": "docs/TC",
     "created": "<ISO 8601 now>",
     "skills_library_path": "<absolute path to skills_library/TC>",
     "auto_track": true,
     "auto_regenerate_html": true,
     "auto_regenerate_dashboard": true,
     "default_author": "Claude",
     "categories": ["feature","bugfix","refactor","infrastructure","documentation","hotfix","enhancement"]
   }
   ```
5. Create `tc_registry.json`:
   ```json
   {
     "project_name": "<name>",
     "created": "<ISO 8601>",
     "updated": "<ISO 8601>",
     "next_tc_number": 1,
     "records": [],
     "statistics": {
       "total": 0,
       "by_status": {"planned":0,"in_progress":0,"blocked":0,"implemented":0,"tested":0,"deployed":0},
       "by_scope": {"feature":0,"bugfix":0,"refactor":0,"infrastructure":0,"documentation":0,"hotfix":0,"enhancement":0},
       "by_priority": {"critical":0,"high":0,"medium":0,"low":0}
     }
   }
   ```
6. Generate empty dashboard: run `python "<skills_path>/generators/generate_dashboard.py" "docs/TC/tc_registry.json"`
7. Update CLAUDE.md: read existing file (or create new). Check for marker `## Technical Change (TC) Tracking (MANDATORY)`. If not found, append the contents of `init/claude_md_snippet.md` with `{skills_library_path}` replaced with the actual absolute path.
8. Update `.claude/settings.local.json`: read existing file (or create `{"permissions":{"allow":[]}}`). Merge TC permissions from `init/settings_template.json` (with paths substituted). Deduplicate. Write back.
9. Report all created/updated files. Suggest `/tc create` as next step.

### /tc create <functionality-name>
Create a new TC record.

**Steps:**
1. Read `docs/TC/tc_registry.json`
2. Generate TC ID: `TC-{next_tc_number:03d}-{MM-DD-YY}-{slugify(name)}`
3. Ask user for:
   - Title (default: formatted version of the slug)
   - Scope: feature, bugfix, refactor, infrastructure, documentation, hotfix, enhancement
   - Priority: critical, high, medium, low (default: medium)
   - Summary (at least 10 characters)
   - Motivation (why is this change needed?)
4. Create directory: `docs/TC/records/TC-NNN-MM-DD-YY-slug/`
5. Create `tc_record.json` with all fields initialized:
   - status = "planned"
   - revision_history = [R1 creation event]
   - session_context.current_session populated with this session's info
   - All arrays initialized to []
   - approval.approved = false, test_coverage_status = "none"
6. Add entry to tc_registry.json records array. Increment next_tc_number. Recompute statistics.
7. Generate HTML: run the tc_record HTML generator
8. Regenerate dashboard: run the dashboard generator
9. Report: display TC ID, link to HTML, suggest next steps

### /tc update <tc-id>
Update an existing TC record. This is the general-purpose update command.

**Steps:**
1. Read the TC record from `docs/TC/records/<tc-dir>/tc_record.json`
2. Determine what to update (user may specify, or you determine from context):
   - **Status change**: validate transition with state machine. Ask for reason.
   - **Add files**: append to files_affected array
   - **Add test case**: create new test entry with sequential ID (T1, T2...)
   - **Update test result**: set actual_result, status, evidence, tested_by, tested_date
   - **Add evidence**: append to a test case's evidence array
   - **Update handoff**: update session_context.handoff fields
   - **Add notes**: append to notes field
   - **Add sub-TC**: append to sub_tcs array
3. For EVERY change:
   - Append a new revision entry to revision_history (sequential R-id, timestamp, author, summary, field_changes with old/new values and reason)
   - Update the `updated` timestamp
   - Update `metadata.last_modified` and `metadata.last_modified_by`
   - Update `session_context.current_session.last_active`
4. Write tc_record.json (atomic: write to .tmp, then rename)
5. Update tc_registry.json (sync status, scope, priority, updated, test_summary). Recompute statistics.
6. If auto_regenerate_html: regenerate TC HTML
7. If status changed and auto_regenerate_dashboard: regenerate dashboard

### /tc status [tc-id]
View TC status.

**Without tc-id**: Read tc_registry.json and display a summary table of all TCs:
- TC ID, Title, Status (with badge), Scope, Priority, Tests (pass/total), Last Updated

**With tc-id**: Read the specific TC record and display:
- Full status including handoff data, test results, revision count, files affected
- Any validation errors

### /tc resume <tc-id>
Resume work on a TC from a previous session.

**Steps:**
1. Read the TC record
2. Display the handoff section prominently:
   - Progress summary
   - Next steps (numbered)
   - Blockers (highlighted)
   - Key context
   - Files in progress with their states
   - Recent decisions
3. Archive the current session to session_history:
   - Move current_session data to a new entry in session_history
   - Set ended = now
4. Create new current_session with this session's info
5. Append revision entry: "Session resumed by [platform/model]"
6. Write tc_record.json
7. Prompt: "Ready to continue. Here are the next steps: [list from handoff]"

### /tc close <tc-id>
Close a TC by transitioning it to deployed.

**Steps:**
1. Read the TC record
2. Validate current status allows transition to `deployed`
3. Check all test cases — warn if any are pending/fail/blocked
4. Ask for:
   - Approval: who is approving? (user name or "self")
   - Approval notes (optional)
   - Final test coverage assessment (none/partial/full)
5. Update:
   - status = "deployed"
   - approval.approved = true
   - approval.approved_by, approved_date, approval_notes, test_coverage_status
   - Append final revision entry
   - Archive session to session_history
6. Write tc_record.json and update registry
7. Regenerate HTML and dashboard
8. Report: "TC-NNN closed and deployed."

### /tc export
Regenerate ALL HTML files from their JSON records.

**Steps:**
1. Read tc_registry.json
2. For each record: run the TC HTML generator on its tc_record.json
3. Run the dashboard generator
4. Report: "Regenerated X TC pages and dashboard."

### /tc dashboard
Regenerate just the dashboard index.html.

**Steps:**
1. Run the dashboard generator on tc_registry.json
2. Report path to generated index.html

### /tc retro <retro_changelog.json>
Retroactively create TC records in bulk from a structured changelog file.
Use this when onboarding an existing project with extensive undocumented history.

**Steps:**
1. Read the retro_changelog.json file (must match `schemas/tc_retro_changelog.schema.json`)
2. Validate the changelog structure
3. Run the batch generator:
   ```bash
   python "{skills_library_path}/generators/generate_retro_tcs.py" "<retro_changelog.json>" "docs/TC"
   ```
4. The generator will:
   - Create a TC record for each entry (TC-001 through TC-NNN)
   - Validate every record against the schema
   - Generate HTML for every record
   - Update the registry with all entries
   - Regenerate the dashboard
5. Report: total created, any errors, link to dashboard

**Retro Changelog Format** (`retro_changelog.json`):
```json
{
  "project": "Project Name",
  "default_author": "retroactive",
  "changes": [
    {
      "title": "Feature or Change Title",
      "scope": "feature|bugfix|refactor|infrastructure|documentation|hotfix|enhancement",
      "priority": "critical|high|medium|low",
      "status": "deployed",
      "date": "YYYY-MM-DD",
      "description": "What changed and why (10+ chars)",
      "motivation": "Why this change was needed (optional)",
      "files": ["path/to/file.py", "path/to/other.py"],
      "tags": ["tag1", "tag2"],
      "version": "v1.0.0"
    }
  ]
}
```

**Building the changelog**: Claude should analyze the project's git history, docs, changelogs,
README, and code to build the retro_changelog.json. Group related changes into single TCs.
Each TC should represent one logical unit of work (a feature, a fix, a refactor).

---

## Auto-Detection Rules — Non-Blocking Subagent Pattern

TC tracking MUST NOT interrupt the main workflow. Use background subagents for all bookkeeping.

### During Work
- **NEVER stop to update TC records inline.** Focus entirely on the task.
- Do not read/write TC files between code changes.
- The main agent's job is to code, not to do paperwork.

### At Natural Milestones
When a logical unit of work is complete (feature done, test passing, stopping point):
- Spawn a **background Agent** (run_in_background=true) with this prompt:
  "Read docs/TC/tc_registry.json. Find the in_progress TC. Read its tc_record.json. Update files_affected with [list files changed]. Append a revision entry summarizing what was done. Update session_context.current_session.last_active. Write the updated record. Regenerate the TC HTML and dashboard."
- The main agent continues working without waiting.

### Only Surface Questions When Genuinely Needed
- "This work doesn't match any active TC — should I create one?" (ask once per session, not per file)
- "TC-NNN looks complete — transition to implemented?" (at milestones only, don't nag)
- Never interrupt the user for routine TC bookkeeping.

### At Session End
Before the session closes, spawn a final background Agent to write the handoff summary:
- progress_summary: what was accomplished
- next_steps: what still needs doing
- blockers: anything preventing progress
- key_context: important decisions, gotchas, patterns the next bot needs
- files_in_progress: which files are mid-edit

### On Session Start
1. Check if `docs/TC/` exists in the project
2. If yes: read tc_registry.json, find in_progress/blocked TCs
3. Display handoff summary for any active TCs
4. Ask user if they want to resume

---

## Validation Rules (Always Enforced)

1. **State machine**: only valid transitions allowed (see diagram above)
2. **Sequential IDs**: revision_history uses R1,R2,R3...; test_cases uses T1,T2,T3...
3. **Append-only history**: revision_history entries are never modified or deleted
4. **Approval consistency**: approved=true requires approved_by and approved_date
5. **TC ID format**: must match `TC-NNN-MM-DD-YY-slug` pattern
6. **Sub-TC ID format**: must match `TC-NNN.A` or `TC-NNN.A.N` pattern
7. **HTML escaping**: all user data is escaped before HTML rendering
8. **Atomic writes**: JSON files written to .tmp then renamed
9. **Registry stats**: recomputed on every registry write

---

## Python Generators

Located at `{skills_library_path}/generators/`:

```bash
# Generate individual TC HTML
python "generators/generate_tc_html.py" "<path_to_tc_record.json>" [--output <path>]

# Generate dashboard
python "generators/generate_dashboard.py" "<path_to_tc_registry.json>" [--output <path>]

# Validate a TC record
python "validators/validate_tc.py" "<path_to_tc_record.json>"

# Validate the registry
python "validators/validate_tc.py" --registry "<path_to_tc_registry.json>"

# Retroactive batch creation
python "generators/generate_retro_tcs.py" "<retro_changelog.json>" "<docs/TC/>"
```

All generators use Python stdlib only — no external dependencies.
All generators validate their input before producing output.
All HTML output is self-contained with inlined CSS (works from file:// URLs).
All HTML output is WCAG AA+ accessible with rem-based fonts, high contrast dark theme, skip links, and aria labels.
