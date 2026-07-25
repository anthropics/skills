---
name: "google-workspace-cli"
description: "Google Workspace administration via the gws CLI (github.com/googleworkspace/cli). Install, authenticate, and automate Gmail, Drive, Sheets, Calendar, Docs, Chat, and Tasks. Run security audits and use local recipe templates and persona bundles. Use for Google Workspace admin, gws CLI setup, Gmail automation, Drive management, or Calendar scheduling."
---

# Google Workspace CLI

Expert guidance and automation for Google Workspace administration using the open-source `gws` CLI ([github.com/googleworkspace/cli](https://github.com/googleworkspace/cli), Apache-2.0). The CLI builds its command surface dynamically from Google's Discovery Service, so it covers every supported Workspace API plus `+`-prefixed helper commands. This skill adds local Python tools (doctor, auth guide, recipe catalog, security audit, output analyzer).

> **Verify before scripting:** `gws` generates commands at runtime from Google's API discovery documents, and the CLI is pre-v1.0. Always confirm a command's exact surface with `gws --help`, `gws <service> --help`, or `gws schema <service>.<resource>.<method>` before putting it in automation. Commands in this skill marked *(verify)* are illustrative of the `gws <service> <resource> <method>` pattern and must be checked against your installed version.

---

## Quick Start

### Check Installation

```bash
# Verify gws is installed and authenticated
python3 scripts/gws_doctor.py
```

### Send an Email

```bash
gws gmail +send --to "team@company.com" \
  --subject "Weekly Update" --body "Here's this week's summary..."
```

### List Drive Files

```bash
gws drive files list --params '{"pageSize": 20}' | python3 scripts/output_analyzer.py --select "name,mimeType,modifiedTime" --format table
```

---

## Installation

### npm (recommended; requires Node.js 18+)

```bash
npm install -g @googleworkspace/cli
gws --version
```

### Homebrew (macOS/Linux)

```bash
brew install googleworkspace-cli
```

### Cargo (from source)

```bash
cargo install --git https://github.com/googleworkspace/cli --locked
gws --version
```

### Pre-built Binaries

Download from [github.com/googleworkspace/cli/releases](https://github.com/googleworkspace/cli/releases) for macOS, Linux, or Windows. Nix users: `nix run github:googleworkspace/cli`.

### Verify Installation

```bash
python3 scripts/gws_doctor.py
# Checks: PATH, version, auth status, service connectivity
```

---

## Authentication

### OAuth Setup (Interactive)

```bash
# Step 1: Create Google Cloud project and OAuth credentials
python3 scripts/auth_setup_guide.py --guide oauth

# Step 2: Run interactive auth setup (uses gcloud if available)
gws auth setup

# Step 3: Log in, requesting only the scopes you need
gws auth login -s drive,gmail,sheets
```

### Headless/CI

```bash
# Generate setup instructions
python3 scripts/auth_setup_guide.py --guide service-account

# Export credentials from an interactive machine, then point the CLI at them
gws auth export --unmasked > credentials.json
export GOOGLE_WORKSPACE_CLI_CREDENTIALS_FILE=/path/to/credentials.json
```

### Environment Variables

```bash
# Generate .env template
python3 scripts/auth_setup_guide.py --generate-env
```

| Variable | Purpose |
|----------|---------|
| `GOOGLE_WORKSPACE_CLI_CLIENT_ID` | OAuth client ID |
| `GOOGLE_WORKSPACE_CLI_CLIENT_SECRET` | OAuth client secret |
| `GOOGLE_WORKSPACE_CLI_CREDENTIALS_FILE` | Path to exported credentials JSON |
| `GOOGLE_WORKSPACE_CLI_TOKEN` | Pre-obtained OAuth token |
| `GOOGLE_WORKSPACE_CLI_CONFIG_DIR` | Override default config location |
| `GOOGLE_WORKSPACE_CLI_LOG` | Enable debug logging |

### Validate Authentication

```bash
python3 scripts/auth_setup_guide.py --validate --json
# Tests each service endpoint
```

---

## Workflow 1: Gmail Automation

**Goal:** Automate email operations — send, search, label, and filter management.

### Send, Reply, Forward (helper commands)

```bash
# Send a new email
gws gmail +send --to "client@example.com" \
  --subject "Proposal" --body "Please find attached..."

# Reply to a message (auto-threading); check exact flags with: gws gmail +reply --help
gws gmail +reply ...

# Forward a message; check exact flags with: gws gmail +forward --help
gws gmail +forward ...

# Unread inbox summary
gws gmail +triage
```

### Search and Inspect (discovery commands)

Discovery commands follow `gws <service> <resource> <method>` and take request
parameters as JSON via `--params` (query/path params) and `--json` (request body).
Inspect any method's exact schema first:

```bash
# What does messages.list accept? (verify)
gws schema gmail.users.messages.list

# Search emails (verify against the schema above)
gws gmail users messages list --params '{"userId": "me", "q": "from:client@example.com after:2025/01/01"}' \
  | python3 scripts/output_analyzer.py --count

# List labels (verify)
gws gmail users labels list --params '{"userId": "me"}'
```

### Bulk Operations

Use `--dry-run` first, and `--page-all` to paginate (one JSON line per page):

```bash
# Preview, then archive read emails older than 30 days (verify method schema first)
gws gmail users messages list --params '{"userId": "me", "q": "is:read older_than:30d"}' --page-all \
  | python3 scripts/output_analyzer.py --select "id" --format json
# Then feed ids to gmail users messages modify (see: gws schema gmail.users.messages.modify)
```

---

## Workflow 2: Drive & Sheets

**Goal:** Manage files, create spreadsheets, configure sharing, and export data.

### File Operations

```bash
# List files
gws drive files list --params '{"pageSize": 50}' \
  | python3 scripts/output_analyzer.py --select "name,mimeType,size" --format table

# Upload a file (helper)
gws drive +upload ./report.pdf --name "Q1 Report"

# Create a Google Sheet
gws sheets spreadsheets create --json '{"properties": {"title": "Budget 2026"}}'

# Download/export — inspect the method first (verify)
gws schema drive.files.export
```

### Sharing (verify schemas first)

```bash
# Inspect the permissions API surface
gws schema drive.permissions.create

# Share with user (verify against schema)
gws drive permissions create --params '{"fileId": "<FILE_ID>"}' \
  --json '{"type": "user", "role": "writer", "emailAddress": "colleague@company.com"}'

# List who has access (verify)
gws drive permissions list --params '{"fileId": "<FILE_ID>"}'
```

### Sheets Data

```bash
# Read values (helper); check exact flags with: gws sheets +read --help
gws sheets +read ...

# Append a row (helper); check exact flags with: gws sheets +append --help
gws sheets +append ...

# Or use discovery methods (verify):
gws schema sheets.spreadsheets.values.update
gws sheets spreadsheets values get --params '{"spreadsheetId": "<SHEET_ID>", "range": "Sheet1!A1:D10"}'
```

---

## Workflow 3: Calendar & Meetings

**Goal:** Schedule events, find available times, and generate standup reports.

### Event Management

```bash
# Create an event (helper); check exact flags with: gws calendar +insert --help
gws calendar +insert ...

# Upcoming events (helper, timezone-aware)
gws calendar +agenda

# Or via discovery (verify):
gws schema calendar.events.insert
gws calendar events list --params '{"calendarId": "primary", "maxResults": 10}'
```

### Find Available Time

```bash
# Free/busy via the Calendar API (verify schema first)
gws schema calendar.freebusy.query
gws calendar freebusy query --json '{"timeMin": "...", "timeMax": "...", "items": [{"id": "alice@co.com"}]}'
```

### Standup Report (workflow helpers)

```bash
# Today's meetings + tasks
gws workflow +standup-report \
  | python3 scripts/output_analyzer.py --format table

# Next meeting prep; check exact flags with: gws workflow +meeting-prep --help
gws workflow +meeting-prep
```

---

## Workflow 4: Security Audit

**Goal:** Audit Google Workspace security configuration and generate remediation commands.

### Run Full Audit

```bash
# Full audit across all services
python3 scripts/workspace_audit.py --json

# Audit specific services
python3 scripts/workspace_audit.py --services gmail,drive,calendar

# Demo mode (no gws required)
python3 scripts/workspace_audit.py --demo
```

### Audit Checks

| Area | Check | Risk |
|------|-------|------|
| Drive | External sharing enabled | Data exfiltration |
| Gmail | Auto-forwarding rules | Data exfiltration |
| Gmail | DMARC/SPF/DKIM records | Email spoofing |
| Calendar | Default sharing visibility | Information leak |
| OAuth | Third-party app grants | Unauthorized access |
| Admin | Super admin count | Privilege escalation |
| Admin | 2-Step verification enforcement | Account takeover |

### Review and Remediate

```bash
# Review findings
python3 scripts/workspace_audit.py --json | python3 scripts/output_analyzer.py \
  --filter "status=FAIL" --select "area,check,remediation"

# Execute remediation (example: check current Drive settings first; verify)
gws drive about get --params '{"fields": "*"}'
# Follow remediation commands from audit output (verify each against gws --help)
```

---

## Python Tools

| Script | Purpose | Usage |
|--------|---------|-------|
| `gws_doctor.py` | Pre-flight diagnostics | `python3 scripts/gws_doctor.py [--json] [--services gmail,drive]` |
| `auth_setup_guide.py` | Guided auth setup | `python3 scripts/auth_setup_guide.py --guide oauth` |
| `gws_recipe_runner.py` | Recipe catalog & runner | `python3 scripts/gws_recipe_runner.py --list [--persona pm]` |
| `workspace_audit.py` | Security/config audit | `python3 scripts/workspace_audit.py [--json] [--demo]` |
| `output_analyzer.py` | JSON/NDJSON analysis | `gws ... --json \| python3 scripts/output_analyzer.py --count` |

All scripts are stdlib-only, support `--json` output, and include demo mode with embedded sample data.

---

## Best Practices

### Security

1. Use OAuth with minimal scopes — request only what each workflow needs
2. Store tokens in the system keyring, never in plain text files
3. Rotate service account keys every 90 days
4. Audit third-party OAuth app grants quarterly
5. Use `--dry-run` before bulk destructive operations

### Automation

1. All `gws` output is structured JSON — pipe it through `output_analyzer.py` for filtering and aggregation
2. Use `gws workflow +*` helpers for multi-step operations instead of chaining raw commands
3. Use the local recipe catalog (`gws_recipe_runner.py`) as command templates, then verify each against `gws --help`
4. `--page-all` emits one JSON line per page (NDJSON) for streaming large result sets
5. Use `--dry-run` to preview any request before executing it

### Performance

1. Request only needed fields via the API's `fields` parameter in `--params` (reduces payload size)
2. Use `pageSize` in `--params` to cap results when browsing
3. Use `--page-all` only when you need complete datasets; tune with `--page-limit` / `--page-delay`
4. Prefer `+` helpers (single optimized calls) over hand-chained API calls
5. Cache frequently accessed data (e.g., label IDs, folder IDs) in variables

---

## Limitations

| Constraint | Impact |
|------------|--------|
| OAuth tokens expire after 1 hour | Re-auth needed for long-running scripts |
| API rate limits (per-user, per-service) | Bulk operations may hit 429 errors |
| Scope requirements vary by service | Must request correct scopes during auth |
| Pre-v1.0 CLI status | Breaking changes possible between releases |
| Google Cloud project required | Free, but requires setup in Cloud Console |
| Admin API needs admin privileges | Some audit checks require Workspace Admin role |

### Required Scopes by Service

```bash
# List scopes for specific services
python3 scripts/auth_setup_guide.py --scopes gmail,drive,calendar,sheets
```

| Service | Key Scopes |
|---------|-----------|
| Gmail | `gmail.modify`, `gmail.send`, `gmail.labels` |
| Drive | `drive.file`, `drive.metadata.readonly` |
| Sheets | `spreadsheets` |
| Calendar | `calendar`, `calendar.events` |
| Admin | `admin.directory.user.readonly`, `admin.directory.group` |
| Tasks | `tasks` |
