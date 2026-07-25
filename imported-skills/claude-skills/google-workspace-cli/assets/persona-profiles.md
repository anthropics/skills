# Google Workspace CLI Persona Profiles

10 role-based bundles that scope recipes and commands to your daily workflow.

> **These are command templates, not verified invocations.** The `gws` CLI ([github.com/googleworkspace/cli](https://github.com/googleworkspace/cli)) generates its command surface dynamically from Google's Discovery Service and is pre-v1.0. Before running any command below, verify its exact syntax with `gws --help`, `gws <service> --help`, or `gws schema <service>.<resource>.<method>`. Verified upstream patterns: discovery commands are `gws <service> <resource> <method> --params '{...}' --json '{...}'`; helpers are `+`-prefixed (`gws gmail +send`, `gws calendar +agenda`, `gws workflow +standup-report`).

---

## 1. Executive Assistant

**Description:** Managing schedules, emails, and communications for executives.

**Top Commands:**
- `python3 scripts/gws_recipe_runner.py --describe morning-briefing` — Start the day with schedule + inbox overview
- `gws calendar freebusy query ...` (verify: `gws schema calendar.freebusy.query`) — Find available slots for meetings
- `gws workflow +meeting-prep` — Prepare for the next meeting
- `gws gmail users.messages send me` — Send emails on behalf
- `python3 scripts/gws_recipe_runner.py --describe eod-wrap` — End of day summary

**Recommended Recipes:** morning-briefing, today-schedule, find-time, send-email, reply-to-thread, meeting-prep, eod-wrap, quick-event, inbox-zero, standup-report

**Daily Workflow:**
1. Run `morning-briefing` at 8:00 AM
2. Process inbox with `inbox-zero`
3. Schedule meetings with `find-time` + `create-event`
4. Prep for meetings with `meeting-prep`
5. Close day with `eod-wrap`

---

## 2. Project Manager

**Description:** Tracking tasks, meetings, and project deliverables.

**Top Commands:**
- `gws workflow +standup-report` — Generate standup updates
- `gws calendar freebusy query ...` (verify: `gws schema calendar.freebusy.query`) — Schedule sprint ceremonies
- `gws tasks tasks insert` — Create and assign tasks
- `gws sheets spreadsheets.values get` — Read project trackers
- `python3 scripts/gws_recipe_runner.py --describe project-status` — Aggregate project status

**Recommended Recipes:** standup-report, create-event, find-time, task-create, task-progress, project-status, weekly-summary, share-folder, sheet-read, morning-briefing

**Daily Workflow:**
1. Run `standup-report` before standup
2. Update project tracker via `sheet-write`
3. Create action items with `task-create`
4. Run `weekly-summary` on Fridays
5. Share updates via `chat-message`

---

## 3. HR

**Description:** Managing people, onboarding, and team communications.

**Top Commands:**
- `gws admin users list` — List all domain users
- `gws admin users get <email>` — Look up employee details
- `gws docs documents create` — Create onboarding docs
- `gws drive permissions create` — Share folders with new hires
- `gws people people.connections list` — Export contact directory

**Recommended Recipes:** list-users, user-info, send-email, create-event, create-doc, share-folder, chat-message, list-groups, export-contacts, today-schedule

**Daily Workflow:**
1. Check new hire onboarding queue
2. Create welcome docs with `create-doc`
3. Set up 1:1s with `create-event`
4. Share team folders with `share-folder`
5. Send announcements via `send-email`

---

## 4. Sales

**Description:** Managing client communications, proposals, and scheduling.

**Top Commands:**
- `gws gmail users.messages send me` — Send proposals and follow-ups
- `gws gmail users.messages list me --query` — Search client conversations
- `gws calendar freebusy query ...` (verify: `gws schema calendar.freebusy.query`) — Schedule client meetings
- `gws docs documents create` — Create proposals
- `gws sheets spreadsheets.values update` — Update pipeline tracker

**Recommended Recipes:** send-email, search-emails, create-event, find-time, create-doc, share-file, sheet-read, sheet-write, export-file, morning-briefing

**Daily Workflow:**
1. Run `morning-briefing` for meeting overview
2. Search emails for client updates
3. Update pipeline in Sheets
4. Send proposals via `send-email` + `share-file`
5. Schedule follow-ups with `create-event`

---

## 5. IT Admin

**Description:** Managing Workspace configuration, security, and user administration.

**Top Commands:**
- `gws admin users list --domain` — Audit user accounts
- `gws admin activities list login` — Monitor login activity
- `gws admin groups list` — Manage groups
- `python3 workspace_audit.py` — Run security audit
- `gws drive files list --orderBy "quotaBytesUsed desc"` — Find storage hogs

**Recommended Recipes:** list-users, list-groups, user-info, audit-logins, drive-activity, find-large-files, cleanup-trash, label-manager, filter-setup, share-folder

**Daily Workflow:**
1. Check `audit-logins` for suspicious activity
2. Run `workspace_audit.py` weekly
3. Process user provisioning requests
4. Monitor storage with `find-large-files`
5. Review group memberships

---

## 6. Developer

**Description:** Using Workspace APIs for automation and data integration.

**Top Commands:**
- `gws sheets spreadsheets.values get` — Read config/data from Sheets
- `gws sheets spreadsheets.values update` — Write results to Sheets
- `gws drive files create --upload` — Upload build artifacts
- `gws chat spaces.messages create` — Post deployment notifications
- `gws tasks tasks insert` — Create tasks from CI/CD

**Recommended Recipes:** sheet-read, sheet-write, sheet-append, upload-file, create-doc, chat-message, task-create, list-files, export-file, send-email

**Daily Workflow:**
1. Read config from Sheets API
2. Run automated reports to Sheets
3. Post updates to Chat spaces
4. Upload artifacts to Drive
5. Create tasks for bugs/issues

---

## 7. Marketing

**Description:** Managing campaigns, content creation, and team coordination.

**Top Commands:**
- `gws docs documents create` — Draft blog posts and briefs
- `gws drive files create --upload` — Upload creative assets
- `gws sheets spreadsheets.values append` — Log campaign metrics
- `gws gmail users.messages send me` — Send campaign emails
- `gws chat spaces.messages create` — Coordinate with team

**Recommended Recipes:** send-email, create-doc, share-file, upload-file, create-sheet, sheet-write, chat-message, create-event, email-stats, weekly-summary

**Daily Workflow:**
1. Check `email-stats` for campaign performance
2. Create content in Docs
3. Upload assets to shared Drive folders
4. Update metrics in Sheets
5. Coordinate launches via Chat

---

## 8. Finance

**Description:** Managing spreadsheets, financial reports, and data analysis.

**Top Commands:**
- `gws sheets spreadsheets.values get` — Pull financial data
- `gws sheets spreadsheets.values update` — Update forecasts
- `gws sheets spreadsheets create` — Create new reports
- `gws drive files export` — Export reports as PDF
- `gws drive permissions create` — Share with auditors

**Recommended Recipes:** sheet-read, sheet-write, sheet-append, create-sheet, export-file, share-file, send-email, find-large-files, drive-activity, weekly-summary

**Daily Workflow:**
1. Pull latest data into Sheets
2. Update financial models
3. Generate PDF reports with `export-file`
4. Share reports with stakeholders
5. Weekly summary for leadership

---

## 9. Legal

**Description:** Managing documents, contracts, and compliance.

**Top Commands:**
- `gws docs documents create` — Draft contracts
- `gws drive files export` — Export final versions as PDF
- `gws drive permissions create` — Manage document access
- `gws gmail users.messages list me --query` — Search for compliance emails
- `gws admin activities list` — Audit trail for compliance

**Recommended Recipes:** create-doc, share-file, export-file, search-emails, send-email, upload-file, list-files, drive-activity, audit-logins, find-large-files

**Daily Workflow:**
1. Draft and review documents
2. Search email for contract references
3. Export finalized docs as PDF
4. Set precise sharing permissions
5. Maintain audit trail

---

## 10. Customer Support

**Description:** Managing customer communications and ticket tracking.

**Top Commands:**
- `gws gmail users.messages list me --query` — Search customer emails
- `gws gmail users.messages reply me` — Reply to tickets
- `gws gmail users.labels create` — Organize by ticket status
- `gws tasks tasks insert` — Create follow-up tasks
- `gws chat spaces.messages create` — Escalate to team

**Recommended Recipes:** search-emails, send-email, reply-to-thread, label-manager, filter-setup, task-create, chat-message, unread-digest, inbox-zero, morning-briefing

**Daily Workflow:**
1. Run `morning-briefing` for ticket overview
2. Process inbox with label-based triage
3. Reply to open tickets
4. Escalate via Chat for urgent issues
5. Create follow-up tasks for pending items
