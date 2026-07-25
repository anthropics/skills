# Google Workspace CLI Command Reference

Working reference for the `gws` CLI ([github.com/googleworkspace/cli](https://github.com/googleworkspace/cli)) covering services, helper commands, global flags, and environment variables.

> **Verify against your installed version.** `gws` builds its command surface dynamically from Google's Discovery Service and is pre-v1.0. Treat command syntax in this document as a template: confirm exact syntax with `gws --help`, `gws <service> --help`, or `gws schema <service>.<resource>.<method>` before scripting. Verified-from-upstream facts: install via `npm install -g @googleworkspace/cli`; discovery commands follow `gws <service> <resource> <method>` with `--params` (query/path params as JSON) and `--json` (request body); helpers are `+`-prefixed (e.g. `gws gmail +send`); all output is structured JSON.

---

## Global Flags (verified)

| Flag | Description |
|------|-------------|
| `--params <json>` | Query/path parameters as JSON for discovery commands |
| `--json <json>` | Request body as JSON for discovery commands |
| `--dry-run` | Preview the request without executing |
| `--page-all` | Auto-paginate; one JSON line per page (NDJSON) |
| `--page-limit <n>` | Max pages to fetch |
| `--page-delay <ms>` | Delay between pages |
| `--sanitize` | Scan responses via a Model Armor template |

---

## Environment Variables (verified)

| Variable | Description |
|----------|-------------|
| `GOOGLE_WORKSPACE_CLI_CLIENT_ID` | OAuth client ID |
| `GOOGLE_WORKSPACE_CLI_CLIENT_SECRET` | OAuth client secret |
| `GOOGLE_WORKSPACE_CLI_CREDENTIALS_FILE` | Path to credentials JSON (from `gws auth export`) |
| `GOOGLE_WORKSPACE_CLI_TOKEN` | Pre-obtained OAuth token |
| `GOOGLE_WORKSPACE_CLI_CONFIG_DIR` | Override default config location |
| `GOOGLE_WORKSPACE_CLI_LOG` | Enable debug logging |

---

## Services

### Gmail

```bash
gws gmail users.messages list me --query "<query>" --json
gws gmail users.messages get me <messageId> --json
gws gmail users.messages send me --to <email> --subject <subj> --body <body>
gws gmail users.messages reply me --thread-id <id> --body <body>
gws gmail users.messages forward me --message-id <id> --to <email>
gws gmail users.messages modify me <id> --addLabelIds <label> --removeLabelIds INBOX
gws gmail users.messages trash me <id>
gws gmail users.labels list me --json
gws gmail users.labels create me --name <name>
gws gmail users.settings.filters create me --criteria <json> --action <json>
gws gmail users.settings.forwardingAddresses list me --json
gws gmail users getProfile me --json
```

### Google Drive

```bash
gws drive files list --json --limit <n>
gws drive files list --query "name contains '<term>'" --json
gws drive files list --parents <folderId> --json
gws drive files get <fileId> --json
gws drive files create --name <name> --upload <path> --parents <folderId>
gws drive files create --name <name> --mimeType application/vnd.google-apps.folder
gws drive files update <fileId> --upload <path>
gws drive files delete <fileId>
gws drive files export <fileId> --mime <mimeType> --output <path>
gws drive files copy <fileId> --name <newName>
gws drive permissions list <fileId> --json
gws drive permissions create <fileId> --type <user|group|domain> --role <reader|writer|owner> --emailAddress <email>
gws drive permissions delete <fileId> <permissionId>
gws drive about get --json
gws drive files emptyTrash
```

### Google Sheets

```bash
gws sheets spreadsheets create --title <title> --json
gws sheets spreadsheets get <spreadsheetId> --json
gws sheets spreadsheets.values get <spreadsheetId> --range <range> --json
gws sheets spreadsheets.values update <spreadsheetId> --range <range> --values <json>
gws sheets spreadsheets.values append <spreadsheetId> --range <range> --values <json>
gws sheets spreadsheets.values clear <spreadsheetId> --range <range>
gws sheets spreadsheets.values batchGet <spreadsheetId> --ranges <range1>,<range2> --json
gws sheets spreadsheets.values batchUpdate <spreadsheetId> --data <json>
```

### Google Calendar

```bash
gws calendar calendarList list --json
gws calendar calendarList get <calendarId> --json
gws calendar events list <calendarId> --timeMin <datetime> --timeMax <datetime> --json
gws calendar events get <calendarId> <eventId> --json
gws calendar events insert <calendarId> --summary <title> --start <datetime> --end <datetime> --attendees <emails>
gws calendar events update <calendarId> <eventId> --summary <title>
gws calendar events patch <calendarId> <eventId> --start <datetime> --end <datetime>
gws calendar events delete <calendarId> <eventId>
gws calendar freebusy query --timeMin <start> --timeMax <end> --items <calendarId1>,<calendarId2> --json
```

### Google Docs

```bash
gws docs documents create --title <title> --json
gws docs documents get <documentId> --json
gws docs documents batchUpdate <documentId> --requests <json>
```

### Google Slides

```bash
gws slides presentations create --title <title> --json
gws slides presentations get <presentationId> --json
gws slides presentations.pages get <presentationId> <pageId> --json
gws slides presentations.pages getThumbnail <presentationId> <pageId> --json
```

### Google Chat

```bash
gws chat spaces list --json
gws chat spaces get <spaceName> --json
gws chat spaces.messages create <spaceName> --text <message>
gws chat spaces.messages list <spaceName> --json
gws chat spaces.messages get <messageName> --json
gws chat spaces.members list <spaceName> --json
```

### Google Tasks

```bash
gws tasks tasklists list --json
gws tasks tasklists get <tasklistId> --json
gws tasks tasklists insert --title <title> --json
gws tasks tasks list <tasklistId> --json
gws tasks tasks get <tasklistId> <taskId> --json
gws tasks tasks insert <tasklistId> --title <title> --due <datetime>
gws tasks tasks update <tasklistId> <taskId> --status completed
gws tasks tasks delete <tasklistId> <taskId>
```

### Admin SDK (Directory)

```bash
gws admin users list --domain <domain> --json
gws admin users get <email> --json
gws admin users insert --primaryEmail <email> --name.givenName <first> --name.familyName <last>
gws admin users update <email> --suspended true
gws admin groups list --domain <domain> --json
gws admin groups get <email> --json
gws admin groups insert --email <email> --name <name>
gws admin groups.members list <groupEmail> --json
gws admin groups.members insert <groupEmail> --email <memberEmail> --role MEMBER
gws admin orgunits list --customerId my_customer --json
```

### Google Groups

```bash
gws groups groups list --domain <domain> --json
gws groups groups get <email> --json
gws groups memberships list <groupEmail> --json
```

### Google People (Contacts)

```bash
gws people people.connections list me --personFields names,emailAddresses --json
gws people people get <resourceName> --personFields names,emailAddresses,phoneNumbers --json
gws people people searchContacts --query <term> --readMask names,emailAddresses --json
```

### Google Meet

```bash
gws meet spaces create --json
gws meet spaces get <spaceName> --json
gws meet conferenceRecords list --json
```

### Google Classroom

```bash
gws classroom courses list --json
gws classroom courses get <courseId> --json
gws classroom courses.courseWork list <courseId> --json
gws classroom courses.students list <courseId> --json
```

### Google Forms

```bash
gws forms forms get <formId> --json
gws forms forms.responses list <formId> --json
```

### Google Keep

```bash
gws keep notes list --json
gws keep notes get <noteId> --json
```

### Google Sites

```bash
gws sites sites list --json
gws sites sites get <siteId> --json
```

### Google Vault

```bash
gws vault matters list --json
gws vault matters get <matterId> --json
gws vault matters.holds list <matterId> --json
```

### Admin Reports / Activities

```bash
gws admin activities list <applicationName> --json
gws admin activities list login --json
gws admin activities list drive --json
gws admin activities list admin --json
```

---

## Helper Commands (verified `+`-prefixed surface)

Helpers are prefixed with `+` so they never collide with Discovery-generated method names. Check each helper's flags with `gws <service> +<helper> --help`.

| Service | Helper | Description |
|---------|--------|-------------|
| gmail | `+send` | Send an email (`gws gmail +send --to a@b.com --subject "Hi" --body "Hello"`) |
| gmail | `+reply` | Reply to a message (auto-threading) |
| gmail | `+reply-all` | Reply-all to a message |
| gmail | `+forward` | Forward a message |
| gmail | `+triage` | Unread inbox summary |
| gmail | `+watch` | Watch for new emails as NDJSON |
| sheets | `+append` | Append a row |
| sheets | `+read` | Read values |
| docs | `+write` | Append text |
| chat | `+send` | Send a space message |
| drive | `+upload` | Upload a file (`gws drive +upload ./report.pdf --name "Q1 Report"`) |
| calendar | `+insert` | Create an event |
| calendar | `+agenda` | Show upcoming events (timezone-aware) |
| script | `+push` | Replace all Apps Script files |
| workflow | `+standup-report` | Today's meetings + tasks |
| workflow | `+meeting-prep` | Next meeting prep |
| workflow | `+email-to-task` | Convert Gmail to Tasks |
| workflow | `+weekly-digest` | Weekly summary |
| workflow | `+file-announce` | Announce Drive file in Chat |
| events | `+subscribe` | Subscribe to Workspace events |
| events | `+renew` | Renew event subscriptions |
| modelarmor | `+sanitize-prompt` | Sanitize user prompt |
| modelarmor | `+sanitize-response` | Sanitize model response |
| modelarmor | `+create-template` | Create Model Armor template |

---

## Schema Introspection

```bash
# View the API schema for any service method
gws schema gmail.users.messages.list
gws schema drive.files.create
gws schema calendar.events.insert

# Discover available schema/introspection options for your version
gws schema --help
```

---

## Authentication Commands (verified)

```bash
gws auth setup                      # Interactive OAuth setup (uses gcloud if available)
gws auth login                      # Log in / re-consent
gws auth login -s drive,gmail,sheets  # Request specific scopes
gws auth export --unmasked          # Export credentials for headless reuse
gws auth --help                     # Discover further auth subcommands in your version
```

---

## Recipe Commands (local catalog, not built into gws)

Recipes ship with this skill as a local catalog of command templates:

```bash
python3 scripts/gws_recipe_runner.py --list                       # List all 43 recipe templates
python3 scripts/gws_recipe_runner.py --search "email"             # Search by keyword
python3 scripts/gws_recipe_runner.py --describe standup-report    # Show recipe details
python3 scripts/gws_recipe_runner.py --run <name> --dry-run       # Preview recipe commands
```

---

## Persona Commands (local catalog, not built into gws)

```bash
python3 scripts/gws_recipe_runner.py --personas                   # List all 10 personas
python3 scripts/gws_recipe_runner.py --list --persona pm          # Recipes for a persona
```
