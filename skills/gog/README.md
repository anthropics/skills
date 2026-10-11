# GOG Personal Assistant Skills

A comprehensive collection of Agent Skills for personal productivity, email management, task tracking, and follow-up automation.

## Overview

The GOG (Go-Organized-Go) skill collection enables Claude to function as your personal assistant by:

- **Triaging and prioritizing** your inbox intelligently
- **Drafting professional emails** with tone variants
- **Sending emails** with explicit confirmation safeguards
- **Managing tasks** with smart prioritization (P0-P3)
- **Reviewing and scheduling** calendar events
- **Tracking follow-ups** to ensure nothing falls through the cracks

These skills work together as a cohesive system, sharing context and data to provide seamless personal assistance.

## Architecture

### Skills Included

1. **gog-email-triage** - Inbox review and prioritization
2. **gog-email-draft** - Email composition with tone variants
3. **gog-email-send** - Secure email sending with confirmation
4. **gog-tasks** - Task creation, prioritization, and daily review
5. **gog-calendar** - Schedule review and meeting management
6. **gog-followups** - Follow-up tracking and reminder generation

### Shared Resources

- **_shared/references/** - Documentation and schemas
  - `gog-interface.md` - GOG CLI specification
  - `schemas.md` - JSON data structures
  - `logging.md` - Audit logging format
  - `testing.md` - Safe testing procedures

- **_shared/scripts/** - Utility scripts
  - `validate_env.sh` - Environment validation
  - `log.sh` - Audit logging utility
  - `smoke_test.sh` - Safe smoke tests

### Data Files

- **~/.gog-assistant/audit.log** - Audit trail of all actions
- **~/.gog-assistant/followups.json** - Follow-up tracking store
- **~/.gog-assistant/config.json** - GOG configuration (if needed)

## Prerequisites

### Critical: Google Cloud OAuth2 Credentials

**⚠️  IMPORTANT: Before you can use GOG, you MUST set up Google Cloud OAuth2 credentials.**

GOG requires OAuth2 credentials from Google Cloud Console to access your Gmail, Calendar, and Tasks.

**Setup steps:**

1. **Get OAuth2 credentials** from Google Cloud Console:
   - Follow the detailed guide: https://github.com/steipete/gogcli?tab=readme-ov-file#1-get-oauth2-credentials
   - You'll need to:
     - Create a Google Cloud project
     - Enable Gmail API, Calendar API, and Tasks API
     - Create OAuth2 credentials (Desktop application type)
     - Download the credentials JSON file

2. **Configure GOG with credentials**:
   ```bash
   # GOG will prompt for credentials on first auth
   gog auth login
   # Paste your OAuth2 client ID and secret when prompted
   ```

3. **Grant permissions**:
   - GOG will open a browser for OAuth consent
   - Grant access to Gmail, Calendar, and Tasks
   - Complete the authentication flow

**Without these credentials, GOG cannot access your Google data and the skills will not work.**

### Required Tools

1. **GOG CLI Tool** (v0.9.0 or later)
   - Install: https://github.com/steipete/gogcli
   - macOS: `brew install gog` (if available)
   - Must be available on your PATH as `gog`
   - Verify: `gog --version`

2. **System Tools**
   - `bash` (for scripts)
   - `jq` (for JSON processing - install: `brew install jq`)
   - Standard Unix utilities (date, cat, etc.)

### Optional

- `python3` - For advanced scripting
- `curl` - For HTTP operations
- `git` - For version control of configurations

## Installation & Setup

### Step 0: Set Up Google Cloud OAuth2 Credentials

**⚠️  DO THIS FIRST: GOG requires Google Cloud OAuth2 credentials to work.**

Before installing the skills or running any GOG commands, you need to set up OAuth2 credentials:

**Complete guide**: 👉 https://github.com/steipete/gogcli?tab=readme-ov-file#1-get-oauth2-credentials

**Quick summary:**

1. **Go to Google Cloud Console**: https://console.cloud.google.com/
2. **Create a project** (or use existing)
3. **Enable APIs**:
   - Gmail API
   - Google Calendar API
   - Google Tasks API
4. **Create OAuth2 credentials**:
   - Type: Desktop application
   - Download the credentials JSON
5. **Run first authentication**:
   ```bash
   gog auth login
   # Paste client ID and secret when prompted
   # Browser will open for OAuth consent
   # Grant Gmail, Calendar, and Tasks permissions
   ```

6. **Verify**:
   ```bash
   gog gmail search "is:inbox" --max 1
   # Should return results, not auth error
   ```

**Without OAuth2 credentials, all GOG commands will fail with authentication errors.**

### Step 1: Make Skills Available to Claude Code

Claude Code looks for skills in `.claude/skills/` (project-specific) or `~/.claude/skills/` (global).

**Automated setup (recommended):**

```bash
bash skills/gog/setup-claude-code.sh
```

This script will:
- Create symlinks so Claude Code can find the skills
- Ask whether you want project-specific or global installation
- Add `.claude/` to `.gitignore` (for project-specific install)

**Manual setup:**

```bash
# Option 1: Project-specific (this project only)
mkdir -p .claude/skills
for skill in skills/gog/gog-*/; do
  skill_name=$(basename "$skill")
  ln -s "../../$skill" ".claude/skills/$skill_name"
done

# Option 2: Global (all Claude Code sessions)
mkdir -p ~/.claude/skills
for skill in $(pwd)/skills/gog/gog-*/; do
  skill_name=$(basename "$skill")
  ln -s "$skill" "$HOME/.claude/skills/$skill_name"
done
```

**Verify installation:**

```bash
ls -la .claude/skills/  # Should show gog-* symlinks
```

After setup, restart Claude Code or open a new session. Type `/skills` to see the GOG skills listed.

### Step 2: Verify GOG CLI

Check if GOG is installed and authenticated:

```bash
# From the skills repository root
bash skills/gog/_shared/scripts/validate_env.sh
```

This script checks:
- GOG command availability
- Authentication status
- Audit log directory
- Required tools

**If GOG is not authenticated**, the script will tell you to complete Step 0 (OAuth2 credentials setup).

### Step 3: Run Smoke Tests (Optional)

Test the skills safely using only your own email:

```bash
# Read-only tests (always safe)
bash skills/gog/_shared/scripts/smoke_test.sh

# With draft creation (safe, draft to self only)
RUN_DRAFT_TEST=1 bash skills/gog/_shared/scripts/smoke_test.sh
```

See `_shared/references/testing.md` for detailed test procedures.

### Step 4: Load Skills in Claude Code

In a Claude Code session, skills from this directory can be loaded individually as needed:

```
/skill load gog-email-triage
```

Or reference them naturally in conversation:
```
"Help me triage my inbox"
"Draft a reply to that email"
"What's on my calendar today?"
```

## Usage Guide

### Daily Workflow

**Morning Routine:**
1. **Review calendar**: "Show today's agenda"
2. **Triage inbox**: "Review my unread emails"
3. **Check tasks**: "Daily task review"
4. **Check follow-ups**: "What emails am I waiting on?"

**Throughout the Day:**
- **Draft replies**: "Draft a reply to [email from person]"
- **Create tasks**: "Create a task for [action item]"
- **Schedule meetings**: "Find time for a 30-minute meeting this week"

**End of Day:**
- **Complete tasks**: "Mark task_xyz as done"
- **Track follow-ups**: "Track follow-up for email I just sent"
- **Review tomorrow**: "What's on my calendar tomorrow?"

### Skill Integration

The skills are designed to work together:

```
1. Triage inbox → 2. Draft reply → 3. Send with confirmation
                ↓
         Create task for follow-up action
                ↓
         Track follow-up for response
```

**Example Flow:**

```
User: "Triage my inbox"
→ gog-email-triage: Shows prioritized list with suggested actions

User: "Draft a reply to the budget approval email"
→ gog-email-draft: Generates concise + warmer variants

User: "YES, SEND"
→ gog-email-send: Sends email, logs to audit trail

User: "Create a task to follow up in 3 days"
→ gog-tasks: Creates high-priority task

User: "Track follow-up for that email"
→ gog-followups: Adds to follow-up store, will nudge in 3 days
```

## Safety Features

### Confirmation Requirements

**Actions requiring explicit confirmation:**
- **Sending emails**: Must type "YES, SEND" exactly
- **Creating/deleting tasks**: Requires "yes" confirmation
- **Creating calendar events**: Requires "yes, create" confirmation
- **Adding/closing follow-ups**: Requires "yes" confirmation

### Audit Logging

All write operations are logged to `~/.gog-assistant/audit.log`:

```bash
# View recent actions
tail -n 20 ~/.gog-assistant/audit.log | jq .

# Find all sends
jq 'select(.action == "email-send")' ~/.gog-assistant/audit.log

# Find failures
jq 'select(.status == "failure")' ~/.gog-assistant/audit.log
```

### Privacy Protection

- Email bodies are NOT logged (only metadata: ID, subject, recipients)
- Audit log file has restrictive permissions (0600)
- Sensitive data is redacted in skill outputs
- All test operations use only your own email address

## Configuration

### User Preferences

Skills learn and remember preferences within a session:

- **Email tone**: Professional, friendly, concise, detailed
- **Task priorities**: How urgently different types of work are classified
- **Follow-up timing**: Typical delay before nudging different types of contacts
- **Calendar preferences**: Meeting duration defaults, time-of-day preferences

### Customization

**Modify shared references:**
- Edit `_shared/references/gog-interface.md` if your GOG CLI differs
- Update `_shared/references/schemas.md` for custom fields
- Adjust `_shared/references/logging.md` for audit requirements

**Script customization:**
- Modify `_shared/scripts/log.sh` for custom logging
- Extend `_shared/scripts/smoke_test.sh` for additional tests

## Troubleshooting

### "gog: command not found"

**Cause**: GOG CLI not installed or not on PATH

**Fix**:
1. Install GOG CLI
2. Add to PATH: `export PATH="/path/to/gog:$PATH"`
3. Or create a wrapper script in `/usr/local/bin/gog`

See `_shared/references/gog-interface.md` for GOG CLI specification.

### "Authentication failed"

**Cause**: OAuth token expired or invalid

**Fix**:
```bash
gog auth login
# Follow browser authentication flow
```

Ensure scopes include: `gmail.modify`, `calendar.events`, `tasks`

### "Invalid JSON from GOG"

**Cause**: GOG CLI output format unexpected

**Fix**:
1. Try without `--json` flag: `gog email list --limit 1`
2. Check GOG version: `gog version`
3. Update skills if GOG interface changed

### "Permission denied" on audit log

**Cause**: Audit log directory not writable

**Fix**:
```bash
mkdir -p ~/.gog-assistant
chmod 700 ~/.gog-assistant
```

### Skills not responding to context

**Cause**: Dynamic context (`!` commands) not executing

**Fix**:
1. Verify GOG is authenticated
2. Check skill SKILL.md for correct context syntax
3. Ensure Claude Code version supports dynamic context injection

## Advanced Usage

### Batch Operations

**Triage and process multiple emails:**
```
"Triage my inbox, then draft replies for the top 3 priorities"
```

**Create multiple tasks:**
```
"Create tasks for emails msg_123, msg_456, and msg_789"
```

### Custom Workflows

**Weekly review:**
```
"Show this week's calendar, pending follow-ups, and overdue tasks"
```

**Pre-meeting prep:**
```
"What meetings do I have today? Create tasks for prep work needed."
```

### Integration with Other Tools

**Export data:**
```bash
# Export follow-ups to CSV
jq -r '.[] | [.person, .topic, .next_nudge_date, .status] | @csv' \
  ~/.gog-assistant/followups.json > followups.csv

# Export tasks (if GOG supports export)
gog tasks list --status open --json > open_tasks.json
```

**Analytics:**
```bash
# Count emails sent this month
jq -r 'select(.action == "email-send" and .status == "success")' \
  ~/.gog-assistant/audit.log | wc -l

# Most active skill
jq -r '.skill' ~/.gog-assistant/audit.log | sort | uniq -c | sort -rn
```

## Security & Privacy

### Data Storage

- **Local only**: All data stored in `~/.gog-assistant/`
- **No cloud sync**: Skills don't transmit data externally (beyond GOG API)
- **User-owned**: You control all data, can delete anytime

### Sensitive Information

- **Email bodies**: Not stored in logs, only metadata
- **Credentials**: Never logged or displayed
- **Personal data**: Minimized in all outputs

### Best Practices

1. **Review audit logs periodically**: `tail ~/.gog-assistant/audit.log`
2. **Backup follow-ups store**: `cp ~/.gog-assistant/followups.json ~/backups/`
3. **Rotate logs**: Compress/archive old audit logs
4. **Use confirmation strings**: Never skip "YES, SEND" for sends
5. **Test with self**: Use your own email for all tests

## Development & Contribution

### Extending Skills

To add functionality:

1. **Create new skill**: Add directory under `skills/gog/my-new-skill/`
2. **Follow spec**: See https://agentskills.io/specification
3. **Integrate**: Reference shared resources and other skills
4. **Test**: Add tests to `smoke_test.sh`

### Reporting Issues

When reporting issues, include:

1. **GOG version**: `gog version`
2. **Error output**: Full error message
3. **Recent logs**: `tail -n 50 ~/.gog-assistant/audit.log`
4. **Test results**: Output of `validate_env.sh` and `smoke_test.sh`

### Testing Changes

Before deploying changes:

```bash
# Validate environment
bash skills/gog/_shared/scripts/validate_env.sh

# Run smoke tests
bash skills/gog/_shared/scripts/smoke_test.sh

# Test individual skill (manually in Claude Code)
# Load skill and verify expected behavior
```

## FAQ

**Q: Do these skills work with Gmail/Outlook/other email providers?**

A: Yes, if your GOG CLI supports them. The GOG CLI acts as an abstraction layer over different email/calendar providers.

**Q: Can I use these skills without the GOG CLI?**

A: The skills are designed for GOG, but you could adapt them to work with other CLIs (Gmail API, Microsoft Graph, etc.) by updating the command syntax in each SKILL.md.

**Q: Will emails be sent automatically?**

A: **No.** All sends require explicit "YES, SEND" confirmation. This is a critical safety feature.

**Q: How do I back up my follow-ups and tasks?**

A:
```bash
# Backup follow-ups
cp ~/.gog-assistant/followups.json ~/backups/followups_$(date +%Y%m%d).json

# Backup audit log
cp ~/.gog-assistant/audit.log ~/backups/audit_$(date +%Y%m%d).log

# Export tasks via GOG
gog tasks list --json > ~/backups/tasks_$(date +%Y%m%d).json
```

**Q: Can I customize the confirmation string for sends?**

A: Not recommended. "YES, SEND" is deliberately chosen to be distinctive and unlikely to occur accidentally. Changing it requires modifying `gog-email-send/SKILL.md`.

**Q: Do these skills work offline?**

A: No. They require network access for GOG CLI to communicate with email/calendar services.

**Q: How do I uninstall?**

A:
```bash
# Remove skills directory (if no longer needed)
rm -rf skills/gog/

# Remove data directory
rm -rf ~/.gog-assistant/

# Remove GOG CLI (platform-specific)
```

## Version History

- **1.0.0** (2026-01-28) - Initial release
  - 6 core skills (triage, draft, send, tasks, calendar, followups)
  - Shared utilities and documentation
  - Safe testing framework

## License

See individual SKILL.md files for license information.

## Support & Documentation

- **Skill specifications**: Each skill's SKILL.md file
- **API reference**: `_shared/references/gog-interface.md`
- **Data schemas**: `_shared/references/schemas.md`
- **Testing guide**: `_shared/references/testing.md`
- **Logging docs**: `_shared/references/logging.md`

## Acknowledgments

Built following the [Agent Skills specification](https://agentskills.io).

---

**Ready to get started?**

1. Run: `bash skills/gog/_shared/scripts/validate_env.sh`
2. Load a skill in Claude Code: `/skill load gog-email-triage`
3. Start with: "Triage my inbox"

Happy productivity! 🚀
