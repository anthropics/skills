# GOG Skills - Quick Start Guide

Get your GOG Personal Assistant up and running in 4 steps.

## ⚠️  Step 0: Google Cloud OAuth2 Credentials (REQUIRED)

**YOU MUST DO THIS FIRST** - Without OAuth2 credentials from Google Cloud, GOG cannot access your Gmail, Calendar, or Tasks.

### Why OAuth2 Credentials?

GOG uses the official Google APIs to access your data. Google requires OAuth2 authentication for security. You need to:
1. Create a Google Cloud project
2. Enable the APIs (Gmail, Calendar, Tasks)
3. Create OAuth2 credentials (free, takes ~10 minutes)
4. Use those credentials to authenticate GOG

### Complete OAuth2 Setup Guide

👉 **Follow this guide**: https://github.com/steipete/gogcli?tab=readme-ov-file#1-get-oauth2-credentials

### Quick Summary

**1. Go to Google Cloud Console**
   - Visit: https://console.cloud.google.com/
   - Sign in with your Google account

**2. Create a Project**
   - Click: "Select a project" → "New Project"
   - Name: "GOG CLI" or similar
   - Click: Create

**3. Enable Required APIs**

   Enable these 3 APIs for your project:

   - **Gmail API**: https://console.cloud.google.com/apis/library/gmail.googleapis.com
   - **Google Calendar API**: https://console.cloud.google.com/apis/library/calendar-json.googleapis.com
   - **Google Tasks API**: https://console.cloud.google.com/apis/library/tasks.googleapis.com

   For each API: Click "Enable"

**4. Create OAuth2 Credentials**

   - Navigate to: APIs & Services → Credentials
   - Click: "Create Credentials" → "OAuth client ID"
   - If prompted, configure OAuth consent screen:
     - User Type: External (for personal) or Internal (for workspace)
     - App name: "GOG CLI"
     - User support email: your email
     - Authorized domains: (can leave empty)
     - Scopes: Add Gmail, Calendar, Tasks
     - Test users: Add your email
     - Save and Continue
   - Back to Create Credentials:
     - Application type: **Desktop app**
     - Name: "GOG CLI Desktop"
     - Click: Create
   - **Download the JSON file** (client_secret_xxx.json)

**5. Authenticate GOG**

   ```bash
   gog auth login
   ```

   - GOG will ask for credentials (first time):
     - Paste your Client ID (from the JSON you downloaded)
     - Paste your Client Secret (from the JSON)
   - Browser opens for OAuth consent:
     - Select your Google account
     - Review permissions
     - Click "Allow"
   - GOG is now authenticated!

**6. Verify It Works**

   ```bash
   # Test email access
   gog gmail search "is:inbox" --max 1

   # Test calendar access
   gog calendar events --today

   # Test tasks access
   gog tasks lists
   ```

   If these commands show data (not authentication errors), you're ready!

---

## ✅ Step 1: Install GOG CLI

If you haven't installed GOG yet:

```bash
# macOS with Homebrew
brew install gog

# Or download from releases
# https://github.com/steipete/gogcli/releases
```

Verify:
```bash
gog --version
# Should show: v0.9.0 or later
```

---

## ✅ Step 2: Make Skills Available to Claude Code

Run the automated setup script:

```bash
cd /path/to/skills/repo
bash skills/gog/setup-claude-code.sh
```

Choose option 1 (project-specific) or 2 (global).

Or manually create symlinks:

```bash
# Project-specific
mkdir -p .claude/skills
for skill in skills/gog/gog-*/; do
  skill_name=$(basename "$skill")
  ln -s "../../$skill" ".claude/skills/$skill_name"
done
```

Verify:
```bash
ls -la .claude/skills/
# Should show 6 gog-* symlinks
```

---

## ✅ Step 3: Verify Everything Works

Run the validation script:

```bash
bash skills/gog/_shared/scripts/validate_env.sh
```

**Expected output:**
```
✓ GOG command found
✓ GOG authenticated
✓ Audit log directory exists
✓ Optional tools check
=== VALIDATION PASSED ===
```

Run smoke tests:

```bash
bash skills/gog/_shared/scripts/smoke_test.sh
```

**Expected output:**
```
✓ Verify GOG is reachable: PASS
✓ List emails (read-only): PASS
✓ Read one email (read-only): PASS
✓ Calendar agenda (read-only): PASS
✓ List tasks (read-only): PASS
✓ Follow-ups store validation: PASS
=== ALL TESTS PASSED ===
```

---

## ✅ Step 4: Use in Claude Code

**Open a NEW Claude Code session** (or restart current one).

Check skills are loaded:
```
/skills
```

You should see:
- gog-calendar
- gog-email-draft
- gog-email-send
- gog-email-triage
- gog-followups
- gog-tasks

Try using them naturally:
```
"What's on my calendar today?"
"Triage my inbox"
"Create a task to follow up"
"Draft a reply to that email about [topic]"
```

The skills will automatically load and use your GOG CLI!

---

## 🆘 Troubleshooting

### "Authentication failed" Error

**Cause**: OAuth2 credentials not set up correctly

**Solution**: Complete Step 0 above. The most common issues:
- Haven't created OAuth2 credentials in Google Cloud Console
- Credentials expired or invalid
- Haven't granted necessary API scopes

### "gog: command not found"

**Cause**: GOG CLI not installed or not on PATH

**Solution**:
```bash
# Install GOG
brew install gog

# Or add to PATH
export PATH="/path/to/gog:$PATH"
```

### Skills Don't Appear in Claude Code

**Cause**: Symlinks not created in `.claude/skills/`

**Solution**:
```bash
# Run setup script
bash skills/gog/setup-claude-code.sh

# Or check symlinks exist
ls -la .claude/skills/
```

### "Permission denied" or "Insufficient scopes"

**Cause**: OAuth consent didn't include all necessary scopes

**Solution**: Re-authenticate and ensure you grant all permissions:
```bash
gog auth login
# Grant access to Gmail, Calendar, AND Tasks
```

---

## 📚 More Help

- **Main documentation**: `skills/gog/README.md`
- **Command reference**: `skills/gog/COMMAND_REFERENCE.md`
- **API details**: `skills/gog/_shared/references/gog-interface.md`
- **Testing guide**: `skills/gog/_shared/references/testing.md`
- **GOG CLI help**: https://github.com/steipete/gogcli

---

## ⏱️  Time Estimate

- **OAuth2 setup**: 10-15 minutes (first time only)
- **GOG install & auth**: 5 minutes
- **Skills setup**: 1 minute
- **Total**: ~20 minutes for complete setup

After initial setup, everything just works! 🎉
