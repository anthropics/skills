# GOG Skills Setup Checklist

Use this checklist to set up GOG Personal Assistant skills.

## 📋 Setup Checklist

### ☐ Step 0: Google Cloud OAuth2 Credentials

**⚠️  MUST DO FIRST**

- [ ] Go to https://console.cloud.google.com/
- [ ] Create a new Google Cloud project (or select existing)
- [ ] Enable Gmail API
- [ ] Enable Google Calendar API
- [ ] Enable Google Tasks API
- [ ] Create OAuth2 credentials:
  - [ ] Navigate to: APIs & Services → Credentials
  - [ ] Click: Create Credentials → OAuth client ID
  - [ ] Application type: **Desktop app**
  - [ ] Download credentials JSON file
- [ ] Configure OAuth consent screen (if prompted)
  - [ ] Add Gmail, Calendar, Tasks scopes
  - [ ] Add your email as test user

**Detailed guide**: https://github.com/steipete/gogcli?tab=readme-ov-file#1-get-oauth2-credentials

**Time estimate**: 10-15 minutes

---

### ☐ Step 1: Install GOG CLI

- [ ] Install GOG CLI:
  ```bash
  brew install gog  # macOS
  # Or download from: https://github.com/steipete/gogcli/releases
  ```
- [ ] Verify installation:
  ```bash
  gog --version
  # Should show: v0.9.0 or later
  ```

**Time estimate**: 2-5 minutes

---

### ☐ Step 2: Authenticate GOG

- [ ] Run authentication:
  ```bash
  gog auth login
  ```
- [ ] When prompted, paste your:
  - [ ] OAuth2 Client ID (from credentials JSON)
  - [ ] OAuth2 Client Secret (from credentials JSON)
- [ ] Browser opens - grant permissions:
  - [ ] Select your Google account
  - [ ] Review requested permissions
  - [ ] Click "Allow"
- [ ] Verify authentication works:
  ```bash
  gog gmail search "is:inbox" --max 1
  # Should show an email, not auth error
  ```

**Time estimate**: 2-3 minutes

---

### ☐ Step 3: Set Up Skills for Claude Code

- [ ] Navigate to skills repository:
  ```bash
  cd /path/to/skills
  ```
- [ ] Run setup script:
  ```bash
  bash skills/gog/setup-claude-code.sh
  ```
- [ ] Choose installation type:
  - [ ] Option 1: Project-specific (this repo only)
  - [ ] Option 2: Global (all Claude Code sessions)
  - [ ] Option 3: Both
- [ ] Verify symlinks created:
  ```bash
  ls -la .claude/skills/
  # Should show 6 gog-* symlinks
  ```

**Time estimate**: 1 minute

---

### ☐ Step 4: Verify and Test

- [ ] Run environment validation:
  ```bash
  bash skills/gog/_shared/scripts/validate_env.sh
  ```
  Expected: "=== VALIDATION PASSED ==="

- [ ] Run smoke tests:
  ```bash
  bash skills/gog/_shared/scripts/smoke_test.sh
  ```
  Expected: "=== ALL TESTS PASSED ===" (6/6 passed, 1 skipped)

- [ ] Open NEW Claude Code session (or restart current)

- [ ] Check skills are loaded:
  ```
  /skills
  ```
  Expected: 6 GOG skills listed

- [ ] Try a skill:
  ```
  What's on my calendar today?
  ```
  Expected: Claude loads gog-calendar skill and shows your schedule

**Time estimate**: 3-5 minutes

---

## ✅ Setup Complete!

If all checkboxes above are checked, you're ready to use GOG Personal Assistant!

### Daily Usage

Now you can naturally interact with your email, calendar, and tasks:

**Email:**
- "Triage my inbox"
- "Draft a reply to the email from [person]"
- "YES, SEND" (to send a draft)

**Calendar:**
- "What's on my calendar today?"
- "When am I free tomorrow?"
- "Schedule a meeting with [person] for [time]"

**Tasks:**
- "What should I focus on today?"
- "Create a task to [action]"
- "Mark task [id] as done"

**Follow-ups:**
- "Track follow-up for that email"
- "What emails am I waiting on?"
- "Draft a reminder for [person]"

---

## 🆘 Common Issues

### ❌ "Authentication failed"

**You skipped Step 0!**

Go back and complete the Google Cloud OAuth2 credentials setup:
👉 https://github.com/steipete/gogcli?tab=readme-ov-file#1-get-oauth2-credentials

Then run: `gog auth login`

### ❌ "gog: command not found"

**GOG CLI not installed.**

Install it:
```bash
brew install gog
# Or download from: https://github.com/steipete/gogcli/releases
```

### ❌ Skills don't appear in Claude Code

**Symlinks not created.**

Run:
```bash
bash skills/gog/setup-claude-code.sh
```

Then restart Claude Code.

### ❌ "Permission denied" or "Insufficient scopes"

**OAuth consent didn't grant all permissions.**

Re-authenticate:
```bash
gog auth login
```

Make sure you click "Allow" for ALL permissions (Gmail, Calendar, Tasks).

---

## 📞 Need Help?

- **Setup issues**: See `skills/gog/README.md` (detailed docs)
- **Command syntax**: See `skills/gog/COMMAND_REFERENCE.md`
- **OAuth2 help**: https://github.com/steipete/gogcli?tab=readme-ov-file#1-get-oauth2-credentials
- **Testing**: See `skills/gog/_shared/references/testing.md`

---

## ⏱️  Total Setup Time

- First time (with OAuth2): **~20 minutes**
- Already have OAuth2: **~5 minutes**
- Already authenticated: **~1 minute**

Worth it for a personal AI assistant! 🚀
