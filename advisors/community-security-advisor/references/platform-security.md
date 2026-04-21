# Platform Security Configuration Guide

## Discord Security

### Server Settings Checklist

#### 2FA Requirement
```
Server Settings > Safety Setup > Moderation
Toggle: "Require 2FA for moderation" = ON
```

#### Verification Level
```
Server Settings > Safety Setup > Verification Level
Recommended: "Medium" or higher
- Medium = registered on Discord 5+ minutes
- High = member of server 10+ minutes
- Highest = verified phone
```

#### Content Filter
```
Server Settings > Safety Setup > Content Filter
Set: "Scan messages from all members"
```

#### Raid Protection
```
Server Settings > Safety Setup > Raid Protection and Captcha
Enable: All relevant settings
- Alerts to designated channel
- CAPTCHA for new users during detected raids
```

### Role Hierarchy Setup

Recommended structure (top to bottom):
1. **Cold Admin** - Backup admin on separate device
2. **Team** - Core team members
3. **Moderator** - Community moderators
4. **Verified** - Verified community members
5. **@everyone** - Default role

#### Permission Guidelines

| Role | Key Permissions |
|------|----------------|
| Cold Admin | Administrator (use sparingly) |
| Team | Manage Server, Manage Roles, Ban Members |
| Moderator | Manage Messages, Kick/Timeout Members |
| Verified | View Channels, Send Messages |
| @everyone | Minimal - view public announcements only |

**Never give to untrusted roles:**
- Administrator
- Manage Webhooks
- Manage Server
- Manage Roles
- Mention @everyone

### Bot Security

#### Audit Bot Permissions
```
Server Settings > Integrations
For each bot:
- Review permissions
- Remove unnecessary permissions
- Apply least privilege principle
```

#### Security Bot Categories

| Category | Purpose | Examples |
|----------|---------|----------|
| Anti-Impersonation | Block copied profiles | Wick |
| Anti-Raid | Prevent mass bot joins | Beemo |
| Anti-Nuke | Monitor destructive changes | Wick |
| Link Whitelisting | Block unapproved links | Goodknight |

### AutoMod Configuration
```
Server Settings > AutoMod
Rules to configure:
- Spam: Block repeated messages
- Harmful Links: Block known phishing domains
- Mention Spam: Limit @mentions
- Keyword Filter: Block "support," "admin," "helpdesk" in usernames
```

### Cold Admin Setup

1. Create new Discord account on factory-reset device
2. Create new email specifically for this account
3. Enable 2FA with hardware key
4. Disable QR code login
5. Never use this account for chatting or clicking links
6. Only access for: bot management, server settings, incident response

---

## Telegram Security

### Privacy Settings Path
```
Settings > Privacy and Security
```

### Essential Configuration

| Setting | Path | Recommended |
|---------|------|-------------|
| Phone Number visibility | Privacy > Phone Number | Nobody |
| Phone Number findability | Privacy > Phone Number | My Contacts |
| P2P Calls | Privacy > Calls | Nobody |
| Last Seen | Privacy > Last Seen | Nobody |
| Profile Photo | Privacy > Profile Photo | Everybody (prevents impersonation) |
| Forwarded Messages | Privacy > Forwarded Messages | Nobody |
| Group Invites | Privacy > Groups | Contacts Only / Nobody |

### Two-Step Verification
```
Settings > Privacy and Security > Two-Step Verification
Set: Strong, unique password
Set: Recovery email (not primary email)
Store: Password in password manager (separately from TOTP)
```

### Session Management
```
Settings > Devices > Active Sessions
- Review and terminate unknown sessions
- Set auto-terminate: 1 month
```

### Secret Chats
For sensitive conversations:
```
Open chat > Contact name > Start Secret Chat
Features:
- End-to-end encrypted
- Self-destruct timer available
- No forwarding
- No screenshots (on some devices)
```

### Auto-Delete Messages
```
Settings > Privacy and Security > Auto-Delete Messages
Set: Based on risk tolerance (1 week recommended)
```

### Admin Security for Groups/Channels

**Permission Guidelines:**
- Only grant necessary permissions per admin
- Avoid "Add Users" permission for untrusted admins
- Verify admin identity through voice call before promotion
- Document admin changes

**Group Settings:**
- Enable Slow Mode for large groups
- Restrict media/link sending for new members
- Use discussion groups for channels

### Alternative Phone Numbers

Options for enhanced privacy:
- Google Voice (limited Telegram support)
- Fragment (TON blockchain anonymous numbers)
- Burner numbers

---

## Twitter/X Security

### Phone Number Removal
```
Settings > Your Account > Account Information > Phone
Action: Delete phone number
Important: Generate and save backup codes FIRST
```

### Two-Factor Authentication
```
Settings > Security and Account Access > Security > Two-Factor Authentication

Disable: Text message
Enable: Authentication app and/or Security key

Backup codes: Store offline (printed paper)
```

### Password Reset Protection
```
Settings > Security and Account Access > Security
Enable: Password reset protect
(Requires email/phone to initiate reset)
```

### Session Audit
```
Settings > Security and Account Access > Apps and Sessions > Sessions
Action: Log out of all unrecognized devices
```

### Connected Apps Review
```
Settings > Security and Account Access > Apps and Sessions > Connected Apps
For each app:
- Review permissions
- Revoke unnecessary or untrusted apps
```

### Delegated Accounts
```
Settings > Security and Account Access > Delegate > Delegate Members
Action: Remove unfamiliar accounts
(Attackers use this for persistence)
```

### Privacy Settings
```
Settings > Privacy and Safety
- Disable: "Allow message requests from everyone"
- Enable: "Filter low-quality messages"
- Discoverability: Disable email and phone discovery
```

---

## Cross-Platform Security Checklist

### Weekly Tasks
- [ ] Check for unknown sessions (all platforms)
- [ ] Review recent DMs for phishing attempts
- [ ] Check announcement channels for unauthorized posts

### Monthly Tasks
- [ ] Full permission audit (Discord roles, Telegram admins)
- [ ] Bot permission review
- [ ] Connected app review (Twitter)
- [ ] Webhook audit (Discord)

### Quarterly Tasks
- [ ] Update server rules
- [ ] Security training refresh for mod team
- [ ] Review and update emergency response plan
- [ ] Archive/delete unused channels
