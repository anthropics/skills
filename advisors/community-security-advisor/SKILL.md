---
name: community-security-advisor
description: Secure Web3 community platforms including Discord, Telegram, and Twitter/X. Use when users ask about server security setup, protecting against raids/scams, admin role configuration, bot security, preventing impersonation attacks, or securing social media accounts. Triggers on questions about "Discord security," "Telegram safety," "protect our community," or "prevent phishing in our server."
---

# Community Security Advisor

Help Web3 projects secure their community platforms against social engineering, raids, and account takeovers.

## Why Community Security Matters

Community channels are prime attack vectors in Web3:
- Compromised Discord/Telegram = phishing links to thousands of users
- Account takeovers can drain treasuries via social engineering
- Impersonation attacks trick users into sending funds
- Raids disrupt operations and damage reputation

## Platform Security Overview

| Platform | Primary Risks | Key Defenses |
|----------|---------------|--------------|
| Discord | Raids, webhook exploits, bot permissions | 2FA requirement, role hierarchy, cold admin |
| Telegram | SIM swaps, MITG attacks, group cloning | Hidden phone, secret chats, admin verification |
| Twitter/X | SIM swaps, phishing, session hijacking | Remove phone, hardware 2FA, app permissions |

## Universal Best Practices

### 1. Strong Authentication
- **Hardware keys** (YubiKey) for all admins
- **Authenticator apps** over SMS (SMS = SIM swap vulnerable)
- **Unique passwords** per platform in password manager
- **Separate 2FA from password manager** (compartmentalization)

### 2. Least Privilege
- Minimum permissions needed for each role
- Regular permission audits (monthly)
- Immediate revocation when team members leave

### 3. Cold Admin Accounts
- Dedicated admin account on separate device
- Never used for browsing or clicking links
- Only accessed for critical server changes
- Different email, different everything

### 4. Phishing Defense
- **Never DM first** - communicate this publicly
- Define official channels clearly
- Warn users about common scam patterns
- Quick response protocol for phishing reports

## Platform Quick Reference

### Discord Essentials
1. Enable 2FA requirement for moderation
2. Set verification level to Medium+
3. Configure AutoMod for spam/links
4. Implement cold admin account
5. Audit bot permissions regularly
6. Use anti-raid bots (Wick, Dyno)

### Telegram Essentials
1. Enable 2-Step Verification (password)
2. Hide phone number (Settings > Privacy)
3. Disable P2P calling
4. Use secret chats for sensitive comms
5. Restrict who can add you to groups
6. Verify group authenticity through multiple channels

### Twitter/X Essentials
1. Remove phone number after verification
2. Use authenticator app or hardware key
3. Enable password reset protection
4. Revoke unnecessary app permissions
5. Log out of old sessions
6. Store backup codes offline

## Common Attack Patterns

### Man-in-the-Group Attack (Telegram)
Attackers create cloned groups impersonating both parties in a deal, relay messages between real users while swapping payment addresses.

**Defense**: Always verify payment details through separate channel (voice call, different platform).

### Discord Webhook Exploit
Compromised webhooks allow attackers to post as official channels.

**Defense**: Audit Server Settings > Integrations regularly, remove unused webhooks.

### Impersonation Attacks
Attackers copy admin profiles (name, picture) and DM users.

**Defense**: Use anti-impersonation bots, verify through public channels, educate community.

## Emergency Response

When community channel is compromised:
1. **Remove compromised account** from admin roles immediately
2. **Post warning** in all channels about the breach
3. **Revoke** all webhooks and bot tokens
4. **Check** for unauthorized role/permission changes
5. **Audit** recent mod actions in logs
6. **Reset** credentials on separate, clean device
7. **Document** what happened for community transparency

## Reference Files

- See `references/platform-security.md` for detailed platform-specific configurations
