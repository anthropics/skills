---
name: web3-security-awareness
description: Provide general Web3 security awareness education and threat recognition guidance. Use when users ask about common scams, phishing attacks, social engineering in crypto, security best practices for individuals, or building security culture in organizations. Triggers on questions about staying safe in crypto, recognizing scams, security training, or general Web3 security advice.
---

# Web3 Security Awareness

Educate users on security threats and best practices in the Web3 ecosystem.

## Key Takeaway

Your awareness is your strongest defense. Recognizing red flags and questioning unexpected requests prevents most attacks.

## Common Attack Vectors

### Social Engineering
| Attack Type | How It Works | Defense |
|-------------|--------------|---------|
| Fake Job Offers | Malicious "interview" tasks run malware | Verify company, never run unknown code |
| Impersonation | Attackers pose as team members/support | Verify through official channels |
| Urgency Tactics | "Act now or lose funds" pressure | Take time, verify independently |
| Airdrop Scams | Free tokens require wallet connection | Legitimate airdrops don't ask for signatures |

### Phishing
| Attack Type | How It Works | Defense |
|-------------|--------------|---------|
| Fake dApps | Cloned UI steals signatures | Bookmark trusted sites, verify URLs |
| Discord/Telegram DMs | "Support" requests seed phrase | Real support NEVER asks for seeds |
| Email Phishing | Links to malicious sites | Don't click email links, go direct |
| DNS Hijacking | Real domain points to fake site | Verify contract addresses independently |

### Technical Attacks
| Attack Type | How It Works | Defense |
|-------------|--------------|---------|
| Malicious Approvals | Unlimited token approval drained | Use revoke.cash, limit approvals |
| Supply Chain | Compromised dependencies | Audit dependencies, pin versions |
| Clipboard Malware | Replaces copied addresses | Always verify pasted addresses |

## Security Principles

### Trust, But Verify
- Verify identities through multiple channels
- Don't trust caller ID, display names, or profile pictures
- When in doubt, reach out through known-good contact methods

### Defense in Depth
- No single security measure is perfect
- Layer protections (hardware wallet + limited approvals + awareness)
- Assume any single layer can fail

### Least Privilege
- Only grant permissions actually needed
- Revoke access when no longer required
- Use separate wallets for different risk levels

## Individual Security Checklist

### Essential
- [ ] Hardware wallet for significant funds
- [ ] Unique passwords for crypto accounts
- [ ] MFA enabled everywhere (hardware key preferred)
- [ ] Seed phrase stored offline securely
- [ ] Bookmarks for frequently used sites

### Recommended
- [ ] Separate browser/profile for crypto
- [ ] Token approval monitoring (revoke.cash)
- [ ] Burner wallet for new mints/experiments
- [ ] Regular security checkups
- [ ] Security-focused social media habits

## Organizational Security Culture

### Building Awareness
1. Security onboarding for all employees
2. Regular (quarterly) awareness training
3. Phishing simulations
4. Security tips in team communications
5. Reward reporting of suspicious activity

### Key Behaviors to Instill
- Question unexpected requests
- Verify before acting
- Report suspicious activity (no blame)
- Assume breaches will happen
- Know incident response procedures

## Reference Files

- See `references/scam-patterns.md` for detailed scam breakdowns
- See `references/security-tips.md` for shareable security tips
