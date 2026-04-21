---
name: seal-community-management
description: >
  Handle security across Discord, Telegram, and social platforms — moderation, social engineering defense, platform-specific security. Use when someone reports a scam in their Discord, asks about Telegram security, needs community moderation guidance, or discusses impersonation attacks. Load seal-incident-management if an actual breach occurred. Load seal-awareness for user-facing security training.
metadata:
  category: security
  tags: ['discord', 'telegram', 'moderation', 'social-engineering']
  related_skills: ["seal-user-team-security", "seal-opsec", "seal-awareness", "seal-incident-management"]
---

# Community Management

Managing security across Discord, Telegram, Twitter, and other community platforms. Covers moderation, social engineering defense, and platform-specific security.

## When to Use
- User asks about community management practices, policies, or procedures
- Incident or scenario involving community management concepts
- Need guidance on community management frameworks or implementations
- Security training or awareness question touching this domain

## Related Domains
This skill connects to: seal-user-team-security, seal-opsec, seal-awareness, seal-incident-management
Use `skill_view("seal-user-team-security")` if the question spans multiple areas.

## Key Concepts
# Community Management
Communities might be the key of many Web3 projects, but they also represent a significant security challenge. From
casual users to top-level executives, everyone within an organization can be targeted by social engineering tactics
across platforms like Telegram, Discord, X (formerly Twitter), Google, and more. When a community channel is
compromised—whether by phishing, fraudulent links, or account takeovers—it can quickly become a vehicle for wider
attacks, putting both users and organizational reputations at risk.
Here, we present essential best practices to safeguard your community. In the following sections, we will explore
platform-specific recommendations in more depth.
## Gotchas
- Telegram group chats are NOT end-to-end encrypted — assume all messages are visible to Telegram
- Discord bots with admin permissions can read all messages — audit bot permissions regularly
- Impersonation accounts often DM members directly — set server rules to auto-flag unsolicited DMs
- Scam bots auto-join servers and DM new members — configure join gate and verification requirements

## References
- Discord
- Google
- Twitter
- Telegram
