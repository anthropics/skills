# Discord Security

> 🔑 **Key Takeaway for Discord:** To secure your Discord server, focus on implementing robust access controls and
> enforcing two-factor authentication for all administrators. Regularly audit roles and permissions, and maintain
> vigilant moderation. Educate your community about security best practices to prevent unauthorized access and protect
> against potential threats.

Discord offers a variety of security features that are essential to use. Despite these, users should stay alert to
threats like phishing, which can target server moderators. Such threats may appear as QR code scams, fake login screens,
or misleading direct messages pretending to be from Discord support.

To enhance the security of your Discord server, take into account these suggestions. They cover important aspects like
server settings, roles and permissions, moderation, bots, channels, invites, member screening, logging, and other
security measures.

## Essential Security Measures

### Server Settings

a) **Enable 2FA Requirement for Moderation**

- Go to Server Settings > Safety Setup > Moderation
- Toggle on "Require 2FA for moderation"
- This ensures all moderators have an extra layer of security

b) **Set Appropriate Verification Level**

- Go to Server Settings > Safety Setup > Verification Level
- Choose from: None, Low, Medium, High, Highest
- Recommended: "Moderate" for public servers (requires users are registered on discord for longer then 5 min.)
- Higher levels protect against spammers and raids

c) **Enable Explicit Content Filter**

- Go to Server Settings > Safety Setup > Content Filter
- Set to "Scan messages from all members"
- This automatically blocks messages containing explicit images in non-age-restricted channels
- Age-restricted channels are exempt from this filter

d) **Enable Raid Protection and CAPTCHA**

- Go to Server Settings > Safety Setup > Raid Protection and Captcha
- Activate all relevant settings to require CAPTCHA for new user actions
- This protection uses machine learning to detect and block bot-driven join-raids
- When activated:
  - Sends alerts to a specified channel
  - Requires CAPTCHA verification for new users for one hour after detection

### Roles and Permissions

a) **Implement Role Hierarchy**

- Go to Server Settings > Roles
- Create roles like: Cold Admin, Team, Moderator, & Verified.
- Drag to reorder; higher roles override lower roles
- Restructure the role hierarchy by dragging roles higher or lower in the roles list:
  - Cold Admin
  - Team
  - Moderator
  - Verified

b) **Restrict Administrative Permissions**

- For each role, carefully review the 32 available permissions
- Key permissions to restrict: Administrator, Manage Webhooks, Manage Server, Manage Roles, & Manage Channels
- Never give Admin or Kick permissions to anyone you don't fully trust
- Good permissions for moderators: Manage Channels, Manage Roles, Manage Messages, Ban Members, Delete Messages
- Good permissions for members: View Channels, View audit logs, Create Invite, Manage Messages, Read Message History,
  Connect, Speak & Use Voice Activity, & Ban/Kick/Timeout

c) **Use Channel-Specific Permissions**

- Right-click on a channel > Edit Channel > Permissions
- Set custom permissions for roles or members in specific channels

d) **Use the "View Server as Role" Feature**

- Go to Server Settings > Roles > Select a role > View Server as Role
- This allows you to see what members with a certain role can see and access

## Advanced Security Measures

### Moderation

a) **Set Up Auto-Moderation Rules**

- Go to Server Settings > AutoMod
- Set up rules for: Spam, Harmful Links, Mention Spam, Inappropriate Words
- Configure custom keyword filters and exempted roles
- Customize the response to spam, like blocking the message, sending an alert, or timing out the member
- Add to the existing automod rule to block keywords in a users name, and put Support, Bot, Admin, Tech, Helpdesk, etc.

b) **Configure Timeout Duration**

- Go to Server Settings > Safety Setup > Timeout
- Set default duration (e.g., 60 minutes)
- Educate moderators on using timeouts effectively

c) **Establish Clear Server Rules**

- Create a #rules channel
- Use Discord's built-in rules screening feature
- Include sections on: Behavior, Content, Moderation Actions, Appeals Process

### Extra Moderation Best Practices

a) **Leverage "Default Notifications to Mentions Only"**

- Go to **Server Settings > Overview** and set **Default Notifications** to **Mentions Only**.
- Reduces potential spam notifications for members, making them more vigilant about suspicious or phishing content.

b) **Stay Alert to New Features & Potential Exploits**

- Keep track of newly introduced features such as Threads, Scheduled Events, or Stage Channels.
- Configure their permissions carefully (e.g., who can start or join a Thread) to prevent abuse by spammers or scammers.

c) **Regularly Check Third-Party Bot Security**

- Ensure bots are from reputable sources and receive frequent updates.
- Review bot permissions after each significant update to avoid newly introduced vulnerabilities.

### Bots

a) **Audit Bot Permissions**

- Go to Server Settings > Integrations
- Review each bot's permissions
- Remove unnecessary permissions
- Remove permissions for bots that ask for Admin or other permissions that aren't needed, use least privilege with
  permissions at the role level and channel level.

b) **Remove Unnecessary Bots**

- Uninstall any bots that aren't actively used or needed

c) **Implement Security/Moderation Bots**

- Consider bots like:
  - Dyno for advanced moderation and logging
  - Carl-bot for reaction roles and custom commands
  - Set up security Bots

### Security-Specific Bots

Various third-party Discord bots offer valuable security and protection features, facilitating automated moderation for
your server. In the sections below, we'll explore different categories of security bots and highlight popular options
for each category.

#### Anti-Impersonation Bots

Set up custom rules to prevent other users from joining using the same username and PFP (profile picture) to impersonate
you or other important members of the server. A popular bot in this category is Wick Bot.

#### Anti-Raid Bots

to prevent spam bots from joining your server all at once, an attack known as raiding, you can also set up bots with
particular rules. Beemo is a good example of a bot in this category.

#### Anti-Nuke Bots

This is a monitoring system to observe and note any changes (spontaneous or planned) that take place in your discord
server. Some key observation markers are channel and role creation/deletions, banning or kicking members, and webhook
creation/deletion.

#### Moderation & Link Whitelisting Bots

Only allows approved links to be used in the discord server. A popular bot in this category is Goodknight Bot.

_The bots above are not all-inclusive but rather a recommended list of bots to help protect your Discord server in these
categories._

## Enhanced Server Configuration

### Channels

a) **Organize Channels Logically**

- Use categories to group related channels
- Suggested categories: Information, General, Voice Channels, Topic-Specific

b) **Set Slow Mode Where Needed**

- Channel Settings > Overview > Slow Mode
- Set appropriate cooldown (e.g., 5-30 seconds) for busy channels

c) **Use Age-Restricted Channels Appropriately**

- Channel Settings > Overview > Age-Restricted Channel
- Enable for channels with mature content

### Invites

a) **Disable Permanent Invites**

- Server Settings > Invites
- Un-check "Allow anyone with administrative permissions to create invites"

b) **Set Invite Expiration and Usage Limits**

- When creating an invite: Set "Expire After" and "Max Number of Uses"
- Recommended: 24 hours expiration, 50-100 uses

c) **Regularly Audit Active Invites**

- Server Settings > Invites
- Review and delete unnecessary or old invites

### Member Screening

a) **Enable Membership Screening**

- Server Settings > Safety Setup > Membership Screening
- Toggle on "Enable Membership Screening"

b) **Set Up Screening Questionnaire**

- Add questions about server rules, age verification, etc.
- Require members to agree to rules before joining

c) **Set Up Membership Requirements**

- Require users to react to a message or post an introduction
- This helps filter out bots and spam accounts from joining

### Logging

a) **Enable Audit Logs**

- Ensure admin/mod roles have "View Audit Log" permission

b) **Set Up a Private Logging Channel**

- Create a private channel visible only to admins/mods
- Use a logging bot like Logger or Dyno to send detailed logs

## Best Practices & Administrative Security

### Regular Reviews

a) **Conduct Periodic Permission Audits**

- Monthly: Review all role permissions
- Use a spreadsheet to track changes and justifications

b) **Review and Update Server Rules**

- Quarterly: Assess if rules need updating
- Announce any changes in a dedicated announcements channel

c) **Check for Unused Channels/Roles**

- Bi-annually: Delete or archive inactive channels
- Remove roles that are no longer needed

### Cold Admin Accounts

a) **Set Up a "Cold" Admin Account**

- Create a new account on a separate device never used for chatting or clicking links
- This account is highly resistant to phishing and provides an extra layer of security for the server owner

b) **Secure the Cold Account**

- Create a new email account for the cold account
- Factory reset the device used for this account

c) **Use the Cold Account for Critical Actions**

- Manage bots, modify server settings, and respond to compromises
- Never use this account for regular server activities

d) **Disable QR Code Login on Cold Device**

- In **User Settings > Privacy & Safety**, deselect any quick login or QR scan options.
- Prevents attackers from using QR phishing tactics to hijack this high-privilege account.

### Additional Community Features

a) **Enable the Community Feature (Newer Discord Update)**

- Go to **Server Settings > Community** to activate the Community Feature.
- Unlocks tools like membership screening, server insights, welcome screen, and discovery settings.
- Helps maintain a structured, secure environment by surfacing official rules and critical info to newcomers.

b) **Review Updated Discord Moderation Resources**

- Consult the official [Discord Moderator Academy](https://discord.com/moderation) for ongoing best practices and new
  features.
- Implement recommended strategies (e.g., improved spam filters, updated role recommendations).

## Platform-Specific Security Considerations

### Additional Security Measures

a) **Verification Systems**

- Implement a verification bot like Wick
- Require users to complete an in-channel captcha before accessing the server
- Advance Settings: Have verification bot filter based on account age, PFP set, and timeout for incomplete captcha

b) **Raid Protection**

- Use anti-raid bots like Wick or Dyno
- Configure automatic lock-down settings for suspicious activity

c) **Privacy Settings**

- Server Settings > Privacy Settings
- Disable "Allow direct messages from server members"

d) **Integration Whitelisting**

- Server Settings > Integrations > Allow new integrations to be added by:
- Set to "Only Administrators" to prevent unauthorized bot additions

e) **Server Insights**

- Enable Server Insights for detailed analytics
- Use this data to inform moderation strategies and server improvements

f) **Backup Systems**

- Use a bot like ServerBackup to regularly backup your server configuration
- Store backups securely off-platform

g) **Audit New Integration/Link Safety Settings**

- Regularly review **Server Settings > Integrations** for newly added apps or link shorteners.
- Disable suspicious integrations or automate link scanning with a bot that checks URLs against known phishing
  databases.

h) **Enable Safe Direct Messaging for All Users**

- In **User Settings > Privacy & Safety**, select **Keep Me Safe** for direct messages.
- Encourages moderators and community members to adopt the same setting to minimize phishing DMs.

## Additional Resources

- [Securing Your Server - Discord](https://discord.com/community/securing-your-server)
- [Four Steps for a Super Safe Server -
  Discord](https://discord.com/safety/360043653152-four-steps-to-a-super-safe-server)
- [How to setup a Discord server
  securely](https://www.ledger.com/academy/basic-basics/launch-a-crypto-project-securely/how-to-set-up-a-crypto-project-discord-server-securely)
{/* Test change: vie 23 may 2025 19:59:52 -03 */}

---

