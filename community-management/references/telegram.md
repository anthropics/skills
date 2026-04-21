# Telegram Security

> 🔑 **Key Takeaway:** Stay vigilant with group chats on Telegram. Implement verification steps and secure communication
> practices to protect against sophisticated interception attacks.

While **Telegram** is widely used in the crypto community, it's crucial to understand its security limitations. Telegram
**does not** offer end-to-end encryption (**E2EE**) by default, which means your messages could potentially be accessed
by third parties. Additionally, Telegram's reliance on phone numbers for account creation can expose users to SIM
swapping attacks, and its peer-to-peer call feature can reveal your IP address to other users. If **E2EE** is a
priority, consider using [Signal](https://signal.org/).

However, if you choose to use **Telegram**, the following best practices can help enhance your security.

## Essential Security Measures

### Configure 2FA

Telegram sign-ups require a phone number, but you can also enable two-factor authentication via a password—your main
protection if you're ever SIM-swapped. **Don't reuse this password anywhere else.**

1. **Go to**: **Settings > Privacy and Security > Two-Step Verification**
2. **Set**: A strong password and recovery email (store both in a password manager)

### Hide Your Phone Number

Making your phone number visible can expose you to unwanted contact or social engineering attacks. Restricting
visibility helps safeguard your personal info.

1. **Go to**: **Settings > Privacy and Security > Phone Number**
2. **Who can see my phone number?**: Select **Nobody**
3. **Who can find me by my number?**: Select **My contacts**

### Disable P2P Calling

By default, Telegram calls can connect you *directly* to the other user, potentially revealing your IP address.

1. **Go to**: **Settings > Privacy and Security > Calls**
2. **Use peer-to-peer with**: Select **Nobody**

### Manage Inactive Sessions

Telegram supports auto-terminating inactive sessions. You can also manually review and end any suspicious active
sessions.

1. **Go to**: **Settings > Devices > Active sessions**
2. **Review**: Delete any sessions you don't recognize
3. **Auto-terminate**: Set inactive sessions to end after **1 month**

### Implement Device-Level Security

Securing the device you use for Telegram is crucial for preventing unauthorized access to your account and messages.

1. **Enable Full Device Encryption**:
   - Ensure your device has full disk encryption enabled
   - For iOS: This is enabled by default with a passcode
   - For Android: Go to **Settings > Security > Encryption** and follow instructions

2. **Set Strong Device Passcodes**:
   - Use alphanumeric passwords rather than simple PINs
   - Enable biometric authentication as a secondary measure

3. **Keep Your Device Updated**:
   - Install OS updates promptly to patch security vulnerabilities
   - Update Telegram to the latest version regularly

4. **Install Security Software**:
   - Use reputable anti-malware software on your device
   - Consider privacy-focused apps that detect network anomalies

5. **Secure Your Backups**:
   - Ensure any device backups containing Telegram data are encrypted
   - Be cautious about cloud backups that might store Telegram messages

## Advanced Security Measures

### Consider Using a Different Phone Number

Even if you implement all the recommended security measures, there are still valid reasons to use a separate phone
number. For instance, it can help prevent your contacts from discovering your Telegram account or reduce the risk of
accidental number exposure. This is particularly important because the **"Share My Phone Number"** option is enabled by
default whenever you add a new contact.

#### Using a VoIP Number

Telegram restricts many VoIP providers, but services like [Google Voice](https://voice.google.com/) or
[Burner](https://www.burnerapp.com/) might work. Purchase a burner number solely for Telegram if you prefer additional
anonymity.

#### Using an Anonymous Number

In December 2022, Telegram introduced support for anonymous numbers purchased through its [TON](https://ton.org/)
blockchain infrastructure. You can also check out [Fragment](https://fragment.com/) for such options.

### Turn On Auto-delete Messages

Consider the photo you shared with a friend several months ago. While it might have slipped your mind, an attacker who
gains access to your account could find such information quite valuable.

1. **Go to**: **Settings > Privacy and Security > Auto-Delete Messages**
2. **Set**: Choose a time frame (e.g., 1 week) based on your risk tolerance

### Use Secret Chats for Enhanced Privacy

For conversations that require an extra layer of security, use Telegram's Secret Chats, which offer **end-to-end
encryption**.

1. **Start a Secret Chat**: Open the chat with the desired contact, tap on their name, and select **Start Secret Chat**
2. **Benefits**:
   - Messages are encrypted and can only be read by you and the recipient
   - Offers self-destruct timers for messages
   - Prevents forwarding of messages to other chats

### Regularly Update the Telegram App

Ensure you are always using the latest version of Telegram to benefit from the newest security patches and features.

1. **Check for Updates**: Visit your device's app store regularly
2. **Enable Automatic Updates**: If possible, turn on automatic updates to stay current

### Be Cautious with Third-Party Bots and Integrations

Third-party bots can enhance functionality but may also introduce vulnerabilities.

1. **Use Trusted Bots**: Only add bots from reputable sources
2. **Review Permissions**: Limit the permissions you grant to bots
3. **Regular Audits**: Periodically review and remove unnecessary bots

### Manage Group and Channel Admin Permissions

If you manage Telegram groups or channels, properly configuring admin permissions is crucial for maintaining security.

1. **Limit Admin Privileges**:
   - Go to your group/channel, tap the group name, select **Administrators**
   - Only grant necessary permissions to each admin
   - Avoid giving "Add Users" permission to untrusted admins

2. **Implement Admin Verification**:
   - Establish a verification process before promoting members to admin
   - Use separate channels (like voice calls) to confirm admin identities
   - Document when admin changes occur and why

3. **Configure Group Settings**:
   - Restrict member actions such as sending media or links
   - Enable "Slow Mode" for large groups to prevent spam
   - Use discussion groups for channels to control information flow

4. **Audit Admin Activities**:
   - Regularly review admin actions in the group
   - Remove inactive or suspicious admins
   - Consider using admin action logs if available

5. **Handle Admin Transitions Securely**:
   - Have protocols for transferring ownership if needed
   - Revoke admin rights immediately when team members leave

## Enhanced Privacy Settings

### Passcode Lock

- **Settings > Privacy and Security > Passcode Lock:** This feature adds a passcode to access your Telegram app after a
  period of inactivity. The default setting is "away for 1 hour."
- **Recommendations:**
  - **Store Passcode Securely:** Do not lose this passcode—store it offline if needed.
  - **Unique Passcode:** Ensure it is different from your phone's unlock passcode.

### Privacy and Security Settings

**Go to:** Settings > Privacy and Security

#### Security

##### Two-Step Verification

- **Overview:** Telegram does not require a login by default. However, you can set up a password that acts as a "second"
  2FA method when logging in from a new device.
- **Security Measures:**
  - **SMS Codes:** Telegram sends a code via SMS, which is not secure.
  - **Email Recovery:** Offers email recovery, which is more secure but lacks options for authenticator apps or hardware
    keys.

- **Important:**
  - **Backup Password:** If you lose this password, access to your account may be compromised.
  - **Secure Storage:** Write it down offline and ensure it is not lost.

#### Additional Privacy Settings

Consider adjusting the following settings based on your country, usage, and purpose for using Telegram:

- **Phone Number:** Set to **Nobody** to prevent exposure.
- **Last Seen & Online:** Set to **Nobody** to enhance privacy.
- **Profile Picture:** Set to **Everybody** to stop scammers from impersonating your profile picture.
- **Bio:** Set to **Nobody** (depending on use of Telegram).
- **Date of Birth:** Set to **Nobody**.
- **Forwarded Messages:** Set to **Nobody**.
- **Calls:** Set to **Nobody** or **Contacts Only** (depending on use of Telegram).
- **Voice Messages:** Set to **Contacts Only** (depending on use of Telegram).
- **Messages:** Set to **Everybody** or **Contacts Only** (depending on use of Telegram).
- **Invites:** Set to **Contacts Only** or **Nobody** to prevent being added to random groups that may impersonate
  legitimate groups and lead to scams.

### Data Settings

**Go to:** Settings > Privacy and Security > Data Settings

- **Sync Contacts:** Disable (depending on use of Telegram) to prevent syncing your contacts.
- **Suggest Frequent Contacts:** Disable (depending on use of Telegram) to avoid unsolicited contact suggestions.

## Best Practices & Tips for Safe Use

- **Use Secret Chats:** When messaging someone, create a 'secret' chat to ensure encrypted 1:1 communication, providing
  end-to-end encryption for sensitive transactions.
- **Verify Group Invites and Authenticity:** Always triple-check group invitations and confirm the legitimacy of group
  chats through separate channels to avoid joining impostor groups that share malicious links.
- **Beware of Unsolicited DMs:** Never trust direct messages from anyone sending links or posing as "support,"
  "exchanges," or "team" members.
- **Double-Check Payment Details:** Verify payment information through multiple methods before transferring funds to
  prevent fund redirection.
- **Block and Report Scammers:** Use the block function to prevent further contact, and report spammers/scammers instead
  of just deleting chats.
- **Limit Group Permissions:** Restrict who can add members to groups to prevent unauthorized cloning and protect
  against raids.

### Educate Community Members on Security Practices

If you're managing a community on Telegram, educating your members about security is vital for collective protection.

1. **Regular Security Announcements**:
   - Schedule periodic reminders about security best practices
   - Pin important security announcements in your group/channel
   - Create dedicated security FAQ channels or posts

2. **Clear Verification Procedures**:
   - Establish and communicate how official communications will occur
   - Create verification steps for new members to follow
   - Document how to verify the authenticity of admins and official messages

3. **Threat Awareness Training**:
   - Share examples of common scams targeting your community
   - Post screenshots of phishing attempts (with sensitive info redacted)
   - Explain the "Man-in-the-Group Attack" and how to avoid it

4. **Incident Reporting Protocol**:
   - Create clear guidelines for reporting suspicious activity
   - Designate security-focused admins to handle reports
   - Acknowledge reports publicly (without specifics) to encourage vigilance

5. **Security Resources**:
   - Develop simple, accessible security guides for members
   - Share platform-specific security updates when Telegram releases them
   - Create a security checklist for new community members

- **Exercise Caution with Mini Apps:** Avoid logging in or providing information to mini apps that redirect outside of
  Telegram. Triple-check the username of the mini app to ensure its legitimacy, as Telegram lacks a bot verification
  system. Never download or run any commands from Telegram on your device.
- **Enhance Privacy with a VPN:** *Advanced tip:* Set up a proxy or VPN to hide your IP address while using the Telegram
  app.
- **Stay Vigilant Against Scam Ads:** Be aware that anyone can post ads in channels, with 99% being scam ads. Exercise
  caution when interacting with advertisements.

## Platform-Specific Risks: Man-in-the-Group Attack

Attackers can exploit Telegram's group chat features to intercept and manipulate communications between two parties.
Here's a concise example of how such an attack might occur:

### Scenario: Intercepting a Payment Deal

#### Step 1: Initial Communication

- **Alice** and **Bob** decide to finalize a cryptocurrency deal using a Telegram group chat named **"Crypto Deals"**.

#### Step 2: Attackers Create Cloned Groups

- **Attacker 1** creates **Group A** impersonating **Alice**.
- **Attacker 2** creates **Group B** impersonating **Bob**.

#### Step 3: Replicating Conversations

- **In Group A (Impersonating Alice):**
  - The attacker, posing as Alice, relays Alice's messages from Group B to maintain the conversation.

- **In Group B (Impersonating Bob):**
  - The attacker, posing as Bob, mirrors Bob's messages from Group A, acting as a middleman without altering the
    content.

#### Step 4: Swapping Payment Details

- **In Group A:**
  - Fake Alice and Bob agree to the terms of the deal.
  - Bob shares his payment address.

- **In Group B:**
  - Fake Bob shares his swapped payment address.
  - The conversation continues normally, with neither Alice nor Bob aware of the swap.

#### Step 5: Execution of the Scam

- **Alice** sends the payment to what she believes are Bob's details but are actually those of Fake Bob.
- The attacker now controls both ends of the conversation, having successfully redirected the funds.

---

