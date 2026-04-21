# Google Security

> 🔑 **Key Takeaway:** Enhance your Google account security by implementing robust 2FA, eliminating redundant recovery
> options, and diligently overseeing third-party access.

**Google** provides a wide range of services—from email to file storage. Safeguarding your Google account is among the
most critical steps you can take to protect your personal and professional data. Below are simple yet effective measures
to improve your Google account security.

## Essential Security Measures

>This section does not include Google Suite or more advanced security configurations. For that, refer to the Operational
> Security Framework, under [Google Suite Security](/opsec/old/cloud-third-party/g-suite-security).

### Configure 2FA

Properly setting up two-factor authentication (2FA) is one of the most crucial steps you can take. Disable SMS 2FA to
avoid SIM swaps, and instead use an authenticator app or a hardware security key (preferred).

1. **Go to** [Google 2-Step Verification](https://myaccount.google.com/signinoptions/two-step-verification)
2. **Disable:** "Voice or text message" if it's enabled
3. **Enable:** "Authenticator app" and/or "Passkeys and security keys". You can also can continue using **Google
  prompts**.
4. **Store Backup Codes:** Keep them offline in a secure place

### Remove Recovery Methods

By default, Google allows account recovery using phone numbers and emails. Attackers can exploit these if they
compromise your phone or email.

1. **Go to**: [Google Recovery Phone](https://myaccount.google.com/signinoptions/rescuephone)
2. **Remove:** Any phone number listed
3. **Optional**: If you're confident you won't need standard recovery processes:
   1. **Go to**: [Google Recovery Email](https://myaccount.google.com/recovery/email)
   2. **Remove:** Any recovery email present

### Manage Active Sessions

Keeping track of active sessions helps you detect unauthorized access.

1. **Go to**: [Google Device Activity](https://myaccount.google.com/device-activity)
2. **Terminate:** Any session you don't recognize

### Manage OAuth Applications

Some apps request extensive permissions (e.g., full inbox or file access). Regularly review these to minimize risks.

1. **Go to**: [Google Connections](https://myaccount.google.com/connections)
2. **Review:** Each connected app's permissions; remove if unnecessary or excessive

### Hide Personal Information

Publicly visible personal info can aid attackers in impersonating you.

1. **Go to**: [Google Profile](https://myaccount.google.com/profile)
2. **Check Visibility:** If any info is set to "Anyone," switch it to private if unnecessary
   - **Birthday:** Consider making it private

## Advanced Security Measures

### Extended Security Settings

1. **Start from**: [Google Security](https://myaccount.google.com/security).
2. **Go to**:"Your connect to third-party apps & Services".
3. **Revoke**: all applications that should not be connected.
4. **Go to**: "Log out of all unknown devices"
5. **Turn off**: "skip password when possible" (below previous step)
6. **Go to**: "How you sign in with Google"
7. **Setup**: your 2FA or Security Key in this section
8. **Ensure you do not have a recovery phone setup. No SMS 2FA or phone number on your account at all.**

Once these steps are completed, please change your password. Remember to note down your backup codes.

If using Google Authenticator as a 2FA app on your phone, disconnect it from the cloud, as backup codes are then stored
in the google cloud associated to email. Use it without an account and ensure backup codes are written down offline.

### Advanced Protection Program

For those who are public figures or need heightened security, Google's **Advanced Protection Program** is worth
considering. It requires the use of security keys, limits access to unverified apps, and makes the process of account
recovery more challenging.

1. **Go to** [Google Advanced Protection Program](https://myaccount.google.com/advanced-protection/landing)
2. **Enroll:** Follow the on-screen steps

## Best Practices & Additional Tips

- **Review Security Alerts:** Pay attention to any email or phone notifications from Google regarding unusual sign-ins
  or account changes.
- **Perform a Security Checkup:** Regularly visit [Google's Security
Checkup](https://myaccount.google.com/security-checkup) to identify potential issues and resolve them.
- **Consider** using identity **monitoring** apps like [Push Security](pushsecurity.com).

---

