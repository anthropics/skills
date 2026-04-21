# X (Twitter) Security

> 🔑 **Key Takeaway for Twitter (X):** To secure your Twitter account, prioritize using an authenticator app or security
> key over SMS-based 2FA, remove your phone number, and regularly review third-party app permissions. Ensure your
> recovery settings are robust and frequently monitor account activity to safeguard your online presence and maintain
> community trust.

A compromised **X** account can harm not only you but also your community. Attackers often use phishing tactics—like SIM
swaps or fake login screens—to seize control of your profile. A few simple steps can significantly reduce these risks.

Securing your Twitter account is not particularly hard or time consuming, so consider following the best practices
below.

## Essential Security Measures

### Remove your phone number

There are no good reasons to keep a phone number attached to your account, and it's the easiest way for a hacker to get
into your account after SIM swapping you. Getting verified requires you to add a phone number, but you can remove it
afterward.

1. **Go to:** [Phone Settings](https://x.com/settings/phone)
2. **Remove:** Click **Delete phone number** if one is listed.

After removing your phone number, it's crucial to navigate to Settings > Security and Account Access > Security >
Two-Factor Authentication > Backup Codes. Store these codes offline, just like your seed phrase. Anyone with these codes
can bypass your 2FA, so it's extremely important to write them down and keep them secure. Remember, when you change
your password, new backup codes are generated.

### Configure 2FA

Two-factor authentication is a great way to keep hackers at bay, but it's not foolproof if you're relying on SMS 2FA and
someone gets hold of your phone number. It's generally better to use an authenticator app or a security key. Also,
ensure your backup codes are stored safely, ideally printed on paper rather than saved on your device.

1. **Go to:** [Login Verification](https://x.com/settings/account/login_verification)
2. **Disable:** Un-check **Text message**
3. **Enable:** Choose **Authentication app** and/or **Security key**
   1. If using an authentication app, store your secret (TOTP) in a reliable app (Authy, Google Authenticator), but
   disable [syncing](https://retool.com/blog/mfa-isnt-mfa) for added security.
   2. If using security keys, keep at least two (e.g., from [Yubico](https://www.yubico.com/)) in case one fails.
4. Under **Additional methods**, below, select **Backup codes** and create a new backup code. Store this code securely,
  offline, ideally in a physical format like a printout, to ensure that if one device is compromised, the code remains
  safe.

### Enable password reset protect

Twitter provides a feature that requires users to input their email or phone number linked to the account before they
can initiate a password reset. This adds an extra layer of security by ensuring that hackers must know your email,
rather than receiving a hint.

1. **Go to:** [Security Settings](https://x.com/settings/security)
2. **Toggle On:** Check **Password reset protect**.

## Advanced Security Measures

### Revoke access from delegated accounts

It's possible to allow other accounts to access your Twitter account. If your account was previously compromised,
attackers could exploit this feature to maintain access even after you've regained control.

1. **Go to:** [Delegate Members](https://x.com/settings/delegate/members)
2. **Review:** Remove any unfamiliar accounts.

### Revoke access from unnecessary apps

It's possible that you've linked your Twitter account to several apps, and some might have more permissions than
necessary. To check and manage these permissions, follow these steps:

1. **Go to:** [Connected Apps](https://x.com/settings/connected_apps)
2. **Review:** Check each app's permissions and **Revoke** if it's no longer needed or trusted.

### Log Out of Unnecessary Sessions

It's possible you've accessed Twitter from devices you don't regularly use, like a friend's phone. Review your active
sessions and log out of any that are unfamiliar or unnecessary.

Old sessions on unfamiliar devices can be risky.

1. **Go to:** [Sessions](https://x.com/settings/sessions)
2. **Log Out:** For any device or session you don't recognize.

### Verify Your Email is Current

If you've changed your email since creating your Twitter account, ensure your current email is linked to receive
security alerts and updates.

1. **Go to:** [Email Settings](https://x.com/settings/email)
2. **Confirm:** Update to your current email if needed.

### Refresh Your Password

Using a unique password for Twitter is crucial. If you haven't set one, now is the time to do so.

1. **Go to:** [Password Settings](https://x.com/settings/password)
2. **Change:** Select a long, complex password.

## Best Practices & Additional Tips

- **Disable Email and Phone Discoverability**
  - **Go to:** [Discoverability and Contacts](https://x.com/settings/contacts)
  - It is recommended to turn both email and phone discoverability off.
- **Privacy & Safety Settings:**
  - In [Privacy & Safety](https://x.com/settings/privacy_and_safety), consider disabling "Allow message requests from
    everyone" to limit spam DMs and phishing attempts and enabling "Filter low-quality messages".
- **Monitor for Suspicious Alerts:**
  - X (Twitter) may notify you about unusual activity. If you suspect a breach, log out of all sessions, revoke
    suspicious apps, and change your password immediately.
- **Use Unique Recovery Methods:**
  - If you choose to use a recovery phone number, which we generally strongly advise against, make sure it isn't your
    main mobile number. Instead, use a separate VoIP or alternative line to minimize the risk of SIM swapping.
- If you received an email about any content moderation, login, or any email from "X"; ensure the email is from "@x.com"

---

