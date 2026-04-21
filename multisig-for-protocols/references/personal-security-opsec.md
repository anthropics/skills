# Personal Security (OpSec)

## Account Security

### Basic requirements
- 2FA enabled on all accounts (authenticator apps or hardware keys)
- Password manager with unique, strong passwords for every account
- Remove phone numbers from account recovery options where possible
- Regular security checkups and removal of unused app permissions
- Backup email for account recovery (separate from primary email)

### For extra security
**YubiKeys**: Use hardware security keys instead of authenticator apps
- Provides stronger protection against phishing and SIM swapping
- Recommended: 3 keys (primary, backup, secure storage)
- Models: YubiKey 5C NFC, YubiKey 5C Nano

**Cold backup accounts**: Separate email/phone for sensitive account recovery
- Backup / cold accounts are tied to sensitive accounts (AppleID, Telegram, Signal, WhatsApp, Password Manager etc). Such email addresses must never be shared with anyone and kept private to remain secure and not targeted.

Example: random44@gmail is tied to your AppleID, and you are only logged in (the email) on a separate secure device. If your main device (laptop) gets compromised, you will be able to recover your account or revoke sessions, moreover your cold account won't be affected / compromised. It prevents people from targeting your accounts by not knowing your email linked to it.
- Use different providers from primary accounts (Gmail, Proton)
- Only access from secure devices
- Never used for regular communications

## Device Security

### Basic requirements
- Full disk encryption enabled (FileVault/BitLocker)
- Automatic updates enabled on all devices
- Screen lock after 5 minutes inactivity on computers, 30 seconds on mobile
- Strong passcodes (6+ digits or alphanumeric on mobile)
- Endpoint protection software on computers
- No admin rights for daily use accounts (create separate admin account)

### For extra security
**Dedicated signing device**: Clean laptop/tablet used only for multisig operations
- Minimal software installation
- Regular security updates
- Clean restart before each use
- Offline storage when not in use
- Justification: Reduces attack surface for high-value operations

## Communication Security

### Basic requirements

**Signal with verified safety number verification** for multisig communications: You MUST check the codes with the person you are interacting to « verify » them. 
How? Click on any chat > Contact name > View Safety Number > Call on another communication channel to verify them > Click at the bottom "Mark as Verified".
If the account connects on a new device these codes will change & you will receive a security notification.
- Screen lock enabled on mobile devices
- 2FA enabled on backup platforms (Telegram/Discord/Slack)
- Privacy settings maximized on all platforms
- Session management - remove old/unknown devices regularly

### Signal configuration
- Registration lock enabled
- Signal PIN configured
- Hide phone number (use username only)
- Safety number verification for all contacts
- Disappearing messages for sensitive chats

### For extra security
**Enhanced verification**: Advanced safety procedures for critical communications
- Code words for identity verification
- Multiple verification channels for important requests
- Regular communication channel security audits

## Travel considerations

### What to bring
- Primary hardware wallet only (leave backups secure at home)
- Essential devices only (laptop + phone)
- Emergency contact information (offline copy)
- Own chargers and cables

### What NOT to bring
- Seed phrases (never travel with these)
- Backup hardware wallets
- USB drives with sensitive data
- Non-essential devices

### Basic travel security
- Use device locks at all times
- Avoid public WiFi (use mobile hotspot or VPN)
- Don't leave devices unattended in hotel rooms
- Use hotel safes for device storage when out
- Have offline backup of emergency contacts

### For extra security
**Enhanced travel procedures**: Additional precautions for high-risk situations
- Disable biometric unlock at airports/borders (use PIN only) - prevents forced unlocking
- Decline hotel housekeeping services - reduces access to devices
- Advance notification to multisig team (72 hours for critical operations)
- Use separate carrier SIM card for travel communications
- Professional security assessment of travel destinations

## Implementation priority

### Start with basics
Focus on fundamental security practices first
- Password manager + 2FA on all accounts
- Device encryption and screen locks
- Signal setup with safety number verification
- Basic travel security practices

### Add extra security
Implement additional measures based on your risk level and operational needs
- YubiKeys for critical accounts
- Dedicated signing devices for high-value operations
- Enhanced travel procedures for international travel
- Professional security assessments for critical roles

Remember: Perfect security doesn't exist - focus on practical improvements that significantly reduce your risk while remaining operationally feasible.

For the full OpSec article, see [Operational Security](/opsec/overview).

