# Travel Security Guide

Travel disrupts normal security routines and introduces elevated risks from theft, surveillance, border inspections, and social engineering.

## Before Traveling

### Quick Threat Model
Take 5 minutes to map:
- What assets are you carrying?
- Who might target them?
- How might attacks happen?
- What mitigations can you apply?

### Device Security

**Encryption**
- Enable full-disk encryption (BitLocker, FileVault, LUKS)
- Use strong password/PIN (not just fingerprint)
- Consider encrypting sensitive files individually (VeraCrypt)

**Updates**
- Install latest OS and app updates before leaving
- Don't update during travel (wait for trusted network)

**Backups**
- Backup all devices before travel
- Record device serial numbers and IMEI
- Test "Find My" and remote wipe capabilities

### Account Preparation

**2FA Redundancy**
- Export backup codes for critical accounts
- Store codes in password manager (separate from main vault)
- Disable SMS 2FA where possible
- Consider eSIM over physical SIM (harder to swap)

**Password Manager**
- Enable Travel Mode (1Password) to hide sensitive vaults
- Ensure accessible from multiple devices
- Have offline copy of critical credentials

### Crypto Security

**Hardware Wallets**
- Update firmware before travel
- Test device functionality
- Set strong PIN and BIP39 passphrase
- **NEVER bring seed phrases** - leave at home

**Keys and Access**
- Carry hardware wallets in carry-on (not checked luggage)
- Separate YubiKeys from laptop
- Leave backup keys at home with trusted party

### Phone Lockdown

**Biometrics**
- Consider disabling Face ID/Touch ID
- Know quick-disable: iPhone = side + volume buttons
- Use strong alphanumeric passcode

**iOS Lockdown Mode**
- Enable for high-risk travel
- Restricts features but significantly increases security

**Settings**
- Disable Control Center from lock screen
- Disable notification previews on lock screen
- Disable USB accessories when locked
- Enable "Send Last Location" for Find My

### Minimize Footprint

**Social Media**
- Don't announce travel plans publicly
- Share trip photos AFTER returning
- Tighten privacy settings

**Identity**
- Use burner/throwaway email for event registration
- Remove crypto stickers from devices
- Don't wear crypto-branded clothing
- Have cover story ready ("I work in IT/finance")

### Emergency Planning

- Share itinerary with trusted contact
- Know how to revoke account access
- Have fallback plan for device loss
- Safe words for emergency communication (beware deepfakes)

---

## During Travel

### Network Safety

**Always Prefer**
- Cellular data / personal hotspot
- Trusted VPN

**Avoid**
- Public WiFi (hotel, airport, conference)
- Auto-connect to networks
- AirDrop / Nearby Share enabled
- Bluetooth when not needed

**If Must Use Public WiFi**
- Verify network name with staff
- Use VPN
- No sensitive transactions
- Assume all traffic is monitored

### Device Handling

**Physical Security**
- Never leave devices unattended
- Use cable lock for laptop if stepping away
- Use hotel safe (but assume not fully secure)
- Keep hardware wallets on person

**Separation Principle**
- Keep YubiKey separate from laptop
- Keep hardware wallet separate from phone
- Different bags = harder to lose everything at once

**Auto-Lock**
- Short timeout (30 seconds - 1 minute)
- Require password on wake

### USB Threats

**Juice Jacking**
- Avoid public USB charging stations
- Use your own charger + wall outlet
- Use USB data blocker if must use USB

**Unknown Devices**
- Never plug in random USB drives
- Decline free USB sticks at events
- Disable USB autorun

### Screen Privacy

**Shoulder Surfing**
- Use privacy screen filter
- Sit with back to wall
- Shield keypad when typing passwords
- Don't log into critical accounts in public

**Hidden Cameras**
- Scan accommodations for unusual devices
- Check smoke detectors, clocks, USB chargers
- Cover/unplug suspicious items

### OpSec in Public

- Don't discuss sensitive matters where eavesdropping possible
- Don't share accommodation details with strangers
- Don't give phone to others (disable Telegram phone sharing)
- Blend in - don't advertise crypto involvement
- Use alias on conference badge if possible

### Crypto Transactions

If you MUST transact while traveling:
- Use your own hardware wallet + laptop
- Use secured network (VPN + cellular)
- Private location only
- Verify all addresses multiple times
- Consider requiring extra multisig signer

---

## Returning Home

### Account Review

- Change passwords for accounts used on trip
- Do this from trusted network, not airport WiFi
- Check email filters for unauthorized rules
- Review crypto withdrawal addresses
- Check connected app permissions

### Device Inspection

- Run antimalware scans
- Check for unusual apps or processes
- Watch for abnormal battery drain
- If high-risk trip: consider full wipe and restore

### Hardware Wallet Check

- Verify firmware hasn't changed
- Check device for tampering signs
- If suspicious: transfer assets to new wallet

### Post-Trip Review

- Note any security incidents or close calls
- Report concerns to security team
- Update threat model based on experience
- Disable travel-specific eSIMs/accounts
- Re-enable hidden password vaults

---

## High-Risk Travelers

Additional precautions for executives, key holders, high-profile individuals:

### Burner Devices
- Travel with clean, minimal devices
- No sensitive data stored locally
- Access systems via VPN/VDI only
- Treat as expendable - wipe after trip

### Border Crossings
- Power off devices before landing
- Have encryption passphrase memorized
- Know legal rights per country
- Consider carrying "nothing incriminating"
- Use dedicated email for government forms

### Enhanced Protection
- iOS Lockdown Mode enabled
- Signal with disappearing messages
- Faraday bag for phones (blocks signals)
- Tamper-evident bags for devices
- Weigh devices before/after (detect implants)

### Crypto Key Protection
- Temporarily require extra multisig signer
- Keep keys geographically split
- Use duress PIN (decoy account)
- Daily check-ins with security team
- Pre-agreed emergency protocols

### Post-Trip
- Treat all devices as compromised
- Full wipe and rebuild
- Restore from known-good backups
- Security debrief with team
