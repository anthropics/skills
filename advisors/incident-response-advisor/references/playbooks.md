# Incident Response Playbooks

## Smart Contract Exploit

### Immediate Actions
1. Pause contract if possible
2. Identify affected functions
3. Estimate funds at risk
4. Contact SEAL 911 if significant funds involved

### Investigation
- Get transaction traces (Tenderly, Phalcon)
- Identify attack vector
- Check if vulnerability exists in other contracts
- Determine if attacker can continue

### Recovery
- Deploy patched contract if needed
- Migrate user funds to new contract
- Consider whitehack recovery if funds still at risk
- Engage with attacker if they seem receptive to bounty

---

## Wallet Drainer Attack

### If User Reports Drained Wallet
1. Have them disconnect wallet from all sites immediately
2. Check recent approvals at revoke.cash
3. Move remaining funds to fresh wallet
4. Do NOT use same seed phrase for new wallet

### Common Causes
- Signed malicious transaction (fake airdrop, NFT mint)
- Phishing site that looked legitimate
- Compromised browser extension
- Malware on device

### Prevention Advice
- Use hardware wallet for significant funds
- Verify URLs carefully (bookmark trusted sites)
- Be skeptical of unsolicited DMs
- Never sign transactions you don't understand

---

## Private Key Compromise

### Immediate
1. Transfer all funds to new wallet immediately
2. Rotate all API keys that used that key
3. Check for any authorized contracts to revoke
4. Assume attacker has full access to that address forever

### Investigation
- How was key exposed?
- What systems had access?
- Are other keys potentially compromised?

### Long-term
- Implement hardware wallet requirement
- Review key management procedures
- Consider MPC or multisig for critical keys

---

## DNS/Frontend Hijack

### Signs
- Users reporting unexpected transactions after using your UI
- DNS records changed without authorization
- SSL certificate issues
- Traffic redirected to different server

### Immediate
1. Alert users to stop using frontend (Twitter, Discord)
2. Contact domain registrar
3. Check DNS records
4. Review SSL certificates
5. Audit any code changes

### Prevention
- Registrar lock enabled
- DNSSEC configured
- MFA on registrar account
- Regular DNS monitoring

---

## Social Engineering / Insider Threat

### Signs
- Unauthorized access from valid credentials
- Unusual activity patterns
- Access from unexpected locations
- Data exfiltration indicators

### Response
1. Preserve evidence before confronting
2. Revoke access quietly
3. Forensic review of their activity
4. Legal consultation
5. Report to authorities if warranted

---

## DPRK / Nation-State Actor

### Indicators
- Sophisticated, patient attack
- Focus on high-value targets
- May involve months of reconnaissance
- Often involves social engineering + technical exploit

### Response
1. Engage professional incident response firm
2. Preserve all evidence
3. Report to relevant authorities (FBI, local law enforcement)
4. Do not attempt to negotiate directly
5. Assume they maintain persistence - full security review needed
