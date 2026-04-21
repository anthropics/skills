# Emergency Procedures

When security incidents occur, quick and decisive action is critical. This page covers procedures for key compromise, lost access, and communication breaches.

## Key Compromise

### Immediate Actions (Within 30 Minutes)

1. **Stop operations** - Halt all non-emergency transactions
2. **Notify team** - Alert via all communication channels using emergency notification template
3. **Assess scope** - Determine which keys may be compromised
4. **Escalate** - Contact Security team immediately
5. **Document** - Record timeline and details

### Recovery Process

1. **Isolate** - Quarantine potentially compromised devices
2. **New hardware setup** - Set up fresh wallet with new seed following [Hardware Wallet Setup](/wallet-security/intermediates-&-medium-funds)
3. **Coordinate replacement** - Plan signer replacement transaction with team
4. **Execute replacement** - Replace compromised signer on multisig, following steps for signer rotation in [Secure Multisig Best Practices](/wallet-security/secure-multisig-best-practices)
5. **Verify security** - Confirm new setup before resuming operations

## Lost Key Access

### Immediate Steps

1. **Try backup device first** if available
2. **Contact team immediately** via backup communication channels
3. **Do not panic** - Lost access doesn't mean compromised keys
4. **Document the situation** - Record what happened and when

### Identity Verification Process

Since you can't sign with your key, verify identity through alternative methods:
- **Video call** with other signers
- **Authentication** via verified social media account
- **Other pre-arranged verification methods**

### Replacement Coordination

1. **Generate new hardware wallet** following standard setup procedures in [Hardware Wallet Setup](/wallet-security/intermediates-&-medium-funds)
2. **Verify new address** through identity verification process above
3. **Coordinate timing** with other signers for replacement transaction
4. **Execute replacement** once team confirms identity
5. **Update documentation** with new signer information

## Communication Account Compromise

### If Telegram/Signal/Discord Gets Taken Over

#### Immediate Actions
1. **Assume all recent messages are suspect** - Don't trust recent communication
2. **Use backup channels** to alert team about compromise
3. **Change passwords** and enable additional security on compromised account

#### Team Verification Process

**For the compromised person:**

- Use alternative contact methods (email, phone, other platforms)
- Verify identity through video call or pre-arranged methods
- Provide proof of the compromise (screenshots, platform confirmation)

**For other team members:**

- Verify all recent requests from compromised account
- Cancel any pending transactions initiated via compromised communication
- Require additional verification for any future requests until resolved

#### Recovery Steps

1. **Regain account control** through platform recovery processes
2. **Enable maximum security** (2FA, security keys, session management)
3. **Review recent message history** for unauthorized communications
4. **Alert team** when account is secured and verified clean
5. **Resume normal operations** only after team confirms account security

## Emergency Notification Template

Use this template for security incidents or key compromises:

```
Subject: [URGENT] Multisig Security Incident - [Multisig Name]

Immediate details:
- Multisig address: [ADDRESS]
- Classification: [Impact Level / Operational Type]
- Incident type: [Key Compromise / Communication Failure / System Issue]
- Time of discovery: [TIMESTAMP]
- Reporting signer: [NAME/HANDLE]

Situation summary: [Brief description of what happened and current status]

Immediate actions taken:
□ Stopped non-emergency operations
□ Isolated affected systems
□ Notified team members
□ [Other actions]

Next steps required:
□ Security team assessment
□ Key rotation process
□ Emergency transaction execution
□ [Other actions]

Current multisig status:
- Available signers: [X/Y]
- Communication status: [Operational/Compromised]
- Operational capability: [Full/Limited/Suspended]
```

## Emergency Communication Protocols

### Multi-Channel Notification

- **Primary channel**: Alert via main communication channel
- **Backup channels**: Simultaneously notify via backup platforms
- **Emergency contacts**: Use emergency contact procedures if established

### Identity Verification

- **Code words**: Use pre-established verification phrases
- **Multiple confirmations**: Verify through multiple channels
- **Video verification**: Use video calls for critical confirmations

### Information Sharing

- **Need-to-know basis**: Share only essential information
- **Secure channels only**: Use most secure available communication
- **Documentation**: Record all emergency communications

## Operational Emergency Procedures

### For Emergency Response Multisigs

#### Rapid Response Protocol

1. **Immediate assessment** - Determine scope and urgency
2. **Signer activation** - Contact threshold number of signers
3. **Streamlined verification** - Use minimal verification appropriate for risk level
4. **Execute response** - Implement emergency measures
5. **Post-action review** - Document and assess response effectiveness

#### 24/7 Availability

- **Geographic distribution** - Ensure coverage across time zones
- **Backup signers** - Have additional signers available for activation
- **Communication redundancy** - Multiple ways to reach each signer

### Emergency Drill Procedures

#### Regular Testing Schedule

- **Quarterly**: Communication system tests
- **Bi-annually**: Emergency paging system tests
- **Annually**: Full emergency simulation with all signers

#### Drill Components

1. **Notification test** - Verify all signers receive alerts
2. **Response time measurement** - Track time to threshold signatures
3. **Process verification** - Ensure procedures work under pressure
4. **Documentation review** - Update procedures based on drill results

## Recovery and Post-Incident

### Immediate Recovery

1. **Restore operations** - Resume normal operations once threat is mitigated
2. **Monitor for issues** - Watch for any residual security concerns
3. **Update security measures** - Implement additional controls if needed

### Post-Incident Analysis

1. **Root cause analysis** - Determine how incident occurred
2. **Process improvement** - Update procedures to prevent recurrence
3. **Team debriefing** - Gather lessons learned from all participants
4. **Documentation updates** - Revise emergency procedures based on experience

### Communication

1. **Team notification** - Inform team when incident is resolved
2. **Stakeholder updates** - Notify relevant parties as appropriate
3. **Documentation** - Complete incident report for future reference

## Emergency Contact Information

### Security Team Contact

- **Email**: [Security team email]
- **Emergency escalation**: [24/7 emergency contact if available]
- **Communication**: Use subject line format from emergency notification template

### Internal Escalation

- **Protocol leadership**: [Contact information]
- **Technical team**: [Emergency technical contact]
- **Legal/compliance**: [If regulatory notification required]

## Related Documents

- [Incident Reporting](/multisig-for-protocols/incident-reporting) - Formal incident reporting procedures
- [Communication Setup](/multisig-for-protocols/communication-setup) - Backup communication channels
- [Hardware Wallet Setup](/wallet-security/intermediates-&-medium-funds) - Device replacement procedures
- [Seed Phrase Management](/wallet-security/seed-phrase-management) - Key recovery procedures
- [Personal Security (OpSec)](/multisig-for-protocols/personal-security-opsec) - Account security measures

