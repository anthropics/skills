---
name: incident-response-advisor
description: Guide users through security incident response for Web3 protocols and individuals. Use when someone reports an active hack, exploit, wallet drain, or security breach. Also triggers on questions about incident preparation, SEAL 911, war rooms, post-incident reports, or communication during crises. Critical for time-sensitive security emergencies.
---

# Incident Response Advisor

Provide immediate, actionable guidance during security incidents in Web3.

## Active Incident Response (URGENT)

### First 5 Minutes - Containment
1. **Pause affected contracts** if you have pause functionality
2. **Revoke compromised credentials** immediately
3. **Alert your security team** via pre-established channels
4. **Do NOT** post publicly yet - attackers monitor social media
5. **Start documenting** everything with timestamps

### SEAL 911 - Emergency Security Response
For active exploits affecting Web3 protocols:
- **Website**: seal.org
- **Service**: 24/7 emergency response from security researchers
- **What to have ready**: Wallet addresses, transaction hashes, timeline

### Information to Gather Immediately
- Affected wallet/contract addresses
- Transaction hashes of suspicious activity
- Timeline of events (when noticed, when started)
- Scope estimate (funds at risk, funds lost)
- Attack vector if known

## Incident Classification

| Severity | Description | Response Time |
|----------|-------------|---------------|
| Critical | Active drain, funds moving | Immediate |
| High | Vulnerability discovered, not exploited | Hours |
| Medium | Potential issue, needs investigation | Days |
| Low | Minor security improvement | Planned |

## Communication Strategy

### Internal (Immediate)
- Alert core team via secure channel (Signal, not Discord)
- Establish incident commander
- Create private war room

### External (After Containment)
- Prepare factual statement
- Notify affected users with actionable steps
- Be transparent but don't speculate
- Provide regular updates

### What NOT to Do
- Don't blame individuals publicly
- Don't share exploit details that could help copycats
- Don't make promises you can't keep
- Don't go silent - even "investigating" is better

## Post-Incident

### Immediate (24-48 hours)
- Complete incident timeline
- Identify root cause
- Implement immediate fixes
- Communicate with affected users

### Report (1-2 weeks)
- Detailed post-mortem
- Root cause analysis
- Remediation steps taken
- Lessons learned
- Future prevention measures

## Reference Files

- See `references/playbooks.md` for specific attack type responses
- See `references/communication-templates.md` for disclosure templates
