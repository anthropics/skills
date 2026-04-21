# Hardening Plan Templates

Use these templates after assessment to create actionable improvement plans.
Pick the template matching user's current readiness band.

## Quick Wins (any band)

These actions help regardless of current state:

1. **Enable MFA everywhere** — especially admin accounts, wallets, GitHub, cloud providers
2. **Create an incident contact list** — who to call when things go wrong (SEAL 911, team leads, legal)
3. **Audit who has access to what** — list all accounts with elevated permissions
4. **Set up basic monitoring** — at minimum, alert on auth failures and unusual transactions
5. **Document your most critical assets** — what would hurt most if compromised?

## Critical → Developing

Focus on stopping the bleeding:

### Wallet/Key Security
- [ ] Move from single-key to multisig for any treasury or admin wallets
- [ ] Store seed phrases in hardware wallets, not plaintext
- [ ] Create a key inventory (who has what, where)
- [ ] Set up transaction approval thresholds

### Incident Readiness
- [ ] Write a basic incident response plan (even 1 page is better than nothing)
- [ ] Assign incident roles (who leads, who communicates, who investigates)
- [ ] Save emergency contacts (SEAL 911, legal counsel, exchange contacts)
- [ ] Practice with a tabletop exercise (walk through a hypothetical breach)

### Access Control
- [ ] Require MFA on all accounts
- [ ] Remove shared credentials
- [ ] Create offboarding checklist (revoke access when people leave)
- [ ] Review admin access quarterly

## Developing → Established

Focus on consistency and documentation:

### DevSecOps
- [ ] Add security linting to CI/CD (semgrep, codeql)
- [ ] Implement secret scanning (git-secrets, trufflehog)
- [ ] Require code review for security-sensitive changes
- [ ] Pin dependencies and use lockfiles
- [ ] Set up automated dependency vulnerability scanning

### Monitoring & Detection
- [ ] Centralize logs (SIEM or at minimum structured logging)
- [ ] Set up alerts for: auth anomalies, large transactions, new admin accounts
- [ ] Define escalation procedures for alerts
- [ ] Monitor for leaked credentials (Hudson Rock, dehashed)

### Governance
- [ ] Document security policies (acceptable use, data handling, access control)
- [ ] Assign a security owner (even part-time)
- [ ] Schedule regular security reviews (monthly or quarterly)
- [ ] Create a risk register

### Supply Chain
- [ ] Audit all third-party dependencies
- [ ] Evaluate build pipeline security
- [ ] Implement artifact signing where possible
- [ ] Review vendor security practices

## Established → Advanced

Focus on proactive hardening and automation:

### Security Automation
- [ ] Policy-as-code for infrastructure (OPA, Sentinel)
- [ ] Automated compliance checks
- [ ] Security gates that block deployments on findings
- [ ] Automated incident response playbooks

### Threat Modeling
- [ ] Formal threat model for your architecture
- [ ] Regular red team exercises or penetration testing
- [ ] Bug bounty program (even small scope)
- [ ] Attack surface monitoring

### Advanced Controls
- [ ] Zero-trust architecture for internal services
- [ ] Hardware security modules (HSMs) for critical keys
- [ ] Formal verification for smart contracts
- [ ] Supply chain attestations (SLSA, in-toto)

### Team & Culture
- [ ] Regular security training for all team members
- [ ] Phishing simulations
- [ ] Security champions program
- [ ] Post-incident review process

## Plan Output Format

When presenting a plan, use this structure:

```
## Security Hardening Plan

**Current State:** [readiness band summary]
**Target:** [next band]
**Timeline:** [estimated based on team size/effort]

### Phase 1: Quick Wins (Week 1-2)
- [ ] Action item with specific steps
- [ ] Action item

### Phase 2: Foundation (Week 3-6)
- [ ] Action item
- [ ] Action item

### Phase 3: Strengthen (Week 7-12)
- [ ] Action item
- [ ] Action item

### Ongoing
- [ ] Recurring actions (reviews, training, monitoring)

**Cross-domain benefits:** These actions also improve [related domains]
```

Adapt timeline to team size — solo dev needs longer phases than a 10-person team.
