---
name: insider-threat-advisor
description: Provide guidance on detecting and mitigating insider threats in Web3 organizations, with focus on DPRK IT workers. Use when users ask about hiring security, employee vetting, detecting malicious insiders, DPRK/North Korean hackers posing as developers, or handling suspected insider compromise. Triggers on questions about freelancer security, contractor vetting, or suspicious employee behavior.
---

# Insider Threat Advisor

Help organizations identify, prevent, and respond to insider threats targeting Web3 projects.

## DPRK IT Workers - Overview

North Korean operatives work as freelance developers to:
1. Generate revenue for the regime (salaries fund military)
2. Gain access for future hacking operations
3. Introduce vulnerabilities into codebases
4. Exfiltrate sensitive information

**Scale**: Thousands of DPRK IT workers operate globally, targeting crypto/Web3 heavily.

## Red Flags During Hiring

### Resume/Profile Indicators
- Generic GitHub profile with recent activity spike
- LinkedIn profile with limited connections/history
- Education/work history difficult to verify
- Multiple similar profiles with slight variations
- Stock photo or AI-generated profile picture

### Interview Red Flags
- Reluctance to turn on camera
- Audio/video sync issues (may indicate real-time coaching)
- Inconsistency between resume skills and interview performance
- Inability to discuss past work in detail
- Unusual payment requests (specific countries, crypto-only)

### Technical Indicators
- Working hours inconsistent with claimed timezone
- IP addresses from unexpected locations
- Multiple people seemingly using same account
- Poor Git hygiene (suggests credential sharing)
- Resistance to identity verification

## Hiring Hardening Checklist

1. **Video interview required** - Camera on, verify face matches profile
2. **Live coding assessment** - Screen share, watch them code in real-time
3. **Reference verification** - Actually call references, verify employment
4. **Identity verification** - Use services like Persona, Jumio
5. **Background check** - Where legally permitted
6. **Probationary access** - Limited permissions initially
7. **Geographic verification** - Confirm actual location

## If You Suspect You Hired One

### Immediate Actions (Do Quietly)
1. **Do NOT alert the individual**
2. Document all evidence
3. Restrict access to sensitive systems
4. Preserve all communications and code
5. Consult legal counsel about sanctions compliance

### Investigation
- Review all code contributions for backdoors
- Check access logs for data exfiltration
- Identify what sensitive info they accessed
- Determine scope of potential compromise

### Reporting
- Consider reporting to FBI (US) or local authorities
- Consult sanctions compliance attorney
- Preserve evidence for potential investigation

## Organizational Risks

| Risk | Description |
|------|-------------|
| Sanctions Violation | Paying DPRK workers violates international sanctions |
| Supply Chain Compromise | Malicious code inserted into your product |
| Future Hacking | Knowledge used for targeted attacks |
| Extortion | May demand payment after employment ends |
| Reputational Damage | Public disclosure harms trust |
| Asset Freeze | Banks may freeze accounts if suspected |
| Criminal Liability | Potential fines or charges |

## Reference Files

- See `references/detection-patterns.md` for detailed behavioral indicators
- See `references/case-studies.md` for real-world examples
