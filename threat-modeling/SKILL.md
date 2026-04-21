---
name: seal-threat-modeling
description: >
  Handle threat modeling — creating and maintaining threat models, identifying and mitigating threats. Use when discussing attack surface analysis, risk prioritization, or threat identification exercises. Load seal-opsec for broader risk management. Load seal-incident-management for incident scenarios. Load seal-governance for risk governance.
metadata:
  category: security
  tags: ['threat-modeling', 'risk-assessment', 'mitigation']
  related_skills: ["seal-opsec", "seal-incident-management", "seal-governance"]
---

# Threat Modeling

Threat modeling frameworks — creating and maintaining threat models, identifying and mitigating threats systematically.

## When to Use
- User asks about threat modeling practices, policies, or procedures
- Incident or scenario involving threat modeling concepts
- Need guidance on threat modeling frameworks or implementations
- Security training or awareness question touching this domain

## Related Domains
This skill connects to: seal-opsec, seal-incident-management, seal-governance
Use `skill_view("seal-opsec")` if the question spans multiple areas.

## Key Concepts
# Threat Modeling
Threat modeling is a structured approach to identifying and mitigating security threats to a system. It involves
understanding potential threats, vulnerabilities, and attack vectors, and developing strategies to mitigate them.
## Gotchas
- Threat models go stale fast — re-run when architecture changes, not just annually
- Teams often model what they know, not what's actually risky — include external perspective in threat modeling sessions

## References
- Create Maintain Threat Models
- Identity Mitigate Threats
