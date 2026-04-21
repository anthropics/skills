---
name: seal-monitoring
description: >
  Handle security monitoring — alerting, SIEM, log management, threshold configuration. Use when discussing how to detect attacks, set up alerting, or configure monitoring. Load seal-incident-management for what to do when alerts fire. Load seal-infrastructure for monitoring infrastructure.
metadata:
  category: security
  tags: ['monitoring', 'alerting', 'thresholds', 'logging']
  related_skills: ["seal-security-automation", "seal-incident-management", "seal-infrastructure"]
---

# Monitoring

Security monitoring and alerting — setting thresholds, guidelines for monitoring infrastructure, and alert management.

## When to Use
- User asks about monitoring practices, policies, or procedures
- Incident or scenario involving monitoring concepts
- Need guidance on monitoring frameworks or implementations
- Security training or awareness question touching this domain

## Related Domains
This skill connects to: seal-security-automation, seal-incident-management, seal-infrastructure
Use `skill_view("seal-security-automation")` if the question spans multiple areas.

## Key Concepts
# Monitoring
Monitoring is a crucial aspect of maintaining the security and integrity of a blockchain project. Effective monitoring
allows you to detect anomalies and potential security breaches in real-time, enabling prompt response and mitigation.
This section focuses on monitoring the on-chain security of a project, including guidelines for setting up monitoring
systems, defining thresholds for alerts, and utilizing existing on-chain monitoring tools.
## Gotchas
- Alert fatigue kills monitoring — tune thresholds aggressively or the team ignores everything
- Logs without centralized collection are useless during an incident — ship logs off the compromised system immediately
- Monitoring without on-call rotation is just surveillance — someone must actually respond to alerts

## References
- Thresholds
- Guidelines
