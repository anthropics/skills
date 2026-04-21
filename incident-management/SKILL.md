---
name: seal-incident-management
description: >
  Handle security incidents — compromised wallets, protocol hacks, suspicious transactions, drainer attacks, malware. Use when someone reports a breach, asks 'what do I do if my wallet was hacked', or needs IR playbooks. Load seal-safe-harbor if whitehat involvement, coordinated disclosure, or post-incident recovery involves external parties. Load seal-wallet-security if wallet-specific. Load seal-monitoring for detection setup. Load seal-dprk-it-workers if DPRK-related.
metadata:
  category: security
  tags: ['incident-response', 'playbooks', 'detection', 'containment']
  related_skills: ["seal-safe-harbor", "seal-opsec", "seal-wallet-security", "seal-monitoring", "seal-threat-modeling", "seal-dprk-it-workers"]
---

# Incident Management

Security incident lifecycle — detection, response, containment, communication, lessons learned, and playbooks for specific attack types.

## When to Use
- User asks about incident management practices, policies, or procedures
- Incident or scenario involving incident management concepts
- Need guidance on incident management frameworks or implementations
- Security training or awareness question touching this domain

## Related Domains
This skill connects to: seal-safe-harbor, seal-opsec, seal-wallet-security, seal-monitoring, seal-threat-modeling, seal-dprk-it-workers
Use `skill_view("seal-safe-harbor")` if the question spans multiple areas.

## Key Concepts
# Incident Management
Incident management involves preparing for, detecting, responding to, and recovering from security incidents. By
thinking about incident management prior to actually experiencing an incident, you can help increase the likelihood of a
timely recovery.
## Gotchas
- Evidence must be preserved BEFORE remediation — screenshot transactions, save logs, document timeline first
- Communicating during an incident is legally risky — get legal review before any public statement
- Auto-pause mechanisms can be exploited to DoS your protocol — balance protection with availability
- The SEAL 911 war room exists specifically for coordinated response — use it rather than going solo

## References
- Lessons Learned
- Incident Detection And Response
- Communication Strategies
- Malware
- Hacked Drainer
- Seal 911 War Room Guidelines
- Hacked Dprk
- Hacked Elusive Comet
- ... and 1 more detailed reference files
