---
name: seal-certs
description: >
  Handle SEAL certification framework questions, protocol certification processes, and auditor partnerships. Use when asking about SFC checklists, self-assessment vs third-party review, or certified auditor programs. Load seal-governance for compliance context.
metadata:
  category: security
  tags: ['certification', 'compliance', 'protocols']
  related_skills: ["seal-opsec", "seal-governance", "seal-devsecops"]
---

# Certs

Security certification frameworks, protocol certification processes, and partner certification guidelines for Web3 organizations.

## When to Use
- User asks about certs practices, policies, or procedures
- Incident or scenario involving certs concepts
- Need guidance on certs frameworks or implementations
- Security training or awareness question touching this domain

## Related Domains
This skill connects to: seal-opsec, seal-governance, seal-devsecops
Use `skill_view("seal-opsec")` if the question spans multiple areas.

## Key Concepts
# SEAL Certification Framework
SEAL Certifications is a certification framework developed by SEAL to provide standardized guidelines and evaluation criteria for assessing the security of DeFi protocols. SEAL Certifications provides targeted modular certifications (e.g., [Incident Response](/certs/sfc-incident-response.mdx), [Treasury Ops](/certs/sfc-treasury-ops.mdx)) that can independently validate specific aspects of a protocol's security posture.
Using SEAL Certifications will help ensure that protocols follow best practices for their security operations, and provides a standard set of criteria for comparing the security of different protocols.
SEAL Certifications is fully open-source and freely available for any protocol to use.
## Gotchas
- Self-assessment doesn't grant formal certification — teams often think they're 'certified' after filling the checklist
- Each SFC (Incident Response, Multisig Ops, etc.) is independent — completing one doesn't cover others

## References
- Certification Guidelines
- Sfc Devops Infrastructure
- Sfc Treasury Ops
- Sfc Workspace Security
- Certified Protocols
- Sfc Multisig Ops
- Sfc Dns Registrar
- Sfc Incident Response
- ... and 2 more detailed reference files
