---
name: seal-iam
description: >
  Handle identity and access management — access control, RBAC, secure authentication, MFA, and identity lifecycle. Use when discussing user permissions, authentication methods, access reviews, or SSO. Load seal-opsec for broader identity security and offboarding procedures. Load seal-encryption for authentication encryption. Load seal-multisig-for-protocols for on-chain identity.
metadata:
  category: security
  tags: ['iam', 'access-control', 'rbac', 'authentication']
  related_skills: ["seal-encryption", "seal-opsec", "seal-infrastructure", "seal-multisig-for-protocols"]
---

# Iam

Identity and access management — access control, RBAC, secure authentication, and identity lifecycle management.

## When to Use
- User asks about iam practices, policies, or procedures
- Incident or scenario involving iam concepts
- Need guidance on iam frameworks or implementations
- Security training or awareness question touching this domain

## Related Domains
This skill connects to: seal-encryption, seal-opsec, seal-infrastructure, seal-multisig-for-protocols
Use `skill_view("seal-encryption")` if the question spans multiple areas.

## Key Concepts
# Identity and Access Management (IAM)
Identity and Access Management (IAM) is defined as managing who has access to your systems and data, and ensuring that
access is secure and appropriate. Effective IAM practices help prevent unauthorized access, reduce the risk of insider
threats, and ensure that users have the necessary access to perform their roles efficiently.
## Gotchas
- SMS-based 2FA is vulnerable to SIM swapping — use hardware keys or authenticator apps, never SMS
- Service accounts with permanent API keys are the #1 lateral movement vector — use short-lived tokens
- RBAC without periodic access reviews leads to permission creep — schedule quarterly reviews

## References
- Secure Authentication
- Access Management
- Role Based Access Control
