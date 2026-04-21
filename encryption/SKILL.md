---
name: seal-encryption
description: >
  Handle encryption strategies across all domains — disk, file, database, email, cloud, and communication encryption. Use when someone asks about VPNs, secure messaging, encrypting data at rest/transit, or PGP. Load seal-privacy for broader privacy tool recommendations. Load seal-wallet-security if the question involves key/seed phrase encryption.
metadata:
  category: security
  tags: ['encryption', 'disk', 'email', 'vpn', 'tls']
  related_skills: ["seal-wallet-security", "seal-privacy", "seal-infrastructure", "seal-iam"]
---

# Encryption

Encryption strategies across all domains — disk, file, database, email, cloud, communication, and in-transit encryption.

## When to Use
- User asks about encryption practices, policies, or procedures
- Incident or scenario involving encryption concepts
- Need guidance on encryption frameworks or implementations
- Security training or awareness question touching this domain

## Related Domains
This skill connects to: seal-wallet-security, seal-privacy, seal-infrastructure, seal-iam
Use `skill_view("seal-wallet-security")` if the question spans multiple areas.

## Key Concepts
# Encryption
Encryption is a fundamental aspect of securing data, ensuring that sensitive information remains confidential and
protected from unauthorized access. This section covers various types of encryption and best practices for implementing
them effectively.
## Gotchas
- PGP email encryption doesn't hide metadata (who you email, when, how often) — only content
- Full disk encryption is useless if the machine is running and unlocked — it protects at-rest data only
- Cloud encryption at rest is controlled by the provider — you often can't prove they don't have the key
- TLS is not a substitute for E2E encryption — the server can read TLS-encrypted data in transit

## References
- Encryption In Transit
- Cloud Data Encryption
- Email Encryption
- File Encryption
- Communication Encryption
- Full Disk Encryption
- Partition Encryption
- Volume Encryption
- ... and 2 more detailed reference files
