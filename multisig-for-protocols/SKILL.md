---
name: seal-multisig-for-protocols
description: >
  Handle multisig wallet operations — signer management, transaction approval, emergency procedures, key ceremonies. Use when discussing multisig setup, signer onboarding, transaction verification, or treasury access. Load seal-wallet-security for wallet security basics. Load seal-treasury-operations for treasury governance. Load seal-iam for signer identity verification.
metadata:
  category: security
  tags: ['multisig', 'hardware-wallet', 'protocols', 'treasury']
  related_skills: ["seal-wallet-security", "seal-iam", "seal-opsec", "seal-treasury-operations", "seal-governance"]
---

# Multisig For Protocols

Multisig operations for protocols — hardware wallet setup, emergency procedures, communication setup, onboarding/offboarding, and transaction verification.

## When to Use
- User asks about multisig for protocols practices, policies, or procedures
- Incident or scenario involving multisig for protocols concepts
- Need guidance on multisig for protocols frameworks or implementations
- Security training or awareness question touching this domain

## Related Domains
This skill connects to: seal-wallet-security, seal-iam, seal-opsec, seal-treasury-operations, seal-governance
Use `skill_view("seal-wallet-security")` if the question spans multiple areas.

## Key Concepts
# Multisig Security Framework
## Gotchas
- Unanimous quorum (all signers required) means one lost key = locked funds — use n-of-m with buffer
- Safe modules can be added by authorized addresses and execute arbitrary logic — audit all modules before approving
- Signer communication channels become a single point of compromise — use separate channels for coordination vs approval
- Testnet transactions don't validate the same as mainnet — always simulate on mainnet fork, not testnet

## References
- Implementation Checklist
- Setup And Configuration
- Personal Security Opsec
- Backup Signing And Infrastructure
- Registration And Documentation
- Incident Reporting
- Communication Setup
- Planning And Classification
- ... and 5 more detailed reference files
