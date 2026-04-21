---
name: seal-wallet-security
description: >
  Handle wallet security — seed phrase management, hardware wallets, multisig, transaction signing, wallet types. Use when someone asks about 'storing seed phrases', 'hardware vs software wallets', 'signing transactions', or 'wallet was compromised'. Load seal-encryption for key encryption. Load seal-multisig-for-protocols for multisig setup. Load seal-incident-management if a wallet was compromised. Load seal-safe-harbor if whitehat is involved.
metadata:
  category: security
  tags: ['wallet', 'seed-phrase', 'hardware-wallet', 'multisig', 'web3']
  related_skills: ["seal-safe-harbor", "seal-iam", "seal-incident-management", "seal-multisig-for-protocols", "seal-encryption"]
---

# Wallet Security

Wallet security across all types — hardware, software, custodial, non-custodial, seed phrases, multisig, and transaction verification.

## When to Use
- User asks about wallet security practices, policies, or procedures
- Incident or scenario involving wallet security concepts
- Need guidance on wallet security frameworks or implementations
- Security training or awareness question touching this domain

## Related Domains
This skill connects to: seal-safe-harbor, seal-iam, seal-incident-management, seal-multisig-for-protocols, seal-encryption
Use `skill_view("seal-safe-harbor")` if the question spans multiple areas.

## Key Concepts
# Wallet Security
In cryptocurrency, the security of digital assets is directly tied to how control over the funds is protected. This
section provides a technical deep-dive into wallet security, covering the range from fundamental concepts to advanced
practices for safeguarding assets against theft, loss, and unauthorized access.
The goal is to move beyond introductory concepts and provide actionable, technical knowledge for securely managing
crypto assets.
## Gotchas
- Never store seed phrases digitally — cloud backups, photos, email drafts, and note apps are all accessible by providers
- Hardware wallet firmware can be compromised — only buy from official vendors, never secondhand
- Same address across chains doesn't mean same security — EVM-compatible chains share addresses but signing schemes differ
- Token approval exploits drain wallets without needing the seed phrase — regularly review and revoke unnecessary approvals

## References
- Signing Verification
- Secure Multisig Squads Verification
- Signing Schemes
- Secure Multisig Best Practices
- Hardware Wallets
- Verifying 7702
- Seed Phrase Management
- Encumbered Wallets
- ... and 10 more detailed reference files
