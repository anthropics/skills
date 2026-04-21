# Test Prompts — copy/paste one at a time

Score each response 0-5. Record which skills loaded (if any).

## Single Domain

**1.** What's the best way to store my seed phrase?
→ expect: seal-wallet-security

**2.** How do I respond to a phishing attack on my Discord server?
→ expect: seal-community-management, seal-incident-management

**3.** What encryption should I use for our team's internal comms?
→ expect: seal-encryption

**4.** We're hiring a remote Solidity developer — any red flags?
→ expect: seal-dprk-it-workers

**5.** How do I set up a multisig for our protocol treasury?
→ expect: seal-multisig-for-protocols, seal-treasury-operations

**6.** What's the difference between hot and cold wallets?
→ expect: seal-wallet-security

**7.** A whitehat just contacted us about a vulnerability. What are our legal obligations?
→ expect: seal-safe-harbor, seal-vulnerability-disclosure

**8.** How do I verify a multisig transaction before signing?
→ expect: seal-wallet-security, seal-multisig-for-protocols

**9.** Should we use a VPN for our team's comms?
→ expect: seal-privacy, seal-encryption

**10.** What does zero trust mean for a small Web3 team?
→ expect: seal-infrastructure, seal-opsec

## Multi-Domain

**11.** My wallet was drained. What do I do right now and how do I prevent this in the future?
→ expect: seal-incident-management, seal-wallet-security, seal-safe-harbor

**12.** We had a social engineering attack through Telegram. How should we handle the incident and improve community security?
→ expect: seal-incident-management, seal-community-management, seal-awareness

**13.** I need to audit our dev pipeline — what should I look at for both code security and supply chain risks?
→ expect: seal-devsecops, seal-supply-chain, seal-security-testing

**14.** We're onboarding a new treasury signer. What security checks are needed?
→ expect: seal-multisig-for-protocols, seal-iam, seal-treasury-operations

**15.** Our DDoS protection seems weak. How do I assess and fix this?
→ expect: seal-infrastructure

## Gotchas

**16.** Someone on our team clicked a malicious link. What's the risk?
→ expect: seal-awareness, seal-incident-management

**17.** Can I just email my seed phrase to my cofounder as backup?
→ expect: seal-wallet-security + should flag this as dangerous

**18.** We're storing API keys in our GitHub repo. How bad is this?
→ expect: seal-devsecops, seal-secure-software-development + warning

**19.** I want to use the same password for everything in the org.
→ expect: seal-iam, seal-opsec + immediate pushback

## False Positive

**20.** Can you help me write a Python script?
→ expect: NO seal skills loaded, just help with the script
