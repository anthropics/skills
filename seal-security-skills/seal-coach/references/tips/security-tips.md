# Security Tips Library

Rotating daily tips from SEAL frameworks. One tip per interaction, track delivered tips in state-log.json.

## Wallet Security

- **Tip:** "If you're using a single key for anything valuable, you're one compromise away from zero. Multisig isn't just for treasuries — use it for any admin or signing authority."
- **Tip:** "Never store seed phrases digitally. Not in notes, not in password managers, not in photos. Hardware wallet + metal backup. That's it."
- **Tip:** "Set transaction limits that require additional approval. If someone gets a key, you want blast radius controls."
- **Tip:** "Audit your key inventory quarterly. Who has access? Where are keys stored? When were they last rotated? If you can't answer these in 5 minutes, you have a gap."

## Incident Management

- **Tip:** "You don't want to figure out your incident process during an incident. Write a 1-page plan now: who to call, what to lock down, how to communicate."
- **Tip:** "Save the SEAL 911 contact before you need it. When your treasury is draining, you won't have time to search for help."
- **Tip:** "Tabletop exercises cost nothing and reveal everything. Walk through 'our deployer key was compromised' with your team. What happens in the first 30 minutes?"

## IAM

- **Tip:** "Shared accounts are a security black hole. When something goes wrong, you can't tell who did what. Individual accounts with MFA, always."
- **Tip:** "When someone leaves the team, their access should be revoked the same day. Not 'when we get around to it.' Same day. Add it to your offboarding checklist."
- **Tip:** "MFA isn't optional anymore. SMS is better than nothing, but authenticator apps or hardware keys are the standard. Enable it on everything admin-level today."

## DevSecOps

- **Tip:** "Run semgrep in CI. It takes 30 seconds to set up and catches real vulnerabilities. There's no excuse for not having at least basic security linting."
- **Tip:** "Pin your dependencies. A malicious package update is a supply chain attack. Lockfiles exist for a reason."
- **Tip:** "Secrets in code are secrets in git history forever. Use environment variables, vault services, or encrypted secrets. Never commit credentials."

## Monitoring

- **Tip:** "You can't respond to what you can't see. Even basic logging of auth events and admin actions gives you something to work with after an incident."
- **Tip:** "Alert on anomalies, not just thresholds. A sudden spike in failed logins at 3am is more interesting than 'CPU is high.'"
- **Tip:** "Check if your credentials have been leaked. Tools like Hudson Rock and dehashed can tell you if your team's emails show up in breaches."

## Governance

- **Tip:** "Security without ownership is security theater. Someone needs to be responsible for security decisions, even if it's not a full-time role."
- **Tip:** "A risk register doesn't need to be fancy. List your top 5 risks, rate them, track what you're doing about each. Review it monthly."

## Supply Chain

- **Tip:** "Know your dependencies. When was the last time you audited what your project pulls in? One compromised transitive dependency can own your entire stack."
- **Tip:** "Verify artifact provenance where possible. If your build pipeline can be tampered with, your code integrity is compromised before it reaches users."

## Awareness

- **Tip:** "The most dangerous phishing emails don't look like phishing. They reference real projects, use real names, create real urgency. Verify out-of-band — call the person, don't just trust the email."
- **Tip:** "Security culture starts with not punishing people for reporting mistakes. If someone clicks a phishing link, you want them to report it immediately, not hide it."

## OpSec

- **Tip:** "Separate work and personal accounts. Your personal email getting phished shouldn't be a path to your organization's infrastructure."
- **Tip:** "Assume your communications can be read. Use end-to-end encrypted channels for sensitive operational discussions."

## Encryption

- **Tip:** "Encrypt everything at rest and in transit. TLS for connections, disk encryption for laptops. The performance cost is negligible; the protection is massive."
- **Tip:** "Key management is the hard part. You can have perfect encryption, but if your keys are exposed, it's worthless. Treat encryption keys like the secrets they protect."

## Threat Modeling

- **Tip:** "You can't defend against everything. Threat modeling forces you to decide: what are we actually protecting, from whom, and what's worth the effort?"
- **Tip:** "Review your threat model when your architecture changes. New feature? New integration? New team member with access? Each changes your attack surface."

## Infrastructure

- **Tip:** "Zero trust isn't just a buzzword. Don't assume anything inside your network is safe. Authenticate and authorize everything, even internal services."
- **Tip:** "Harden your DNS. DNS hijacking is a real vector. Use DNSSEC where possible, monitor for unauthorized changes."

## Community Management

- **Tip:** "Your Discord/Telegram mods are a security layer. Train them on social engineering, give them clear escalation procedures, and don't let random users have admin powers."
- **Tip:** "Impersonation attacks target communities. Verify team members through multiple channels, and make it easy for your community to identify official accounts."

## Treasury Operations

- **Tip:** "Classify your assets by sensitivity. Not everything needs the same level of protection. Focus your strongest controls on what matters most."
- **Tip:** "Transaction verification should be multi-step. Verify the recipient, the amount, and the purpose. Especially for large or unusual transfers."
