---
name: seal-safe-harbor
description: >
  Handle whitehat protection — safe harbor terms, scope of authorized research, legal protection for security researchers. Use when someone reports a vulnerability, discusses responsible disclosure, or asks about legal protections for security research. Load seal-incident-management for the incident handling process. Load seal-vulnerability-disclosure for disclosure procedures. Load seal-governance for legal/compliance context.
metadata:
  category: security
  tags: ['safe-harbor', 'whitehat', 'bug-bounty', 'legal']
  related_skills: ["seal-incident-management", "seal-governance"]
---

# Safe Harbor

Whitehat protection frameworks — scope and terms, on-chain adoption, self-adoption guides, and safe harbor for security researchers.

## When to Use
- User asks about safe harbor practices, policies, or procedures
- Incident or scenario involving safe harbor concepts
- Need guidance on safe harbor frameworks or implementations
- Security training or awareness question touching this domain

## Related Domains
This skill connects to: seal-incident-management, seal-governance
Use `skill_view("seal-incident-management")` if the question spans multiple areas.

## Key Concepts
# SEAL Whitehat Safe Harbor
<img src="https://frameworks-static.s3.us-east-2.amazonaws.com/images/safe-harbor/whitehat-full-logo-blue.svg"
alt="Whitehat Logo" />
> 💡 An industry-standard framework, letting your protocol pre-authorize whitehats to rescue funds during active
> exploits
<source src="https://frameworks-static.s3.us-east-2.amazonaws.com/images/safe-harbor/Protocol_Explainer_Video.mp4"
type="video/mp4" />
Your browser does not support the video tag.
## Gotchas
- Safe harbor only covers actions within the defined scope — out-of-scope testing can still be prosecuted
- Verbal agreements don't protect you — get safe harbor terms in writing before any research begins
- On-chain attestations via EAS provide immutable proof of safe harbor adoption — use them

## References
- Self Checklist
- Scope Terms
- Whitehat
- On Chain Adoption Guide
- Self Adoption Guide
