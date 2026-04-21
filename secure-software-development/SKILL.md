---
name: seal-secure-software-development
description: >
  Handle secure coding practices — code reviews, peer audits, repository security, coding standards. Use when discussing code review processes, secure coding guidelines, or repository hardening. Load seal-devsecops for CI/CD integration. Load seal-security-testing for testing methodology. Load seal-supply-chain for dependency management.
metadata:
  category: security
  tags: ['secure-coding', 'code-review', 'repositories']
  related_skills: ["seal-security-testing", "seal-supply-chain", "seal-devsecops"]
---

# Secure Software Development

Secure coding practices — code reviews, peer audits, secure repositories, coding standards, and threat modeling for software design.

## When to Use
- User asks about secure software development practices, policies, or procedures
- Incident or scenario involving secure software development concepts
- Need guidance on secure software development frameworks or implementations
- Security training or awareness question touching this domain

## Related Domains
This skill connects to: seal-security-testing, seal-supply-chain, seal-devsecops
Use `skill_view("seal-security-testing")` if the question spans multiple areas.

## Key Concepts
# Secure Software Development
Secure software development is the practice of integrating security measures throughout the entire software development
lifecycle (SDLC). This approach ensures that software is designed, developed, and maintained with security in mind,
protecting against vulnerabilities and threats. This section provides guidelines and best practices for secure software
development, including code reviews, secure coding standards, version control, and threat modeling.
## Gotchas
- Code review alone doesn't catch logic bugs — pair reviews with formal verification for critical paths
- Static analysis tools generate false positives that desensitize teams — tune rules and triage regularly

## References
- Code Reviews Peer Audits
- Secure Code Repositories Version Control
- Threat Modeling Secure Design Principles
- Secure Coding Standards Guidelines
