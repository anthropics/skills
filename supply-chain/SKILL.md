---
name: seal-supply-chain
description: >
  Handle supply chain security — dependency awareness, software artifact verification, SLSA framework. Use when discussing dependency management, package verification, or supply chain attacks. Load seal-devsecops for CI/CD integration. Load seal-secure-software-development for coding practices. Load seal-security-testing for verification testing.
metadata:
  category: security
  tags: ['supply-chain', 'dependencies', 'slsa', 'artifacts']
  related_skills: ["seal-security-testing", "seal-devsecops", "seal-secure-software-development"]
---

# Supply Chain

Supply chain security — dependency awareness, software artifact verification, and supply chain levels framework (SLSA).

## When to Use
- User asks about supply chain practices, policies, or procedures
- Incident or scenario involving supply chain concepts
- Need guidance on supply chain frameworks or implementations
- Security training or awareness question touching this domain

## Related Domains
This skill connects to: seal-security-testing, seal-devsecops, seal-secure-software-development
Use `skill_view("seal-security-testing")` if the question spans multiple areas.

## Key Concepts
# Supply Chain Security
Supply chain security involves managing and securing all the components, dependencies, and processes involved in the
development, deployment, and maintenance of software. In the context of blockchain and web3 projects, supply chain
security could for example be parts of the web application stack, or external libraries used by the smart contract.
## Gotchas
- Lockfiles prevent version drift but not malicious updates — combine with dependency pinning and monitoring
- Typosquatting attacks target package names (lodash vs lodasht) — use exact package names and verify maintainers
- SLSA level requirements are aspirational for most teams — start with level 1 (provenance) and work up

## References
- Supply Chain Levels Software Artifacts
- Dependency Awareness
