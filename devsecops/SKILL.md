---
name: seal-devsecops
description: >
  Handle CI/CD security, code signing, repository hardening, and secure development workflows. Use when discussing GitHub/GitLab security, supply chain attacks, dependency management, or pipeline vulnerabilities. Load seal-supply-chain for dependency-specific concerns. Load seal-security-testing for testing methodology. Load seal-secure-software-development for coding standards.
metadata:
  category: security
  tags: ['devops', 'ci-cd', 'code-signing', 'development']
  related_skills: ["seal-security-testing", "seal-infrastructure", "seal-security-automation", "seal-supply-chain", "seal-secure-software-development"]
---

# Devsecops

Security integrated into development workflows — CI/CD security, code signing, repository hardening, and security testing automation.

## When to Use
- User asks about devsecops practices, policies, or procedures
- Incident or scenario involving devsecops concepts
- Need guidance on devsecops frameworks or implementations
- Security training or awareness question touching this domain

## Related Domains
This skill connects to: seal-security-testing, seal-infrastructure, seal-security-automation, seal-supply-chain, seal-secure-software-development
Use `skill_view("seal-security-testing")` if the question spans multiple areas.

## Key Concepts
# DevSecOps
Traditionally, rapid development and deployment is often prioritized at the expense of security considerations. This is
generally speaking no different in web3, but it is important to take integrity, confidentiality, and availability into
consideration too. To effectively address this without compromising on rapid development and deployment, it is essential
to integrate security into the process, which is where devsecops comes into play. By implementing devsecops, projects
can not only deploy faster, but also be more secure.
When operating in a devsecops mindset, projects prioritizes automation and collaboration between the development,
operations and security teams.
Some of the key areas to consider are:
1. Integrate security measures early in the development process, such as by utilizing security tools such as fuzzing,
static and dynamic analysis tools in your CI/CD process, to identify and mitigate vulnerabilities before they turn into
critical issues.
2. Implement automated security testing and monitoring.
3. Development, Operations and Security teams should be aligned and work closely together.
## Gotchas
- Storing secrets in git history is permanent — even if removed, they're in every clone. Use secret scanning and rotate immediately
- GitHub Actions secrets are available to ALL branches by default — use environment protection rules for production
- npm/yarn supply chain attacks target popular packages — pin dependencies and use lockfiles, but also verify with SRI hashes
- CI/CD pipelines with write access to repos are high-value targets — restrict permissions and audit pipeline configs

## References
- Repository Hardening
- Security Testing
- Integrated Development Environments
- Continuous Integration Continuous Deployment
- Code Signing
