---
name: seal-security-automation
description: >
  Handle automated security — compliance-as-code, infrastructure-as-code security, automated threat detection. Use when discussing security automation, policy-as-code, or automated compliance checks. Load seal-devsecops for CI/CD automation. Load seal-monitoring for detection automation. Load seal-infrastructure for IaC security.
metadata:
  category: security
  tags: ['automation', 'iac', 'compliance', 'detection']
  related_skills: ["seal-monitoring", "seal-infrastructure", "seal-devsecops"]
---

# Security Automation

Automating security — compliance checks, infrastructure as code security, and automated threat detection and response.

## When to Use
- User asks about security automation practices, policies, or procedures
- Incident or scenario involving security automation concepts
- Need guidance on security automation frameworks or implementations
- Security training or awareness question touching this domain

## Related Domains
This skill connects to: seal-monitoring, seal-infrastructure, seal-devsecops
Use `skill_view("seal-monitoring")` if the question spans multiple areas.

## Key Concepts
# Security Automation
Security automation involves using technology to perform security tasks with minimal human intervention. By automating
repetitive and complex security processes, teams can improve efficiency, reduce the risk of human error, and respond to
threats more quickly. This section covers best practices and tools for automating various aspects of security, including
compliance checks, infrastructure as code, and threat detection and response.
## Gotchas
- Automated security that can't be overridden during incidents becomes a liability — always include manual overrides
- IaC drift means actual infrastructure doesn't match code — run drift detection regularly

## References
- Compliance Checks
- Threat Detection Response
- Infrastructure As Code
