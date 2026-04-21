---
name: seal-infrastructure
description: >
  Handle infrastructure security — OS hardening, network security, DDoS protection, cloud security, DNS security, zero-trust. Use when discussing server hardening, firewall rules, cloud configurations, or network architecture. Load seal-devsecops for CI/CD security. Load seal-monitoring for infrastructure monitoring. Load seal-encryption for data-in-transit protection.
metadata:
  category: security
  tags: ['infrastructure', 'network', 'cloud', 'zero-trust', 'dns']
  related_skills: ["seal-encryption", "seal-iam", "seal-devsecops", "seal-monitoring"]
---

# Infrastructure

Infrastructure security — OS hardening, network security, DDoS protection, cloud security, DNS security, and zero-trust principles.

## When to Use
- User asks about infrastructure practices, policies, or procedures
- Incident or scenario involving infrastructure concepts
- Need guidance on infrastructure frameworks or implementations
- Security training or awareness question touching this domain

## Related Domains
This skill connects to: seal-encryption, seal-iam, seal-devsecops, seal-monitoring
Use `skill_view("seal-encryption")` if the question spans multiple areas.

## Key Concepts
# Infrastructure
Infrastructure can often be overlooked in web3, but it's often a very important area given that most front-end web
applications are running on centralized infrastructure. This section focuses on Infrastructure Security, encompassing
critical aspects such as cloud infrastructure, DNS providers, domain registrars, and DDoS (Distributed Denial of
Service) protection.
When designing your architecture, it may be worth considering how many different providers you rely on. Are you going to
use different providers for infrastructure, DDoS protection, domain registration, and DNS, or will you choose a
provider that provides all of these? On one hand, putting all eggs in one basket means a failure on said service would
cause downtime, however by using a single service and ensuring it’s following all best practices with regards to
security measures means a lower risk surface.
## Gotchas
- Default cloud security groups are often too permissive — audit inbound rules on every deployment
- DNS hijacking can redirect your entire domain without touching your servers — use DNSSEC and registrar locks
- Zero trust for a small team doesn't mean buying expensive tools — it means authenticating every request regardless of source

## References
- Ddos Protection
- Asset Inventory
- Network Security
- Operating System Security
- Identity And Access Management
- Cloud
- Zero Trust Principles
- Dns Basics And Attacks
- ... and 3 more detailed reference files
