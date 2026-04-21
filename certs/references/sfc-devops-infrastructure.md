# SFC: SEAL Framework Checklist

SFC DevOps & Infrastructure certification: development environment security, source code management, supply chain security, CI/CD pipeline controls, infrastructure access, and cloud security monitoring.

**Controls and baselines for self-assessment and certification.**

## di-1: Governance & Development Environment

### di-1.1.1 — DevOps Security Owner
**Q:** Is there a clearly designated person or team accountable for development and infrastructure security?

**Baselines:**
- Accountability scope covers policy maintenance, security reviews, access control oversight, pipeline governance, and incident escalation

### di-1.1.2 — DevOps Security Policy
**Q:** Do you maintain documented security policies governing development and infrastructure operations?

**Baselines:**
- Policy covers environment standards, access controls, deployment procedures, code management, and supply chain security
- Accessible to all developers and infrastructure operators
- Reviewed at least annually and after significant changes (security incidents, technology shifts, organizational restructuring)

### di-1.1.3 — Development Environment Isolation
**Q:** Do you isolate development environments from production systems?

**Baselines:**
- Development activities performed in containerized or virtualized environments
- Each code repository has its own isolated environment to prevent cross-contamination
- Production credentials not accessible from development environments
- Separate accounts or profiles for development vs. privileged operations (e.g., wallet signing, cloud admin)
- Code execution sandboxed to prevent host system compromise

### di-1.1.4 — Development Tools Approval
**Q:** Do you evaluate and approve development tools before organizational use?

**Baselines:**
- Evaluation criteria cover IDEs, extensions, plugins, AI-powered tools, and third-party services
- Extensions and plugins obtained only from official repositories
- AI tools assessed for data privacy risks (does the tool send code to third parties for training or analytics?)
- Approved tool list maintained; unapproved tools restricted
- Regular reviews of installed tools to identify unused or unrecognized items

## di-2: Source Code & Supply Chain Security

### di-2.1.1 — Repository Security
**Q:** Do you enforce security controls on your source code repositories?

**Baselines:**
- Role-based access control with least-privilege permissions
- Branch protection rules enforced on main/production branches
- Signed commits required for all code changes
- Multi-party code review required for merges to protected branches
- MFA required for all repository members
- Repository access reviewed periodically

### di-2.1.2 — Secret Scanning
**Q:** Do you scan source code for accidentally committed secrets?

**Baselines:**
- Automated scanning for committed secrets (API keys, private keys, credentials) in all repositories
- Pre-commit hooks deployed to prevent secrets from being committed in the first place
- Remediation procedures for discovered secrets (immediate rotation, revocation)
- Scanning integrated into CI/CD pipeline

### di-2.1.3 — External Contributor Review
**Q:** Do you apply enhanced review for code contributions from external collaborators?

**Baselines:**
- Additional approvers required for all external code contributions
- Code contributions tracked; unexpected changes flagged (e.g., commit rewrites, unprompted edits)
- External collaborators restricted to minimum necessary repository permissions
- CI/CD pipelines do not automatically execute for external contributor PRs without approval

### di-2.1.4 — Dependency and Supply Chain Security
**Q:** Do you verify and manage dependencies to prevent supply chain attacks?

**Baselines:**
- Packages obtained from official repositories and trusted sources only
- Package names verified against typosquatting patterns before installation
- Dependencies scanned for known vulnerabilities before deployment
- Dependency version pinning enforced to prevent automatic updates to compromised versions
- Regular dependency audits for outdated or vulnerable components
- Changelog reviewed for dependency updates to verify expected functionality

## di-3: CI/CD Pipeline Security

### di-3.1.1 — Pipeline Security Controls
**Q:** Do you control who can modify and execute your deployment pipelines?

**Baselines:**
- Pipeline configuration changes require multi-party approval
- Separate service accounts with minimal permissions used for pipeline execution
- Manual deployment by humans restricted; deployments automated through controlled pipelines
- Pipeline and build configurations version-controlled and reviewed
- Builds are deterministic with strict dependency sets

### di-3.1.2 — Secrets Management
**Q:** Do you securely manage secrets used in pipelines and applications?

**Baselines:**
- Dedicated secrets management system used (not environment variables in plain text)
- Secrets never stored in source code or unencrypted configuration files
- Production secrets not directly accessible by humans
- Pipeline secrets accessible only by service accounts
- Secret rotation schedule defined; rotation triggered immediately after suspected compromise

### di-3.1.3 — Security Testing Integration
**Q:** Do you integrate security testing into your development and deployment pipelines?

**Baselines:**
- Static analysis (SAST) tools integrated into CI/CD pipeline
- Dependency vulnerability scanning automated in CI/CD
- Security scan results reviewed before deployment approval
- Testing and validation performed in staging environments before production deployment

## di-4: Infrastructure & Cloud Security

### di-4.1.1 — Infrastructure as Code
**Q:** Do you manage infrastructure through code with version control and review?

**Baselines:**
- All infrastructure defined and managed through code (e.g., Terraform, CloudFormation)
- Infrastructure changes deployed through automated pipelines, no manual steps required
- Infrastructure changes require multi-party approval
- IaC security scanning performed before deployment

### di-4.1.2 — Infrastructure Access Controls
**Q:** Do you enforce least-privilege access controls for infrastructure?

**Baselines:**
- Individual accounts with MFA required; no shared accounts
- Privileged access is time-limited and requires multi-party approval (JIT access)
- Day-to-day operations use minimum necessary permissions (read-only where possible)
- Break-glass accounts established for emergency access with individual accountability
- Break-glass usage triggers immediate alerts to the entire team and requires post-incident review
- All access activities logged and monitored

### di-4.1.3 — Backup and Disaster Recovery
**Q:** Do you maintain backup and disaster recovery procedures with periodic testing?

**Baselines:**
- Critical systems have automated backup procedures
- Disaster recovery plan documented with recovery time and recovery point objectives defined
- Backup and recovery procedures tested regularly
- Backups stored independently of primary infrastructure

### di-4.1.4 — Cloud Security Monitoring
**Q:** Do you monitor cloud security configurations and respond to provider security notifications?

**Baselines:**
- Cloud security configurations continuously monitored for drift and unauthorized changes
- Administrative actions trigger alerts
- Cloud provider security notifications subscribed to and promptly reviewed
- Comprehensive logging enabled (e.g., CloudTrail, Azure Monitor, Google Cloud Logging)
- Multi-cloud strategies considered to reduce single-provider dependency
