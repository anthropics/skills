# Codebase Review — Detailed Checklist

This file contains the full detailed review checklist for the synthesis-codebase-review skill. Each item is marked with a tier indicator:

- **Essential** (Tier 1) — Apply to ALL projects
- **Standard** (Tier 2) — Apply to team projects and production apps
- **Enterprise** (Tier 3) — Apply to large-scale, multi-team, or regulated systems
- **Mission-Critical** (Tier 4) — Apply to financial, healthcare, infrastructure, or high-stakes systems

---

## 1. Architecture & System Design

### 1.1 Architectural Foundation

- [ ] Essential: **Code Organization** — Is there a logical folder/module structure?
- [ ] Essential: **Separation of Concerns** — Is business logic separated from I/O and presentation?
- [ ] Standard: **Pattern Identification** — What architectural pattern is implemented (MVC, microservices, modular monolith, etc.)?
- [ ] Standard: **Pattern Appropriateness** — Is the chosen architecture suitable for the scale and team size?
- [ ] Enterprise: **Architecture Documentation** — Is there an Architecture Decision Record (ADR)?
- [ ] Enterprise: **Dependency Graph** — Are there circular dependencies between modules/services?
- [ ] Enterprise: **Domain Boundaries** — Are bounded contexts clearly defined?
- [ ] Mission-Critical: **Layer Separation** — Is there strict separation between layers with enforced boundaries?

### 1.2 API Design & Contracts

- [ ] Essential: **Consistent Endpoints** — Are API endpoints named consistently?
- [ ] Standard: **API Documentation** — Is there basic API documentation (README, comments, or OpenAPI)?
- [ ] Standard: **Error Format Consistency** — Are error responses formatted consistently?
- [ ] Enterprise: **API Versioning** — Are APIs versioned?
- [ ] Enterprise: **Contract Documentation** — Is there OpenAPI/Swagger or GraphQL schema?
- [ ] Enterprise: **Deprecation Strategy** — Is there a documented process for deprecating APIs?
- [ ] Mission-Critical: **API Gateway** — Is there proper gateway implementation with routing, auth, rate limiting?
- [ ] Mission-Critical: **Contract Testing** — Are API contracts tested for backward compatibility?

### 1.3 Service Communication (Tier 3+)

- [ ] Enterprise: **Sync vs Async** — Are synchronous and asynchronous patterns used appropriately?
- [ ] Enterprise: **Timeout Configuration** — Are timeouts configured for all network calls?
- [ ] Enterprise: **Resilience Patterns** — Are circuit breakers and retries implemented?
- [ ] Mission-Critical: **Message Contracts** — For event-driven systems, are message schemas versioned?
- [ ] Mission-Critical: **Service Discovery** — How do services find each other? Is it robust?
- [ ] Mission-Critical: **Data Consistency** — How is eventual consistency handled across services?

### 1.4 Data Architecture

- [ ] Essential: **Data Store Exists** — Is there a proper database (not just files)?
- [ ] Standard: **Schema Design** — Is the database schema reasonably normalized?
- [ ] Standard: **Indexes Present** — Are there indexes on frequently queried columns?
- [ ] Enterprise: **Data Store Selection** — Are the right databases used for the right purposes?
- [ ] Enterprise: **Caching Strategy** — Is there a caching strategy?
- [ ] Mission-Critical: **Data Flow Documentation** — Is data flow through the system documented?

---

## 2. Secrets, Credentials & Sensitive Data

### 2.1 Active Secret Scanning

- [ ] Essential: **No Hardcoded Secrets** — Search for passwords, API keys, tokens in code
- [ ] Essential: **Environment Files Not Committed** — `.env` files are in `.gitignore`
- [ ] Standard: **Secret Scanner Run** — Run tools like `truffleHog`, `gitleaks`, or `detect-secrets`
- [ ] Enterprise: **Git History Clean** — No secrets in git history (even if removed from current code)
- [ ] Enterprise: **CI/CD Configs Clean** — No secrets in workflow files, Dockerfiles, or IaC

### 2.2 Secret Types to Search For

- [ ] Essential: Passwords and passphrases
- [ ] Essential: API keys (AWS, GCP, Stripe, etc.)
- [ ] Essential: Database connection strings with credentials
- [ ] Standard: Private keys (RSA, SSH, PGP)
- [ ] Standard: OAuth client secrets
- [ ] Standard: JWT signing secrets
- [ ] Enterprise: Encryption keys and salts
- [ ] Enterprise: Webhook secrets
- [ ] Enterprise: Service account credentials

### 2.2a AI Tool Configuration Files

- [ ] Essential: **AI Tool Files Checked** — Search for `.cursorrules`, `.cursor/`, `.aider*`, `.github/copilot-instructions.md`, and similar AI tool configuration files
- [ ] Essential: **No Infrastructure in AI Config** — AI tool files do not contain server IPs, instance IDs, security group IDs, SSH key paths, deployment directories, or environment-specific paths
- [ ] Standard: **AI Config in .gitignore** — AI tool configuration files are listed in `.gitignore`

### 2.2b Comment-Aware Credential Scanning

- [ ] Standard: **Comments Scanned for Secrets** — Code comments, TODOs, and commented-out blocks are included in credential scanning
- [ ] Standard: **No Secrets in Commented-Out Code** — Commented-out sections do not contain real API keys, passwords, or infrastructure details
- [ ] Enterprise: **CI/CD Comments Clean** — Workflow file comments do not contain credentials

### 2.3 Secret Management

- [ ] Standard: **Environment Variables** — Secrets loaded from environment variables
- [ ] Standard: **Not in Logs** — Secrets are not logged
- [ ] Enterprise: **Secrets Manager** — Using Vault, AWS Secrets Manager, or equivalent
- [ ] Enterprise: **Secret Rotation** — Secrets can be rotated without code changes
- [ ] Mission-Critical: **Secret Access Audit** — Access to secrets is logged
- [ ] Mission-Critical: **Least Privilege** — Services only access secrets they need

### 2.4 Preventive Controls

- [ ] Standard: **`.gitignore` Coverage** — Sensitive file patterns in `.gitignore`
- [ ] Standard: **Pre-Commit Secret Scanning** — Pre-commit hooks using tools like `gitleaks`, `truffleHog`, or `detect-secrets` to block secret commits before they enter git history
- [ ] Enterprise: **CI/CD Scanning** — Secret scanning in the pipeline
- [ ] Enterprise: **GitHub Secret Scanning Enabled** — If using GitHub, built-in secret scanning is enabled
- [ ] Mission-Critical: **PR Checks** — Automated PR checks for secrets

---

## 3. Code Duplication & Reusability

### 3.1 Duplication Analysis

- [ ] Standard: **No Copied Files** — No nearly-identical files
- [ ] Standard: **No Large Repeated Blocks** — No blocks of 20+ lines repeated
- [ ] Enterprise: **Duplication Scanner Run** — Run jscpd, PMD CPD, or SonarQube
- [ ] Enterprise: **Duplication Under 5%** — Total duplication is under 5% of codebase
- [ ] Mission-Critical: **Cross-Module Duplication** — No significant duplication across services

### 3.2 Shared Code & Libraries

- [ ] Standard: **Utility Functions Centralized** — Common utilities in one place
- [ ] Standard: **No Copy-Paste Coding** — Similar problems solved the same way
- [ ] Enterprise: **Internal Libraries** — Shared code in proper internal packages
- [ ] Enterprise: **Library Versioning** — Internal packages are versioned
- [ ] Mission-Critical: **Library Documentation** — Shared libraries are documented

### 3.3 Abstraction Quality

- [ ] Enterprise: **Appropriate Abstraction** — Not over-abstracted or under-abstracted
- [ ] Enterprise: **DRY Applied Sensibly** — DRY used where it reduces complexity
- [ ] Enterprise: **Rule of Three** — Abstraction after 3+ occurrences
- [ ] Mission-Critical: **Cross-Cutting Concerns** — Logging, auth, validation handled consistently

---

## 4. Code Quality, Efficiency & Optimization

### 4.1 Basic Code Quality

- [ ] Essential: **No Obvious Bugs** — No clearly broken code paths
- [ ] Essential: **No Dead Code** — No large blocks of commented-out or unreachable code
- [ ] Essential: **Reasonable Function Size** — Functions generally under 50 lines
- [ ] Standard: **Consistent Style** — Code style is consistent throughout
- [ ] Standard: **Linting Passes** — Linting configured and passing

### 4.2 Algorithmic Efficiency

- [ ] Standard: **No O(n^2) in Hot Paths** — No nested loops over large collections
- [ ] Standard: **Appropriate Data Structures** — Using maps/sets instead of array searches
- [ ] Enterprise: **Hot Path Optimization** — Performance-critical paths identified and optimized
- [ ] Mission-Critical: **Complexity Documented** — Complex algorithms have documented complexity

### 4.3 Database Efficiency

- [ ] Standard: **No N+1 Queries** — No loops that execute queries
- [ ] Standard: **Pagination** — Large datasets are paginated
- [ ] Enterprise: **Indexes Appropriate** — Queries use indexes effectively
- [ ] Enterprise: **Connection Pooling** — Database connections are pooled
- [ ] Mission-Critical: **Query Analysis** — Slow queries identified and optimized

### 4.4 Memory & Resource Efficiency

- [ ] Enterprise: **No Memory Leaks** — Event listeners removed, no circular references
- [ ] Enterprise: **Streaming for Large Data** — Large files/datasets streamed
- [ ] Enterprise: **Resources Released** — Connections and handles properly closed
- [ ] Mission-Critical: **Resource Limits** — Timeouts and limits configured
- [ ] Mission-Critical: **Graceful Shutdown** — Resources released on shutdown

### 4.5 Concurrency & Thread Safety

- [ ] Enterprise: **Race Conditions Addressed** — Shared mutable state is synchronized
- [ ] Enterprise: **Async Patterns Correct** — async/await used correctly
- [ ] Mission-Critical: **Deadlock Prevention** — Lock ordering is consistent
- [ ] Mission-Critical: **Atomic Operations** — Used where needed for counters, flags

---

## 5. Clean Code & Software Engineering Principles

### 5.1 Naming & Readability

- [ ] Essential: **Meaningful Names** — Variables and functions have descriptive names
- [ ] Essential: **No Magic Numbers** — Named constants instead of unexplained literals
- [ ] Standard: **Consistent Naming** — Naming conventions applied consistently
- [ ] Standard: **Self-Documenting** — Code intent is clear from reading it

### 5.2 Function Design

- [ ] Standard: **Single Purpose** — Functions do one thing
- [ ] Standard: **Few Arguments** — Functions have 4 or fewer arguments typically
- [ ] Standard: **No Side Effects** — Side effects are explicit and minimized
- [ ] Enterprise: **Command-Query Separation** — Functions either do or return, not both

### 5.3 SOLID Principles

- [ ] Enterprise: **Single Responsibility** — Classes have one reason to change
- [ ] Enterprise: **Open/Closed** — Open for extension, closed for modification
- [ ] Enterprise: **Liskov Substitution** — Derived classes substitute for base
- [ ] Enterprise: **Interface Segregation** — Interfaces are focused
- [ ] Enterprise: **Dependency Inversion** — Depend on abstractions

### 5.4 Error Handling

- [ ] Essential: **Errors Not Swallowed** — Errors are logged or propagated
- [ ] Essential: **User-Friendly Messages** — End users see helpful messages
- [ ] Standard: **Specific Exceptions** — Using specific error types, not generic
- [ ] Standard: **Error Context** — Errors include context for debugging
- [ ] Enterprise: **Exception Hierarchy** — Clear exception/error type hierarchy
- [ ] Enterprise: **Recovery Where Possible** — Graceful recovery when appropriate
- [ ] Mission-Critical: **Circuit Breakers** — For external dependencies

### 5.5 Defensive Programming

- [ ] Standard: **Input Validation** — User input validated at boundaries
- [ ] Standard: **Null Safety** — Null/undefined handled safely
- [ ] Enterprise: **Bounds Checking** — Array/collection bounds checked
- [ ] Enterprise: **Type Safety** — Type system used effectively
- [ ] Mission-Critical: **Assertions** — Invariants checked with assertions

---

## 6. Code Readability & AI/Human Maintainability

### 6.1 Human Readability

- [ ] Essential: **Scannable** — Code structure is clear at a glance
- [ ] Essential: **Reasonable File Length** — Files generally under 500 lines
- [ ] Standard: **Low Nesting** — Nesting depth 3-4 levels or less
- [ ] Standard: **Early Returns** — Guard clauses reduce nesting
- [ ] Enterprise: **Cyclomatic Complexity** — Under 10 per function

### 6.2 Documentation

- [ ] Essential: **README Exists** — Project has a README with setup instructions
- [ ] Standard: **Complex Logic Explained** — Non-obvious code has comments
- [ ] Standard: **Why Comments** — Comments explain WHY, not WHAT
- [ ] Enterprise: **API Documentation** — Public interfaces documented
- [ ] Enterprise: **Architecture Documented** — System design is documented
- [ ] Mission-Critical: **Runbooks Exist** — Operational procedures documented

### 6.3 AI & Automation Friendliness

- [ ] Standard: **Clear Intent** — Purpose of each module/function is obvious
- [ ] Standard: **Modular Design** — Discrete, understandable modules
- [ ] Standard: **Consistent Patterns** — Similar problems solved the same way
- [ ] Enterprise: **Explicit Over Implicit** — Behaviors do not rely on hidden conventions
- [ ] Enterprise: **Searchable Names** — Names are unique and searchable
- [ ] Enterprise: **Context Independence** — Functions understandable without reading whole file
- [ ] Enterprise: **Type Information** — Types available (TypeScript, type hints, etc.)
- [ ] Enterprise: **Tests as Examples** — Tests demonstrate correct usage
- [ ] Mission-Critical: **Contract Clarity** — Function contracts (input/output) are explicit

---

## 7. Testing

### 7.1 Test Existence

- [ ] Essential: **Tests Exist** — There are automated tests
- [ ] Essential: **Tests Pass** — All tests pass
- [ ] Essential: **Tests Run in CI** — Tests run automatically on commits

### 7.2 Test Coverage

- [ ] Standard: **Happy Path Covered** — Main functionality is tested
- [ ] Standard: **Edge Cases** — Some edge cases tested
- [ ] Standard: **Error Paths** — Error conditions tested
- [ ] Enterprise: **Coverage Measured** — Coverage >70% for critical paths
- [ ] Enterprise: **No Flaky Tests** — Tests are deterministic
- [ ] Mission-Critical: **Mutation Testing** — Test quality validated

### 7.3 Test Types

- [ ] Enterprise: **Unit Tests** — Isolated unit tests exist
- [ ] Enterprise: **Integration Tests** — Integration points tested
- [ ] Enterprise: **API Tests** — API endpoints tested
- [ ] Mission-Critical: **E2E Tests** — Critical user journeys tested
- [ ] Mission-Critical: **Performance Tests** — Load testing performed
- [ ] Mission-Critical: **Security Tests** — Security scanning integrated

### 7.4 Test Quality

- [ ] Standard: **Tests Verify Behavior** — Read 3-5 test files. Tests assert on actual behavior and outputs, not just that modules are importable or that mocks return expected values
- [ ] Standard: **Tests Would Catch Regressions** — For each test read, ask: would this test fail if the underlying logic broke? If the answer is no, the test is not providing value
- [ ] Enterprise: **Tests Are Readable** — Tests serve as documentation
- [ ] Enterprise: **Tests Are Maintainable** — Tests do not break on refactors
- [ ] Enterprise: **Test Data Managed** — Test fixtures are managed properly — no silent skips when test data is missing
- [ ] Mission-Critical: **Contract Tests** — For microservices, contracts tested

---

## 8. Security

### 8.1 Authentication

- [ ] Standard: **Auth Exists** — Authentication is implemented (if users exist)
- [ ] Standard: **Passwords Hashed** — Passwords use bcrypt/argon2/scrypt
- [ ] Standard: **Session Security** — Sessions are secure (HttpOnly, Secure cookies)
- [ ] Enterprise: **MFA Available** — Multi-factor authentication available
- [ ] Enterprise: **OAuth/OIDC** — Using standard protocols
- [ ] Mission-Critical: **SSO Support** — Enterprise SSO (SAML, OIDC) supported

### 8.2 Authorization

- [ ] Standard: **Authz Exists** — Authorization checks exist
- [ ] Standard: **Authz Enforced** — Checks happen on backend, not just UI
- [ ] Enterprise: **Role-Based Access** — RBAC or similar model
- [ ] Enterprise: **Resource-Level** — Per-resource authorization
- [ ] Mission-Critical: **Audit Trail** — Permission changes logged

### 8.3 Input Validation

- [ ] Essential: **Input Validated** — User input is validated
- [ ] Essential: **SQL Injection Prevented** — Parameterized queries used
- [ ] Standard: **XSS Prevented** — Output encoding applied
- [ ] Standard: **CSRF Protected** — State-changing operations protected
- [ ] Enterprise: **File Upload Validated** — Uploads validated (type, size)

### 8.4 Data Protection

- [ ] Standard: **HTTPS Only** — TLS for all external communication
- [ ] Standard: **Sensitive Data Identified** — PII is identified
- [ ] Enterprise: **Encryption at Rest** — Sensitive data encrypted
- [ ] Enterprise: **Data Masked in Logs** — Sensitive data not logged
- [ ] Mission-Critical: **Key Management** — Encryption keys properly managed

### 8.5 Dependency Security

- [ ] Standard: **No Critical Vulnerabilities** — No known critical CVEs
- [ ] Standard: **Dependencies Updated** — Dependencies reasonably current
- [ ] Enterprise: **Automated Scanning** — Vulnerability scanning in CI
- [ ] Enterprise: **Update Process** — Process for regular updates

---

## 9. Multi-Tenancy (Tier 3+)

### 9.1 Tenant Isolation

- [ ] Enterprise: **Data Segregation** — Tenant data cannot leak across tenants
- [ ] Enterprise: **Query Scoping** — All queries scoped to tenant
- [ ] Enterprise: **Cache Isolation** — Cached data segregated by tenant
- [ ] Mission-Critical: **File Isolation** — Uploaded files isolated by tenant
- [ ] Mission-Critical: **Background Job Isolation** — Jobs scoped to tenant

### 9.2 Tenant Configuration

- [ ] Enterprise: **Per-Tenant Settings** — Tenants can customize settings
- [ ] Enterprise: **Feature Flags** — Features can be toggled per tenant
- [ ] Mission-Critical: **Custom Domains** — Tenants can use own domains
- [ ] Mission-Critical: **Branding** — White-label support

### 9.3 Tenant Lifecycle

- [ ] Mission-Critical: **Provisioning** — Automated tenant provisioning
- [ ] Mission-Critical: **Data Export** — Tenants can export their data
- [ ] Mission-Critical: **Data Deletion** — Complete tenant deletion supported
- [ ] Mission-Critical: **Tenant Admin** — Tenant self-service administration

---

## 10. Identity & SSO (Tier 3+)

### 10.1 SSO Support

- [ ] Enterprise: **SAML 2.0** — SAML SSO supported
- [ ] Enterprise: **OIDC** — OpenID Connect supported
- [ ] Enterprise: **IdP Tested** — Tested with major IdPs (Okta, Azure AD, etc.)
- [ ] Mission-Critical: **SCIM** — SCIM provisioning supported
- [ ] Mission-Critical: **SSO Enforcement** — SSO can be enforced (disable password)

### 10.2 Session Management

- [ ] Enterprise: **Session Timeout** — Appropriate idle and absolute timeouts
- [ ] Enterprise: **Concurrent Sessions** — Control over concurrent sessions
- [ ] Mission-Critical: **Session Revocation** — Can revoke all sessions
- [ ] Mission-Critical: **Session Visibility** — Users can see active sessions

---

## 11. Scalability & Performance (Tier 2+)

### 11.1 Scalability

- [ ] Standard: **Stateless Design** — Application state externalized
- [ ] Standard: **Database Not Bottleneck** — Database can handle expected load
- [ ] Enterprise: **Horizontal Scaling** — Can scale horizontally
- [ ] Enterprise: **Auto-Scaling** — Auto-scaling configured
- [ ] Mission-Critical: **No Single Points of Failure** — Redundancy in place

### 11.2 Performance

- [ ] Standard: **Acceptable Response Time** — API responses <500ms typical
- [ ] Standard: **Caching Used** — Caching where beneficial
- [ ] Enterprise: **Background Jobs** — Expensive operations offloaded
- [ ] Enterprise: **CDN for Static Assets** — Static assets served via CDN
- [ ] Mission-Critical: **Performance Baselines** — SLOs defined and monitored

---

## 12. Reliability (Tier 2+)

### 12.1 Fault Tolerance

- [ ] Standard: **Errors Handled Gracefully** — App does not crash on errors
- [ ] Standard: **External Calls Have Timeouts** — All network calls timeout
- [ ] Enterprise: **Retries with Backoff** — Retries use exponential backoff
- [ ] Enterprise: **Circuit Breakers** — Circuit breakers for external deps
- [ ] Mission-Critical: **Graceful Degradation** — Fallbacks when dependencies fail

### 12.2 Data Durability

- [ ] Standard: **Backups Exist** — Database is backed up
- [ ] Enterprise: **Backups Tested** — Backups verified for recoverability
- [ ] Enterprise: **Transactions Used** — Database transactions used correctly
- [ ] Mission-Critical: **Point-in-Time Recovery** — PITR available
- [ ] Mission-Critical: **DR Plan** — Disaster recovery plan documented and tested

---

## 13. Observability (Tier 2+)

### 13.1 Logging

- [ ] Standard: **Logs Exist** — Application produces logs
- [ ] Standard: **Log Levels Used** — Appropriate use of DEBUG, INFO, WARN, ERROR
- [ ] Enterprise: **Structured Logging** — Logs are structured (JSON)
- [ ] Enterprise: **Correlation IDs** — Request tracing across components
- [ ] Enterprise: **Centralized Logs** — Logs aggregated centrally
- [ ] Mission-Critical: **Sensitive Data Excluded** — No secrets/PII in logs

### 13.2 Monitoring

- [ ] Enterprise: **Health Checks** — Health check endpoints exist
- [ ] Enterprise: **Metrics Collected** — Key metrics instrumented
- [ ] Enterprise: **Dashboards Exist** — Operational dashboards available
- [ ] Mission-Critical: **SLI/SLO Defined** — Service levels defined and tracked
- [ ] Mission-Critical: **Distributed Tracing** — Traces across service boundaries

### 13.3 Alerting

- [ ] Enterprise: **Alerts Configured** — Alerts for critical failures
- [ ] Enterprise: **Alerts Actionable** — Alerts are not noisy
- [ ] Mission-Critical: **Runbooks Linked** — Alerts link to runbooks
- [ ] Mission-Critical: **On-Call Rotation** — Proper on-call process

---

## 14. Deployment & Operations

### 14.1 Build & Deploy

- [ ] Essential: **Build Documented** — How to build is documented
- [ ] Essential: **Deploy Documented** — How to deploy is documented
- [ ] Standard: **Automated Build** — CI builds on every commit
- [ ] Standard: **Automated Deploy** — Deployment is automated
- [ ] Enterprise: **Infrastructure as Code** — IaC for infrastructure
- [ ] Enterprise: **Environment Parity** — Environments are similar

### 14.2 Deployment Strategy

- [ ] Enterprise: **Zero-Downtime** — Deployments do not cause downtime
- [ ] Enterprise: **Rollback Capability** — Can rollback quickly
- [ ] Mission-Critical: **Canary/Blue-Green** — Gradual rollout supported
- [ ] Mission-Critical: **Feature Flags** — Feature flags for releases

### 14.3 Configuration

- [ ] Standard: **Config Externalized** — Config not hardcoded
- [ ] Standard: **Env-Specific Config** — Different config per environment
- [ ] Enterprise: **Config Validated** — Config validated at startup
- [ ] Enterprise: **Config Documented** — All config options documented

---

## 15. Licensing & Legal

### 15.1 Dependencies

- [ ] Standard: **Licenses Known** — Dependencies' licenses are known
- [ ] Standard: **No Problematic Licenses** — No GPL/AGPL if incompatible with use
- [ ] Enterprise: **License Inventory** — Complete license inventory exists
- [ ] Enterprise: **Attribution Met** — Attribution requirements satisfied

### 15.2 Intellectual Property

- [ ] Enterprise: **Copyright Notices** — Appropriate copyright notices
- [ ] Enterprise: **Code Provenance Clear** — Origin of all code is clear
- [ ] Mission-Critical: **CLA if Needed** — Contributor agreement if accepting contributions

---

## 16. Developer Experience

### 16.1 Getting Started

- [ ] Essential: **Setup Documented** — README has setup instructions
- [ ] Essential: **Setup Works** — Following docs actually works
- [ ] Standard: **Setup Time <30min** — New dev productive in 30 minutes
- [ ] Standard: **Local Dev Easy** — Can run locally without cloud access

### 16.2 Development Workflow

- [ ] Standard: **PR Process Clear** — How to contribute is documented
- [ ] Standard: **CI Fast** — CI feedback in <10 minutes
- [ ] Enterprise: **Hot Reload** — Fast iteration with hot reload
- [ ] Enterprise: **Debugging Easy** — Debug configurations available

---

## Open Source Software Addendum

Include this section if the project is open source. Key areas:

- **License & Legal** — LICENSE file, SPDX identifier, DCO/CLA, third-party license compatibility
- **Community Documentation** — README quality, CONTRIBUTING.md, CODE_OF_CONDUCT.md, issue/PR templates, GOVERNANCE.md, ROADMAP.md, CHANGELOG.md
- **Security for OSS** — SECURITY.md with vulnerability reporting process, security advisories, CVE process
- **Versioning & Releases** — Semantic versioning, git tags, release notes, deprecation policy
- **Distribution & Packaging** — Published to appropriate registry, install works, minimal dependencies
- **Contribution Workflow** — Easy first contribution, CI on PRs, review process, good first issues, timely responses
- **Project Health & Sustainability** — Multiple maintainers, succession plan, bus factor >1
- **Testing & Quality for OSS** — Public CI, coverage visible, matrix testing, platform testing
- **Documentation for OSS** — API reference, examples, tutorials, migration guides

---

## Proprietary Software Addendum

Include this section for proprietary/closed-source software:

- **Trade Secret Protection** — Proprietary algorithms protected, license enforcement, code obfuscation
- **Vendor Management** — Commercial library licenses tracked, compliance with seat/usage limits
- **Customer Data Protection** — Data isolation, DPA compliance, data residency, customer audit support

---

## Industry-Specific Addenda

### Financial Services
Audit logging, PCI-DSS, reconciliation, regulatory reporting, AML/KYC

### Healthcare
HIPAA safeguards, PHI identification, minimum necessary, BAA compliance, emergency access

### E-Commerce
PCI compliance, inventory accuracy, fraud detection, tax calculation

### Government / Public Sector
FedRAMP, Section 508 accessibility, FIPS 140-2 cryptography, data sovereignty
