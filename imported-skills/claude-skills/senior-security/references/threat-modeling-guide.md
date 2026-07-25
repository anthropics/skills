# Threat Modeling Guide

Systematic approaches for identifying, analyzing, and mitigating security threats.

---

## Table of Contents

- [Threat Modeling Process](#threat-modeling-process)
- [STRIDE Framework](#stride-framework)
- [Attack Trees](#attack-trees)
- [DREAD Risk Scoring](#dread-risk-scoring)
- [Data Flow Diagrams](#data-flow-diagrams)
- [Common Attack Patterns](#common-attack-patterns)

---

## Threat Modeling Process

### Workflow: Conduct Threat Model

1. Define the scope and objectives:
   - System boundaries
   - Assets to protect
   - Trust levels
2. Create data flow diagram:
   - External entities
   - Processes
   - Data stores
   - Data flows
   - Trust boundaries
3. Identify threats using STRIDE:
   - Apply STRIDE to each DFD element
   - Document threat scenarios
4. Analyze and prioritize risks:
   - Score using DREAD
   - Rank by severity
5. Define mitigations:
   - Map controls to threats
   - Identify gaps
6. Validate and iterate:
   - Review with team
   - Update as system evolves
7. Document in threat model report
8. **Validation:** All DFD elements analyzed; threats documented; mitigations mapped; residual risks accepted

### Threat Model Template

```
THREAT MODEL REPORT

System: [System Name]
Version: [Version]
Date: [Date]
Author: [Name]

1. SYSTEM OVERVIEW
   - Purpose: [Description]
   - Users: [User types]
   - Data: [Data classification]

2. SCOPE
   - In Scope: [Components included]
   - Out of Scope: [Components excluded]
   - Assumptions: [Security assumptions]

3. DATA FLOW DIAGRAM
   [DFD image or ASCII representation]

4. THREATS IDENTIFIED
   | ID | Element | STRIDE | Threat | DREAD | Mitigation |
   |----|---------|--------|--------|-------|------------|

5. RESIDUAL RISKS
   [Accepted risks with justification]

6. RECOMMENDATIONS
   [Prioritized security improvements]
```

---

## STRIDE Framework

Categorization model for identifying threats.

### STRIDE Categories

| Category | Description | Violated Property |
|----------|-------------|-------------------|
| **S**poofing | Pretending to be someone/something else | Authentication |
| **T**ampering | Modifying data or code | Integrity |
| **R**epudiation | Denying actions occurred | Non-repudiation |
| **I**nformation Disclosure | Exposing data to unauthorized parties | Confidentiality |
| **D**enial of Service | Making system unavailable | Availability |
| **E**levation of Privilege | Gaining unauthorized access | Authorization |

### STRIDE per Element

| DFD Element | Applicable Threats |
|-------------|-------------------|
| External Entity | S, R |
| Process | S, T, R, I, D, E |
| Data Store | T, R, I, D |
| Data Flow | T, I, D |

### STRIDE Analysis Template

```
STRIDE ANALYSIS

Element: User Authentication Service
Type: Process

┌─────────────────────────────────────────────────────────────────┐
│ SPOOFING                                                        │
├─────────────────────────────────────────────────────────────────┤
│ Threat: Attacker uses stolen credentials to impersonate user   │
│ Attack Vector: Phishing, credential stuffing, session hijack   │
│ Likelihood: High                                                │
│ Impact: High - Full account access                              │
│ Mitigation: MFA, session binding, anomaly detection             │
└─────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────┐
│ TAMPERING                                                       │
├─────────────────────────────────────────────────────────────────┤
│ Threat: Attacker modifies authentication request in transit    │
│ Attack Vector: Man-in-the-middle, request manipulation         │
│ Likelihood: Medium                                              │
│ Impact: High - Bypass authentication                            │
│ Mitigation: TLS 1.3, request signing, HSTS                      │
└─────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────┐
│ REPUDIATION                                                     │
├─────────────────────────────────────────────────────────────────┤
│ Threat: User denies performing privileged action               │
│ Attack Vector: Claim account was compromised                   │
│ Likelihood: Medium                                              │
│ Impact: Medium - Dispute resolution difficulty                  │
│ Mitigation: Comprehensive audit logging, log integrity         │
└─────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────┐
│ INFORMATION DISCLOSURE                                          │
├─────────────────────────────────────────────────────────────────┤
│ Threat: Password hashes exposed via SQL injection              │
│ Attack Vector: SQLi, backup exposure, error messages           │
│ Likelihood: Medium                                              │
│ Impact: Critical - Mass credential compromise                   │
│ Mitigation: Parameterized queries, encryption, error handling  │
└─────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────┐
│ DENIAL OF SERVICE                                               │
├─────────────────────────────────────────────────────────────────┤
│ Threat: Brute force attacks overwhelm authentication service   │
│ Attack Vector: Credential stuffing, distributed attacks        │
│ Likelihood: High                                                │
│ Impact: High - Users cannot authenticate                        │
│ Mitigation: Rate limiting, CAPTCHA, account lockout            │
└─────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────┐
│ ELEVATION OF PRIVILEGE                                          │
├─────────────────────────────────────────────────────────────────┤
│ Threat: Regular user gains admin privileges                    │
│ Attack Vector: JWT manipulation, IDOR, role confusion          │
│ Likelihood: Medium                                              │
│ Impact: Critical - Full system compromise                       │
│ Mitigation: Server-side authorization, signed tokens, RBAC     │
└─────────────────────────────────────────────────────────────────┘
```

### Threat Mitigation Matrix

| STRIDE Category | Standard Mitigations |
|-----------------|---------------------|
| Spoofing | Authentication (passwords, MFA, certificates) |
| Tampering | Integrity controls (signing, hashing, checksums) |
| Repudiation | Audit logging, digital signatures, timestamps |
| Information Disclosure | Encryption, access controls, data masking |
| Denial of Service | Rate limiting, redundancy, filtering |
| Elevation of Privilege | Authorization, least privilege, input validation |

---

## Attack Trees

Visual representation of attack paths to a specific goal.

### Attack Tree Structure

```
ATTACK TREE: Compromise User Account

                    ┌─────────────────────┐
                    │ GOAL: Access User   │
                    │      Account        │
                    └──────────┬──────────┘
                               │
           ┌───────────────────┼───────────────────┐
           │                   │                   │
    ┌──────┴──────┐     ┌──────┴──────┐     ┌──────┴──────┐
    │   Obtain    │     │   Bypass    │     │   Exploit   │
    │ Credentials │     │    Auth     │     │   Session   │
    │    [OR]     │     │    [OR]     │     │    [OR]     │
    └──────┬──────┘     └──────┬──────┘     └──────┬──────┘
           │                   │                   │
     ┌─────┼─────┐       ┌─────┼─────┐       ┌─────┼─────┐
     │     │     │       │     │     │       │     │     │
   ┌─┴─┐ ┌─┴─┐ ┌─┴─┐   ┌─┴─┐ ┌─┴─┐ ┌─┴─┐   ┌─┴─┐ ┌─┴─┐ ┌─┴─┐
   │Phi│ │Crd│ │Key│   │SQL│ │JWT│ │Pwd│   │XSS│ │Fix│ │Sid│
   │sh │ │Stf│ │Log│   │ i │ │Frg│ │Rst│   │   │ │tn │ │Hj │
   └───┘ └───┘ └───┘   └───┘ └───┘ └───┘   └───┘ └───┘ └───┘

Legend:
- Phi: Phishing
- CrdStf: Credential Stuffing
- KeyLog: Keylogger
- SQLi: SQL Injection
- JWTFrg: JWT Forgery
- PwdRst: Password Reset Flaw
- XSS: Cross-Site Scripting
- Fixtn: Session Fixation
- SidHj: Session Hijacking
```

### Attack Tree Analysis

| Attack Path | Difficulty | Detection | Priority |
|-------------|------------|-----------|----------|
| Phishing → Credential theft | Low | Medium | High |
| SQL Injection → Auth bypass | Medium | High | Critical |
| XSS → Session steal | Medium | Medium | High |
| JWT forgery → Privilege escalation | High | Low | Critical |

### Calculating Attack Probability

```python
def calculate_attack_probability(attack_tree_node):
    """
    Calculate cumulative probability of attack success.

    For OR nodes: P = 1 - (1-P1)(1-P2)...(1-Pn)
    For AND nodes: P = P1 * P2 * ... * Pn
    """
    if node.is_leaf:
        return node.probability

    child_probs = [calculate_attack_probability(c) for c in node.children]

    if node.operator == 'OR':
        # At least one path succeeds
        prob_all_fail = 1
        for p in child_probs:
            prob_all_fail *= (1 - p)
        return 1 - prob_all_fail

    elif node.operator == 'AND':
        # All paths must succeed
        prob_all_succeed = 1
        for p in child_probs:
            prob_all_succeed *= p
        return prob_all_succeed
```

---

## DREAD Risk Scoring

Quantitative risk assessment for prioritizing threats.

### DREAD Components

| Factor | Description | Scale |
|--------|-------------|-------|
| **D**amage | How bad is the impact? | 1-10 |
| **R**eproducibility | How easy to reproduce? | 1-10 |
| **E**xploitability | How easy to exploit? | 1-10 |
| **A**ffected Users | How many users impacted? | 1-10 |
| **D**iscoverability | How easy to find? | 1-10 |

### DREAD Scoring Guide

**Damage Potential:**
| Score | Description |
|-------|-------------|
| 10 | Complete system compromise, data destruction |
| 7-9 | Large data breach, significant financial loss |
| 4-6 | Partial data exposure, service degradation |
| 1-3 | Minor information disclosure, low impact |

**Reproducibility:**
| Score | Description |
|-------|-------------|
| 10 | Always reproducible, automated |
| 7-9 | Reproducible most of the time |
| 4-6 | Reproducible with some effort |
| 1-3 | Difficult to reproduce, timing dependent |

**Exploitability:**
| Score | Description |
|-------|-------------|
| 10 | No skills required, exploit exists |
| 7-9 | Basic skills, tools available |
| 4-6 | Moderate skills required |
| 1-3 | Advanced skills, custom exploit needed |

**Affected Users:**
| Score | Description |
|-------|-------------|
| 10 | All users |
| 7-9 | Large subset of users |
| 4-6 | Some users |
| 1-3 | Few or individual users |

**Discoverability:**
| Score | Description |
|-------|-------------|
| 10 | Publicly documented, obvious |
| 7-9 | Easy to find via scanning |
| 4-6 | Requires investigation |
| 1-3 | Obscure, requires insider knowledge |

### DREAD Calculation

```python
def calculate_dread_score(damage, reproducibility, exploitability,
                           affected_users, discoverability):
    """
    Calculate DREAD risk score.

    Returns: Float between 1-10
    Risk Levels:
        8-10: Critical
        6-7.9: High
        4-5.9: Medium
        1-3.9: Low
    """
    score = (damage + reproducibility + exploitability +
             affected_users + discoverability) / 5
    return round(score, 1)

def get_risk_level(dread_score):
    if dread_score >= 8:
        return 'Critical'
    elif dread_score >= 6:
        return 'High'
    elif dread_score >= 4:
        return 'Medium'
    else:
        return 'Low'
```

### DREAD Assessment Example

```
THREAT: SQL Injection in Login Form

| Factor | Score | Justification |
|--------|-------|---------------|
| Damage | 9 | Full database access, credential theft |
| Reproducibility | 9 | Consistent, automated tools exist |
| Exploitability | 8 | Well-documented attack, easy tools |
| Affected Users | 10 | All users with accounts |
| Discoverability | 7 | Scanners detect easily |

DREAD Score: (9+9+8+10+7)/5 = 8.6
Risk Level: CRITICAL
Priority: Immediate remediation required
```

---

## Data Flow Diagrams

Visual representation of system data movement for security analysis.

### DFD Elements

| Symbol | Element | Security Considerations |
|--------|---------|------------------------|
| Rectangle | External Entity | Trust boundary crossing |
| Circle/Oval | Process | All STRIDE threats apply |
| Parallel Lines | Data Store | Tampering, disclosure, DoS |
| Arrow | Data Flow | Tampering, disclosure, DoS |
| Dashed Line | Trust Boundary | Authentication required |

### DFD Levels

| Level | Description | Use Case |
|-------|-------------|----------|
| Level 0 (Context) | Single process, external entities | Executive overview |
| Level 1 | Major processes expanded | Architecture review |
| Level 2 | Detailed subprocesses | Detailed threat modeling |

### Example: E-Commerce DFD

```
LEVEL 0: CONTEXT DIAGRAM

                              ┌──────────────────┐
                              │                  │
     ┌────────────┐           │   E-Commerce     │           ┌────────────┐
     │            │  Orders   │    System        │  Payment  │            │
     │  Customer  │──────────▶│                  │──────────▶│  Payment   │
     │            │◀──────────│                  │◀──────────│  Gateway   │
     └────────────┘  Status   │                  │  Result   └────────────┘
                              │                  │
                              └──────────────────┘
                                      │
                                      │ Fulfillment
                                      ▼
                              ┌────────────────┐
                              │   Warehouse    │
                              │    System      │
                              └────────────────┘


LEVEL 1: EXPANDED VIEW

┌─────────────────────────────────────────────────────────────────────┐
│                         TRUST BOUNDARY                               │
│  - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  │
│                                                                      │
│   ┌─────────┐       ┌─────────┐       ┌─────────┐       ┌─────────┐ │
│   │         │       │   Web   │       │  Order  │       │ Payment │ │
│   │   CDN   │──────▶│ Server  │──────▶│ Service │──────▶│ Service │ │
│   │         │       │         │       │         │       │         │ │
│   └─────────┘       └────┬────┘       └────┬────┘       └────┬────┘ │
│                          │                 │                 │      │
│                          │                 │                 │      │
│                          ▼                 ▼                 ▼      │
│                    ╔═══════════╗     ╔═══════════╗    ╔═══════════╗ │
│                    ║  Session  ║     ║  Orders   ║    ║  Payment  ║ │
│                    ║   Store   ║     ║    DB     ║    ║    DB     ║ │
│                    ╚═══════════╝     ╚═══════════╝    ╚═══════════╝ │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
                          │
                          │ Crosses Trust Boundary
                          ▼
                    ┌───────────┐
                    │  Payment  │
                    │  Gateway  │
                    │ (External)│
                    └───────────┘
```

### Trust Boundary Analysis

| Boundary Crossing | Authentication | Authorization | Encryption |
|-------------------|----------------|---------------|------------|
| Customer → Web Server | Session cookie | - | TLS 1.3 |
| Web Server → Order Service | mTLS | Service account | Internal TLS |
| Order Service → DB | Connection pool | DB user roles | TLS |
| Payment Service → Gateway | API key + HMAC | IP whitelist | TLS 1.3 |

---

## Common Attack Patterns

### OWASP Top 10 Mapping

| Rank | Vulnerability | STRIDE | Common Attack |
|------|---------------|--------|---------------|
| A01 | Broken Access Control | E | IDOR, privilege escalation |
| A02 | Cryptographic Failures | I | Weak encryption, exposed keys |
| A03 | Injection | T, E | SQLi, XSS, command injection |
| A04 | Insecure Design | All | Logic flaws, missing controls |
| A05 | Security Misconfiguration | I, E | Default creds, verbose errors |
| A06 | Vulnerable Components | All | Outdated libraries, CVEs |
| A07 | Authentication Failures | S, E | Credential stuffing, weak passwords |
| A08 | Software/Data Integrity | T | Unsigned updates, CI/CD attacks |
| A09 | Logging Failures | R | Missing logs, log injection |
| A10 | SSRF | I, T | Internal service access |

### Attack Pattern Catalog

```
ATTACK PATTERN: SQL Injection (A03)

Threat: T (Tampering), E (Elevation of Privilege)

Attack Vector:
1. Identify input fields that construct SQL queries
2. Test for injection: ' OR '1'='1' --
3. Extract data: UNION SELECT password FROM users
4. Escalate: Execute stored procedures, write files

Detection:
- WAF rules for SQL patterns
- Prepared statement verification
- Database query logging

Mitigation:
- Parameterized queries (primary)
- Input validation (secondary)
- Least privilege database accounts
- Web application firewall

Test Cases:
- Single quote injection: '
- Boolean-based: ' OR 1=1 --
- Time-based: '; WAITFOR DELAY '0:0:5' --
- UNION-based: ' UNION SELECT NULL, username, password FROM users --
```

### Threat Intelligence Integration

| Source | Purpose | Update Frequency |
|--------|---------|------------------|
| CVE/NVD | Known vulnerabilities | Daily |
| MITRE ATT&CK | Attack techniques | Quarterly |
| OWASP | Web application threats | Annual |
| Industry ISACs | Sector-specific threats | Real-time |
