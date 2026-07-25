# Medical Device Cybersecurity Guidance

Complete framework for FDA cybersecurity requirements based on FDA guidance documents and recognized consensus standards.

---

## Table of Contents

- [Regulatory Framework](#regulatory-framework)
- [Premarket Cybersecurity](#premarket-cybersecurity)
- [Postmarket Cybersecurity](#postmarket-cybersecurity)
- [Threat Modeling](#threat-modeling)
- [Security Controls](#security-controls)
- [Software Bill of Materials](#software-bill-of-materials)
- [Vulnerability Management](#vulnerability-management)
- [Documentation Requirements](#documentation-requirements)

---

## Regulatory Framework

### FDA Guidance Documents

| Document | Scope | Key Requirements |
|----------|-------|------------------|
| Premarket Cybersecurity (2023) | 510(k), PMA, De Novo | Security design, SBOM, threat modeling |
| Postmarket Management (2016) | All marketed devices | Vulnerability monitoring, patching |
| Content of Premarket Submissions | Submission format | Documentation structure |

### PATCH Act Requirements (2023)

**Cyber Device Definition:**
- Contains software
- Can connect to internet
- May be vulnerable to cybersecurity threats

**Manufacturer Obligations:**
1. Submit plan to monitor, identify, and address vulnerabilities
2. Design, develop, and maintain processes to ensure device security
3. Provide software bill of materials (SBOM)
4. Comply with other requirements under section 524B

### Recognized Consensus Standards

| Standard | Scope | FDA Recognition |
|----------|-------|-----------------|
| IEC 62443 | Industrial automation security | Recognized |
| NIST Cybersecurity Framework | Security framework | Referenced |
| UL 2900 | Software cybersecurity | Recognized |
| AAMI TIR57 | Medical device cybersecurity | Referenced |
| IEC 81001-5-1 | Health software security | Recognized |

---

## Premarket Cybersecurity

### Cybersecurity Documentation Requirements

```
Cybersecurity Documentation Package:
├── 1. Security Risk Assessment
│   ├── Threat model
│   ├── Vulnerability assessment
│   ├── Risk analysis
│   └── Risk mitigation
├── 2. Security Architecture
│   ├── System diagram
│   ├── Data flow diagram
│   ├── Trust boundaries
│   └── Security controls
├── 3. Cybersecurity Testing
│   ├── Penetration testing
│   ├── Vulnerability scanning
│   ├── Fuzz testing
│   └── Security code review
├── 4. SBOM
│   ├── Software components
│   ├── Versions
│   └── Known vulnerabilities
├── 5. Vulnerability Management Plan
│   ├── Monitoring process
│   ├── Disclosure process
│   └── Patch management
└── 6. Labeling
    ├── Security instructions
    └── End-of-life plan
```

### Device Tier Classification

**Tier 1 - Higher Cybersecurity Risk:**
- Device can connect to another product or network
- A cybersecurity incident could directly result in patient harm

**Tier 2 - Standard Cybersecurity Risk:**
- Device NOT a Tier 1 device
- Still requires cybersecurity documentation

**Documentation Depth by Tier:**

| Element | Tier 1 | Tier 2 |
|---------|--------|--------|
| Threat model | Comprehensive | Basic |
| Penetration testing | Required | Recommended |
| SBOM | Required | Required |
| Security testing | Full suite | Core testing |

### Security by Design Principles

```markdown
## Secure Product Development Framework (SPDF)

### 1. Security Risk Management
- Integrate security into QMS
- Apply throughout product lifecycle
- Document security decisions

### 2. Security Architecture
- Defense in depth
- Least privilege
- Secure defaults
- Fail securely

### 3. Cybersecurity Testing
- Verify security controls
- Test for known vulnerabilities
- Validate threat mitigations

### 4. Cybersecurity Transparency
- SBOM provision
- Vulnerability disclosure
- Coordinated vulnerability disclosure

### 5. Cybersecurity Maintenance
- Monitor for vulnerabilities
- Provide timely updates
- Support throughout lifecycle
```

---

## Postmarket Cybersecurity

### Vulnerability Monitoring

**Sources to Monitor:**
- National Vulnerability Database (NVD)
- ICS-CERT advisories
- Third-party component vendors
- Security researcher reports
- Customer/user reports

**Monitoring Process:**

```
Daily/Weekly Monitoring:
├── NVD feed check
├── Vendor security bulletins
├── Security mailing lists
└── ISAC notifications

Monthly Review:
├── Component vulnerability analysis
├── Risk re-assessment
├── Patch status review
└── Trending threat analysis

Quarterly Assessment:
├── Comprehensive vulnerability scan
├── Third-party security audit
├── Update threat model
└── Security metrics review
```

### Vulnerability Assessment and Response

**CVSS-Based Triage:**

| CVSS Score | Severity | Response Timeframe |
|------------|----------|-------------------|
| 9.0-10.0 | Critical | 24-48 hours assessment |
| 7.0-8.9 | High | 1 week assessment |
| 4.0-6.9 | Medium | 30 days assessment |
| 0.1-3.9 | Low | Quarterly review |

**Exploitability Assessment:**

```markdown
## Vulnerability Exploitation Assessment

### Device-Specific Factors
- [ ] Is the vulnerability reachable in device configuration?
- [ ] Are mitigating controls in place?
- [ ] What is the attack surface exposure?
- [ ] What is the potential patient harm?

### Environment Factors
- [ ] Is exploit code publicly available?
- [ ] Is the vulnerability being actively exploited?
- [ ] What is the typical deployment environment?

### Risk Determination
Uncontrolled Risk = Exploitability × Impact × Exposure

| Risk Level | Action |
|------------|--------|
| Unacceptable | Immediate remediation |
| Elevated | Prioritized remediation |
| Acceptable | Monitor, routine update |
```

### Patch and Update Management

**Update Classification:**

| Type | Description | Regulatory Path |
|------|-------------|-----------------|
| Security patch | Addresses vulnerability only | May not require new submission |
| Software update | New features + security | Evaluate per guidance |
| Major upgrade | Significant changes | New 510(k) evaluation |

**FDA's Cybersecurity Policies:**

1. **Routine Updates:** Generally do not require premarket review
2. **Remediation of Vulnerabilities:** No premarket review if:
   - No new risks introduced
   - No changes to intended use
   - Adequate design controls followed

---

## Threat Modeling

### STRIDE Methodology

| Threat | Description | Device Example |
|--------|-------------|----------------|
| **S**poofing | Pretending to be someone/something else | Fake device identity |
| **T**ampering | Modifying data or code | Altering dosage parameters |
| **R**epudiation | Denying actions | Hiding malicious commands |
| **I**nformation Disclosure | Exposing information | PHI data leak |
| **D**enial of Service | Making resource unavailable | Device becomes unresponsive |
| **E**levation of Privilege | Gaining unauthorized access | Admin access from user |

### Threat Model Template

```markdown
## Device Threat Model

### 1. System Description
Device Name: _____________________
Device Type: _____________________
Intended Use: ____________________

### 2. Architecture Diagram
[Include system diagram with trust boundaries]

### 3. Data Flow Diagram
[Document data flows and data types]

### 4. Entry Points
| Entry Point | Protocol | Authentication | Data Type |
|-------------|----------|----------------|-----------|
| USB port | USB HID | None | Config data |
| Network | HTTPS | Certificate | PHI |
| Bluetooth | BLE | Pairing | Commands |

### 5. Assets
| Asset | Sensitivity | Integrity | Availability |
|-------|-------------|-----------|--------------|
| Patient data | High | High | Medium |
| Device firmware | High | Critical | High |
| Configuration | Medium | High | Medium |

### 6. Threat Analysis
| Threat ID | STRIDE | Entry Point | Asset | Mitigation |
|-----------|--------|-------------|-------|------------|
| T-001 | Spoofing | Network | Auth | Mutual TLS |
| T-002 | Tampering | USB | Firmware | Secure boot |
| T-003 | Information | Network | PHI | Encryption |

### 7. Risk Assessment
| Threat | Likelihood | Impact | Risk | Accept/Mitigate |
|--------|------------|--------|------|-----------------|
| T-001 | Medium | High | High | Mitigate |
| T-002 | Low | Critical | High | Mitigate |
| T-003 | Medium | High | High | Mitigate |
```

### Attack Trees

**Example: Unauthorized Access to Device**

```
Goal: Gain Unauthorized Access
├── 1. Physical Access Attack
│   ├── 1.1 Steal device
│   ├── 1.2 Access debug port
│   └── 1.3 Extract storage media
├── 2. Network Attack
│   ├── 2.1 Exploit unpatched vulnerability
│   ├── 2.2 Man-in-the-middle attack
│   └── 2.3 Credential theft
├── 3. Social Engineering
│   ├── 3.1 Phishing for credentials
│   └── 3.2 Insider threat
└── 4. Supply Chain Attack
    ├── 4.1 Compromised component
    └── 4.2 Malicious update
```

---

## Security Controls

### Authentication and Access Control

**Authentication Requirements:**

| Access Level | Authentication | Session Management |
|--------------|----------------|-------------------|
| Patient | PIN/biometric | Auto-logout |
| Clinician | Password + MFA | Timeout 15 min |
| Service | Certificate | Per-session |
| Admin | MFA + approval | Audit logged |

**Password Requirements:**
- Minimum 8 characters (12+ recommended)
- Complexity requirements
- Secure storage (hashed, salted)
- Account lockout after failed attempts
- Forced change on first use

### Encryption Requirements

**Data at Rest:**
- AES-256 for sensitive data
- Secure key storage (TPM, secure enclave)
- Key rotation procedures

**Data in Transit:**
- TLS 1.2 or higher
- Strong cipher suites
- Certificate validation
- Perfect forward secrecy

**Encryption Implementation Checklist:**

```markdown
## Encryption Controls

### Key Management
- [ ] Keys stored in hardware security module or equivalent
- [ ] Key generation uses cryptographically secure RNG
- [ ] Key rotation procedures documented
- [ ] Key revocation procedures documented
- [ ] Key escrow/recovery procedures (if applicable)

### Algorithm Selection
- [ ] AES-256 for symmetric encryption
- [ ] RSA-2048+ or ECDSA P-256+ for asymmetric
- [ ] SHA-256 or better for hashing
- [ ] No deprecated algorithms (MD5, SHA-1, DES)

### Implementation
- [ ] Using well-vetted cryptographic libraries
- [ ] Proper initialization vector handling
- [ ] Protection against timing attacks
- [ ] Secure key zeroing after use
```

### Secure Communications

**Network Security Controls:**

| Layer | Control | Implementation |
|-------|---------|----------------|
| Transport | TLS 1.2+ | Mutual authentication |
| Network | Firewall | Whitelist only |
| Application | API security | Rate limiting, validation |
| Data | Encryption | End-to-end |

### Code Integrity

**Secure Boot Chain:**

```
Root of Trust (Hardware)
    ↓
Bootloader (Signed)
    ↓
Operating System (Verified)
    ↓
Application (Authenticated)
    ↓
Configuration (Integrity-checked)
```

**Software Integrity Controls:**
- Code signing for all software
- Signature verification before execution
- Anti-rollback protection
- Secure update mechanism

---

## Software Bill of Materials

### SBOM Requirements

**NTIA Minimum Elements:**
1. Supplier name
2. Component name
3. Version of component
4. Other unique identifiers (PURL, CPE)
5. Dependency relationship
6. Author of SBOM data
7. Timestamp

### SBOM Formats

| Format | Standard | Use Case |
|--------|----------|----------|
| SPDX | ISO/IEC 5962:2021 | Comprehensive |
| CycloneDX | OWASP | Security-focused |
| SWID | ISO/IEC 19770-2 | Asset management |

### SBOM Template (CycloneDX)

```xml
<?xml version="1.0" encoding="UTF-8"?>
<bom xmlns="http://cyclonedx.org/schema/bom/1.4">
  <metadata>
    <timestamp>2024-01-15T00:00:00Z</timestamp>
    <tools>
      <tool>
        <vendor>Manufacturer</vendor>
        <name>SBOM Generator</name>
        <version>1.0.0</version>
      </tool>
    </tools>
    <component type="device">
      <name>Medical Device XYZ</name>
      <version>2.0.0</version>
      <supplier>
        <name>Device Manufacturer</name>
      </supplier>
    </component>
  </metadata>
  <components>
    <component type="library">
      <name>openssl</name>
      <version>1.1.1k</version>
      <purl>pkg:generic/openssl@1.1.1k</purl>
      <licenses>
        <license>
          <id>Apache-2.0</id>
        </license>
      </licenses>
    </component>
    <!-- Additional components -->
  </components>
  <dependencies>
    <dependency ref="device-xyz">
      <dependency ref="openssl"/>
    </dependency>
  </dependencies>
</bom>
```

### SBOM Management Process

```
1. Initial SBOM Creation
   └── During development, before submission

2. Vulnerability Monitoring
   └── Continuous monitoring against NVD

3. SBOM Updates
   └── With each software release

4. Customer Communication
   └── SBOM provided on request

5. FDA Submission
   └── Included in premarket submission
```

---

## Vulnerability Management

### Vulnerability Disclosure

**Coordinated Vulnerability Disclosure (CVD):**

```markdown
## Vulnerability Disclosure Policy

### Reporting
- Security contact: security@manufacturer.com
- PGP key available at: [URL]
- Bug bounty program: [if applicable]

### Response Timeline
- Acknowledgment: Within 48 hours
- Initial assessment: Within 5 business days
- Status updates: Every 30 days
- Target remediation: Per severity

### Public Disclosure
- Coordinated with reporter
- After remediation available
- Include mitigations if patch delayed

### Safe Harbor
[Statement on not pursuing legal action against good-faith reporters]
```

### Vulnerability Response Process

```
Discovery
    ↓
Triage (CVSS + Exploitability)
    ↓
Risk Assessment
    ↓
Remediation Development
    ↓
Testing and Validation
    ↓
Deployment/Communication
    ↓
Verification
    ↓
Closure
```

### Customer Communication

**Security Advisory Template:**

```markdown
## Security Advisory

### Advisory ID: [ID]
### Published: [Date]
### Severity: [Critical/High/Medium/Low]

### Affected Products
- Product A, versions 1.0-2.0
- Product B, versions 3.0-3.5

### Description
[Description of vulnerability without exploitation details]

### Impact
[What could happen if exploited]

### Mitigation
[Steps to reduce risk before patch available]

### Remediation
- Patch version: X.X.X
- Download: [URL]
- Installation instructions: [Link]

### Credits
[Acknowledge reporter if agreed]

### References
- CVE-XXXX-XXXX
- Manufacturer reference: [ID]
```

---

## Documentation Requirements

### Premarket Submission Checklist

```markdown
## Cybersecurity Documentation for Premarket Submission

### Device Description (Tier 1 and 2)
- [ ] Cybersecurity risk level justification
- [ ] Global system diagram
- [ ] Data flow diagram

### Security Risk Management (Tier 1 and 2)
- [ ] Threat model
- [ ] Security risk assessment
- [ ] Traceability matrix

### Security Architecture (Tier 1 and 2)
- [ ] Defense-in-depth description
- [ ] Security controls list
- [ ] Trust boundaries identified

### Testing Documentation
#### Tier 1
- [ ] Penetration test report
- [ ] Vulnerability scan results
- [ ] Fuzz testing results
- [ ] Static code analysis
- [ ] Third-party component testing

#### Tier 2
- [ ] Security testing summary
- [ ] Known vulnerability analysis

### SBOM (Tier 1 and 2)
- [ ] Complete component inventory
- [ ] Known vulnerability assessment
- [ ] Support and update plan

### Vulnerability Management (Tier 1 and 2)
- [ ] Vulnerability handling policy
- [ ] Coordinated disclosure process
- [ ] Security update plan

### Labeling (Tier 1 and 2)
- [ ] User security instructions
- [ ] End-of-support date
- [ ] Security contact information
```

### Recommended File Structure

```
Cybersecurity_Documentation/
├── 01_Executive_Summary.pdf
├── 02_Device_Description/
│   ├── System_Diagram.pdf
│   └── Data_Flow_Diagram.pdf
├── 03_Security_Risk_Assessment/
│   ├── Threat_Model.pdf
│   ├── Risk_Assessment.pdf
│   └── Traceability_Matrix.xlsx
├── 04_Security_Architecture/
│   ├── Architecture_Description.pdf
│   ├── Security_Controls.pdf
│   └── Trust_Boundary_Analysis.pdf
├── 05_Security_Testing/
│   ├── Penetration_Test_Report.pdf
│   ├── Vulnerability_Scan_Results.pdf
│   ├── Fuzz_Testing_Report.pdf
│   └── Code_Analysis_Report.pdf
├── 06_SBOM/
│   ├── SBOM.xml (CycloneDX)
│   └── Vulnerability_Analysis.pdf
├── 07_Vulnerability_Management/
│   ├── Vulnerability_Policy.pdf
│   └── Disclosure_Process.pdf
└── 08_Labeling/
    └── Security_Instructions.pdf
```

---

## Quick Reference

### Common Cybersecurity Deficiencies

| Deficiency | Resolution |
|------------|------------|
| Incomplete threat model | Document all entry points, assets, threats |
| No SBOM provided | Generate using automated tools |
| Weak authentication | Implement MFA, strong passwords |
| Missing encryption | Add TLS 1.2+, AES-256 |
| No vulnerability management plan | Create monitoring and response procedures |
| Insufficient testing | Conduct penetration testing |

### Security Testing Requirements

| Test Type | Tier 1 | Tier 2 | Tools |
|-----------|--------|--------|-------|
| Penetration testing | Required | Recommended | Manual + automated |
| Vulnerability scanning | Required | Required | Nessus, OpenVAS |
| Fuzz testing | Required | Recommended | AFL, Peach |
| Static analysis | Required | Recommended | SonarQube, Coverity |
| Dynamic analysis | Required | Recommended | Burp Suite, ZAP |

### Recognized Standards Mapping

| FDA Requirement | IEC 62443 | NIST CSF |
|-----------------|-----------|----------|
| Threat modeling | SR 3 | ID.RA |
| Access control | SR 1, SR 2 | PR.AC |
| Encryption | SR 4 | PR.DS |
| Audit logging | SR 6 | PR.PT, DE.AE |
| Patch management | SR 7 | PR.MA |
| Incident response | SR 6 | RS.RP |
