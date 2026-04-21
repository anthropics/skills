# Expectations

## Scoping Phase

The team looking for a security review will agree with the auditors/security researchers the exact parameters of the
review. What *exact* contracts should they review? What should they not review? This is incredibly important so the can
clearly estimate timelines on how long a review may take. This is also where compensation is discussed, usually the more
aspects a team wants to review, the more expensive the audit will be.

## Initial Assessment Phase

- **Automated Testing**: Auditors will run various automated security tools including static analysis, fuzz testing,
  formal verification, and unit testing to identify basic vulnerabilities
- **Manual Code Review**: Security researchers will manually analyze the code to understand context, complexity, and
  identify deeper vulnerabilities that automated tools might miss
- **Documentation Review**: Auditors will review project specifications and documentation to understand intended
  functionality

## Deliverables

A comprehensive security review will generate the following:

### Initial Report

- **Vulnerability Identification**: Security vulnerabilities classified by severity (High, Medium, Low)
- **Proof of Concept**: Demonstration of potential exploit scenarios where applicable
- **Gas Optimizations**: Recommendations for improving contract efficiency
- **Informational Findings**: Code quality improvements and best practice recommendations
- **Mitigation Strategies**: Specific recommendations for addressing each identified issue

### Mitigation Phase

- **Fix Review Period**: Time allocated for your team to address identified vulnerabilities
- **Collaborative Support**: Ongoing communication with auditors during the fix implementation
- **Code Re-review**: Assessment of implemented fixes to ensure issues are properly resolved

### Final Report

- **Updated Assessment**: Review of all implemented fixes and their effectiveness
- **Residual Risk Analysis**: Documentation of any remaining risks or limitations
- **Public Publication**: In web3, audit reports are commonly published publicly to build community trust

## Timeline and Cost Expectations

The following are *incredibly rough estimates* for timelines/costs based on Solidity smart contract audits from around
the industry. Actual timelines and costs will vary significantly based on the complexity of the codebase, the number of
contracts, and the specific requirements of the project.

### Duration

- **Small Projects** (< 1000 lines): 1-2 weeks
- **Medium Projects** (1000-4000 lines): 2-5 weeks
- **Large Projects** (> 4000 lines): 5+ weeks

### Cost Range

- **Per Week**: $1,000 - $60,000 depending on complexity and auditor expertise
- **Factors Affecting Cost**: Codebase size, complexity, timeline requirements, auditor reputation

## Important Limitations

- **No Guarantee**: Audits do not guarantee bug-free code or complete security. However, the engagement with the team
  should still provide value (teaching better security practices, improving code quality, etc.)
- **Snapshot in Time**: Audits assess code at a specific commit hash - any changes create unaudited code
- **Ongoing Process**: Security should be viewed as a continuous journey, not a one-time event
- **Emergency Preparedness**: Even audited protocols should have incident response plans and emergency communication
  channels

---

