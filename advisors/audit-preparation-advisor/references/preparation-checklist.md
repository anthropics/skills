# Detailed Audit Preparation Checklist

## 4 Weeks Before Audit

### Code Preparation
- [ ] Feature freeze - no new functionality
- [ ] Remove dead code and unused imports
- [ ] Consistent code style throughout
- [ ] Clear variable and function naming
- [ ] Remove console.log and debug code

### Testing
- [ ] Unit tests for all functions
- [ ] Integration tests for contract interactions
- [ ] Edge case tests (zero values, max values)
- [ ] Access control tests (who can call what)
- [ ] Fuzz tests for mathematical operations
- [ ] Fork tests against mainnet (if integrating)

### Static Analysis
- [ ] Run Slither, fix all highs/mediums
- [ ] Run Aderyn, review all findings
- [ ] Document any false positives with justification
- [ ] Run Mythril or other tools

## 2 Weeks Before Audit

### Documentation Package
Prepare a single document or repo with:

#### 1. Protocol Overview
```markdown
# Protocol Name

## Purpose
[2-3 sentences on what the protocol does]

## Key Features
- Feature 1
- Feature 2

## Architecture Diagram
[Include visual diagram of contract relationships]
```

#### 2. Contract Descriptions
For each contract in scope:
```markdown
## ContractName.sol

**Purpose**: [What this contract does]

**Key Functions**:
- `functionA()`: [Description]
- `functionB()`: [Description]

**Access Control**:
- Owner can: [list]
- Anyone can: [list]

**State Variables**:
- `variableA`: [Purpose and constraints]

**External Interactions**:
- Calls to: [External contracts]
- Called by: [Other contracts]
```

#### 3. Trust Assumptions
```markdown
## Trust Assumptions

### Trusted Entities
- Owner/Admin: [What they can do, what they can't]
- Oracles: [Which oracles, failure modes]
- External protocols: [Dependencies and risks]

### User Assumptions
- Users are expected to: [list]
- Protocol does NOT protect against: [list]
```

#### 4. Known Issues
```markdown
## Known Issues / Accepted Risks

1. **Issue**: [Description]
   **Risk**: [Impact if exploited]
   **Mitigation**: [Why it's acceptable]
   **Status**: Accepted / To be fixed
```

### Technical Package
- [ ] Git repository access (or zip of code)
- [ ] Compilation instructions
- [ ] Test run instructions
- [ ] Deployment scripts
- [ ] Environment variables template

## 1 Week Before Audit

### Final Checks
- [ ] All tests passing on clean clone
- [ ] Dependencies locked to specific versions
- [ ] No uncommitted changes
- [ ] Tag the commit being audited
- [ ] Verify scope matches contract with auditor

### Communication Setup
- [ ] Shared Slack/Discord channel created
- [ ] Primary contacts identified (both sides)
- [ ] Kickoff meeting scheduled
- [ ] Response time expectations set

## During Audit

### Your Responsibilities
- [ ] Respond to questions within 24 hours
- [ ] Don't change code during audit
- [ ] Clarify any assumptions promptly
- [ ] Review preliminary findings quickly

### Track Findings
Create a spreadsheet:
| ID | Severity | Title | Status | Fix Commit | Notes |
|----|----------|-------|--------|------------|-------|
| H-1 | High | ... | Fixed | abc123 | ... |

## Post-Audit

### Remediation Phase
- [ ] Fix all Critical/High findings
- [ ] Fix Medium findings (or document acceptance)
- [ ] Review Low/Info for quick wins
- [ ] Create fix commits with clear messages
- [ ] Request re-review of fixes

### Before Mainnet
- [ ] All critical/high fixes verified by auditor
- [ ] Final audit report received
- [ ] Bug bounty program launched
- [ ] Monitoring and alerting set up
- [ ] Incident response plan documented

### Public Disclosure
- [ ] Publish audit report
- [ ] Announce audit completion
- [ ] Share bug bounty details
- [ ] Document any accepted risks publicly
