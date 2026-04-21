---
name: audit-preparation-advisor
description: Guide protocols through security audit preparation, auditor selection, and post-audit processes. Use when users ask about getting smart contracts audited, choosing audit firms, preparing documentation for auditors, understanding audit reports, or timing audits before launch. Triggers on questions about "when should I get audited," "how to prepare for audit," or "which auditor should I use."
---

# Audit Preparation Advisor

Help protocols prepare for and get maximum value from security audits.

## Audit Timeline

| Phase | Duration | Activities |
|-------|----------|------------|
| **Pre-Audit** | 2-4 weeks | Code freeze, documentation, internal testing |
| **Audit** | 2-6 weeks | Auditor review (depends on codebase size) |
| **Remediation** | 1-2 weeks | Fix findings, get re-review |
| **Post-Audit** | Ongoing | Monitor, bug bounty, incident response |

**Key Rule**: Never rush an audit. Budget 2-3 months minimum from "code complete" to mainnet.

## When to Get Audited

**Must audit before:**
- Mainnet deployment
- Major upgrades affecting funds
- New integrations with external protocols
- Significant logic changes

**Consider re-audit when:**
- >20% of code changed since last audit
- New attack vectors discovered in ecosystem
- Integrating new dependencies
- 12+ months since last audit

## Auditor Selection

### Evaluation Criteria
1. **Relevant Experience** - Have they audited similar protocols?
2. **Track Record** - Check past audit quality, not just quantity
3. **Methodology** - Manual review + tools + formal methods?
4. **Team Quality** - Who specifically will review your code?
5. **Communication** - Responsive during scoping and questions?
6. **Timeline** - Can they fit your schedule?

### Red Flags
- Guaranteed "no bugs" claims
- Extremely low prices (you get what you pay for)
- No questions during scoping
- Won't share sample reports
- Rushed timeline pressure

### Price Expectations (2024)
| Codebase Size | Typical Range |
|---------------|---------------|
| Small (<1k LoC) | $15k-$40k |
| Medium (1k-5k LoC) | $40k-$100k |
| Large (5k-15k LoC) | $100k-$250k |
| Complex/DeFi | $150k-$500k+ |

## Pre-Audit Checklist

### Code Readiness
- [ ] Code complete and frozen
- [ ] All tests passing
- [ ] >80% test coverage
- [ ] Static analysis clean (Slither, Aderyn)
- [ ] No known bugs or TODOs in scope

### Documentation
- [ ] Architecture overview
- [ ] Contract descriptions and interactions
- [ ] Access control documentation
- [ ] Deployment instructions
- [ ] Known risks and assumptions

### Technical Preparation
- [ ] Clean, commented code
- [ ] NatSpec documentation
- [ ] Dependency list with versions
- [ ] Previous audit reports (if any)
- [ ] List of areas of concern

## Understanding Audit Reports

### Severity Levels
| Severity | Meaning | Action |
|----------|---------|--------|
| Critical | Direct fund loss possible | Must fix before deploy |
| High | Significant risk or loss | Must fix before deploy |
| Medium | Limited risk or edge case | Should fix |
| Low | Best practice/minor issue | Consider fixing |
| Informational | Suggestions | Optional |

### Common Finding Types
- **Reentrancy** - External calls before state updates
- **Access Control** - Missing or incorrect permissions
- **Integer Issues** - Overflow, underflow, precision loss
- **Logic Errors** - Incorrect business logic
- **Oracle Manipulation** - Price feed vulnerabilities
- **Front-running** - MEV-susceptible operations

## Reference Files

- See `references/preparation-checklist.md` for detailed preparation steps
- See `references/auditor-questions.md` for questions to ask auditors
