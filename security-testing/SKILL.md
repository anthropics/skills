---
name: seal-security-testing
description: >
  Handle security testing — unit testing, integration testing, fuzz testing, static analysis, formal verification. Use when discussing testing strategies, fuzzing, static analysis tools, or formal verification. Load seal-devsecops for CI/CD integration. Load seal-secure-software-development for code standards. Load seal-external-security-reviews for external audits.
metadata:
  category: security
  tags: ['testing', 'fuzz-testing', 'static-analysis']
  related_skills: ["seal-external-security-reviews", "seal-devsecops", "seal-secure-software-development"]
---

# Security Testing

Security testing methodologies — unit testing, integration testing, fuzz testing, mutation testing, static analysis, and formal verification.

## When to Use
- User asks about security testing practices, policies, or procedures
- Incident or scenario involving security testing concepts
- Need guidance on security testing frameworks or implementations
- Security training or awareness question touching this domain

## Related Domains
This skill connects to: seal-external-security-reviews, seal-devsecops, seal-secure-software-development
Use `skill_view("seal-external-security-reviews")` if the question spans multiple areas.

## Key Concepts
# Security Testing
The objective of Security testing, while most likely impossible, is to ensure that applications and systems are
resilient to attacks and free from vulnerabilities. This section covers various security testing methodologies,
including dynamic and static application security testing, fuzz testing, and security regression testing.
There are several types of testing:
- **Unit Testing**: Tests individual components or functions of the codebase.
- **Integration Testing**: Tests the interaction between different components or systems.
- **Fuzz Testing**: Tests the application by providing random or unexpected inputs to identify vulnerabilities.
- **Static Analysis**: Analyzes the code without executing it to find potential vulnerabilities.
- **Formal Verification**: Uses mathematical methods to prove the correctness of algorithms and protocols.
Some types of testing overlap, for example, a unit test could also be a fuzz test. We will focus on testing and how it
applies to smart contracts, and use solidity as an example.
## Gotchas
- Fuzz testing finds edge cases but not logic bugs — combine with formal verification for critical contracts
- 100% code coverage doesn't mean secure — coverage measures execution, not correctness
- Mutation testing reveals weak tests but is slow — run it in nightly CI, not on every commit

## References
- Fuzz Testing
- Formal Verification
- Unit Testing
- Integration Testing
- Mutation Testing
- Static Analysis
