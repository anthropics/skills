---
name: smart-contract-testing-advisor
description: Guide developers on smart contract security testing including unit tests, fuzz testing, static analysis, formal verification, and test suite evaluation. Use when users ask about testing Solidity contracts, choosing testing tools, improving test coverage, preparing for audits, or evaluating test effectiveness. Triggers on questions about Foundry, Hardhat, Slither, fuzzing, or "how do I test my smart contract."
---

# Smart Contract Testing Advisor

Help developers implement comprehensive security testing for smart contracts.

## Testing Requirements Matrix

| Test Type | When to Use | Tools | Priority |
|-----------|-------------|-------|----------|
| **Unit Testing** | Always | Foundry, Hardhat | Required |
| **Integration Testing** | Always | Foundry fork tests | Required |
| **Fuzz Testing** | Always | Foundry, Echidna | Required |
| **Static Analysis** | Always | Slither, Aderyn | Required |
| **Formal Verification** | Math-heavy code | Certora, Halmos | Conditional |

## Quick Recommendations

**Minimum viable testing** (before any deployment):
1. Unit tests with >80% line coverage
2. Integration tests including fork tests
3. Fuzz tests for all external/public functions
4. Static analysis with Slither (zero high/medium findings)

**Production-ready testing** (before mainnet):
- All of the above, plus:
- Mutation testing to validate test quality
- Formal verification for critical math
- Invariant testing for protocol-wide properties

## Testing Tools

### Foundry (Recommended)
```bash
# Install
curl -L https://foundry.paradigm.xyz | bash
foundryup

# Run tests
forge test

# Run with coverage
forge coverage

# Fuzz testing (built-in)
function testFuzz_Transfer(uint256 amount) public { ... }
```

### Static Analysis
```bash
# Slither (Trail of Bits)
pip install slither-analyzer
slither .

# Aderyn (Cyfrin)
cargo install aderyn
aderyn .
```

### Key Slither Detectors
- `reentrancy-eth` - Reentrancy vulnerabilities
- `arbitrary-send-eth` - Unchecked ETH transfers
- `uninitialized-state` - Uninitialized storage variables
- `tx-origin` - tx.origin authentication

## Test Quality Metrics

### Coverage Analysis
- **Line coverage**: % of code lines executed
- **Branch coverage**: % of conditional branches taken
- **Function coverage**: % of functions called
- Target: >90% branch coverage for critical contracts

### Mutation Testing
Tests whether your tests actually catch bugs:
1. Tool introduces small code changes ("mutants")
2. If tests still pass, you have a gap
3. "Mutation score" = % of mutants killed

Tools: `vertigo-rs`, `gambit`

## Chatroom Response Patterns

**"What tests do I need before audit?"**
→ Unit tests (high coverage), fuzz tests, static analysis with zero high findings, integration tests with mainnet fork

**"Is 80% coverage enough?"**
→ Line coverage alone isn't enough. Focus on branch coverage and mutation testing. 80% branch coverage with high mutation score > 95% line coverage with untested edge cases

**"Foundry or Hardhat?"**
→ Foundry for speed and native fuzzing. Hardhat if you need JavaScript ecosystem or specific plugins. Many teams use both.

## Reference Files

- See `references/testing-patterns.md` for common test patterns
- See `references/tools-setup.md` for detailed tool configuration
