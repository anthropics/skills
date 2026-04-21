# Static Analysis

At a high level, static analysis examines the structure, syntax, and patterns of your code without executing it. There
are many forms of static analysis, and compilers like solc rely on these techniques. From a security perspective, static
analysis can help identify potential vulnerabilities and code quality issues.

Some static analysis tools are helpful for finding bugs too. Unlike dynamic testing (unit tests, fuzz tests, integration
tests), these bug-finding-focused static analysis examines your code's structure, syntax, and patterns to identify
potential vulnerabilities and code quality issues. You can think of these static analysis as being an automated code
reviewer that never gets tired and knows common vulnerability patterns.

## Static Analysis in Practice

Static analysis tools parse your source code and analyze it against known vulnerability patterns, coding standards, and
best practices. They can quickly identify issues like:

- **Known vulnerability patterns** (reentrancy, integer overflow, etc.)
- **Code quality issues** (unused variables, dead code)
- **Style violations** (naming conventions, formatting)
- **Logic errors** (unreachable code, incorrect assertions)

For example, this code has a classic reentrancy vulnerability:

```solidity
contract VulnerableContract {
    mapping(address => uint256) public balances;

    function withdraw() public {
        uint256 amount = balances[msg.sender];
        (bool success,) = msg.sender.call{value: amount}("");
        require(success, "Transfer failed");
        balances[msg.sender] = 0; // ❌ State update after external call
    }
}
```

A static analysis tool will automatically detect this reentrancy pattern and flag it as a high-severity issue.

## Static Analysis Tools

- [Aderyn](https://cyfrin.gitbook.io/cyfrin-docs/aderyn-cli/readme)
- [Slither](https://github.com/crytic/slither)
- [Solhint](https://github.com/protofire/solhint)

## References

This document incorporates knowledge from:

- [Cyfrin Updraft Security Testing Curriculum](https://updraft.cyfrin.io)
- [Trail of Bits secure contracts](https://secure-contracts.com/program-analysis/slither/docs/src/api/static_analysis.html)

---

