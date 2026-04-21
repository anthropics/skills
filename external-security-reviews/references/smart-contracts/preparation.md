# Preparation

A common misconception is that when doing a security review, you can just hand off the written code and let reviewers do
their work. This approach is inefficient and costly, as auditors will spend time on issues you could have resolved
beforehand. Proper preparation maximizes the value of your security review investment and helps auditors focus on
complex vulnerabilities rather than basic issues.

## How to Get the Most Out of Your Security Review

## Set a Goal for the Review

This is the most important step of a security review and often the most overlooked. By setting a scope that is not too
large or undefined, you are more likely to have a successful audit. If the project is very large, you may want to focus
on the most critical aspects of the project.

## Internal Due Diligence

Conduct internal testing before engaging an external security provider. You can do this by creating and running test
vectors for your code, and leverage automated tools to identify low-hanging fruit. Here’s a list of free/open-source
tools your project could use:

- **Solidity**: slither, mythril, semgrep-smart-contracts
- **Golang**: golangci-lint, go-critic, gosec
- **Rust**: cargo audit, cargo outdated, clippy, cargo geiger, cargo tarpaulin

## Write Clear Documentation

Providing comprehensive documentation is essential for auditors to understand your protocol's intended functionality.
Since 80% of all bugs are due to business logic issues, auditors need to understand what your protocol should do, not
just what the code does.

Documentation should include:

- **Project Overview**: Describe your protocol in plain English—what it does and its components.
- **Flow Diagrams**: Outline all possible interaction paths within your system.
- **Design Choices**: Document design decisions and any known potential issues.
- **Known Restrictions / Limitations**: Document centralization risks and known limitations (e.g., limited TVL, token
support).
- **Dependencies**: List all external dependencies.
- **Access Control / Privileged Roles**: Record all roles and their privileges.

## Provide a Robust Test Suite

Maintaining a comprehensive test suite that covers significant portions of your codebase allows auditors to focus on
finding vulnerabilities rather than understanding basic functionality. Before an audit, ensure you have:

- **Unit Tests**: Test individual functions and components
- **Integration Tests**: Test interactions between different parts of your system
- **Fuzz Testing**: Automated testing with random inputs to find edge cases
- **High Code Coverage**: Aim for substantial coverage of your critical code paths
- **Formal Verification**: If applicable, use formal methods to prove correctness of critical components

## Conduct an Initial Code Walkthrough

The first step in a security audit should be a high-level video walkthrough where you:

- Explain your codebase architecture and key components
- Describe how the code is intended to function
- Highlight critical areas that need special attention
- Provide context for design decisions and trade-offs
- Guide auditors on where to find answers to common questions

This walkthrough helps auditors understand your system quickly and focus their time on security analysis rather than
code comprehension.

---

