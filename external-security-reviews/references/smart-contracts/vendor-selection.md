# Vendor Selection

Choosing the right security vendor is crucial for getting maximum value from your security review. There are numerous
security vendors in both the web3 and web2 ecosystems, each with different specializations and approaches.

## Types of Security Audits

Understanding the different types of security audits available helps you choose the right approach for your project:

### Private Security Audits

Private smart contract security audits are performed by security companies or solo auditors, typically involving one or
multiple security researchers specifically chosen by your team or assigned by the security firm.

**Characteristics:**

- Confidential engagement with limited access to code
- Dedicated focus from chosen security researchers
- Personalized attention and direct communication
- Typically higher cost but more thorough coverage

### Public/Competitive Security Audits

Public or competitive audits involve tens or hundreds of security researchers competing to find the highest number of
issues to win a share of a prize pool.

**Characteristics:**

- Open participation from multiple researchers
- Competitive environment drives thorough analysis
- Often more cost-effective than private audits, but less personalized
- Can identify a broader range of issues through diverse perspectives

## Vendor Selection Criteria

### 1. Track Record and Reputation

- Evaluate potential vendors based on their track record, reputation, and experience in your specific technology stack
- Look for vendors with a proven history of addressing security challenges similar to your project's needs
- Check for published audit reports and client testimonials

### 2. Domain Expertise

- **Web3 Focus**: For smart contracts, DeFi protocols, or blockchain infrastructure, choose vendors with deep web3
  security expertise
- **Web2 Focus**: For traditional infrastructure, APIs, or backend systems, consider vendors with strong web2 security
  backgrounds
- **Specialized Knowledge**: If building an L2, DEX, or other specialized system, prioritize vendors with relevant
  experience

### 3. Technical Capabilities

- Ensure the vendor has experience with your specific:
  - Programming languages (Solidity, Rust, Go, etc.)
  - Blockchain platforms (Ethereum, Polygon, Arbitrum, etc.)
  - Protocol types (DeFi, NFTs, DAOs, etc.)
  - Architecture patterns (proxy contracts, multisig, etc.)

### 4. Security Methodology

- **Tool Usage**: Verify they use appropriate automated security tools
- **Manual Review**: Ensure they conduct thorough manual code reviews
- **Testing Approach**: If applicable, look for comprehensive testing methodologies including fuzz testing or formal
  verification

## Due Diligence Process

1. **Request References**: Ask for previous client references and audit examples
2. **Evaluate Methodology**: Understand their specific audit process and deliverables
3. **Assess Communication**: Ensure clear communication channels and responsive support
4. **Review Pricing**: Compare costs against scope and expected value
5. **Timeline Alignment**: Confirm availability matches your project timeline

## Red Flags to Avoid

- Vendors who guarantee finding all vulnerabilities
- Extremely low pricing without clear scope limitations
- Lack of relevant experience in your technology stack
- Poor communication or unresponsive during initial discussions
- No clear methodology or standardized reporting process

# Audit the Auditors

As of today, the best review of the security reviewers that we have is the historical performance of security reviewers.
One of the best ways to evaluate this is to review the historical performance of the security team.

If you see codebases that they reviewed were hacked, this doesn't mean that the team is bad. There are two types of
security teams out there:

- Those who have had codebases they have reviewed hacked
- Those who have not reviewed enough codebases

Additionally, comparing sequential audits of the same codebase can be misleading. If auditor A reviews codebase X, and
then auditor B reviews the same codebase and finds more bugs, some insight from auditor A could have been used to find
those extra bugs. However, if two auditors review the same codebase at the same time, this can be a much better
comparison of the two auditors.

---

