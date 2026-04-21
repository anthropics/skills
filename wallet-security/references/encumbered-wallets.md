# TEE-based Encumbered Wallets

### User Profile

Advanced users, developers, and organizations wanting to implement fine-grained security policies, that don't want to (EVM, Solana, Sui) or can't (Bitcoin, Litecoin, Dogecoin, XRP) make fully customizable logic on each chain individually. Additionally, encumbered wallets can use encrypted storage thus providing a level of transaction privacy.

### Primary Goal

To implement optionally private smart contract-like logic and programmable policies for wallet operations across any blockchain by encumbering private keys with restrictions. This enables features like conditional signing, multi-party authorization, time-locked transactions, and compliance policies that work universally, regardless of the underlying chain's capabilities, by instead relying on TEEs.

### Core Concept: Key Encumbrance

Key encumbrance refers to placing cryptographic or policy-based restrictions on a private key’s signing power. Instead of a raw key being free to sign any message, its use is “handcuffed” by rules or proofs, and access to it is limited to a preset interface. Examples include:

* A key can only sign if a specific policy is met (e.g., only transfers to whitelisted addresses).
* A key must co-sign with another party’s key (multi-sig or MPC).
* A key’s signing rights are tied to a verifiable execution environment (e.g., inside a TEE or governed by smart contract logic).

Essentially, key encumbrance adds programmable controls to private keys, enabling fine-grained access, delegation, and compliance.

### Core Concept: Trusted Execution Environments (TEEs)

A Trusted Execution Environment (TEE) is a secure area of a processor that provides hardware-level protection for code and data. TEEs create an isolated environment where sensitive operations can run protected from the main operating system, other applications, and even privileged system software.

**Key TEE Properties:**
* **Hardware-based Isolation**: Code and data within the TEE are protected by CPU-level security features, not just software isolation.
* **Attestation**: TEEs can cryptographically prove their identity and the integrity of the code running inside them.
* **Sealed Storage**: Data can be encrypted and tied to the specific TEE instance, ensuring it cannot be accessed outside the secure environment.
* **Memory Protection**: TEE memory is encrypted and isolated from the host system, preventing external access to sensitive data.

**Common TEE Technologies:**
* **Intel SGX (Software Guard Extensions)**: Creates secure enclaves within applications that protect against privileged malware and physical attacks.
* **ARM TrustZone**: Divides the processor into "secure" and "non-secure" worlds, with hardware-enforced separation.
* **AMD Memory Guard**: Provides memory encryption and isolation features similar to Intel SGX.
* **Confidential Computing Platforms**: Cloud-based TEE services like Azure Confidential Computing or AWS Nitro Enclaves.

**In Encumbered Wallets:**
TEEs enable private keys to be generated, stored, and used within a protected environment where:
* Keys never exist in plaintext outside the TEE
* Policy logic runs confidentially within the secure enclave
* External observers cannot see the encumbrance rules or key operations
* Attestation proves the wallet is running authentic, unmodified code

This hardware-level protection makes TEE-based encumbered wallets significantly more secure than software-only solutions, as even root or physical access to the host system cannot compromise the keys or policies within the TEE.

**Please note that lately there has been a lot of controversy around TEEs, and many researchers are proving that it is not always the case that they add a layer of security. For more information on this, you can check out [TEE.fail](https://TEE.fail), which addresses vulnerabilities in Intel's and AMD's implementation.**

### Key Benefits & Features

**Cross-Chain Compatibility:**
* **Universal Policy Logic**: Implement sophisticated access controls and transaction policies on any blockchain, including Bitcoin, Litecoin, Dogecoin, and other non-smart contract chains.
* **Chain-Agnostic Security**: Deploy consistent security policies across multiple blockchains without depending on each chain's native capabilities.

**Advanced Access Control:**
* **Fine-Grained Permissions**: Delegate specific rights (voting, trading, asset transfer) to different parties without revealing the full wallet structure.
* **Time-Bounded Policies**: Implement temporary access controls that automatically expire after specified periods.
* **Hierarchical Delegation**: Create multi-level permission structures where sub-policies can grant further access down the chain.
* **Asset-Time Segmentation**: Ensure that specific assets are controlled by exactly one policy at any given time, preventing conflicts.

**Privacy & Selective Disclosure:**
* **Confidential Operations**: Policy logic and key operations remain encrypted and hidden from external observers.
* **Compartmentalized Access**: Each delegatee only sees their authorized subset of operations, maintaining privacy of the overall wallet structure.
* **Selective Transparency**: Use view keys to prove compliance or ownership to auditors without revealing spending control or full delegation hierarchy.

**Compliance & Auditability:**
* **Regulatory Compliance**: Support AML/KYC requirements through selective disclosure mechanisms without compromising user privacy.
* **Institutional Auditing**: Enable institutions to prove 1:1 collateralization or policy adherence to regulators using view keys.
* **Non-Transferability Proofs**: Demonstrate that certain assets (like compliance-bound RWAs or soulbound tokens) remain under original owner control.

**Operational Flexibility:**
* **Programmable Recovery**: Implement sophisticated recovery mechanisms that work across any blockchain without relying on smart contract support.
* **Dynamic Policy Updates**: Modify access controls and delegation structures without changing the underlying blockchain infrastructure.
* **Multi-Asset Management**: Apply consistent policies across different cryptocurrencies and blockchain networks from a single encumbered wallet system.

### Security Considerations & Best Practices

* Implement threshold or multi-party computation-based key custody rather than placing sole trust in a single TEE enclave. Use multi-party threshold signatures or distributed key generation so that a single compromised node cannot break the entire system, providing resilience against both hardware attacks and operational failures.
* Incorporate economic incentive mechanisms such as staking requirements for TEE operators to align security incentives through cryptoeconomic design. Require operators to post collateral that can be slashed for malicious behavior, attestation failures, or policy violations, creating financial disincentives for compromise attempts and encouraging proactive security maintenance of TEE infrastructure.
* Carefully evaluate TEE technology selection based on application memory requirements and security priorities. For encumbered wallet applications with modest memory needs (under 256MB), prefer Intel SGX v1 (Client SGX) which provides integrity protection against hardware attacks, whereas applications requiring larger secure memory may need to accept the trade-offs of newer implementations like Scalable SGX or SEV-SNP that offer greater memory capacity but lack integrity protection against physical attacks.
* Establish continuous re-attestation processes that periodically re-verify enclave conformance on a regular schedule such as hourly or per-block intervals. This helps detect drift, tampering, or compromise attempts over time and ensures that the enclave maintains its security properties throughout its operational lifetime.
* Implement dual-attestation architectures for cloud-deployed nodes by requiring both Intel DCAP quotes and cloud provider attestation services (such as Azure MAA or AWS Nitro Attestation). This approach provides defense-in-depth by anchoring trust through multiple independent attestation roots with different threat models and security assumptions.
* Maintain transparent attestation policy publication by documenting and publicly sharing allowed CPU models, TCB versions, QE/PCS builds, and upgrade paths. This enables operators and auditors to verify compliance independently while providing clear guidance for secure deployment configurations and helping detect potentially compromised or outdated systems.
* Collaborate with hardware vendors and ecosystem partners to push for enhanced TEE security features including replay protection, alias detection, and memory mapping integrity. Engage in industry efforts to improve the fundamental security properties of TEE implementations and advocate for standardized security enhancements across different TEE platforms.

### Relevant Papers

- Austgen, J., Fábrega, A., Kelkar, M., Vilardell, D., Allen, S., Babel, K., Yu, J., & Juels, A. (2024, December 3). Liquefaction: Privately liquefying blockchain assets. arXiv.org. https://arxiv.org/abs/2412.02634
- Dai, W., Deng, J., Wang, Q., Cui, C., Zou, D., & Jin, H. (2018). SBLWT: a secure blockchain lightweight wallet based on TrustZone. IEEE Access, 6, 40638–40648. https://doi.org/10.1109/access.2018.2856864
- Yu, J. (n.d.). PASS: A Provenanced Access Subaccount System for Blockchain Wallets [Stanford University]. https://cs191.stanford.edu/projects/Yu,%20Jay_Systems%20191W.pdf
- Aublin, P.-L., Mahhouk, M., & Kapitza, R. (n.d.). Towards TEEs with Large Secure Memory and Integrity Protection Against HW Attacks [IIJ Innovation Institute, TU Braunschweig]. https://www.ibr.cs.tu-bs.de/bib/xml/aublin2022scalableSGX.html

---

