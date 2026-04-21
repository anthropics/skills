# Secure Multisig Best Practices

> Guidance for designing, operating, and auditing high-assurance multisigs. Use this as your single source for baseline rules, setup guidance, and daily operations.

## Who This Is For

Advanced technical users, developers, Decentralized Autonomous Organizations (DAOs), and organizations responsible for
managing protocol treasuries, smart contract ownership, or significant personal/collective assets.

## Primary Goal

The primary objective is to eliminate single points of failure and establish robust, distributed control over high-value
assets and critical smart contract functions.

## Core Concept: M-of-N Scheme

A multisignature (multisig) wallet is a smart contract that requires a predefined minimum number of approvals `M` from a
total set of authorized signers `N` to execute a transaction. This is known as an `M-of-N` scheme (e.g., 2-of-3,
3-of-5).

By distributing signing authority, a multisig ensures that the compromise of a single private key is insufficient to
authorize the movement of funds or execute a privileged action.

## General Rules

### Thresholds & Configuration

- Minimum of 3 signers
- 50% signing threshold
- 7+ signers for multisigs holding 1M+ in assets (USD equivalent)
- Please see Classification Matrix in [Planning & Classification](/multisig-for-protocols/planning-and-classification#step-3-classification-matrix) for more information on threshold selection.
- All signers must use hardware wallets
- Multisigs managing assets on behalf of a DAO should set unlimited allowance with primary DAO agent
- Signers on multisigs with critical protocol configuration or security roles are discouraged from using their addresses for other purposes. They should create a brand new wallet for that purpose instead.
- No multisigs should use modules/guards except those mentioned in [Setup & Configuration → Modules & Guards](/multisig-for-protocols/setup-and-configuration#modules--guards) unless clear justification and security review is provided
- Threshold exceptions can be made for multisigs that are used in frequent operations but are highly constrained by smart contracts. For example, rate setting operations with tight bounds and a backup recovery mechanism to replace the multisig.

#### Threshold Selection

Avoid `N-of-N` schemes, as the loss of a single key would result in a permanent loss of access to all funds.

#### Strategic Signer Distribution

The security of a multisig depends entirely on the operational security (OpSec) of its individual signer keys. Storing multiple signer keys on the same device or in the same physical location negates the security benefits. Effective distribution strategies include:
- Using different hardware wallet models and manufacturers.
- Maintaining geographical separation for devices holding signer keys.
- Assigning signer keys to different trusted individuals within an organization.
- Using diverse client software to interact with the multisig to mitigate single-point-of-failure risks from a software vulnerability.

### Communication & Documentation

- In the event of loss of access to keys or potential compromise of keys or communication channels, the signer must immediately notify the other multisig participants and email your security contact - [Incident Reporting](/multisig-for-protocols/incident-reporting)
- Signers should use dedicated communication channels for multisig operations and maintain backup ways of reaching other signers
- All multisigs should be documented in the protocol documenting its purpose, general operating rules, multisig wallet address, and list of signer addresses
- Signers should verify their addresses by signing a message stating their affiliation and the multisig they intend to join (entity affiliation is ok)

#### Out-of-Band Verification for Admin Changes

Any critical administrative action, such as adding or replacing a signer, must be verified through multiple, independent communication channels (e.g., a video call and a signed message) to prevent social engineering attacks.

### Signer rotation

- Signers can be rotated, but detailed documentation should be maintained
- Any changes to signer composition should be documented in the protocol documentation
- Any signer change should not reduce the number of signers or decrease the threshold unless clear justification is given and documented

#### Updating signer addresses

If the original key is accessible:
- The signer proves ownership of a new address by signing a message with their existing address.
- The signer must follow the steps in [Signer Verification process](/multisig-for-protocols/registration-and-documentation#signer-verification-process)

If the original key is lost:
- The signer must verify their identity to the other signers through alternative methods such as:
  - Authentication via a verified social media account.
  - A video call with other signers for confirmation.
  - Other sufficient methods.

### Training & Drills

- All signers should complete training as outlined in the [Implementation Checklist](/multisig-for-protocols/implementation-checklist)
- For multisigs that perform emergency operations like pausing, teams should have processes to regularly conduct drills to ensure operational readiness and signer availability

## Setup Best Practices

See General Rules above for thresholds and signer distribution guidance.

* **Practice on Testnet:** Before deploying on mainnet, thoroughly practice wallet creation, transaction signing, and
owner management on a test network.

* **Timelocks:** Enforce a mandatory delay between the approval of a transaction and its execution. This provides a
critical window for the community or team to detect and react to malicious proposals.

* **Role-Based Access Control (RBAC):** Implement modules that grant specific, limited permissions to certain addresses
(e.g., a "pauser" or "executor" role) without making them full owners, adhering to the principle of least privilege.

* **Disaster Recovery Plan:** Establish a clear, documented process for what to do when a signer is compromised, the
multi-signature UI is down, or other emergencies arise. These should be done at regular intervals.

## Operational Best Practices

* **Signer Key Revocation and Replacement:** A  feature of multisigs is the ability to add, remove, or replace signer
keys. If a signer's key is compromised or lost, it can be revoked and replaced with a new, secure key through a
transaction approved by the remaining owners, preserving the integrity of the wallet's assets without needing to migrate
funds.

* **Secure Signing Environment:** For maximum security, all signing activities should be performed on a dedicated,
air-gapped, or hardened device running a secure OS. Using a primary work laptop significantly increases the risk of
malware interference.

* **Independent Transaction Verification:**  Before signing, always verify the raw transaction data (target address,
function call, parameters) to ensure it matches the intended operation.

* **Out-of-Band Verification for Admin Changes:** Any critical administrative action, such as adding or replacing a
signer, must be verified through multiple, independent communication channels (e.g., a video call and a signed message)
to prevent social engineering attacks.

* **Active Monitoring:** Implement monitoring and alerting systems to be immediately notified of any on-chain activity
related to the multisig, including proposed transactions, new signatures, and owner changes (e.g., using tools like
[Safe Watcher](https://github.com/Gearbox-protocol/safe-watcher) ).

* **Documented Procedures:** Maintain clear, secure, and accessible documentation for all multisig procedures, including transaction creation, signing, and emergency recovery plans.
* **General Signing Guidelines:** Use hardware wallets, dedicated signing profiles, and re-verify before execution. Require a "how to check" guide and communicate status after signing (e.g., "checked, signed, X more required"). Last signer executes when applicable.

## Acknowledgements

Some ideas were borrowed from the [EF's multisig SOP notes](https://notes.ethereum.org/@fredrik/multisig-sop) and
[Manifold Finance multisig best practices](https://hackmd.io/@manifoldx/multisig-best-practices).

---

