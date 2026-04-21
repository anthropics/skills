# For Intermediates & Medium Balances

## User Profile

An intermediate user who is comfortable with web3 interactions and is now managing a significant, but not life-altering,
amount of assets. This user understands the inherent risks of hot wallets and is actively seeking to upgrade their
security posture to protect their capital.

## Primary Goal

The main objective is to secure balances against online threats while still retaining the ability to interact with dApps
when necessary. This involves **separating the bulk of assets** from daily operational balances.

## Recommended Setup

A **hardware wallet** is the core of this setup. This dedicated physical device stores private keys offline in a secure,
tamper-resistant environment, acting as a vault for the majority of the user's balances.

## Key Considerations & Trade-offs

Adopting a hardware wallet introduces a new set of security considerations focused on physical and supply chain vectors.

* **Physical Security:** A hardware wallet is a physical asset that must be protected from theft, damage, or coercion.
* **Supply Chain Integrity:** Hardware wallets must only be purchased directly from the manufacturer or an authorized reseller to avoid receiving a tampered device.
* **Convenience vs. Security:** Using a hardware wallet introduces friction into the transaction process, as it requires
physical access and approval on the device for every signature.

## How to Select a Hardware Wallet

* **Open Source:** Evaluate if the wallet's firmware and software are open-source, which allows for public auditing and
verification by the security community.
* **Secure Element (SE)** Look for devices with a SE certified, tamper-resistant chip that protects against physical
attacks. Check for high assurance ratings like `EAL6+` and features like **attestation**, which verifies the device is
genuine.
* **Reputation & Incident:** Investigate the manufacturer's security track record, including their response to past
vulnerabilities, data breaches, and overall transparency.
* **Verify Device Integrity**: A legitimate hardware wallet will arrive uninitialized, requiring you to perform the
initial setup. Reject any device that comes with a pre-set PIN, a pre-generated recovery phrase, or appears to be
already configured, as it is likely compromised.

## Initial Setup

### Purchase & Verification
 - Verify tamper-resistant packaging is untouched
 - Check for authenticity indicators on packaging

### Device Configuration
- Update firmware to latest version before creating accounts
- Configure PIN - Use unique, strong PIN (different from other devices)
- Generate seed following device instructions
- Create accounts as needed

## Backup Device (For Critical Operations & Multisigs)

Maintain a backup hardware wallet to avoid needing to access your seed phrase if your primary device fails.
- Second hardware wallet with same seed phrase
- Test both devices can create valid signatures
- Store backup securely
- Monthly verification that backup device functions correctly

---

