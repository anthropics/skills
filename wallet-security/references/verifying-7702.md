# Using EIP-7702

The Pectra network upgrade introduces **EIP-7702**, which allows a standard Externally Owned Account (EOA) to
temporarily function like a smart contract wallet. This is achieved via a new transaction type (`0x04`) that lets an EOA
delegate its authority to a smart contract's code for the duration of a transaction or until it's changed.

## Benefits of EIP-7702

This EIP unlocks several key user experience improvements:

- **Transaction Batching**: Users can combine multiple operations (e.g., an ERC-20 `approve` and a `swap`) into a
single, atomic transaction, saving on gas fees and reducing confirmation fatigue.
- **Gas Sponsorship**: It enables third parties to pay for a user's transaction fees, which can simplify onboarding and
abstract away gas management for the user.
- **Privilege De-escalation**: Users can delegate to contracts that enforce specific permissions, such as daily spending
limits or interactions with only certain dApps.

## Risks of EIP-7702

While powerful, this feature introduces a new attack vector. If an attacker tricks a user into signing a message that
sets the wallet's code to a malicious contract, the attacker can gain full control and drain all assets.

- **Phishing Attacks**: The primary threat is phishing sites or scams that trick users into signing a `SetCode`
delegation to a malicious contract under the guise of a wallet "upgrade."
- **Multi-Chain Replay Attacks**: A signature authorizing a delegation with `chain ID 0` can be replayed on other EVM
chains. An attacker could deploy a malicious contract at the same address on a different chain and use the replayed
signature to take control there.

## Guidance for Users

- **Trust Your Wallet's Implementation**: Major wallets mitigate phishing risks by **hardcoding** the *only* valid
delegation contract. This prevents malicious websites from tricking you into delegating to an unsafe contract. Only
approve delegations to contracts vetted and integrated by your wallet provider.
- **Verify Delegation Targets**: Only delegate your account to contracts that are well-known and audited.
- **Understand Revocation**: You can revoke a delegation and return your account to a standard EOA by authorizing a new
transaction that sets the delegation address to the zero address (`0x0000000000000000000000000000000000000000`).
- **Protect Your Private Key**: Delegation does not eliminate the fundamental risk of a private key compromise. If your
key is stolen, an attacker can still authorize delegations.
- **Beware of Phishing**: Be skeptical of any request to "upgrade" or "enable" smart account features, especially if it
comes from an external link or pop-up.

> ⚠️ Wallets will only prompt you to switch to a smart account within the wallet's native. Any request to do so via
> email, a website, or a direct message is a phishing scam.

---

