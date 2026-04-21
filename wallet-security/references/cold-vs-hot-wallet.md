# Cold vs. Hot Wallets

The primary distinction between wallet types is their connectivity to the internet. This factor dictates their security
threat model, risk profile, and ideal use cases.

## Cold Wallets

### What Are They?

Cold wallets are cryptocurrency wallets that store private keys in an offline environment. By being disconnected from
the internet, or "air-gapped," by default, they provide the highest level of security against online attacks like
malware and phishing.

Transactions are signed offline and then broadcast to the network using a connected device, ensuring the private keys
are stored on device with minimal connectivity.

> ❓ Did you know?
>
> Most cold wallets come with some way to connect to the internet, such as via a USB connection. This technically makes
> them "hot" when connected. However, the key distinction is that they are not continuously online and are designed to
> minimize exposure to online threats.

### Types of Cold Wallets

- **Hardware Wallets**: Dedicated physical devices that store private keys offline and sign transactions without
exposing the keys to a connected internet device.
- **Paper Wallets**: Physical printouts or handwritten notes of private keys and QR codes.
- **Software Wallets on Air-Gapped Devices**: Standard wallet software installed on a device that is permanently
disconnected from the internet, used for offline transaction signing.
- **Brain Wallets**: Private keys that are memorized.
- **Account Abstraction Wallets**: Using smart contracts to manage keys and transactions without exposing private keys.
- **Multisig Wallets**: Require multiple signatures to authorize a transaction, enhancing security.

### Use Cases

- **Long-Term Storage**: Ideal for storing large amounts of cryptocurrency for extended periods.
- **High-Security Needs**: Essential for individuals securing significant value and operating with a low risk tolerance.

## Hot Wallets

### What Are They?

Hot wallets are actively and consistently connected to the internet. This connectivity makes them highly convenient for
daily use but also inherently more vulnerable to online attacks.

### Types of Hot Wallets

- **Browser Wallets (Extensions)**: Software that integrates directly into a web browser, allowing seamless interaction
with dApps.
- **Mobile Wallets**: Apps installed on smartphones.

### Use Cases

- **Daily Transactions & dApp Interaction**: Perfect for users who need quick and frequent access to their funds for
interacting with applications.
- **Small Balances**: Suitable for storing smaller, non-critical amounts of cryptocurrency that are used regularly.

## Comparison

| **Feature**     | **Cold Wallets**     | **Hot Wallets**         |
| :-------------- | :------------------- | :---------------------- |
| **Convenience** | Low                  | High                    |
| **Use Case**    | Long-term storage    | Daily transactions      |
| **Risk**        | Physical loss/damage | Online attacks, malware |

## **Key Security Considerations**

Regardless of the type, non-custodial wallets place the full burden of security on the user:

- **Online Vulnerabilities**: If the device they are on (computer or phone) is compromised, your assets can be stolen.
- **Supply Chain Attacks**: Be cautious of both software and hardware integrity. Always download wallet software from
official sources and purchase hardware wallets directly from the manufacturer to avoid receiving a tampered device.

---

