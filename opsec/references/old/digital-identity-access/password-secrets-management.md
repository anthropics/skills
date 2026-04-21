# Password/Secrets Management

Effective management of passwords and cryptographic keys help maintain the security and integrity of digital assets and
sensitive information.

## Best Practices

1. Do not reuse passwords across services as it increases the risk of multiple accounts being compromised when one
service is breached. Instead, use a password vault that can generate complex, random, and unique passwords for each
service.

   - While browsers provide password vaults with passwords, it is recommended to use an external password vault with
   improved security features.

2. Check if your email has been in any breach on [Have I Been Pwned](https://haveibeenpwned.com/) and set up
notifications for future breaches. Change passwords on the services where you may have been breached.
3. If you suspect a breach of your password, change it as soon as possible.
4. Use MFA whenever possible. It is a key measure in preventing account breaches. It is highly recommended to use a
hardware token such as Yubikey to protect your accounts. If you use a mobile authenticator such as Authy to store your
MFA tokens, ensure that you also set an encryption password to mitigate the risk of SIM swapping. Avoid using SMS for
MFA unless there is no other option, as there are multiple cases where people have been SIM swapped and their accounts
taken over. If SMS is the only option, it is still better than having no MFA enabled at all. It is recommended to not
use the password manager/vault used for your passwords to store your MFA codes.
5. **Reminder:** Do not derive wallets from self generated passwords, even if they look random. It is very easy to make
mistakes in the derivation process and end up with a wallet that is easy to compromise. It is always better to use an
appropriate wallet software to generate your seed phrases.

## Password and Key Security

### Passphrases

Utilizing long, memorable phrases as passwords. They are easier to remember than complex passwords and can be equally
secure. For example, "CorrectHorseBatteryStaple" is more secure and memorable than a shorter, complex password.

![XKCD Password Strength](https://imgs.xkcd.com/comics/password_strength.png)

### Password Cards (e.g., Qwertycards)

Aids in generating and recalling complex passwords using a physical card as a mnemonic device. These can be particularly
useful for creating strong, unique passwords without relying on digital tools.

### Non-default BIP-44 Derivation Path

Using custom paths for key generation in crypto wallets to enhance security. For example, MyEtherWallet allows users to
set custom derivation paths.

### Password Managers

Digital solutions for securely storing and managing various passwords. They reduce the risk of password reuse and
simplify password management by generating and storing complex, unique passwords for each service.

## Key Storage and Recovery

### Memory and Notebook

Relying on human memory or physical writing to store keys. It's highly secure against digital theft but vulnerable to
forgetting or physical loss. Always have a secure backup plan.

### Paper Wallets

Involves printing or writing down keys on paper. Offers protection from online hacks but can be lost, damaged, or
deteriorate over time. Store paper wallets in secure, dry, and fireproof locations.

### Encrypted Drives

Storing keys on encrypted drives balances digital convenience with security. However, it is vulnerable to physical theft
and damage. Always have multiple backups in different locations.

### Back-ups / Rotation / Recovery

Regular backup and update of key information to ensure recovery. This is critical for maintaining access in case of
primary key loss. Use secure, redundant backup solutions and periodically test recovery procedures.

### Shamir Backup

Shamir's Secret Sharing is a method to split a secret, such as a private key, into multiple parts, where a subset of
these parts is required to reconstruct the secret. This enhances security and ensures recoverability.

## Authentication and Access Control

### 2FA / MFA (Multi-Factor Authentication)

Employs multiple verification methods, significantly increasing security by adding layers beyond just passwords. Use
hardware tokens like Yubikeys for the highest level of security.

### SSO (Single Sign-On)

Allows using one set of credentials to access multiple services. Convenient but necessitates strong security for the
primary credentials. Ensure SSO solutions are configured with strong security measures and regularly audited.

### Trusted Key Management System (KMS)

Systems designed to manage and protect digital keys, critical for securing cryptographic operations and sensitive data.
Use a reputable KMS to handle key generation, storage, and rotation securely.

### Hardware Security Keys

Physical devices used for authentication, offering a high level of security against remote attacks. They are
particularly effective when combined with MFA.

## Biometric Security

### Fingerprint Scanners

Uses fingerprints, unique to every individual, as a means of secure and convenient authentication. They are widely used
in mobile devices and some laptops.

### Facial Recognition

Employs facial characteristics for verification, increasingly popular in mobile and personal devices.

---

