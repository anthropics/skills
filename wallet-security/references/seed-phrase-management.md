# Seed Phrase Management

## Private Key & Seed Phrase Management

The **seed phrase** (or mnemonic phrase) is the master key to a non-custodial wallet, granting complete control over all
its derived **private keys** and assets. The management of this phrase is the single most important aspect of
self-custody security.

> ⚠️ If you suspect for even a moment that your private key or seed phrase has been lost, viewed by another person, or
> exposed digitally (e.g., shown on-screen, copied to a clipboard on a connected device), you must **consider it
> compromised.** Immediately create a new, secure wallet and transfer all assets to it.

### Secure Storage Practices

The goal is to protect the seed phrase from both physical threats (theft, fire, water damage) and digital threats
(hacking, malware). The foundational principle is to keep your seed phrase offline at all times.

As soon as a new wallet is created, back it up using one of the following offline methods. Wallet providers do not have
access to your seed phrase and cannot help you recover it.

- **Physical Written Copies**: Writing the phrase on paper or a notebook is a common starting point. To mitigate risks
of loss or damage from fire or water, store multiple copies in secure, geographically separate locations (e.g., a
personal safe, a trusted family member's home, a bank deposit box).

- **Durable Metal Storage**: For superior protection against physical damage, etch or stamp your seed phrase onto a
metal plate (e.g., steel, titanium). Commercial products are available for this purpose. These should also be stored in
secure, separate locations.

### Enhanced security option

For extra security, split seed into 3 pieces:
- **Piece 1**: Words 1-16
- **Piece 2**: Words 9-24
- **Piece 3**: Words 1-8 and 17-24

#### Storage locations:
- Different secure locations (safe deposit box, home safe, trusted family)
- Each piece stored with clear labeling system

### Tamper evident bags:

Storing sensitive devices or documents in a tamper evident bag offers high confidentiality and integrity. You can sign & date these bags, and also take a picture of its serial number.

![Tamper evident bag example](https://frameworks-static.s3.us-east-2.amazonaws.com/images/multisig-for-protocols/tamper-evident-bag-example.png)

**Use case:**
You can put your Piece 1: Words 1-16 of your seed, inside a safe.
Piece 2: Words 9-24 of your seed, somewhere safe (different location) in a tamper evident bag (could be at your parents place).
Piece 3: Words 1-8 and 17-24 of your seed, somewhere safe (different location) in a tamper evident bag (could be somewhere else, at a family member or trusted friend).
You can put your backup ledger while traveling inside this, in the safe of your hotel room to detect tampering.
The main idea is to never have at the same place your 24 words, but still be able to recover your seed within 2 pieces of paper out of 3.
You can find a useful [link here to our EthCC swag](https://drive.google.com/file/d/1L1CMiKRL3TXQBE5bWYNv6dfF94HSdZ8C/view?usp=sharing) that shows you how to easily split your seed in 3 as recommended.

### Prohibited Practices

Under no circumstances should you ever store your seed phrase in any of the following ways:

- Taking a digital photograph of it.
- Uploading it to cloud storage (iCloud, Google Drive, Dropbox).
- Sending it via text message or any messaging app.
- Sending it in an email, even to yourself.
- Storing it in a plain text file on a computer or phone.
- Sharing it with anyone. Wallet providers will **never** ask for your seed phrase.
- Never use a device obtained from an untrusted source, such as a conference, hackathon, or third-party online marketplace, as it may be tampered with.
- Password managers or digital storage
- Traveling with seed phrases
- Storing all pieces in same location

### Ongoing Security Hygiene

**1. Periodic Security Audits:**

On a recurring basis (e.g., every 6 months), conduct a security review by asking:

- Do I know the physical location of all my seed phrase backups?
- Are my storage methods still secure and uncompromised?
- If my primary device were destroyed, do I have a clear plan to recover my assets?

**2. Key Rotation:**

While you can use the same keys for years, it is a best practice to periodically rotate them by moving assets to new
wallets.

**3. Succession Planning:**

Establish a clear, secure protocol for a trusted next-of-kin to access your assets in case of incapacitation or death.
This may involve sealed instructions stored with a lawyer or in a safe deposit box.

## Emergency access plan

### Trusted contacts
- Designate 2-3 trusted individuals who can access backup locations
- Clear instructions for emergency seed access
- Regular check-ins with trusted contacts

### Recovery scenario example
"Call [trusted person] with code word [predetermined phrase], tell them to get the metal plate from safe location A, they give you words 1-16 over the phone. Then call [second person] with code word for location B to get words 9-24. Use both pieces to reconstruct seed immediately, then change all security settings."

### Documentation
- Emergency contact information stored separately from seed
- Code words/phrases for identity verification
- Access instructions for trusted contacts
- Regular testing of emergency procedures
- Update procedures when contacts or locations change

Remember: Your seed phrase security is the foundation of multisig security. Take time to implement proper storage procedures appropriate for your risk level.

