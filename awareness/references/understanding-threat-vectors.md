# 2. Understanding Threat Vectors

> 🔑 **Key Takeaway**: Understanding the various ways attackers can target you and your organization is essential for
> effective defense. By recognizing common attack patterns like phishing, social engineering, and emerging threats in
> digital spaces, you can better protect yourself and your team from potential security breaches.

## 2.1. Traditional Attack Vectors

### 2.1.1. Social Engineering & Phishing

- **Phishing Emails:**

Look for red flags like misspellings, odd URLs, and urgent language.
**Scenario Example:** An email that claims "Your account will be locked in 24 hours" but uses a suspicious domain.

- **SMS & Messaging Scams:**

Attackers may use text messages or direct social media messages to bypass email filters.
**Scenario Example:** A text message that claims to be from a delivery service asking for a confirmation code.

- **Voice Phishing (Vishing):**

Phone calls that pretend to be from a trusted organization, often using spoofed caller IDs.
**Scenario Example:** A staff member receives a voicemail warning about a potential security breach and instructing them
to call a specific number immediately.

- **Pretexting:**

Attackers create a fabricated scenario to steal personal information or gain access.
**Scenario Example:** Someone pretending to be a new contractor who needs urgent access to systems or information.

- **Baiting:**

Offering something enticing to entrap the victim.
**Scenario Example:** Leaving infected USB drives in public places or offering free downloads that contain malware.

- **Tailgating:**

Physically following authorized personnel into restricted areas without proper credentials.
**Scenario Example:** An unknown person following an employee through a secure door by claiming they forgot their access
card.

- **Shoulder Surfing:**

Observing someone's screen, keyboard, or device to gather information.
**Scenario Example:** A threat actor monitoring your screen in a shared co-working space to capture sensitive
information or credentials.

### 2.1.2. Malware & Technical Attacks

- **Ransomware:**

Malicious software that encrypts files and demands payment for decryption.
**Scenario Example:** An organization finds their critical files encrypted with a ransom note demanding cryptocurrency
payment.

- **Man-in-the-Middle Attacks:**

Intercepting communications between two parties.
**Scenario Example:** An attacker on a public Wi-Fi network intercepts unencrypted traffic to steal credentials.

- **Credential Stuffing:**

Using stolen username/password combinations to attempt access to multiple services.
**Scenario Example:** After a data breach at one service, attackers try the same credentials on financial or email
accounts.

## 2.2. Web3-Specific Threats

### 2.2.1. Crypto-Focused Attacks

- **Crypto Drainers:**

A common attack where a threat actor suggests users can participate in an airdrop by visiting a provided link.
Unsuspecting users who click the link are directed to a counterfeit website, where they are asked to authenticate their
wallet and sign a transaction. Once signed, the threat actor gains access to steal funds from the wallet.

- **Rug Pulls:**

In the context of web3 and cryptocurrencies, these scams typically involve fraudulent schemes designed to swindle
individuals out of their digital assets. For example, an enticing new project may promise revolutionary technology and
unprecedented returns. However, the project developers quickly vanish, leaving investors with worthless tokens and empty
promises.

- **Token Approval Exploits:**

Attackers may trick users into approving smart contracts that give unlimited access to tokens in their wallet. These
"allowances" permit the approved contract to transfer any amount of a specific token without further permission. Always
verify what permissions you're granting when signing transactions and set specific approval limits when possible.

### 2.2.2. Smart Contract Vulnerabilities

- **Reentrancy Attacks:**

Exploiting a contract's execution flow to repeatedly withdraw funds.
**Scenario Example:** A malicious contract calls back into the victim contract before the first execution is complete,
draining funds with each call.

- **Flash Loan Attacks:**

Using uncollateralized loans to manipulate market prices and exploit vulnerabilities.
**Scenario Example:** An attacker borrows a large amount of cryptocurrency, manipulates a price oracle, exploits a
vulnerability, and repays the loan in a single transaction.

## 2.3. Common Indicators & Red Flags

### 2.3.1. Behavioral Cues

- **Inconsistencies:**

Look for changes in tone or style in communications from known contacts.
**Scenario Example:** A normally formal manager sends a casual message with unexpected requests.

- **Unusual Requests:**

Requests for urgent transfers of money, sensitive information, or changes in process should always trigger caution.

- **Environmental Anomalies:**

Spotting unexpected logins or unfamiliar devices in account activity reports can indicate compromised accounts.

### 2.3.2. Technical Indicators

- **Unexpected Authentication Prompts:**

Sudden requests to re-authenticate without clear reason.
**Scenario Example:** Being asked to provide credentials on a site you're already logged into.

- **Browser Certificate Warnings:**

Alerts about invalid or expired security certificates.
**Scenario Example:** Your browser displays a warning that a connection is not secure when visiting a familiar website.

- **Unusual System Behavior:**

Slowdowns, crashes, or unexpected pop-ups.
**Scenario Example:** Your computer suddenly runs significantly slower or displays unfamiliar advertisements.

### 2.3.3. Checklist for Suspicious Communications

- Does the message contain spelling errors or unusual formatting?
- Is the sender's email or username slightly different from the norm?
- Are there requests for urgent action without proper verification channels?
- Does the message create a sense of fear, urgency, or excitement?
- Is there an unexpected attachment or link?
- Does the request bypass normal security procedures?

## 2.4. Preventive Measures

### 2.4.1. General Security Practices

- **Double-Check Requests:**

Always verify the identity of individuals requesting sensitive information, especially if the request is unusual or
urgent.
**Scenario Example:** If you receive an email from your CEO asking for an urgent wire transfer, call them directly using
a known phone number to confirm.

- **Use Secure Channels:**

Communicate through official channels and avoid sharing sensitive information over unsecured methods.
**Scenario Example:** Use your organization's established communication platforms rather than responding to external
email links.

### 2.4.2. Web3-Specific Protections

- **Check & Remove Token Approvals:**

Regularly check which smart contracts have approvals to handle funds in your wallet and revoke unnecessary approvals to
improve your security posture.
**Useful Tools:**

- [Unrekt](https://app.unrekt.net/)
- [Etherscan Token Approval Checker](https://etherscan.io/tokenapprovalchecker)

- **Scrutinize Transaction Requests:**

Never sign a transaction unless you are completely sure exactly what you are signing. Be especially skeptical of offers
that seem too good to be true.

- **Hardware Wallets for Critical Assets:**

Use hardware wallets for storing significant cryptocurrency holdings.
**Scenario Example:** Keeping your long-term investments on a hardware wallet while only maintaining small amounts in
hot wallets for daily transactions.

---

