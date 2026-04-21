# Detecting and Mitigating Insider Threats

Insider threats, whether intentional or unintentional, pose a significant risk to any project. These threats can come
from current or former employees, contractors, or business associates who have inside information concerning the
project's security practices, data, and computer systems. Effective detection and mitigation strategies are crucial for
safeguarding your project against these risks.

## What Are Insider Threats?

Insider threats can be categorized into three main types:

1. **Malicious Insiders**: Individuals who intentionally cause harm to the project by stealing data, sabotaging systems,
or leaking sensitive information.
2. **Negligent Insiders**: Team members who unintentionally cause security breaches through careless actions, such as
falling for phishing attacks or mishandling sensitive data.
3. **Compromised Insiders**: Team members whose accounts or systems are compromised by external threat actors and used
to gain access to the project's resources.

## Understanding Insider Threat Motivations

Understanding what motivates insider threats is crucial for detection and prevention:

### Financial Motivations

* Financial gain is one of the most common motivations
* Employees may be offered substantial bribes to compromise systems
* In the blockchain space, the potential rewards can be particularly high

### Coercion and Social Engineering

* External actors may blackmail or threaten employees to gain cooperation
* Social engineering techniques can manipulate employees into providing access
* As reported by Krebs on Security, employees at domain registrars have been targeted by threat actors who persuaded
them to modify DNS records or provide unauthorized access to high-value domains[^1]

### Ideological or Political Reasons

* Some insiders act based on political beliefs or ideological disagreements
* They may believe they're exposing perceived wrongdoing or supporting a cause

### Personal Grievances

* Disgruntled employees seeking revenge for perceived mistreatment
* Former employees with lingering access and unresolved issues

### Lack of Awareness

* Some insiders don't realize the value of what they're compromising
* They may not understand the security implications of their actions

### Some Examples

* The 2020 Twitter breach exemplifies compromised insiders - employees with legitimate access were socially engineered
to provide their credentials, allowing attackers to take control of high-profile accounts[^2]. While the employees
didn't intend harm, they became unwitting insider threats after being manipulated.

* Similarly, the 2022 Ronin Network hack ($625 million) began with social engineering of a Sky Mavis senior engineer.
This employee became a compromised insider, giving attackers access to four validator nodes. Combined with a third-party
validator, this allowed the massive cryptocurrency theft[^3]. This demonstrates how social engineering creates insider
threats even when employees have no malicious intent.

* The 2019 SIM-swapping attacks represent a more direct insider threat scenario. Mobile carrier employees were bribed or
socially engineered to transfer victims' phone numbers to attacker-controlled SIMs. In Michael Terpin's case against
AT&T, an employee allegedly accepted payment to compromise his account, leading to $24 million in cryptocurrency
theft[^4]. This represents both compromised insiders and potentially malicious insiders who knowingly participated in
exchange for payment.

These examples highlight the intersection of social engineering and insider threats, where external attackers manipulate
employees to gain unauthorized access.

[^1]: Brian Krebs, "How Paypal and GoDaddy Got Hijacked: A Cautionary Tale," Krebs on Security, 2019.
[^2]: Twitter Support, "An update on our security incident," Twitter Blog, July 2020.
[^3]: Ronin Network, "Ronin Network Breach Postmortem," April 2022.
[^4]: "Cryptocurrency investor sues AT&T for $224 million over SIM-swap fraud," Reuters, August 2018.

## Detecting Insider Threats

### Monitoring and Analytics

1. Implement systems to monitor team member's activity and identify unusual behavior patterns. This includes tracking
logins and on-chain transactions related to the project.
2. Use anomaly detection to establish a baseline of normal user behavior and detect deviations that may indicate
malicious activity.

### Access Controls

1. Implement RBAC to ensure that employees have access only to the information and systems necessary for their job
functions.
2. Enforce the principle of least privilege, granting users the minimum level of access required to perform their
duties.
3. Conduct regular reviews of user access permissions to ensure they are still appropriate for their current roles.

### Training and Awareness

1. Conduct regular security training sessions to educate employees about the risks of insider threats and the importance
of following security protocols.
2. Run (spear) phishing simulations to test employees' awareness and response to potential (spear) phishing attacks.

## Mitigating Insider Threats

### Incident Response Plan

1. Create a detailed [incident response plan](/incident-management/overview) that outlines the steps to be taken in the
event of an insider threat incident.
2. Clearly define roles and responsibilities for the incident response team to ensure a coordinated and effective
response.

### Technical Controls

1. Require MFA for access to critical systems and sensitive data to add an extra layer of security.
2. Encrypt sensitive data both at rest and in transit to protect it from unauthorized access.

### Project Policies

1. Establish clear policies and procedures for handling sensitive information and responding to security incidents.
2. Be aware that malicious organizations/countries may try to obtain access to your project for reasons of financial or
technology theft. Conduct thorough background checks on new employees and contractors to identify potential risks.
3. Implement strict exit procedures for departing employees, including revoking access to systems and multi-signature
wallets.

### Behavioral and Cultural Measures

1. Foster a [culture of security awareness] {/* TODO: link not found: ../../awareness/security-culture/overview.md
*/} where team members understand the importance of protecting sensitive information and reporting suspicious
activities.

---

