# Common Vulnerabilities

Understanding and mitigating common vulnerabilities is crucial for securing your web and mobile applications. Here are
some frequently encountered vulnerabilities:

## General Vulnerabilities

- **Account Takeovers**: Having the administrator accounts for your services (DNS, Cloud, Domain Registrar, Email,
Github, etc.) is likely to be devastating to your project, as a threat actor can then make malicious changes. To protect
against this, it is recommended to follow best practices with regards to account security and use hardware 2FA
solutions to secure the accounts.

## Web Application Vulnerabilities

- **Cross-Site Scripting (XSS)**: Malicious scripts injected into trusted websites, leading to data theft or session
hijacking.
- **Cross-Site Request Forgery (CSRF)**: Unauthorized commands transmitted from a user trusted by the web application.
- **Insecure Direct Object Reference (IDOR)**: Unauthorized access to data by manipulating input parameters.

## Mobile Application Vulnerabilities

- **Insecure Data Storage**: Sensitive data stored in an insecure manner on the device.
- **Insufficient Transport Layer Protection**: Lack of encryption for data transmitted over the network.
- **Insecure Authentication and Authorization**: Weak authentication mechanisms and improper authorization checks.
- **Code Tampering**: Modifications to the application code by attackers.

Refer to the [OWASP Top 10](https://owasp.org/www-project-top-ten/) and [OWASP Mobile Security
Project](https://owasp.org/www-project-mobile-top-10/) for more details on common vulnerabilities and mitigation
strategies.

---

