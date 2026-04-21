---
name: seal-front-end-web-app
description: >
  Handle web application and mobile security — common vulnerabilities (XSS, CSRF), API security, frontend hardening. Use when discussing web app vulnerabilities, mobile app security, or frontend security practices. Load seal-devsecops for CI/CD integration. Load seal-security-testing for testing approaches.
metadata:
  category: security
  tags: ['web-security', 'frontend', 'mobile', 'vulnerabilities']
  related_skills: ["seal-security-testing", "seal-supply-chain", "seal-devsecops"]
---

# Front End Web App

Web application and mobile security — common vulnerabilities, security tools, and frontend hardening practices.

## When to Use
- User asks about front end web app practices, policies, or procedures
- Incident or scenario involving front end web app concepts
- Need guidance on front end web app frameworks or implementations
- Security training or awareness question touching this domain

## Related Domains
This skill connects to: seal-security-testing, seal-supply-chain, seal-devsecops
Use `skill_view("seal-security-testing")` if the question spans multiple areas.

## Key Concepts
# Front-End Web Application Security Best Practices
Often an overlooked area, but ensuring the security of your front-end web and potential mobile applications is crucial
for protecting your users. If the front-end web application is compromised, it could have severe effects on your users
as they for example could start interacting with a malicious contract instead of your official contract.
## Gotchas
- XSS in Web3 dApps can steal wallet connection data and trigger malicious transactions — sanitize all user inputs
- Content Security Policy headers break inline scripts — plan CSP migration carefully
- Mobile apps often store auth tokens insecurely — use platform keychain/keystore APIs

## References
- Common Vulnerabilities
- Web Application Security
- Mobile Application Security
- Security Tools Resources
