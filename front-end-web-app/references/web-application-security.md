# Web Application Security

Providing a secure front-end (web application) for users to interact with your web3 protocol is often essential. Web
application vulnerabilities have however been exploited in the past to steal user funds, and as such it's important to
take web application security into consideration for your project.

## Best Practices

1. Utilize popular and well-maintained web application frameworks when developing your application.
2. Familiarize yourself with common web application vulnerabilities that may affect your decentralized application such
as Cross-Site Scripting (XSS).
Refer to the [OWASP Top 10](https://owasp.org/www-project-top-ten/) for a comprehensive list.
3. Minimize the introduction of custom components in your framework. Ensure that any custom code undergoes thorough
internal and external security testing.
4. Refer to the [Infrastructure/DDoS Protection](/infrastructure/ddos-protection) section for insights on ensuring high
availability of your protocol’s front-end.
5. Lock down access to associated back-end services, such as S3 buckets, to prevent unauthorized access.
6. Consider deploying additional versions of your front-end on IPFS to ensure availability and resilience.

---

