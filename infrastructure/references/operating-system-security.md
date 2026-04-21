# Operating System Security

This document outlines some general best practices one should follow with regards to operating system security, however
if you're interested in a much more comprehensive guide you could look at [NIST
800-123](https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-123.pdf).

## Best Practices

1. Keep your operating systems updated with the latest security patches and updates.
2. Block the remote shell port from all but required IPs.
3. Block all ports except absolutely required ones from public.
4. Use tools such as fail2ban to protect against attacks.
5. Enforce personal account and SSH key login
6. Enable multi factor authentication.
7. Implement strict access controls to limit administrative privileges and use role-based access control (RBAC).
8. Use antivirus and anti-malware software to detect and prevent malicious activities on systems where relevant
9. Configure host-based firewalls to control incoming and outgoing network traffic.
10. Implement host-based intrusion detection and prevention systems (HIDS/HIPS).
11. Follow secure configuration guides, such as the NIST 800-123 guidelines, to harden your operating systems.

---

