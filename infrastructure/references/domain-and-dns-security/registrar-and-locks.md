# Registrar Security & Registry Locks

## Choosing a Secure Registrar

Your domain registrar is the company that manages your domain registration with the central registry. This is often the weakest link in domain security, as many registrars have poor security practices and are vulnerable to social engineering attacks.

### Enterprise-Grade Registrars (Recommended)

These registrars are designed for high-value domains and have security measures that consumer registrars lack:

- **MarkMonitor**: Used by Fortune 500 companies, requires legal documentation for changes, dedicated security team
- **AWS Route53**: IAM policy integration, CloudTrail logging, uses Amazon Registrar for major TLDs (but check TLD support)
- **Cloudflare Registrar**: No markup pricing, automatic DNSSEC, built-in DDoS protection, requires Cloudflare services

### Consumer Registrars to Avoid for Critical Domains

These registrars are designed for personal use and lack the security measures needed for Web3 projects:

- **GoDaddy**: History of social engineering vulnerabilities, call center support vulnerable to manipulation
  - [2020 incident: Employees tricked into compromising cryptocurrency domains](https://threatpost.com/godaddy-employees-tricked-compromise-cryptocurrency/161520/)
  - [Multiple low-tech, high-impact breaches](https://krebsonsecurity.com/2023/02/when-low-tech-hacks-cause-high-impact-breaches/)
- **Namecheap**: While better than GoDaddy, still vulnerable to social engineering and lacks enterprise-grade security controls
- **Consumer-focused services** (Google Domains/Squarespace): Designed for personal use, not enterprise security
- **Resellers**: Add another layer of complexity and potential attack surface

**Due diligence**: Check [ICANN Compliance Notices](https://www.icann.org/compliance/notices) for registrar terminations, breaches, and compliance issues. ICANN has terminated several registrars due to security issues and breaches. Review your registrar's compliance history before trusting them with critical domains.

## Registry Lock (EPP Lock)

Registry lock prevents unauthorized transfers at the registry level, not just the registrar. This is the strongest protection available for domain security.

**Important distinction**: EPP status codes apply to **registry objects** (transfers, deletes, nameserver sets, contact updates), NOT DNS zone edits at your provider's DNS panel. You can still edit A records, MX records, TXT records, etc. in your DNS hosting provider's interface even with EPP locks enabled.

**EPP Status Codes** that protect your domain:
- `clientTransferProhibited`: Prevents domain transfers to another registrar
- `clientUpdateProhibited`: Prevents registry object updates (nameservers, contact information)
- `clientDeleteProhibited`: Prevents domain deletion
- `serverTransferProhibited`: Registry-level transfer protection (stronger than client-level)
- `serverUpdateProhibited`: Registry-level update protection (nameservers, contacts)
- `serverDeleteProhibited`: Registry-level deletion protection

**How it protects you**: Standard transfer locks only prevent transfers between registrars, but registry locks with full EPP protections prevent unauthorized changes to critical registry objects including transfers, deletions, nameserver changes, and contact modifications. Server-level locks require manual verification with the registry operator (like Verisign for .com domains), making social engineering attacks at the registrar level completely ineffective.

**What EPP locks do NOT block**: DNS record edits (A, AAAA, MX, TXT, etc.) in your DNS provider's panel remain fully functional. EPP locks protect registry-level changes, not zone-level DNS record edits.

**Setup**: Contact enterprise registrars for registry-operator level locks. This typically requires additional fees and documentation but provides the highest level of security.

## Multi-Factor Authentication

Multi-factor authentication (MFA) adds an extra layer of security beyond just passwords, which are easily compromised through phishing or data breaches.

**Strong recommendation**: Use **Hardware Security Keys (FIDO2/WebAuthn)** for registrar accounts. Given the critical nature of domain security and the irreversibility of domain hijacks, hardware keys are the ONLY authentication method we strongly recommend for Web3 projects.

**Authentication options**:

1. **Hardware Security Keys (YubiKey, Titan, etc.) - STRONGLY RECOMMENDED**
   - **Immune to phishing**: Cannot be tricked by fake login pages
   - **No shared secrets**: Private key never leaves the device
   - **No SIM swap vulnerability**: Physical device required
   - **FIDO2/WebAuthn standard**: Industry-standard cryptographic authentication
   - **Why critical for domains**: Domain control = organization control; hardware keys provide the highest assurance

2. **TOTP Applications (Google Authenticator, Authy) - DISCOURAGED**
   - Vulnerable to phishing through man-in-the-middle attacks
   - Shared secrets can be compromised during setup
   - QR codes can be intercepted or screenshotted
   - Only use as a last resort if registrar doesn't support hardware keys
   - If forced to use TOTP, ensure registrar has additional protections

3. **SMS 2FA - DO NOT USE**
   - **Extremely vulnerable to SIM swapping attacks**
   - SMS can be intercepted via SS7 vulnerabilities
   - Social engineering attacks target mobile carriers
   - No cryptographic security
   - Numerous high-profile compromises via SMS 2FA
   - **Never use SMS 2FA for domain registrar accounts**

**Action item**: If your registrar only supports SMS or TOTP, consider **migrating to an enterprise registrar** (MarkMonitor, AWS Route53 Registrar, Cloudflare Registrar) that supports hardware security keys.

## Dedicated Security Contact Email

Use a dedicated email address for domain security that's completely separate from your main domain and personal accounts.

**Why this matters**: If your main domain is compromised, you need a way to receive security notifications and regain control. Using the same domain creates a circular dependency.

```
❌ admin@yourdomain.com (circular dependency - if domain is hijacked, you lose email access)
❌ personal@gmail.com (too many attack vectors, likely used across multiple services)
⚠️ domain-security@protonmail.com (better than gmail, but still a shared service)
✅ security@yourcompany-domains.com (best - separate domain dedicated to domain management)
```
As a best practice register a separate domain specifically for domain management (e.g., `yourproject-domains.com` or `yourproject-security.com`) with a different registrar than your main domain. This ensures you maintain communication channels even if your primary domain is completely compromised.

## Access Control Best Practices

Limit and monitor who has access to your domain registrar account, as each person with access represents a potential attack vector.

**Key practices**:
- Document all personnel with registrar access
- Use role-based access where available
- Implement approval workflows for critical changes
- Regular access audits (quarterly minimum)

## WHOIS Privacy Protection

WHOIS records contain personal information about domain owners that is publicly accessible by default, including names, addresses, phone numbers, and email addresses.

**Why it matters**: Without WHOIS privacy, your personal information is exposed to:
- Attackers gathering information for social engineering attacks
- Spammers harvesting contact details
- Competitors researching your infrastructure
- Anyone running a simple WHOIS lookup

**Setup**:
- Enable WHOIS privacy/proxy service through your registrar (often free or low-cost)
- Use company information instead of personal details where privacy isn't available
- Consider using a separate business entity for domain registration
- Be aware that some TLDs (.us, .ca) don't allow WHOIS privacy

**Important**: WHOIS privacy doesn't affect your legal ownership - you remain the legitimate owner, the privacy service just shields your personal information from public view.

## WHOIS vs RDAP

**RDAP (Registration Data Access Protocol)** is the modern replacement for WHOIS. While WHOIS is still widely used, RDAP should be preferred for domain information lookups.

**Why RDAP is better**:
- **Structured data**: JSON-based responses are machine-readable and easier to parse
- **Standardized**: Consistent format across registries and registrars
- **Better display**: Modern CLIs and tools display RDAP data in organized, readable formats
- **More reliable**: Built on RESTful APIs with better authentication and access control
- **Links to authoritative sources**: Provides direct links to registrar and registry RDAP endpoints

**Using RDAP**:
- **Command-line tools**: Use RDAP CLIs like `rdap` (Rust-based) or `nicinfo` (Ruby-based)
- **Web tools**: Many registries provide RDAP web interfaces
- **Example lookup**: `rdap yourdomain.com` displays domain status, EPP codes, nameservers, registrar info, and expiration dates

**Example RDAP output**:

```
❯ rdap google.com
2025-10-06T20:36:58.203437Z  INFO rdap: ICANN RDAP 0.0.23 Command Line Interface
2025-10-06T20:36:58.203497Z  INFO rdap: query type is Domain Lookup for value 'google.com'
――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――
 • host                       : rdap.verisign.com
 • Request URI                : https://rdap.verisign.com/com/v1/domain/google.com

――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――
                                   Domain GOOGLE.COM

  ┌────────────────────────────┬─────────────────────────────────────────────────────┐
  │                     Summary│Domain GOOGLE.COM                                    │
  │                            │• 292 (Registrar)                                    │
  │                            │  • Abuse                                            │
  │                            │• Nameserver NS1.GOOGLE.COM                          │
  │                            │• Nameserver NS2.GOOGLE.COM                          │
  │                            │• Nameserver NS3.GOOGLE.COM                          │
  │                            │• Nameserver NS4.GOOGLE.COM                          │
  ├────────────────────────────┼─────────────────────────────────────────────────────┤
  │        Identifiers         │                                                     │
  ├────────────────────────────┼─────────────────────────────────────────────────────┤
  │                    LDH Name│GOOGLE.COM                                           │
  │                Unicode Name│                                                     │
  │                      Handle│2138514_DOMAIN_COM-VRSN                              │
  ├────────────────────────────┼─────────────────────────────────────────────────────┤
  │        Information         │                                                     │
  ├────────────────────────────┼─────────────────────────────────────────────────────┤
  │                      Status│• Client Delete Prohibited                           │
  │                            │• Client Transfer Prohibited                         │
  │                            │• Client Update Prohibited                           │
  │                            │• Server Delete Prohibited                           │
  │                            │• Server Transfer Prohibited                         │
  │                            │• Server Update Prohibited                           │
  ├────────────────────────────┼─────────────────────────────────────────────────────┤
  │           Events           │                                                     │
  ├────────────────────────────┼─────────────────────────────────────────────────────┤
  │                Registration│• Mon, 15-Sep-1997 04:00:00 +00:00                   │
  │                  Expiration│• Thu, 14-Sep-2028 04:00:00 +00:00                   │
  │                Last Changed│• Mon,  9-Sep-2019 15:39:04 +00:00                   │
  │Last Update Of RDAP Database│• Mon,  6-Oct-2025 20:36:39 +00:00                   │
  ├────────────────────────────┼─────────────────────────────────────────────────────┤
  │           Links            │                                                     │
  ├────────────────────────────┼─────────────────────────────────────────────────────┤
  │                        Self│• https://rdap.verisign.com/com/v1/domain/GOOGLE.COM │
  │                     Related│• https://rdap.markmonitor.com/rdap/domain/GOOGLE.COM│
  └────────────────────────────┴─────────────────────────────────────────────────────┘

                                    292 (Registrar)

                ┌─────────────────┬────────────────────────────────────┐
                │          Summary│292 (Registrar)                     │
                │                 │• Abuse                             │
                ├─────────────────┼────────────────────────────────────┤
                │   Identifiers   │                                    │
                ├─────────────────┼────────────────────────────────────┤
                │           Handle│292                                 │
                │            Roles│• registrar                         │
                │IANA Registrar ID│292                                 │
                ├─────────────────┼────────────────────────────────────┤
                │     Contact     │                                    │
                ├─────────────────┼────────────────────────────────────┤
                │        Full Name│MarkMonitor Inc.                    │
                ├─────────────────┼────────────────────────────────────┤
                │      Links      │                                    │
                ├─────────────────┼────────────────────────────────────┤
                │            About│• http://www.markmonitor.com        │
                │                 │• https://rdap.markmonitor.com/rdap/│
                └─────────────────┴────────────────────────────────────┘
```

**What RDAP shows**:
- Domain status and EPP lock codes (clientTransferProhibited, serverUpdateProhibited, etc.)
- Nameserver information
- Registrar details and abuse contacts
- Registration, expiration, and last update dates
- Links to registry and registrar RDAP endpoints

**For security audits**: Use RDAP to verify your domain's EPP status codes, confirm registry locks are active, check nameserver configurations, and validate expiration dates. The structured output makes it ideal for automated monitoring and compliance checks.

## Domain Expiration Protection

Domain expiration is a critical yet often overlooked security risk. When domains expire, they enter a grace period before becoming publicly available, creating an opportunity for attackers to snipe your domain.

**Expiration timeline (typical for gTLDs following ICANN rules)**:
- Day 0: Domain expires (site goes down)
- Day 1-45: Auto-renew grace period (can renew at normal price)
- Day 46-75: Redemption period (costs 10x+ to recover)
- Day 76-80: Pending delete
- Day 81: Public availability (bot armies compete to register)

**Important**: Grace and redemption periods **differ per TLD**. Generic TLDs (gTLDs like .com, .org, .net) follow ICANN rules with the timeline above. Country code TLDs (ccTLDs like .uk, .de, .ca) often have different policies set by their respective registries. Always verify your specific TLD's expiration policy with your registrar or registry.

**Protection measures**:
- **Enable auto-renewal** on all critical domains
- **Set multiple renewal reminders** at 90, 60, 30, and 7 days before expiration
- **Register domains for maximum period** (up to 10 years for most TLDs)
- **Use a domain monitoring service** that alerts on upcoming expirations
- **Document renewal dates** in your security calendar
- **Ensure payment methods stay current** - expired credit cards are a common cause of accidental expiration
- **Designate a backup person** responsible for domain renewals

**Pro tip**: Set calendar reminders to check auto-renewal status quarterly - don't assume it's working until you verify.

---

