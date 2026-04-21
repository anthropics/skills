# DNSSEC, CAA, and Email Security

## DNSSEC Implementation

DNSSEC (DNS Security Extensions) provides cryptographic authentication of DNS responses, preventing attackers from redirecting your users to malicious sites by tampering with DNS queries. Think of it as a digital signature that proves the DNS response came from the legitimate source.

**How it protects you**: Without DNSSEC, attackers can intercept DNS queries and return fake IP addresses, redirecting users to malicious sites that look identical to yours. DNSSEC prevents this by cryptographically signing all DNS responses.

**Preconditions**: 
- Domain is using the provider's nameservers
- Registrar supports DS records
- If registrar supports CDS/CDNSKEY auto-publish, enable that if offered

**Practical setup**:

1) **Enable signing at DNS provider**
   - Turn on DNSSEC in the zone settings
   - Provider generates KSK (Key Signing Key) and ZSK (Zone Signing Key), signs the zone, and shows DS parameters:
     - **Key Tag**: Unique identifier for the key
     - **Algorithm**: Common options:
       - `13` (ECDSAP256SHA256) - Recommended
       - `8` (RSASHA256)
       - `15` (ECDSAP384SHA384)
     - **Digest Type**: 
       - `2` (SHA-256) - Recommended for widest compatibility
       - `4` (SHA-384)
     - **Digest**: Hex string of the hash

2) **Publish DS at registrar**
   - Create a DS record with the exact four fields above
   - Prefer Algorithm `13` (ECDSAP256SHA256) with Digest Type `2` (SHA-256) where supported
   - If both digest types 2 and 4 are offered, pick 2 for the widest compatibility

   Example registrar DS template:
   ```
   Owner: yourdomain.tld
   Key Tag: 2371
   Algorithm: 13
   Digest Type: 2
   Digest: 5C9F3E7B3F...A1C7
   ```

3) **Verify validation**
   - Wait for registrar DS propagation (can take minutes to hours)
   - Verify from a validating resolver using command-line tools:
     - `dig +dnssec example.com A` (check for AD flag in response)
     - `kdig +dnssec example.com A` (Knot DNS tool)
     - `drill -D example.com A` (LDNS tool)
   - For detailed analysis, use web tools:
     - [Verisign DNSSEC Analyzer](https://dnssec-analyzer.verisignlabs.com/yourdomain.org)
     - [DNSViz](https://dnsviz.net/d/yourdomain.org/analyze/)

4) **Monitor validation and changes**
   - Set up alerts for DS record changes at the registrar
   - Monitor DNSSEC validation status regularly
   - Watch for DNSKEY rollovers and ensure they complete successfully

**Security notes**:
- DNSSEC authenticates data; it does **not** encrypt queries. Use DoT (DNS over TLS) or DoH (DNS over HTTPS) for transport privacy if needed.
- Harden registrar accounts, protect transfer locks, and monitor for DS changes; DS removal downgrades protection.
- A hijacked registrar account can remove DS records, eliminating DNSSEC protection
- Add alerts on registrar activity to detect unauthorized changes

## CAA Records

Certificate Authority Authorization (CAA) records specify which Certificate Authorities (CAs) are allowed to issue SSL certificates for your domain. This prevents unauthorized certificate issuance, which attackers could use to create fake SSL certificates for your domain.

**How it protects you**: Without CAA records, any Certificate Authority can issue SSL certificates for your domain. Attackers could potentially obtain fake certificates and use them in sophisticated phishing attacks that appear to have valid SSL encryption.

Before setting CAA records, identify which CA issued your current certificate:
- **Command line**: `openssl s_client -connect yourdomain.com:443 -servername yourdomain.com | openssl x509 -noout -issuer`
- **Web tools**: [SSL Labs Server Test](https://www.ssllabs.com/ssltest/) provides comprehensive certificate analysis including issuer information
- **Browser**: Click the padlock icon → Certificate details → Issuer information

**Setup process**: Add CAA records to your DNS zone. Most DNS providers allow you to add these through their web interface:

```
# Allow only specific CAs to issue certificates
example.com. CAA 0 issue "letsencrypt.org"
example.com. CAA 0 issue "digicert.com"

# Send violation reports when unauthorized CAs attempt issuance
example.com. CAA 0 iodef "mailto:security@example.com"

# Control wildcard certificate issuance separately
example.com. CAA 0 issuewild "letsencrypt.org"

# Completely disable all certificate issuance (useful for non-web domains)
example.com. CAA 0 issue ";"
```

## Email Security Configuration

Email security records protect against email spoofing and phishing attacks. When your domain is compromised, attackers often change email settings to intercept password reset emails and other sensitive communications.

### SPF (Sender Policy Framework)

SPF records specify which mail servers are authorized to send emails on behalf of your domain. This prevents attackers from spoofing your domain in phishing emails.

**How it protects you**: Without SPF, anyone can send emails claiming to be from your domain. Attackers use this for sophisticated phishing campaigns that appear to come from your legitimate email address. 

This is particularly dangerous as attackers can impersonate executives or team members to target your own organization and users - imagine receiving a "urgent wire transfer" request from your CFO's email address, or your users getting a "mandatory wallet update" from your official support email.

**Setup**: Add an SPF record to your DNS zone:
```
example.com. TXT "v=spf1 include:_spf.google.com ~all"
```

### DKIM (DomainKeys Identified Mail)

DKIM adds a digital signature to your emails, allowing receiving servers to verify that emails actually came from your domain and haven't been tampered with.

**How it protects you**: DKIM signatures prove email authenticity and integrity, making it much harder for attackers to successfully spoof your domain in phishing campaigns.

**Setup**: Configure with your email provider and publish public keys in DNS (your email provider will provide the specific records).

### MTA-STS (Mail Transfer Agent Strict Transport Security)

MTA-STS enforces encrypted connections between mail servers, preventing man-in-the-middle attacks on email transmission.

**How it protects you**: Without MTA-STS, emails can be intercepted in transit. This is especially critical for password reset emails and other sensitive communications.

**Deployment steps**:

1) **Create the MTA-STS policy file**
   
   Host a plain text file at: `https://mta-sts./.well-known/mta-sts.txt`
   
   Policy file structure:
   ```
   version: STSv1
   mode: testing
   mx: smtp.example.com
   mx: alt1.smtp.example.com
   max_age: 86400
   ```
   
   **Mode options**:
   - `testing` - Monitor TLS failures but don't block mail (recommended to start)
   - `enforce` - Require TLS for mail delivery
   - `none` - Disable policy
   
   **Important**: List all your MX servers. Ensure they have valid TLS certificates matching their hostnames.

2) **Host the policy file over HTTPS**
   
   The file must be:
   - Publicly accessible at the exact path
   - Served over HTTPS with a valid certificate
   - Available 24/7 (use reliable hosting)

3) **Publish DNS TXT record**
   
   Create a TXT record at `_mta-sts.`:
   ```
   _mta-sts.example.com. TXT "v=STSv1; id=20250101000000"
   ```
   
   The `id` value (often a timestamp or version) signals mail servers to fetch the latest policy. Update it whenever you change the policy file.

4) **Testing and enforcement**
   - Start with `mode: testing` to monitor without blocking
   - Collect and review TLS failure reports
   - Once confident, change to `mode: enforce`
   - Update the `id` in DNS TXT record after policy changes

**Provider-specific tips**:
- **Google Workspace**: Manage MX in Admin console; host policy yourself; add TXT via DNS
- **Cloudflare**: Host policy on Workers/Pages; manage TXT in DNS; HTTPS auto via Cloudflare SSL
- **Amazon SES**: Host on S3 or CloudFront; manage TXT in Route 53; ensure domains are verified

**Security notes**:
- `max_age` determines how long mail servers cache the policy (86400 = 1 day)
- All MX servers must support TLS with valid certificates
- Monitor policy file availability - if unreachable, mail delivery may fail in enforce mode

### DMARC (Domain-based Message Authentication)

DMARC builds on SPF and DKIM to provide policy enforcement for email authentication. It tells receiving mail servers what to do with emails that fail authentication checks.

**How it protects you**: DMARC prevents email spoofing by instructing receiving servers to reject or quarantine emails that fail authentication, protecting your users from phishing attacks.

**Setup**: Add a DMARC record to your DNS zone:

**Baseline example (aggregate reports only)**:
```
_dmarc.example.com. TXT "v=DMARC1; p=reject; rua=mailto:dmarc@example.com"
```

**Report types**:
- **`rua=`** (Aggregate reports): Daily summaries of authentication results. This is the baseline and widely supported.
- **`ruf=`** (Failure reports): Real-time forensic reports for individual failures. Not recommended as they are:
  - Not widely supported by mail providers
  - Raise privacy concerns (contain message content/headers)
  - May not deliver reliably
  - Often unnecessary for monitoring purposes

**Recommendation**: Start with aggregate reports only (`rua=`). They provide sufficient visibility into authentication issues without the privacy and reliability concerns of failure reports.

---

