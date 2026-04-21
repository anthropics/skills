# Monitoring, Alerts, and Incident Response

## DNS Record Monitoring

DNS record monitoring involves continuously checking your domain's DNS records for unauthorized changes. Attackers often modify DNS records to redirect traffic to malicious servers while keeping your site partially functional.

**What to watch for**:
- **Nameserver (NS) record changes**: Attackers change your nameservers to point to their own DNS servers, giving them complete control over all DNS records
- **Sudden TTL drops**: Very low TTLs *can* indicate preparation for rapid DNS changes during an attack
  - **Note**: Low TTL is common and legitimate with CDNs and auto-scaling contexts; Cloudflare "Auto" is often 300s
  - **Context**: Cloudflare allows TTL 30-60s for [unproxied records](https://developers.cloudflare.com/dns/manage-dns-records/reference/ttl/); this is not inherently malicious
  - **Monitor for**: *Unexpected* drops from higher values or drops combined with other suspicious activity
- **CAA record removal or overrides**: Allows any Certificate Authority to issue certificates for your domain
  - **Note**: Child zones override parent CAA records
  - **Advanced monitoring**: Watch for parameters like `accounturi` and `validationmethods` which provide finer control over certificate issuance
- **DNSSEC disabled unexpectedly**: Removes cryptographic protection from DNS responses

**If nameservers remain unchanged, also monitor**:
- **A/AAAA record modifications**: IP address changes could redirect users to malicious sites
- **MX record modifications**: Email server changes could intercept password reset emails
- **TXT record changes**: Could affect email security (SPF/DMARC) or domain validation

**Monitoring tools** (continuous change tracking):
- [MXToolbox](https://mxtoolbox.com/) - Comprehensive DNS record monitoring and alerts
- [HetrixTools](https://hetrixtools.com/) - Free DNS monitoring with email alerts
- [SecurityTrails](https://securitytrails.com/) - Historical DNS data and change tracking

**Analysis and debugging tools**:
- [DNSViz](https://dnsviz.net/) - DNSSEC chain validation and debugging
- [DNS Dumpster](https://dnsdumpster.com/) - DNS reconnaissance and record discovery

**GitOps and zone control**:
- [OctoDNS](https://github.com/octodns/octodns) - Infrastructure-as-code for DNS; manage zones via code with auditable, reviewed changes through CI/CD
- [DNSControl](https://github.com/StackExchange/dnscontrol) - Synchronize DNS across multiple providers; declarative configuration with version control

**Note**: If attackers change your NS records, they control everything. But attackers with DNS panel access might make subtle changes without touching NS records to avoid detection, which is why monitoring individual record types remains important.

## Certificate Transparency Monitoring

Certificate Transparency (CT) logs are public records of all SSL certificates issued by Certificate Authorities. Monitoring these logs helps detect unauthorized certificate issuance.

**Why it matters**: Attackers sometimes obtain fake SSL certificates for legitimate domains to make phishing sites appear more credible. CT monitoring helps you detect these certificates before they're used in attacks.

**Setup and tools**:
- [crt.sh](https://crt.sh/) - Search and monitor CT logs for your domain
- [Cert Spotter](https://sslmate.com/certspotter/) - Free CT monitoring with API access
- Watch for wildcard certificates if you don't use them (could indicate broader compromise)

## Passive DNS Monitoring

Passive DNS monitoring tracks historical DNS resolution data across the internet, helping you detect brief changes that might be missed by periodic checks.

**What it detects**:
- **Brief record changes**: Attackers often make quick changes to avoid detection
- **Geographic anomalies**: DNS records resolving to unexpected countries or regions
- **Suspicious hosting provider changes**: Sudden switches to hosting providers known for malicious activity

**Tools for passive DNS**:
- [PassiveTotal (RiskIQ)](https://community.riskiq.com/) - Comprehensive passive DNS database
- [Mnemonic Passive DNS](https://passivedns.mnemonic.no/) - Free passive DNS lookup
- [SecurityTrails](https://securitytrails.com/) - Historical DNS and WHOIS data

## Setting Up Alerts

### Critical Alerts (Immediate Response Required)

1. **Registrar Changed**
   - **What it monitors**: Changes to your domain's registrar
   - **Why it's critical**: Indicates potential domain hijacking or unauthorized transfer
   - **Response**: Immediate verification and potential incident response activation

2. **Nameserver Changed** 
   - **What it monitors**: Changes to nameserver records
   - **Why it's critical**: Attackers often change nameservers to redirect traffic to malicious servers
   - **Response**: Verify legitimacy, check if you initiated the change

3. **DNSSEC Broken**
   - **What it monitors**: DNSSEC validation failures or disabled DNSSEC
   - **Why it's critical**: DNS responses can be tampered with, leading to man-in-the-middle attacks
   - **Response**: Investigate signing issues, check for configuration changes

4. **CAA Records Removed or Overridden**
   - **What it monitors**: Removal of Certificate Authority Authorization records or child zone overrides
   - **Why it's critical**: Allows any CA to issue certificates for your domain, enabling SSL certificate attacks
   - **Response**: Restore CAA records immediately, investigate who removed them
   - **Note**: Child zones override parent CAA; parameters like `accounturi` and `validationmethods` can provide finer control

5. **Unexpected TTL Drops**
   - **What it monitors**: Sudden TTL drops from higher values
   - **Why it's important**: Can indicate preparation for rapid DNS changes (attack preparation)
   - **Context**: Low TTL (30-300s) is normal for CDNs and auto-scaling; Cloudflare allows 30-60s for [unproxied records](https://developers.cloudflare.com/dns/manage-dns-records/reference/ttl/)
   - **Response**: Investigate *unexpected* drops or drops combined with other suspicious activity; verify if legitimate infrastructure changes

### High Priority Alerts (When NS Unchanged)

1. **A Record Changed**
   - **What it monitors**: IP redirects without NS changes
   - **Why it's important**: Could redirect users to malicious servers
   - **Response**: Verify the new IP address is legitimate and expected

2. **MX Record Changed**
   - **What it monitors**: Changes to mail server configurations
   - **Why it's important**: Could intercept emails, including password reset messages
   - **Response**: Verify mail server changes are authorized

3. **DMARC Policy Weakened**
   - **What it monitors**: Changes from "reject" to "quarantine" or "none"
   - **Why it's important**: Weaker policies allow more spoofed emails to reach users
   - **Response**: Investigate why policy was weakened, restore if unauthorized

4. **Unexpected Certificate Issued**
   - **What it monitors**: New SSL certificates issued for your domain
   - **Why it's important**: Could indicate certificate-based attacks or unauthorized issuance
   - **Response**: Verify the certificate was requested by your team, revoke if unauthorized

## Incident Response Plan

### Immediate Response
1. **Verify the compromise** - Check DNS records via multiple resolvers
2. **Access registrar account** - Attempt login, check for lockout
3. **Contact registrar security team** - Use pre-documented emergency contacts
4. **Document everything** - Screenshot all current settings

### Containment
1. **Invoke registry lock** if available
2. **Update NS records** if you maintain access
3. **Warn users** via social media/status page
4. **Contact law enforcement** if significant theft occurred

### Recovery
1. **Regain control** through registrar security procedures
2. **Audit all DNS records** against known-good baseline
3. **Reset all credentials** for registrar and DNS hosting
4. **Review access logs** to understand attack vector

### Post-Incident
1. **Conduct thorough investigation**
2. **Update security measures** based on lessons learned
3. **Consider legal action** if appropriate
4. **Publish transparency report** to rebuild trust

---

