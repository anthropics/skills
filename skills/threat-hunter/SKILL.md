---
name: threat-hunter
description: Security intelligence aggregator. Analyzes IPs, domains, URLs, file hashes, and email addresses against multiple threat databases. Use when investigating security incidents, checking indicators of compromise (IOCs), analyzing suspicious IPs or domains, security research, checking if an IP is malicious, or threat intelligence gathering. Triggers on phrases like "is this IP malicious", "check this domain", "analyze this URL", "IOC analysis", "threat intelligence", "security check", "is this suspicious", "check for malware", "OSINT on IP", "investigate domain".
license: Complete terms in LICENSE.txt
allowed-tools: Bash(python:*) WebFetch
metadata:
  author: Maksim Soltan
  version: 1.0.0
  apis: ip-api.com, AbuseIPDB, VirusTotal, urlscan.io, Have I Been Pwned, NVD/NIST CVE
  auth: partial-some-apis-need-keys
---

# Threat Hunter

Multi-source security intelligence. Correlates signals across threat databases to generate IOC reports.

## APIs Used

**No auth required:**
- **ip-api.com**: `http://ip-api.com/json/{IP}` — geolocation, ASN, ISP (free, no auth)
- **NVD/NIST CVE**: `https://services.nvd.nist.gov/rest/json/cves/2.0` — vulnerability database
- **Shodan InternetDB**: `https://internetdb.shodan.io/{IP}` — open ports, vulns (no auth, limited)

**API key required (check if configured):**
- **AbuseIPDB**: `https://api.abuseipdb.com/api/v2/check` — IP abuse reports
- **VirusTotal**: `https://www.virustotal.com/api/v3/{resource_type}/{resource}` — multi-AV scan
- **urlscan.io**: `https://urlscan.io/api/v1/search/` — URL analysis
- **Have I Been Pwned**: `https://haveibeenpwned.com/api/v3/breachedaccount/{account}` — breach data

## IOC Type Detection

Parse user input to determine IOC type:
```
IPv4 regex: ^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$
IPv6 regex: contains colons, hex chars
Domain: contains dots, no slashes, not IP
URL: starts with http:// or https://
Hash MD5: 32 hex chars
Hash SHA1: 40 hex chars
Hash SHA256: 64 hex chars
Email: contains @
```

## Workflows by IOC Type

### IP Address Analysis

```python
scripts/threat_check.py --ioc 1.2.3.4 --type ip
```

**Step 1: Geolocation (no auth)**
```
GET http://ip-api.com/json/1.2.3.4?fields=status,message,country,regionName,city,isp,org,as,query,proxy,hosting
```

**Step 2: Shodan InternetDB (no auth)**
```
GET https://internetdb.shodan.io/1.2.3.4
```
Returns: open ports, known vulns, CPEs, tags (tor, vpn, etc.)

**Step 3: AbuseIPDB (if key available)**
```
GET https://api.abuseipdb.com/api/v2/check?ipAddress=1.2.3.4&maxAgeInDays=90&verbose
Header: Key: {ABUSEIPDB_API_KEY}
```

**Step 4: Score & classify**
```
Score 0-100:
- Shodan tags (tor, vpn, scanner): +30 each
- AbuseIPDB confidence > 50: +40
- Hosting provider / datacenter (not residential): +10
- Known malicious ASN: +20
```

### Domain Analysis

**Step 1: DNS resolution** (via ip-api for the resolved IP)
**Step 2: VirusTotal** (if key available)
```
GET https://www.virustotal.com/api/v3/domains/{DOMAIN}
Header: x-apikey: {VT_API_KEY}
```
**Step 3: urlscan.io search** (limited free search)
```
GET https://urlscan.io/api/v1/search/?q=domain:{DOMAIN}&size=5
```

### URL Analysis

**VirusTotal URL scan:**
```
POST https://www.virustotal.com/api/v3/urls
Body: url={URL}
```
Then poll:
```
GET https://www.virustotal.com/api/v3/analyses/{ANALYSIS_ID}
```

### Hash Analysis (VirusTotal)

```
GET https://www.virustotal.com/api/v3/files/{HASH}
Header: x-apikey: {VT_API_KEY}
```

### Email / Breach Check (HIBP)

```
GET https://haveibeenpwned.com/api/v3/breachedaccount/{EMAIL}
Header: hibp-api-key: {HIBP_KEY}
Header: User-Agent: threat-hunter
```

## Output Format

```
## Threat Intelligence Report
IOC: {VALUE} | Type: {TYPE}
Score: {N}/100 — {CLASSIFICATION}
Date: {DATE}

### Verdict
[CLEAN / SUSPICIOUS / MALICIOUS / UNKNOWN] — [1-sentence reason]

### Geolocation & Infrastructure
- Country: [X]
- ISP/ASN: [X]
- Hosting: [datacenter/residential/cloud]
- Tags: [tor, vpn, scanner, etc.]

### Open Ports (Shodan)
[port list if available]

### Threat Database Results
| Source | Result | Details |
|--------|--------|---------|
| AbuseIPDB | X reports | Confidence: X% |
| VirusTotal | X/Y detections | [engines] |
| Shodan | [tags] | [vulns] |

### Associated Infrastructure
[Related IPs/domains if found]

### Recommended Actions
- [Block/allow/investigate/monitor]
```

## API Key Configuration

Check environment variables:
```bash
echo $ABUSEIPDB_API_KEY
echo $VIRUSTOTAL_API_KEY
echo $URLSCAN_API_KEY
echo $HIBP_API_KEY
```

If not set, run no-auth checks only (Shodan InternetDB + ip-api + NVD) and note in output which sources were skipped.

## Error Handling

- API key missing: skip that source, note in output
- Rate limited: note which source hit limit, continue with others
- IOC not found in database: report as "not found" (not same as clean)
- Network timeout: retry once, then skip

## Examples

User: "Is 185.220.101.45 malicious?"
→ IP analysis: ip-api + Shodan + AbuseIPDB

User: "Check this domain: evil-phishing-site.ru"
→ Domain analysis: DNS + VirusTotal + urlscan.io

User: "Analyze this URL for malware: http://suspicious.site/download"
→ URL analysis: VirusTotal submission + urlscan.io

User: "Was my email compromised: user@domain.com"
→ HIBP breach lookup
