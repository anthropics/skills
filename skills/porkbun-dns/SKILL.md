---
name: porkbun-dns
description: DNS and domain management CLI for Porkbun registrar. Use when (1) managing DNS records (A, AAAA, CNAME, MX, TXT, etc), (2) listing and configuring domains, (3) setting up URL forwarding, (4) bulk importing/exporting DNS configurations, or (5) automating DNS operations.
license: MIT
---

# Porkbun DNS Management

CLI toolkit for managing domains and DNS records through the Porkbun API. Supports all DNS record types, URL forwarding, bulk operations, and interactive mode.

## Helper Scripts Available

- `scripts/dns.py` - DNS record management (list, create, edit, delete)
- `scripts/domain.py` - Domain listing and information
- `scripts/url.py` - URL forwarding configuration
- `scripts/bulk.py` - Bulk import/export operations
- `scripts/configure.py` - API credential configuration

**Always run scripts with `--help` first** to see usage.

## Setup

### API Credentials
1. Log into Porkbun account
2. Go to Account → API Access
3. Generate API key and Secret API key
4. Configure credentials:

```bash
python scripts/configure.py
# Or manually create ~/.config/porkbun-cli/config.json
```

### Configuration File
```json
{
  "apikey": "pk1_your_api_key",
  "secretapikey": "sk1_your_secret_key"
}
```

## Quick Start

### List Domains
```bash
python scripts/domain.py list
```

### List DNS Records
```bash
python scripts/dns.py list example.com
```

### Create DNS Record
```bash
# A record
python scripts/dns.py create example.com A 192.168.1.1

# CNAME record
python scripts/dns.py create example.com CNAME target.example.com --name www

# MX record
python scripts/dns.py create example.com MX mail.example.com --prio 10

# TXT record (SPF)
python scripts/dns.py create example.com TXT "v=spf1 include:_spf.google.com ~all"
```

### Delete DNS Record
```bash
python scripts/dns.py delete example.com RECORD_ID
```

## DNS Record Types

| Type | Description | Example Content |
|------|-------------|-----------------|
| A | IPv4 address | 192.168.1.1 |
| AAAA | IPv6 address | 2001:db8::1 |
| CNAME | Canonical name | target.example.com |
| ALIAS | ANAME record | target.example.com |
| MX | Mail exchange | mail.example.com |
| TXT | Text record | v=spf1 ... |
| NS | Nameserver | ns1.porkbun.com |
| SRV | Service record | 10 5 5060 sip.example.com |
| CAA | CA Authorization | 0 issue "letsencrypt.org" |
| TLSA | TLS Authentication | 3 1 1 abc123... |

## URL Forwarding

### List Forwards
```bash
python scripts/url.py list example.com
```

### Create Forward
```bash
# Simple redirect
python scripts/url.py set example.com https://newsite.com

# Subdomain redirect
python scripts/url.py set example.com https://newsite.com --subdomain old

# With wildcard
python scripts/url.py set example.com https://newsite.com --wildcard

# Permanent (301) redirect
python scripts/url.py set example.com https://newsite.com --type 301
```

### Delete Forward
```bash
python scripts/url.py delete example.com FORWARD_ID
```

## Bulk Operations

### Export DNS Records
```bash
# Export to JSON
python scripts/bulk.py export example.com -o records.json

# Export to CSV
python scripts/bulk.py export example.com -o records.csv --format csv
```

### Import DNS Records
```bash
# Import from JSON
python scripts/bulk.py import records.json --domain example.com

# Import from CSV
python scripts/bulk.py import records.csv --domain example.com

# Dry run (preview changes)
python scripts/bulk.py import records.json --domain example.com --dry-run
```

### Import File Format (JSON)
```json
{
  "domain": "example.com",
  "records": [
    {
      "type": "A",
      "name": "",
      "content": "192.168.1.1",
      "ttl": 600
    },
    {
      "type": "CNAME",
      "name": "www",
      "content": "example.com"
    }
  ]
}
```

### Import File Format (CSV)
```csv
type,name,content,prio,ttl
A,,192.168.1.1,,600
CNAME,www,example.com,,
MX,,mail.example.com,10,
```

## Common Options

```bash
--name, -n      Subdomain name (empty for root)
--prio, -p      Priority (for MX, SRV records)
--ttl, -t       TTL in seconds (default: 600)
--type          Record type (A, AAAA, CNAME, etc.)
--output, -o    Output file for exports
--format, -f    Output format (json, csv)
--dry-run       Preview changes without applying
```

## Common Workflows

### Set Up Email (Google Workspace)
```bash
# MX records
python scripts/dns.py create example.com MX aspmx.l.google.com --prio 1
python scripts/dns.py create example.com MX alt1.aspmx.l.google.com --prio 5
python scripts/dns.py create example.com MX alt2.aspmx.l.google.com --prio 5

# SPF record
python scripts/dns.py create example.com TXT "v=spf1 include:_spf.google.com ~all"

# DKIM (get value from Google Admin)
python scripts/dns.py create example.com TXT "v=DKIM1; k=rsa; p=..." --name google._domainkey
```

### Set Up Subdomain
```bash
# Point subdomain to server
python scripts/dns.py create example.com A 192.168.1.1 --name app

# Or use CNAME to another domain
python scripts/dns.py create example.com CNAME app.railway.app --name app
```

### Migrate DNS
```bash
# Export from current domain
python scripts/bulk.py export oldsite.com -o dns_backup.json

# Review and edit the JSON if needed
# Import to new domain
python scripts/bulk.py import dns_backup.json --domain newsite.com --dry-run
python scripts/bulk.py import dns_backup.json --domain newsite.com
```

## Environment Variables

```bash
# Alternative to config file
export PORKBUN_API_KEY=pk1_your_key
export PORKBUN_SECRET_KEY=sk1_your_secret
```

## Troubleshooting

**"API key required"**: Run `python scripts/configure.py` to set credentials

**"Domain not found"**: Ensure domain is registered with Porkbun and API access is enabled

**"Invalid record type"**: Check supported types (A, AAAA, CNAME, MX, TXT, NS, SRV, CAA, TLSA, ALIAS, HTTPS, SVCB, SSHFP)

**"Rate limited"**: Porkbun has rate limits; add delays between bulk operations

## API Reference

Porkbun API documentation: https://porkbun.com/api/json/v3/documentation

## Security Notes

- Store API keys securely (config file is chmod 600)
- Never commit credentials to version control
- Use environment variables in CI/CD pipelines
- Rotate keys periodically
