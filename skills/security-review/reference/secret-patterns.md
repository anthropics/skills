# Secret & Credential Detection Patterns

Load this file during Step 3 (Secrets & Exposure Scan).

---

## High-Confidence Secret Patterns

These patterns almost always indicate a real secret:

### API Keys & Tokens
```regex
# OpenAI
sk-[a-zA-Z0-9]{48}

# Anthropic
sk-ant-[a-zA-Z0-9\-_]{90,}

# AWS Access Key
AKIA[0-9A-Z]{16}

# AWS Secret Key (look for near AWS_ACCESS_KEY_ID assignment)
[0-9a-zA-Z/+]{40}

# GitHub Token
gh[pousr]_[a-zA-Z0-9]{36,}
github_pat_[a-zA-Z0-9]{82}

# Stripe
sk_live_[a-zA-Z0-9]{24,}
rk_live_[a-zA-Z0-9]{24,}

# Twilio
AC[a-z0-9]{32}  (Account SID)
SK[a-z0-9]{32}  (API Key)

# SendGrid
SG\.[a-zA-Z0-9\-_.]{66}

# Slack
xoxb-[0-9]+-[0-9]+-[a-zA-Z0-9]+
xoxp-[0-9]+-[0-9]+-[0-9]+-[a-zA-Z0-9]+
xapp-[0-9]+-[A-Z0-9]+-[0-9]+-[a-zA-Z0-9]+

# Google API Key
AIza[0-9A-Za-z\-_]{35}

# Google OAuth
[0-9]+-[0-9A-Za-z_]{32}\.apps\.googleusercontent\.com

# Cloudflare
[a-zA-Z0-9_\-]{37}  (near CF_API_TOKEN)

# Mailgun
key-[a-zA-Z0-9]{32}

# Heroku
[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}
```

### Private Keys
```regex
-----BEGIN (RSA |EC |OPENSSH |DSA |PGP )?PRIVATE KEY( BLOCK)?-----
-----BEGIN CERTIFICATE-----
```

### Database Connection Strings
```regex
# MongoDB
mongodb(\+srv)?:\/\/[^:]+:[^@]+@

# PostgreSQL / MySQL
(postgres|postgresql|mysql):\/\/[^:]+:[^@]+@

# Redis with password
redis:\/\/:[^@]+@

# Generic connection string with password
(connection[_-]?string|connstr|db[_-]?url).*password=
```

### Hardcoded Passwords (variable name signals)
```regex
# Variable names that suggest secrets
(password|passwd|pwd|secret|api_key|apikey|auth_token|access_token|private_key)
  \s*[=:]\s*["'][^"']{8,}["']
```

---

## Entropy-Based Detection

Apply to string literals > 20 characters in assignment context.
High entropy (Shannon entropy > 4.5 bits/char) + length > 20 = likely secret.

```
Calculate entropy: -sum(p * log2(p)) for each character frequency p
Threshold: > 4.5 bits/char AND > 20 chars AND assigned to a variable
```

Common false positives to exclude:
- Lorem ipsum text
- HTML/CSS content
- Base64-encoded non-sensitive config (but flag and note)
- UUID/GUID (entropy is high but format is recognizable)

---

## Files That Should Never Be Committed

Flag if these files exist in the repo root or are tracked by git:
```
.env
.env.local
.env.production
.env.staging
*.pem
*.key
*.p12
*.pfx
id_rsa
id_ed25519
credentials.json
service-account.json
gcp-key.json
secrets.yaml
secrets.json
config/secrets.yml
```

Also check `.gitignore` — if a secret file pattern is NOT in .gitignore, flag it.

---

## CI/CD & IaC Secret Risks

### GitHub Actions — flag these patterns:
```yaml
# Hardcoded values in env: blocks (should use ${{ secrets.NAME }})
env:
  API_KEY: "actual-value-here"   # VULNERABLE

# Printing secrets
- run: echo ${{ secrets.MY_SECRET }}   # leaks to logs
```

### Docker — flag these:
```dockerfile
# Secrets in ENV (persisted in image layers)
ENV AWS_SECRET_KEY=actual-value

# Secrets passed as build args (visible in image history)
ARG API_KEY=actual-value
```

### Terraform — flag these:
```hcl
# Hardcoded sensitive values (should use var or data source)
password = "hardcoded-password"
access_key = "AKIAIOSFODNN7EXAMPLE"
```

---

## Safe Patterns (Do NOT flag)

These are intentional placeholders — recognize and skip:
```
"your-api-key-here"
"<YOUR_API_KEY>"
"${API_KEY}"
"${process.env.API_KEY}"
"os.environ.get('API_KEY')"
"REPLACE_WITH_YOUR_KEY"
"xxx...xxx"
"sk-..." (in documentation/comments)
```
