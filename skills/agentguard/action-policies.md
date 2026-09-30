# Action Evaluation Policies Reference

Detailed detector rules and policies for the `action` subcommand.

## Network Request Detector

### Webhook / Exfiltration Domains (auto-block if not in allowlist)

| Domain | Service |
|--------|---------|
| `discord.com` / `discordapp.com` | Discord webhooks |
| `api.telegram.org` | Telegram bot API |
| `hooks.slack.com` | Slack webhooks |
| `webhook.site` | Webhook testing |
| `requestbin.com` | Request inspection |
| `pipedream.com` | Workflow automation |
| `ngrok.io` / `ngrok-free.app` | Tunneling |
| `beeceptor.com` | API mocking |
| `mockbin.org` | HTTP mocking |

### High-Risk TLDs

`.xyz`, `.top`, `.tk`, `.ml`, `.ga`, `.cf`, `.gq`, `.work`, `.click`, `.link`

Domains with these TLDs are flagged as medium risk. POST/PUT to high-risk TLD escalates to high risk.

### Request Body Secret Scanning

Scan request body for sensitive data. Priority determines risk level:

| Secret Type | Priority | Risk Level | Decision |
|------------|----------|------------|----------|
| Private Key (`0x` + 64 hex) | 100 | critical | DENY |
| Mnemonic (12-24 BIP-39 words) | 100 | critical | DENY |
| SSH Private Key (`-----BEGIN.*PRIVATE KEY`) | 90 | critical | DENY |
| AWS Secret Key (`[A-Za-z0-9/+=]{40}` near AWS context) | 80 | high | CONFIRM |
| AWS Access Key (`AKIA[0-9A-Z]{16}`) | 70 | high | CONFIRM |
| GitHub Token (`gh[pousr]_[A-Za-z0-9_]{36,}`) | 70 | high | CONFIRM |
| Bearer/JWT Token (`ey[A-Za-z0-9-_]+\.ey[A-Za-z0-9-_]+`) | 60 | medium | CONFIRM |
| API Secret (generic `api.*secret` patterns) | 50 | medium | CONFIRM |
| DB Connection String (`(postgres|mysql|mongodb)://`) | 50 | medium | CONFIRM |
| Password in Config (`password\s*[:=]`) | 40 | low | CONFIRM |

### Network Decision Logic

1. Invalid URL -> DENY (high)
2. Domain in webhook list & not in allowlist -> DENY (high)
3. Body contains private key / mnemonic / SSH key -> DENY (critical)
4. Body contains other secrets -> risk based on priority
5. High-risk TLD & not in allowlist -> CONFIRM (medium)
6. POST/PUT to untrusted domain -> escalate medium to high
7. Domain in allowlist -> ALLOW (low)

## Command Execution Detector

### Dangerous Commands (always DENY, critical)

| Command | Risk |
|---------|------|
| `rm -rf` / `rm -fr` | Recursive delete |
| `mkfs` | Format filesystem |
| `dd if=` | Raw disk write |
| `:(){:\|:&};:` (and space variants) | Fork bomb (regex: `:\s*\(\s*\)\s*\{.*:\s*\|\s*:.*&.*\}`) |
| `chmod 777` / `chmod -R 777` | World-writable permissions |
| `> /dev/sda` | Disk overwrite |
| `mv /* ` | Move root contents |
| `wget\|sh` / `curl\|sh` | Download and execute |
| `wget\|bash` / `curl\|bash` | Download and execute |

### Sensitive Data Access (high)

| Command | Target |
|---------|--------|
| `cat /etc/passwd` | User database |
| `cat /etc/shadow` | Password hashes |
| `cat ~/.ssh` | SSH keys |
| `cat ~/.aws` | AWS credentials |
| `cat ~/.kube` | Kubernetes config |
| `cat ~/.npmrc` | npm auth tokens |
| `cat ~/.netrc` | Network credentials |
| `printenv` / `env` / `set` | All environment variables |

### System Modification Commands (medium)

`sudo`, `su`, `chown`, `chmod`, `chgrp`, `useradd`, `userdel`, `groupadd`, `passwd`, `visudo`, `systemctl`, `service`, `init`, `shutdown`, `reboot`, `halt`

### Network Commands (medium)

`curl`, `wget`, `nc`/`netcat`/`ncat`, `ssh`, `scp`, `rsync`, `ftp`, `sftp`

### Shell Injection Patterns (medium)

| Pattern | Description |
|---------|-------------|
| `; command` | Command separator |
| `\| command` | Pipe |
| `` `command` `` | Backtick execution |
| `$(command)` | Command substitution |
| `&& command` | Conditional chain |
| `\|\| command` | Or chain |

### Sensitive Environment Variables

Flag env vars containing: `API_KEY`, `SECRET`, `PASSWORD`, `TOKEN`, `PRIVATE`, `CREDENTIAL`

### Safe Command Allowlist

Commands matching the safe list are allowed without restriction, **unless** they contain shell metacharacters (`;`, `|`, `&`, `` ` ``, `$`, `(`, `)`, `{`, `}`) or access sensitive paths.

| Category | Commands |
|----------|----------|
| **Basic** | `ls`, `echo`, `pwd`, `whoami`, `date`, `hostname`, `uname`, `tree`, `du`, `df`, `sort`, `uniq`, `diff`, `cd` |
| **Read** | `cat`, `head`, `tail`, `wc`, `grep`, `find`, `which`, `type` |
| **File ops** | `mkdir`, `cp`, `mv`, `touch` |
| **Git** | `git status`, `git log`, `git diff`, `git branch`, `git show`, `git remote`, `git clone`, `git checkout`, `git pull`, `git fetch`, `git merge`, `git add`, `git commit`, `git push` |
| **Package managers** | `npm install`, `npm run`, `npm test`, `npm ci`, `npm start`, `npx`, `yarn`, `pnpm`, `pip install`, `pip3 install` |
| **Build & run** | `node`, `python`, `python3`, `tsc`, `go build`, `go run`, `go version`, `cargo build`, `cargo run`, `cargo test`, `make`, `rustc --version`, `java -version` |

### Exec Decision Logic

1. Matches fork bomb (regex) -> DENY (critical)
2. Matches dangerous command -> DENY (critical)
3. Matches safe command (no metacharacters, no sensitive paths) -> ALLOW (low)
4. Exec not allowed in capability model -> CONFIRM (non-critical) — balanced mode prompts user
5. Matches sensitive data access -> flag HIGH
6. Matches system command -> flag MEDIUM
7. Matches network command -> flag MEDIUM
8. Contains shell injection pattern -> flag MEDIUM
9. Sensitive env vars passed -> flag evidence

**Note**: In balanced mode, non-critical blocked commands (step 4) trigger a user prompt instead of a hard block. Only critical threats (steps 1-2) are always denied regardless of protection level.

## Default Policies

```
secret_exfil:
  private_key: DENY (always block)
  mnemonic: DENY (always block)
  api_secret: CONFIRM (require user approval)

exec_command: DENY (default, unless capability allows)

web3:
  unlimited_approval: CONFIRM
  unknown_spender: CONFIRM
  user_not_present: CONFIRM

network:
  untrusted_domain: CONFIRM
  body_contains_secret: DENY
```

## Capability Presets

### none (Most Restrictive)
```json
{
  "network_allowlist": [],
  "filesystem_allowlist": [],
  "exec": "deny",
  "secrets_allowlist": []
}
```

### read_only
```json
{
  "network_allowlist": [],
  "filesystem_allowlist": ["./**"],
  "exec": "deny",
  "secrets_allowlist": []
}
```

### trading_bot
```json
{
  "network_allowlist": [
    "api.binance.com", "api.bybit.com", "api.okx.com",
    "api.coinbase.com", "*.dextools.io", "*.coingecko.com"
  ],
  "filesystem_allowlist": ["./config/**", "./logs/**"],
  "exec": "deny",
  "secrets_allowlist": ["*_API_KEY", "*_API_SECRET"],
  "web3": {
    "chains_allowlist": [1, 56, 137, 42161],
    "rpc_allowlist": ["*"],
    "tx_policy": "confirm_high_risk"
  }
}
```

### defi
```json
{
  "network_allowlist": ["*"],
  "filesystem_allowlist": [],
  "exec": "deny",
  "secrets_allowlist": [],
  "web3": {
    "chains_allowlist": [1, 56, 137, 42161, 10, 8453, 43114],
    "rpc_allowlist": ["*"],
    "tx_policy": "confirm_high_risk"
  }
}
```

## GoPlus Integration

The `action-cli.ts decide` command integrates with the [GoPlus Security API](https://docs.gopluslabs.io/) for enhanced Web3 action evaluation. GoPlus provides three checks:

| Check | Description | Triggers |
|-------|-------------|----------|
| **Phishing Site Detection** | Checks if the transaction origin URL is a known phishing site | `PHISHING_ORIGIN` → DENY (critical) |
| **Address Security** | Checks if the target address is blacklisted, associated with phishing, stealing attacks, or honeypots | `MALICIOUS_ADDRESS` → DENY (critical), `HONEYPOT_RELATED` → flag (high) |
| **Transaction Simulation** | Simulates the transaction to detect balance changes, approval changes, and risk indicators | `UNLIMITED_APPROVAL` → CONFIRM (high), `SIMULATION_FAILED` → flag (medium) |

### Environment Variables

```
GOPLUS_API_KEY=your_key         # Required for simulation
GOPLUS_API_SECRET=your_secret   # Required for simulation
```

Phishing site detection and address security checks work without API keys. Transaction simulation requires configured credentials.

### Degradation Strategy

When GoPlus is unavailable (no API keys, network errors, rate limiting):

1. The `SIMULATION_UNAVAILABLE` or `SIMULATION_FAILED` risk tag is set
2. Phishing and address checks that fail are silently skipped
3. The decision falls back to **policy-based rules only** (capability model, webhook detection, secret scanning)
4. For `web3_tx` and `web3_sign` without GoPlus, the skill should apply prompt-based rules and note the limitation in the output
