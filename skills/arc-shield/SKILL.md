---
name: arc-shield
version: 1.0.0
category: security
tags: [security, sanitization, secrets, output-filter, privacy]
requires: [bash, python3]
author: OpenClaw
description: Output sanitization for agent responses - prevents accidental secret leaks
---

# arc-shield

**Output sanitization for agent responses.** Scans ALL outbound messages for leaked secrets, tokens, keys, passwords, and PII before they leave the agent.

⚠️ **This is NOT an input scanner** — `clawdefender` already handles that. This is an **OUTPUT filter** for catching things your agent accidentally includes in its own responses.

## Why You Need This

Agents have access to sensitive data: 1Password vaults, environment variables, config files, wallet keys. Sometimes they accidentally include these in responses when:
- Debugging and showing full command output
- Copying file contents that contain secrets
- Generating code examples with real credentials
- Summarizing logs that include tokens

Arc-shield catches these leaks before they reach Discord, Signal, X, or any external channel.

## What It Detects

### 🔴 CRITICAL (blocks in `--strict` mode)
- **API Keys & Tokens**: 1Password (`ops_*`), GitHub (`ghp_*`), OpenAI (`sk-*`), Stripe, AWS, Bearer tokens
- **Passwords**: Assignments like `password=...` or `passwd: ...`
- **Private Keys**: Ethereum (0x + 64 hex), SSH keys, PGP blocks
- **Wallet Mnemonics**: 12/24 word recovery phrases
- **PII**: Social Security Numbers, credit card numbers
- **Platform Tokens**: Slack, Telegram, Discord

### 🟠 HIGH (warns loudly)
- **High-entropy strings**: Shannon entropy > 4.5 for strings > 16 chars (catches novel secret patterns)
- **Credit cards**: 16-digit card numbers
- **Base64 credentials**: Long base64 strings that look like tokens

### 🟡 WARN (informational)
- **Secret file paths**: `~/.secrets/*`, paths containing "password", "token", "key"
- **Environment variables**: `ENV_VAR=secret_value` exports
- **Database URLs**: Connection strings with credentials

## Installation

```bash
cd ~/.openclaw/workspace/skills
git clone <arc-shield-repo> arc-shield
chmod +x arc-shield/scripts/*.sh arc-shield/scripts/*.py
```

Or download as a skill bundle.

## Usage

### Command-line

```bash
# Scan agent output before sending
agent-response.txt | arc-shield.sh

# Block if critical secrets found (use before external messaging)
echo "Message text" | arc-shield.sh --strict || echo "BLOCKED"

# Redact secrets and return sanitized text
cat response.txt | arc-shield.sh --redact

# Full report
arc-shield.sh --report < conversation.log

# Python version with entropy detection
cat message.txt | output-guard.py --strict
```

### Integration with OpenClaw Agents

#### Pre-send hook (recommended)

Add to your messaging skill or wrapper:

```bash
#!/bin/bash
# send-message.sh wrapper

MESSAGE="$1"
CHANNEL="$2"

# Sanitize output
SANITIZED=$(echo "$MESSAGE" | arc-shield.sh --strict --redact)
EXIT_CODE=$?

if [[ $EXIT_CODE -eq 1 ]]; then
    echo "ERROR: Message contains critical secrets and was blocked." >&2
    exit 1
fi

# Send sanitized message
openclaw message send --channel "$CHANNEL" "$SANITIZED"
```

#### Manual pipe

Before any external message:

```bash
# Generate response
RESPONSE=$(agent-generate-response)

# Sanitize
CLEAN=$(echo "$RESPONSE" | arc-shield.sh --redact)

# Send
signal send "$CLEAN"
```

### Testing

```bash
cd skills/arc-shield/tests
./run-tests.sh
```

Includes test cases for:
- Real leaked patterns (1Password tokens, Instagram passwords, wallet mnemonics)
- False positive prevention (normal URLs, email addresses, file paths)
- Redaction accuracy
- Strict mode blocking

## Configuration

Patterns are defined in `config/patterns.conf`:

```conf
CRITICAL|GitHub PAT|ghp_[a-zA-Z0-9]{36,}
CRITICAL|OpenAI Key|sk-[a-zA-Z0-9]{20,}
WARN|Secret Path|~\/\.secrets\/[^\s]*
```

Edit to add custom patterns or adjust severity levels.

## Modes

| Mode | Behavior | Exit Code | Use Case |
|------|----------|-----------|----------|
| Default | Pass through + warnings to stderr | 0 | Development, logging |
| `--strict` | Block on CRITICAL findings | 1 if critical | Production outbound messages |
| `--redact` | Replace secrets with `[REDACTED:TYPE]` | 0 | Safe logging, auditing |
| `--report` | Analysis only, no pass-through | 0 | Auditing conversations |

## Entropy Detection

The Python version (`output-guard.py`) includes Shannon entropy analysis to catch secrets that don't match regex patterns:

```python
# Detects high-entropy strings like:
kJ8nM2pQ5rT9vWxY3zA6bC4dE7fG1hI0  # Novel API key format
Zm9vOmJhcg==                      # Base64 credentials
```

Threshold: **4.5 bits** (configurable with `--entropy-threshold`)

## Performance

- **Bash version**: ~10ms for typical message (< 1KB)
- **Python version**: ~50ms with entropy analysis
- **Zero external dependencies**: bash + Python stdlib only

Fast enough to run on every outbound message without noticeable delay.

## Real-World Catches

From our own agent sessions:

```bash
# 1Password token
"ops_eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9..."

# Instagram password in debug output
"instagram login: user@example.com / MyInsT@Gr4mP4ss!"

# Wallet mnemonic in file listing
"cat ~/.secrets/wallet-recovery-phrase.txt
abandon ability able about above absent absorb abstract..."

# GitHub PAT in git config
"[remote "origin"]
url = https://ghp_abc123:@github.com/user/repo"
```

All blocked by arc-shield before reaching external channels.

## Best Practices

1. **Always use `--strict` for external messages** (Discord, Signal, X, email)
2. **Use `--redact` for logs** you want to review later
3. **Run tests after adding custom patterns** to check for false positives
4. **Pipe through both** bash and Python versions for maximum coverage:
   ```bash
   message | arc-shield.sh --strict | output-guard.py --strict
   ```
5. **Don't rely on this alone** — educate your agent to avoid including secrets in the first place (see AGENTS.md output sanitization directive)

## Limitations

- **Context-free**: Can't distinguish between "here's my password: X" (bad) and "set your password to X" (instruction)
- **No semantic understanding**: Won't catch "my token is in the previous message"
- **Pattern-based**: New secret formats require pattern updates

Use in combination with agent instructions and careful prompt engineering.

## Integration Example

Full OpenClaw agent integration:

```bash
# In your agent's message wrapper
send_external_message() {
    local message="$1"
    local channel="$2"
    
    # Pre-flight sanitization
    if ! echo "$message" | arc-shield.sh --strict > /dev/null 2>&1; then
        echo "ERROR: Message blocked by arc-shield (contains secrets)" >&2
        return 1
    fi
    
    # Double-check with entropy detection
    if ! echo "$message" | output-guard.py --strict > /dev/null 2>&1; then
        echo "ERROR: High-entropy secret detected" >&2
        return 1
    fi
    
    # Safe to send
    openclaw message send --channel "$channel" "$message"
}
```

## Troubleshooting

**False positives on normal text:**
- Adjust entropy threshold: `output-guard.py --entropy-threshold 5.0`
- Edit `config/patterns.conf` to refine regex patterns
- Add exceptions to the pattern file

**Secrets not detected:**
- Check pattern file for coverage
- Run with `--report` to see what's being scanned
- Test with `tests/run-tests.sh` using your sample
- Consider lowering entropy threshold (but watch for false positives)

**Performance issues:**
- Use bash version only (skip entropy detection)
- Limit input size with `head -c 10000`
- Run in background: `arc-shield.sh --report &`

## Contributing

Add new patterns to `config/patterns.conf` following the format:

```
SEVERITY|Category Name|regex_pattern
```

Test with `tests/run-tests.sh` before deploying.

## License

MIT — use freely, protect your secrets.

---

**Remember**: Arc-shield is your safety net, not your strategy. Train your agent to never include secrets in responses. This tool catches mistakes, not malice.
