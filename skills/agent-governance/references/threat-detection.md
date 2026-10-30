```python
PROMPT_INJECTION_PATTERNS = [
    r"ignore\s+(all\s+)?previous\s+instructions",
    r"disregard\s+(your\s+)?(system\s+)?prompt",
    r"override\s+(your\s+)?(previous\s+)?instructions",
    r"you\s+are\s+now\s+(?:a\s+)?(?:different|new|another)",
    r"act\s+as\s+if\s+you\s+have\s+no\s+restrictions",
    r"pretend\s+you\s+(?:have\s+no|don't\s+have)",
    r"forget\s+everything\s+(?:above|before|previously)",
    r"new\s+instructions?\s*:",
    r"system\s*:\s*(ignore|override|disregard)",
    r"\[INST\].*?\[/INST\]",                      # llama injection
    r"<\|system\|>.*?<\|end\|>",                  # chatml injection
]
```

### Data Exfiltration

Patterns that attempt to send data outside the agent's environment:

```python
EXFILTRATION_PATTERNS = [
    r"curl\s+.{0,100}https?://(?!trusted-domain\.com)",
    r"wget\s+.{0,100}https?://(?!trusted-domain\.com)",
    r"send\s+(all\s+)?(data|results?|output|files?)\s+to\s+https?://",
    r"POST\s+.{0,100}https?://",
    r"base64\s+.+\|\s*(curl|wget|nc|netcat)",
    r"nc\s+-e\s+/bin/",                           # reverse shell
    r"/dev/tcp/",                                  # bash TCP redirect
    r"python\s+-c\s+.{0,200}socket",              # python socket shell
]
```

### Privilege Escalation

Patterns that attempt to gain elevated permissions:

```python
PRIVILEGE_ESCALATION_PATTERNS = [
    r"\bsudo\s+",
    r"chmod\s+(777|[0-7]{3,4}\s+/)",
    r"chown\s+root",
    r"/etc/sudoers",
    r"setuid|setgid",
    r"pkexec",
    r"doas\s+",
]
```

### Severity Classification

| Threat Type | Default Severity | Block or Alert? |
|------------|-----------------|-----------------|
| Prompt injection | Critical | Always block |
| Data exfiltration | Critical | Always block |
| Dangerous commands (rm -rf, DROP TABLE) | Critical | Always block |
| Privilege escalation | High | Block in production |
| PII in unexpected fields | Medium | Alert + log |
| Unusual argument lengths | Low | Log only |

## Adding Custom Patterns

```python
# Extend the pattern library for your domain
CUSTOM_PATTERNS = {
    ThreatType.DATA_EXFILTRATION: {
        "patterns": [
            r"send\s+to\s+https?://evil\.com",
            r"upload\s+to\s+s3://untrusted-bucket",
        ],
        "severity": "critical",
    }
}
THREAT_PATTERNS.update(CUSTOM_PATTERNS)